mod bigint;

use bigint::SimpleBigint;

use lazy_static::lazy_static;
use num_bigint::BigUint;
use rand::Rng;
use subtle::{ConditionallySelectable, ConstantTimeLess};

/// The prime modulus used in ML-KEM
const MLKEM_Q: u16 = 3329;

pub fn rand_vec<const N: usize>(rng: &mut impl Rng) -> [u16; N] {
    let mut out = [0u16; N];
    for coeff in out.iter_mut().rev() {
        *coeff = rng.gen::<u16>() % MLKEM_Q;
    }

    out
}

/// Attempts to run the Kemeleon encoding for the given NTT vector. Top few bits
/// get set to random.
pub fn vector_encode<const N: usize>(rng: &mut impl Rng, v: &[u16; N]) -> Option<Vec<u8>> {
    // Compute Σᵢ qⁱ vᵢ
    let mut sum = BigUint::ZERO;

    for coeff in v.iter() {
        sum *= MLKEM_Q;
        sum += *coeff;
    }

    // Check if the top bit is set. If not, then this input can be encoded
    // Top bit (0-indexed) is ⌈log₂(q^N + 1)⌉ - 1
    let top_bit_idx = ((N as f64) * (MLKEM_Q as f64).log2()).ceil() as u64 - 1;
    // Need to pad to a byte boundary
    let next_byte_boundary = top_bit_idx + (8 - (top_bit_idx % 8) % 8);

    if !sum.bit(top_bit_idx) {
        // We need the number of bits to be a multiple of 8. So set the remaining bits to
        // random values
        for i in top_bit_idx..next_byte_boundary {
            sum.set_bit(i, rng.gen());
        }
        Some(sum.to_bytes_be())
    } else {
        None
    }
}

// Rather than dividing x by q (or a power thereof), we can multiply x by ⌊2^u / q⌋ for
// sufficiently large u, then divide by 2^u (ie right-shift by u)
// In addition, rather than using the same u for every x, we can use
// smaller u for smaller x.
lazy_static! {
    static ref QPOWS: Vec<BigUint> = (0..10)
        .map(|i| BigUint::from(MLKEM_Q).pow(2u32.pow(i)))
        .collect();
    static ref TWOQPOWS: Vec<BigUint> = QPOWS.iter().map(|x| 2u8 * x).collect();
    static ref US: Vec<u32> = QPOWS
        .iter()
        .map(|qpow| 2 * (qpow.bits() + 1) as u32)
        .collect();
    static ref TWOPOWUS: Vec<BigUint> = US.iter().map(|u| BigUint::from(2u8).pow(*u)).collect();
    static ref SCALEDQPOWINVS: Vec<BigUint> = TWOPOWUS
        .iter()
        .zip(QPOWS.iter())
        .map(|(tpu, qpow)| tpu / qpow)
        .collect();
    static ref SIMPLE_QPOWS: Vec<SimpleBigint> = QPOWS.iter().map(SimpleBigint::from).collect();
    // Bigints with the same number of limbs as SIMPLE_QPOWS, but all 0
    static ref SIMPLE_QPOWS_ZEROS: Vec<SimpleBigint> = SIMPLE_QPOWS
        .iter()
        .map(|n| SimpleBigint::zero(n.num_limbs()))
        .collect();
    static ref SIMPLE_TWOQPOWS: Vec<SimpleBigint> =
        TWOQPOWS.iter().map(SimpleBigint::from).collect();
    static ref SIMPLE_SCALEDQPOWINVS: Vec<SimpleBigint> =
        SCALEDQPOWINVS.iter().map(SimpleBigint::from).collect();
    static ref SIMPLE_TWOPOWUS: Vec<SimpleBigint> =
        TWOPOWUS.iter().map(SimpleBigint::from).collect();
}

/// Divides x by q^(2^pow) and returns (quotient, remainder)
// For this Barrett division, we follow Algorithm 1 in
//     http://koclab.cs.ucsb.edu/teaching/ecc/project/2015Projects/Terner.pdf
fn divrem_by_qpow(mut x: SimpleBigint, pow: u32) -> (SimpleBigint, SimpleBigint) {
    let u_idx = pow as usize;
    let qpow = &SIMPLE_QPOWS[u_idx];
    let two_qpow = &SIMPLE_TWOQPOWS[u_idx];
    let zero = &SIMPLE_QPOWS_ZEROS[u_idx];

    // Rather than computing (x * qinvpow) >> shift, we can split the shift:
    //     ((x >> shift1) * qinvpow) >> shift2
    // This makes the multiplication smaller
    let preshift = (US[u_idx] >> 1) - 1;
    let postshift = US[u_idx] - preshift;
    let mut quot = {
        let mut tmp = &(&x >> preshift) * &SIMPLE_SCALEDQPOWINVS[u_idx];
        tmp >>= postshift;
        tmp
    };
    // TODO: justify this truncation (beyond "it works and produces faster mults")
    quot.truncate_to(x.num_limbs() / 2 + 1);
    // The quotient is at most the difference of the number of limbs of x and qpow, plus 1
    //quot.truncate_to(x.num_limbs() - qpow.num_limbs() + 1);

    x.truncate_to(postshift as usize);
    let mut rem = &x - &(&quot * &qpow);
    // The size of rem is the same as that of qpow, plus maybe 1 limb for rem overflow
    rem.truncate_to(qpow.num_limbs() + 1);

    // If rem >= qpow, then we need to subtract qpow to rem and increment quot
    // If it's still >= qpow, then we need to do it again
    let greater_than_two_qpow = rem.ct_gte(&two_qpow);
    let greater_than_qpow = rem.ct_gte(&qpow);
    // if rem > 2*qpow, quot += 2. Elsif rem > qpow, quot += 1. Else, do nothing
    let mut add_to_quot = u64::conditional_select(&0, &1, greater_than_qpow);
    add_to_quot.conditional_assign(&2, greater_than_two_qpow);
    // if rem > 2*qpow, rem -= 2*qpow. Elsif rem > 2*qpow, rem -= qpow. Else, do nothing
    let mut sub_from_rem = SimpleBigint::conditional_select(&zero, &qpow, greater_than_qpow);
    sub_from_rem.conditional_assign(two_qpow, greater_than_two_qpow);

    quot += add_to_quot;
    rem -= &sub_from_rem;

    (quot, rem)
}

/// Given a sequence of limbs x in big-endian order in base b, returns a sequence of limbs in
/// big-endian order in base b/q^(2^pow)
fn lower_base_by(x: Vec<SimpleBigint>, pow: u32) -> Vec<SimpleBigint> {
    // For each limb, divide the limb by q^(2^pow) and record (quotient, remainder) in that order.
    // The final sequence of (quotient1, remainder1, quotient2, remainder2, etc...) is `x` in the
    // new base.
    x.into_iter()
        .flat_map(|limb| {
            let (quot, rem) = divrem_by_qpow(limb, pow);

            // Sanity check: rem < q^(2^pow)
            debug_assert!(
                rem.as_biguint() < QPOWS[pow as usize],
                "rem too big: {:?}, rest = {:?}",
                rem,
                quot
            );

            [quot, rem]
        })
        .collect()
}

macro_rules! impl_native_base_lowering {
    ($smallnum:ty, $biggernum:ty, $biggerernum:ty, $qpow:expr, $fnname:ident) => {
        /// Same thing as lower_base_by, but specialized to `x: Vec<$biggernum>` and `pow=1` or `0`
        fn $fnname(x: Vec<$biggernum>, pow: u32) -> Vec<$smallnum> {
            // Divides x by q and returns (quotient, remainder)
            fn native_divrem_by_qpow(x: $biggernum, pow: u32) -> ($smallnum, $smallnum) {
                debug_assert_eq!(pow, $qpow);

                let u_idx = pow as usize;
                let qpow = SIMPLE_QPOWS[pow as usize].u64_limbs().next().unwrap() as $smallnum;
                let two_qpow = qpow << 1;
                let scaledinv = {
                    let mut it = SIMPLE_SCALEDQPOWINVS[u_idx].u64_limbs();
                    let ret = it.next().unwrap() as $biggernum;
                    debug_assert!(it.next().is_none());
                    ret
                };

                let preshift = (US[u_idx] >> 1) - 1;
                let postshift = US[u_idx] - preshift;
                let mut quot: $smallnum = (((x >> preshift) as $biggerernum
                    * scaledinv as $biggerernum)
                    >> postshift) as $smallnum;
                let mut rem: $smallnum =
                    (x - &(quot as $biggernum * qpow as $biggernum)) as $smallnum;

                let greater_than_two_qpow = !rem.ct_lt(&two_qpow);
                let greater_than_qpow = !rem.ct_lt(&qpow);
                let mut add_to_quot = <$smallnum>::conditional_select(&0, &1, greater_than_qpow);
                add_to_quot.conditional_assign(&2, greater_than_two_qpow);
                let mut sub_from_rem =
                    <$smallnum>::conditional_select(&0, &qpow, greater_than_qpow);
                sub_from_rem.conditional_assign(&two_qpow, greater_than_two_qpow);

                quot += add_to_quot;
                rem -= sub_from_rem;

                (quot as $smallnum, rem as $smallnum)
            }

            x.iter()
                .flat_map(|&limb| {
                    let (quot, rem) = native_divrem_by_qpow(limb, pow);

                    // Sanity check: rem < q^(2^pow)
                    debug_assert!(
                        BigUint::from(rem) < QPOWS[pow as usize],
                        "rem too big: {:?}, rest = {:?}",
                        rem,
                        quot
                    );

                    [quot, rem]
                })
                .collect()
        }
    };
}

impl_native_base_lowering!(u16, u32, u64, 0, u32_lower_base_by);
impl_native_base_lowering!(u32, u64, u128, 1, u64_lower_base_by);

/// Undoes Kemeleon encoding
pub fn vector_decode<const N: usize>(bytes: &[u8]) -> [u16; N] {
    // Parse the bytes and clear the top few bits bc we set them to be random
    let mut repr = SimpleBigint::from(BigUint::from_bytes_be(bytes));
    // Top bit (0-indexed) is ⌈log₂(q^kn + 1)⌉ - 1. n=256 in ML-KEM
    let top_bit_idx = ((N as f64) * (MLKEM_Q as f64).log2()).ceil() as u64 - 1;
    // Need to pad to a byte boundary
    let next_byte_boundary = top_bit_idx + (8 - (top_bit_idx % 8) % 8);

    // Remove the padding that was added to make it fit a byte boundary
    for i in top_bit_idx..next_byte_boundary {
        repr.set_bit(i, false);
    }

    // Change the base from q^N to q^(N/2) to q^(N/4), etc. until we get to q^4
    let mut cur_limbs = vec![repr];

    // The value i such that our next division will be q^(2^i)
    let mut starting_pow = N.ilog2() - 1;

    if N == 768 {
        // If N == 768, then we need to lower the base to q^256 first. Divide by q^512
        cur_limbs = lower_base_by(cur_limbs, 9);
        // This leaves with one limb of base q^256, and one limb of base q^512. Divide the latter
        // by q^256
        let last_limb = cur_limbs.pop().unwrap();
        let next_limbs = lower_base_by(vec![last_limb], 8);
        cur_limbs.extend(next_limbs);

        // Next power is q^128
        starting_pow = 7;
    }

    // Now lower by halving powers of q
    for pow in (2..=starting_pow).rev() {
        cur_limbs = lower_base_by(cur_limbs, pow);
    }

    // Everything is now base q^4.
    // Now continue to lower the base, but use native arithmetic for a speedup.
    let pow = 1;
    // Convert existing bigints to u64
    let u64_limbs: Vec<u64> = cur_limbs
        .into_iter()
        .map(|l| {
            let mut it = l.u64_limbs();
            let out = it.next().unwrap();
            // Make sure all the remaining limbs are 0
            debug_assert!(it.all(|l| l == 0));
            out
        })
        .collect();
    let u32_limbs = u64_lower_base_by(u64_limbs, pow);

    // Do it again one last time. The base is now q.
    let pow = 0;
    let final_u16_limbs = u32_lower_base_by(u32_limbs, pow);

    let mut out = [0u16; N];
    out.copy_from_slice(&final_u16_limbs);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_encode_decode<const N: usize>() {
        let mut rng = rand::thread_rng();

        // Make random vectors and round-trip encode them
        let mut num_encoded = 0;
        for i in 0..1000 {
            let v = rand_vec::<N>(&mut rng);
            let encoded = vector_encode(&mut rng, &v);
            if let Some(bytes) = encoded {
                num_encoded += 1;
                let decoded = vector_decode(&bytes);
                let diff = v
                    .iter()
                    .zip(decoded.iter())
                    .map(|(x, y)| if x > y { x - y } else { y - x })
                    .collect::<Vec<_>>();
                assert_eq!(v, decoded, "iteration {i}: diff is {:?}", diff);
            }
        }

        // Make sure the above loop didn't just do nothing
        assert!(num_encoded > 0);
    }

    #[test]
    fn test_encode_decode_512() {
        test_encode_decode::<512>();
    }

    // TODO: make decoding work with non-pow-2 N
    #[test]
    fn test_encode_decode_768() {
        test_encode_decode::<768>();
    }

    #[test]
    fn test_encode_decode_1024() {
        test_encode_decode::<1024>();
    }
}
