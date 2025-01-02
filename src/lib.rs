mod bigint;

use bigint::SimpleBigint;

use lazy_static::lazy_static;
use num_bigint::BigUint;
use rand::Rng;
use subtle::{Choice, ConditionallySelectable, ConstantTimeLess};

/// The prime modulus used in ML-KEM
const MLKEM_Q: u16 = 3329;

// Test/bench helper. Returns an array of random numbers in [0, MLKEM_Q)
pub fn rand_vec<const N: usize>(rng: &mut impl Rng) -> [u16; N] {
    let mut out = [0u16; N];
    for coeff in out.iter_mut().rev() {
        *coeff = rng.gen_range(0..MLKEM_Q);
    }

    out
}

/// Generates an element in [0, ub] in constant time. We expect ub >= 2^127.5, so we don't have
/// to try too many times.
fn ct_gen_range(rng: &mut impl Rng, ub: u128) -> u128 {
    let mut out = 0u128;
    // If we sample a random x, the likelihood x <= ub is at least 2^127.5 / 2^128 = 2^-.5
    // The likelihood that x >= ub is thus at most 1 - 2^-.5.
    // The likelihood of failure 46 times in a row is < 2^-81.
    for _ in 0..46 {
        let x = rng.gen();
        let satisfied = Choice::from((x <= ub) as u8);
        out.conditional_assign(&x, satisfied);
    }

    out
}

/// Attempts to run the Kemeleon encoding for the given NTT vector. Top few bits
/// get set to random.
// We say "Kemeleon1" to refer to the rejection sampling variant of Kemeleon, whereby a given
// public key or ciphertext may fail encoding (triggering a retry)
pub fn kemeleon1_encode<const N: usize>(rng: &mut impl Rng, v: &[u16; N]) -> Option<Vec<u8>> {
    let mut sum = bigint_encode(v);

    // Check if the top bit is set. If not, then this input can be encoded
    // Top bit (0-indexed) is ⌈log₂(q^N + 1)⌉ - 1
    let top_bit_idx = ((N as f64) * (MLKEM_Q as f64).log2()).ceil() as u64 - 1;
    // Need to pad to a byte boundary
    let next_byte_boundary = top_bit_idx + (8 - (top_bit_idx % 8) % 8);

    if !sum.get_bit(top_bit_idx) {
        // We need the number of bits to be a multiple of 8. So set the remaining bits to
        // random values
        for i in top_bit_idx..next_byte_boundary {
            sum.set_bit(i, rng.gen());
        }
        Some(sum.to_bytes_le().collect())
    } else {
        None
    }
}

// We say "Kemeleon2" to refer to the non-rejection sampling variant of Kemeleon, whereby a given
// public key or ciphertext can always be encoded (at the cost of ~16B of overhead).
pub fn kemeleon2_encode<const N: usize>(rng: &mut impl Rng, v: &[u16; N]) -> Vec<u8> {
    // We only support vectors of size 256 right now
    assert_eq!(N, 256);
    let sum = bigint_encode(v);

    // Get pow such that N = 2^pow
    assert!(N.is_power_of_two());
    let pow = N.ilog2();

    // We will compute a + kQ, where k is uniformly chosen from [0, ⌊(2^(r+t) - u) / Q⌋] and
    // Q = q^N, r = ⌈log₂ Q⌉ = 2996, and t = 127
    let r = 2996;
    let t = 127;

    let ub = {
        // Compute 2^(n+t) - u
        let mut twopow = SimpleBigint::twopow(r + t);
        twopow -= &sum;
        assert!(N.is_power_of_two());
        // Divide by q^N = q^(2^(log2(N)))
        divrem_by_qpow(twopow, pow).0
    };
    // Convert from bigint to u128
    let ub = {
        let mut it = ub.u128_limbs();
        let out = it.next().unwrap();
        // Make sure this bigint was < 2^128
        debug_assert!(it.all(|x| x == 0));
        out
    };

    // TODO: replace gen_range with something constant-time
    let k = SimpleBigint::from(ct_gen_range(rng, ub));
    let kq = &k * &SIMPLE_QPOWS[pow as usize];

    let out = &sum + &kq;
    out.to_bytes_le().collect()
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
/// big-endian order in base b*q^(2^pow)
fn raise_base_by(x: &[SimpleBigint], pow: u32) -> Vec<SimpleBigint> {
    assert!(x.len() % 2 == 0);

    let mut out = Vec::with_capacity(x.len() / 2);
    for chunk in x.chunks_exact(2) {
        let [hi, lo] = chunk else { unreachable!() };
        let mut combined = hi * &SIMPLE_QPOWS[pow as usize];
        combined += lo;
        out.push(combined);
    }

    out
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

/// Undoes Kemeleon1 encoding
pub fn kemeleon1_decode<const N: usize>(bytes: &[u8]) -> [u16; N] {
    // Parse the bytes and clear the top few bits bc we set them to be random
    let mut repr = SimpleBigint::from_bytes_le(bytes);
    // Top bit (0-indexed) is ⌈log₂(q^kn + 1)⌉ - 1. n=256 in ML-KEM
    let top_bit_idx = ((N as f64) * (MLKEM_Q as f64).log2()).ceil() as u64 - 1;
    // Need to pad to a byte boundary
    let next_byte_boundary = top_bit_idx + (8 - (top_bit_idx % 8) % 8);

    // Remove the padding that was added to make it fit a byte boundary
    for i in top_bit_idx..next_byte_boundary {
        repr.set_bit(i, false);
    }

    // Decode the bigint
    bigint_decode(repr)
}

/// Undoes Kemeleon1 encoding
pub fn kemeleon2_decode<const N: usize>(bytes: &[u8]) -> [u16; N] {
    // This only works for power-of-two N for now
    assert!(N.is_power_of_two());
    let pow = N.ilog2();

    // Parse the bytes and clear the blind by modding by the correct power of q
    let repr = SimpleBigint::from_bytes_le(bytes);
    let (_, rem) = divrem_by_qpow(repr, pow);

    // Now decode the unblinded integer
    bigint_decode(rem)
}

/// Given a sequence of integers mod q, returns the bigint Σᵢ qⁱ vᵢ
fn bigint_encode(v: &[u16]) -> SimpleBigint {
    let mut cur_limbs: Vec<SimpleBigint> =
        v.iter().map(|&x| SimpleBigint::from(x as u64)).collect();

    // Raise the power until we cannot raise anymore. Or if the input is 768 elements (ie not a
    // power of two), raise until we have 3 elements left, each of magnitude ~q^256 = q^(2^8).
    let len = v.len();
    let ending_power = if len == 768 { 8 } else { len.ilog2() };
    for pow in 0..ending_power {
        let next_limbs = raise_base_by(&cur_limbs, pow);
        cur_limbs = next_limbs;
    }

    // If the length isn't a power of two then we have one more operation to do.
    // Take the three elements in cur_limbs and make them into 1 bigint
    if len == 768 {
        // We will calculate q^512 a0 + q^256 a1 + a2
        // First calculate q^256 a1 + a2
        let lower_limb = raise_base_by(&cur_limbs[1..], 8);
        assert_eq!(lower_limb.len(), 1);

        // Now the final sum. Calculate q^512 a0
        let mut final_out = &cur_limbs[0] * &SIMPLE_QPOWS[9];
        // Add in the rest of the limbs
        final_out += &lower_limb[0];
        cur_limbs = vec![final_out];
    }

    assert_eq!(cur_limbs.len(), 1);
    core::mem::take(&mut cur_limbs[0])
}

/// Given a bigint, returns the sequence of mod-q values that were used in its encoding
fn bigint_decode<const N: usize>(x: SimpleBigint) -> [u16; N] {
    // Change the base from q^N to q^(N/2) to q^(N/4), etc. until we get to q^4
    let mut cur_limbs = vec![x];

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

    fn test_kemleon1_round_trip<const N: usize>() {
        let mut rng = rand::thread_rng();

        // Make random vectors and round-trip encode them
        let mut num_encoded = 0;
        for i in 0..1000 {
            let v = rand_vec::<N>(&mut rng);
            let encoded = kemeleon1_encode(&mut rng, &v);
            if let Some(bytes) = encoded {
                num_encoded += 1;
                let decoded = kemeleon1_decode(&bytes);
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

    fn test_kemleon2_round_trip<const N: usize>() {
        let mut rng = rand::thread_rng();

        // Make random vectors and round-trip encode them
        for i in 0..1000 {
            let v = rand_vec::<N>(&mut rng);
            let encoded = kemeleon2_encode(&mut rng, &v);
            let decoded = kemeleon2_decode(&encoded);
            let diff = v
                .iter()
                .zip(decoded.iter())
                .map(|(x, y)| if x > y { x - y } else { y - x })
                .collect::<Vec<_>>();
            assert_eq!(v, decoded, "iteration {i}: diff is {:?}", diff);
        }
    }

    #[test]
    fn kemeleon1_512() {
        test_kemleon1_round_trip::<512>();
    }

    #[test]
    fn kemeleon2_256() {
        test_kemleon2_round_trip::<256>();
    }

    #[test]
    fn kemeleon1_768() {
        test_kemleon1_round_trip::<768>();
    }

    #[test]
    fn kemeleon1_1024() {
        test_kemleon1_round_trip::<1024>();
    }
}
