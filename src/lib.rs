use num_bigint::BigUint;
use rand::Rng;

/// The prime modulus used in ML-KEM
const MLKEM_Q: u16 = 3329;

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

/* The absolute most naive implementation
fn divrem_by_q(x: &BigUint) -> (BigUint, BigUint) {
    let quot = x / MLKEM_Q;
    let rem = x - &(&quot * MLKEM_Q);

    (quot, rem)
}
*/

fn divrem_by_q(x: &BigUint) -> (BigUint, BigUint) {
    // Rather than dividing by q, we can multiply by ⌊2^u / q⌋ for sufficiently
    // large u, then divide by 2^u
    let u = 2u32.pow(20);
    let twopowu = BigUint::from(2u8).pow(u);
    let twoqinv = &twopowu / MLKEM_Q;

    let quot = (x * &twoqinv) >> u;
    let rem = x - &(&quot * MLKEM_Q);

    if rem >= BigUint::from(MLKEM_Q) {
        (quot + 1u32, BigUint::ZERO)
    } else {
        (quot, rem)
    }
}

/// Undoes Kemeleon encoding
pub fn vector_decode<const N: usize>(bytes: &[u8]) -> [u16; N] {
    // Parse the bytes and clear the top few bits bc we set them to be random
    let mut repr = BigUint::from_bytes_be(bytes);
    // Top bit (0-indexed) is ⌈log₂(q^kn + 1)⌉ - 1. n=256 in ML-KEM
    let top_bit_idx = ((N as f64) * (MLKEM_Q as f64).log2()).ceil() as u64 - 1;
    // Need to pad to a byte boundary
    let next_byte_boundary = top_bit_idx + (8 - (top_bit_idx % 8) % 8);

    // Remove the padding that was added to make it fit a byte boundary
    for i in top_bit_idx..next_byte_boundary {
        repr.set_bit(i, false);
    }

    let mut out = [0u16; N];
    let mut i = 0;
    for coeff in out.iter_mut().rev() {
        // Compute quot, rem such that repr = quot*q + rem
        let (quot, rem) = divrem_by_q(&repr);

        // Sanity check: rem < Q
        assert!(
            rem < BigUint::from(MLKEM_Q),
            "i={i}: rem too big: {:?}, rest = {:?}",
            rem,
            quot
        );

        // Now convert rem to a u16 and set the coefficient to it
        *coeff = {
            let mut it = rem.iter_u32_digits();
            it.next().unwrap_or(0) as u16
        };
        // Continue
        repr = quot;
        i += 1;
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const N: usize = 512;

    fn rand_vec(rng: &mut impl Rng) -> [u16; N] {
        let mut out = [0u16; N];
        for coeff in out.iter_mut().rev() {
            *coeff = rng.gen::<u16>() % MLKEM_Q;
        }

        out
    }

    #[test]
    fn test_encode_decode() {
        let mut rng = rand::thread_rng();

        // Make random vectors and round-trip encode them
        let mut num_encoded = 0;
        for i in 0..100 {
            let v = rand_vec(&mut rng);
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
}
