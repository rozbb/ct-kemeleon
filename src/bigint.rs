use num_bigint::BigUint;

type Limb = u32;
type WideLimb = u64;

/// A little endian representation of a non-negative integer
#[derive(Debug)]
struct SimpleBigint(Vec<Limb>);

// Copied from https://github.com/RustCrypto/crypto-bigint/blob/f9f2e4aec43b87ebb5595e35b28eab45d74d9886/src/primitives.rs#L58
/// Computes `a + (b * c) + carry`, returning the result along with the new carry.
#[inline(always)]
pub(crate) const fn mac(a: Limb, b: Limb, c: Limb, carry: Limb) -> (Limb, Limb) {
    let a = a as WideLimb;
    let b = b as WideLimb;
    let c = c as WideLimb;
    let carry = carry as WideLimb;
    let ret = a + (b * c) + carry;
    (ret as Limb, (ret >> Limb::BITS) as Limb)
}

// Copied from https://github.com/RustCrypto/crypto-bigint/blob/f9f2e4aec43b87ebb5595e35b28eab45d74d9886/src/uint/mul.rs#L16
/// Schoolbook multiplication a.k.a. long multiplication, i.e. the traditional method taught in
/// schools.
///
/// The most efficient method for small numbers.
fn schoolbook_multiplication(lhs: &[Limb], rhs: &[Limb]) -> (Vec<Limb>, Vec<Limb>) {
    let mut lo = vec![0 as Limb; lhs.len()];
    let mut hi = vec![0 as Limb; rhs.len()];

    let mut i = 0;
    while i < lhs.len() {
        let mut j = 0;
        let mut carry = 0;
        let xi = lhs[i];

        while j < rhs.len() {
            let k = i + j;

            if k >= lhs.len() {
                (hi[k - lhs.len()], carry) = mac(hi[k - lhs.len()], xi, rhs[j], carry);
            } else {
                (lo[k], carry) = mac(lo[k], xi, rhs[j], carry);
            }

            j += 1;
        }

        if i + j >= lhs.len() {
            hi[i + j - lhs.len()] = carry;
        } else {
            lo[i + j] = carry;
        }
        i += 1;
    }

    (hi, lo)
}

impl<'a> core::ops::Mul<&'a SimpleBigint> for &'a SimpleBigint {
    type Output = SimpleBigint;

    fn mul(self, rhs: Self) -> Self::Output {
        let (hi, lo) = schoolbook_multiplication(&self.0, &rhs.0);
        SimpleBigint([lo, hi].concat())
    }
}

impl<'a> core::ops::Shr<u32> for &'a SimpleBigint {
    type Output = SimpleBigint;

    fn shr(self, rhs: u32) -> Self::Output {
        // We get rid of the rhs/BITS lowest limbs
        let new_lowest_limb = rhs / Limb::BITS;

        let remaining_shift = rhs % Limb::BITS;
        // This covers all the bits that are shifted away
        let lower_bitmask = (Limb::from(1u8) << remaining_shift) - 1;

        // Now we just have to do a smaller shift for the remaining limbs
        let mut carry = 0;
        let buf = self
            .0
            .iter()
            .skip(new_lowest_limb as usize)
            .rev() // build the new value starting at the most significant limb
            .map(|l| {
                // Save the shifted bits
                let next_carry = l & lower_bitmask;
                // Shift the limb
                let mut new_limb = l >> remaining_shift;
                // Add in the carryover from the previous shift
                new_limb |= carry << (Limb::BITS - remaining_shift);

                carry = next_carry;
                new_limb
            })
            .rev() // reverse to make it little-endian
            .collect();
        SimpleBigint(buf)
    }
}

impl From<BigUint> for SimpleBigint {
    fn from(value: BigUint) -> Self {
        let limbs = BigUint::to_u32_digits(&value);
        SimpleBigint(limbs)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::Rng;

    impl PartialEq<BigUint> for SimpleBigint {
        fn eq(&self, other: &BigUint) -> bool {
            let ref_val = BigUint::from_slice(&self.0);
            ref_val == *other
        }
    }

    fn rand_biguint(rng: &mut impl Rng) -> SimpleBigint {
        let num_limbs = rng.gen_range(0..20);
        let limbs = core::iter::repeat_with(|| rng.gen())
            .take(num_limbs)
            .collect::<Vec<_>>();
        SimpleBigint(limbs)
    }

    #[test]
    fn mul() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let a = rand_biguint(&mut rng);
            let b = rand_biguint(&mut rng);
            let prod = &a * &b;

            let ref_a = BigUint::from_slice(&a.0);
            let ref_b = BigUint::from_slice(&b.0);
            let ref_prod = ref_a * ref_b;

            assert_eq!(prod, ref_prod);
        }
    }

    #[test]
    fn shr() {
        let mut rng = rand::thread_rng();

        let a = rand_biguint(&mut rng);
        let shift_size = rng.gen_range(0..32 * (a.0.len() as u32 - 1));
        let shr = &a >> shift_size;

        let ref_a = BigUint::from_slice(&a.0);
        let ref_shr = ref_a >> shift_size;

        assert_eq!(shr, ref_shr);
    }
}
