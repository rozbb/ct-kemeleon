use num_bigint::BigUint;
use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
};

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

impl SimpleBigint {
    pub fn set_bit(&mut self, bit: u64, value: bool) {
        let value = Choice::from(value as u8);
        // Find the limb and bit index
        let limb_idx = bit / Limb::BITS as u64;
        let bit_idx = bit % Limb::BITS as u64;

        // We don't support setting bits beyond the highest limb
        assert!((limb_idx as usize) < self.0.len());

        // Compute the new limb for when value is 0 or 1
        let newlimb_when_true = self.0[limb_idx as usize] | (1 << bit_idx);
        let newlimb_when_false = self.0[limb_idx as usize] & !(1 << bit_idx);

        // Assign the new limb based on the value
        self.0[limb_idx as usize].conditional_assign(&newlimb_when_true, value);
        self.0[limb_idx as usize].conditional_assign(&newlimb_when_false, !value);
    }
}

impl ConstantTimeEq for SimpleBigint {
    fn ct_eq(&self, other: &Self) -> Choice {
        panic!("ct_eq should never be called");

        if self.0.len() != other.0.len() {
            return Choice::from(0u8);
        }

        let mut eq = Choice::from(1u8);
        for (a, b) in self.0.iter().zip(other.0.iter()).rev() {
            eq &= a.ct_eq(b);
        }

        eq
    }
}

impl ConstantTimeGreater for SimpleBigint {
    /// Constant time greater-than comparison. `self` and `other` MUST have the same number of limbs
    fn ct_gt(&self, other: &Self) -> Choice {
        assert_eq!(self.0.len(), other.0.len());

        let mut greater = Choice::from(0u8);
        let mut equal_so_far = Choice::from(1u8);

        // Iterate limbs from most to least significant.
        // We set `greater` iff the current limb is greater than the other, AND all previously
        // checked limbs were equal.
        for (a, b) in self.0.iter().zip(other.0.iter()).rev() {
            greater |= a.ct_gt(b) & equal_so_far;
            equal_so_far &= a.ct_eq(b);
        }

        greater
    }
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
        let mut new_limbs: Vec<Limb> = self
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
                new_limb |= carry << ((Limb::BITS - remaining_shift) % Limb::BITS);

                carry = next_carry;
                new_limb
            })
            .collect();
        new_limbs.reverse(); // Make it big-endian
        SimpleBigint(new_limbs)
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

        for _ in 0..100 {
            let a = rand_biguint(&mut rng);
            if a.0.len() < 1 {
                continue;
            }

            let shift_size = rng.gen_range(0..Limb::BITS * a.0.len() as u32);
            let shr = &a >> shift_size;

            let ref_a = BigUint::from_slice(&a.0);
            let ref_shr = ref_a >> shift_size;

            assert_eq!(shr, ref_shr);
        }
    }

    #[test]
    fn set_bit() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let mut a = rand_biguint(&mut rng);
            let mut ref_a = BigUint::from_slice(&a.0);
            if a.0.len() < 1 {
                continue;
            }

            let bit = rng.gen_range(0..Limb::BITS as u64 * a.0.len() as u64);
            let value = rng.gen_bool(0.5);

            a.set_bit(bit, value);
            ref_a.set_bit(bit, value);

            assert_eq!(a, ref_a);
        }
    }

    #[test]
    fn ct_gt() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            // We need to sample the same number of limbs for both numbers, since that's all that's
            // supported
            let num_limbs = rng.gen_range(0..20);
            let a_limbs = core::iter::repeat_with(|| rng.gen())
                .take(num_limbs)
                .collect::<Vec<_>>();
            let b_limbs = core::iter::repeat_with(|| rng.gen())
                .take(num_limbs)
                .collect::<Vec<_>>();
            let a = SimpleBigint(a_limbs);
            let b = SimpleBigint(b_limbs);

            let ref_a = BigUint::from_slice(&a.0);
            let ref_b = BigUint::from_slice(&b.0);

            let ct_gt = a.ct_gt(&b);
            let ref_gt = ref_a > ref_b;

            assert_eq!(bool::from(ct_gt), ref_gt);
        }
    }
}
