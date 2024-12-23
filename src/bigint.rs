use num_bigint::BigUint;
use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
};

type Limb = u64;
type WideLimb = u128;

/// A little endian representation of a non-negative integer
#[derive(Debug)]
pub(crate) struct SimpleBigint(Vec<Limb>);

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

// Copied from https://github.com/RustCrypto/crypto-bigint/blob/f9f2e4aec43b87ebb5595e35b28eab45d74d9886/src/primitives.rs#L39C1-L39C86
/// Computes `self - (rhs + borrow)`, returning the result along with the new borrow.
pub(crate) const fn sbb(lhs: Limb, rhs: Limb, borrow: Limb) -> (Limb, Limb) {
    let a = lhs as WideLimb;
    let b = rhs as WideLimb;
    let borrow = (borrow >> (Limb::BITS - 1)) as WideLimb;
    let ret = a.wrapping_sub(b + borrow);
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
    pub(crate) fn set_bit(&mut self, bit: u64, value: bool) {
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

    pub(crate) fn increment(&mut self) {
        // Add a limb in case this increment overflows
        self.0.push(0);

        // Add 1 to the least significant limb and carry
        let mut carry = true;
        for limb in self.0.iter_mut() {
            let (new_limb, new_carry) = limb.overflowing_add(carry as Limb);
            *limb = new_limb;
            carry = new_carry;
        }

        // Sanity check: we cannot have overflown
        debug_assert!(!carry);
    }

    /// The number of limbs being used by this bigint
    pub(crate) fn num_limbs(&self) -> usize {
        self.0.len()
    }

    /// Truncates this bigint to the given number of limbs. The limbs being truncated MUST all be 0.
    pub(crate) fn truncate_to(&mut self, num_limbs: usize) {
        // Make sure the things we're truncating are all 0
        debug_assert!(self.0.iter().skip(num_limbs).all(|&x| x == 0));
        self.0.truncate(num_limbs);
    }

    /// Constant-time greater-than-or-equal-to
    // This is identical to ct_gt except for the return value
    pub(crate) fn ct_gte(&self, other: &Self) -> Choice {
        let mut greater = Choice::from(0u8);
        let mut equal_so_far = Choice::from(1u8);

        // Iterate limbs from most to least significant.
        // We set `greater` iff the current limb is greater than the other, AND all previously
        // checked limbs were equal.
        for (a, b) in self.zip_limbs_iter_rev(other) {
            greater |= a.ct_gt(b) & equal_so_far;
            equal_so_far &= a.ct_eq(b);
        }

        // At this point, equal_so_far == true iff all limbs were equal
        greater | equal_so_far
    }

    pub(crate) fn as_biguint(&self) -> BigUint {
        // Convert to u32 representation first
        BigUint::from_slice(&self.u32_limbs().collect::<Vec<_>>())
    }

    /// Returns a little-endian iterator of the u64 limbs representing this bigint
    pub(crate) fn u64_limbs(&self) -> impl ExactSizeIterator<Item = u64> + '_ {
        self.0.iter().copied()
    }

    /// Returns a little-endian iterator of the u32 limbs representing this bigint
    pub(crate) fn u32_limbs(&self) -> impl Iterator<Item = u32> + '_ {
        self.0.iter().flat_map(|&x| {
            let hi = (x >> 32) as u32;
            let lo = x as u32;
            [lo, hi]
        })
    }

    /// Returns an iterator over the limbs of this bigint and the other bigint, padding the shorter
    /// one with 0s.
    fn zip_limbs_iter<'a>(
        &'a self,
        other: &'a SimpleBigint,
    ) -> impl Iterator<Item = (&'a Limb, &'a Limb)> + 'a {
        let zeros = core::iter::repeat(&0);
        let max_len = core::cmp::max(self.0.len(), other.0.len());

        self.0
            .iter()
            .chain(zeros.clone())
            .zip(other.0.iter().chain(zeros))
            .take(max_len)
    }

    /// Returns the reversed version of `zip_limbs_iter`
    fn zip_limbs_iter_rev<'a>(
        &'a self,
        other: &'a SimpleBigint,
    ) -> impl Iterator<Item = (&'a Limb, &'a Limb)> + 'a {
        let zeros = core::iter::repeat(&0);
        let max_len = core::cmp::max(self.0.len(), other.0.len());

        // Figure out how many zero's we'll need on each side in advance
        let self_zeros = zeros.clone().take(max_len.saturating_sub(self.num_limbs()));
        let other_zeros = zeros.take(max_len.saturating_sub(other.num_limbs()));

        // Now reverse the iterators and place the zeros first
        let padded_reversed_self = self_zeros.chain(self.0.iter().rev());
        let padded_reversed_other = other_zeros.chain(other.0.iter().rev());

        padded_reversed_self.zip(padded_reversed_other)
    }
}

impl ConstantTimeEq for SimpleBigint {
    fn ct_eq(&self, other: &Self) -> Choice {
        assert_eq!(self.0.len(), other.0.len());

        let mut eq = Choice::from(1u8);
        for (a, b) in self.0.iter().zip(other.0.iter()).rev() {
            eq &= a.ct_eq(b);
        }

        eq
    }
}

impl ConstantTimeGreater for SimpleBigint {
    /// Constant time greater-than comparison
    fn ct_gt(&self, other: &Self) -> Choice {
        let mut greater = Choice::from(0u8);
        let mut equal_so_far = Choice::from(1u8);

        // Iterate limbs from most to least significant.
        // We set `greater` iff the current limb is greater than the other, AND all previously
        // checked limbs were equal.
        for (a, b) in self.zip_limbs_iter_rev(other) {
            greater |= a.ct_gt(b) & equal_so_far;
            equal_so_far &= a.ct_eq(b);
        }

        greater
    }
}

impl ConstantTimeLess for SimpleBigint {
    fn ct_lt(&self, other: &Self) -> Choice {
        !self.ct_gte(other)
    }
}

impl<'a> core::ops::Mul<&'a SimpleBigint> for &'a SimpleBigint {
    type Output = SimpleBigint;

    fn mul(self, rhs: Self) -> Self::Output {
        let (hi, lo) = schoolbook_multiplication(&self.0, &rhs.0);
        SimpleBigint([lo, hi].concat())
    }
}

impl<'a> core::ops::Sub<&'a SimpleBigint> for &'a SimpleBigint {
    type Output = SimpleBigint;

    // Copied from https://github.com/RustCrypto/crypto-bigint/blob/f9f2e4aec43b87ebb5595e35b28eab45d74d9886/src/uint/sub.rs#L11
    fn sub(self, rhs: &'a SimpleBigint) -> SimpleBigint {
        let mut borrow = 0;
        let limbs = self
            .zip_limbs_iter(rhs)
            .map(|(&left, &right)| {
                let (w, b) = sbb(left, right, borrow);
                borrow = b;
                w
            })
            .collect();

        assert_eq!(borrow, 0, "attempted to subtract with underflow");

        SimpleBigint(limbs)
    }
}

impl<'a> core::ops::SubAssign<&'a SimpleBigint> for SimpleBigint {
    fn sub_assign(&mut self, rhs: &'a SimpleBigint) {
        *self = &*self - rhs;
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

impl<'a> From<&'a BigUint> for SimpleBigint {
    fn from(value: &'a BigUint) -> Self {
        let limbs = BigUint::to_u64_digits(value);
        SimpleBigint(limbs)
    }
}

impl From<BigUint> for SimpleBigint {
    fn from(value: BigUint) -> Self {
        SimpleBigint::from(&value)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::Rng;

    impl PartialEq<BigUint> for SimpleBigint {
        fn eq(&self, other: &BigUint) -> bool {
            self.as_biguint() == *other
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

            let ref_a = a.as_biguint();
            let ref_b = b.as_biguint();
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

            let ref_a = a.as_biguint();
            let ref_shr = ref_a >> shift_size;

            assert_eq!(shr, ref_shr);
        }
    }

    #[test]
    fn set_bit() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let mut a = rand_biguint(&mut rng);
            let mut ref_a = a.as_biguint();
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
            let a = rand_biguint(&mut rng);
            let b = rand_biguint(&mut rng);

            let ref_a = a.as_biguint();
            let ref_b = b.as_biguint();

            let ct_gt = a.ct_gt(&b);
            let ref_gt = ref_a > ref_b;
            let ct_gte = a.ct_gte(&b);
            let ref_gte = ref_a >= ref_b;

            assert_eq!(bool::from(ct_gt), ref_gt);
            assert_eq!(bool::from(ct_gte), ref_gte);

            // Check the reflexive properties
            let refl_ct_gt = a.ct_gt(&a);
            let refl_ct_gte = a.ct_gte(&a);
            assert_eq!(bool::from(refl_ct_gt), false);
            assert_eq!(bool::from(refl_ct_gte), true);
        }
    }

    #[test]
    fn increment() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let mut a = rand_biguint(&mut rng);
            let mut ref_a = a.as_biguint();

            a.increment();
            ref_a += 1u32;

            assert_eq!(a, ref_a);
        }
    }

    #[test]
    fn sub() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let a = rand_biguint(&mut rng);
            let b = rand_biguint(&mut rng);

            let ref_a = a.as_biguint();
            let ref_b = b.as_biguint();

            if ref_a >= ref_b {
                let sub = &a - &b;
                let ref_sub = ref_a - ref_b;
                assert_eq!(sub, ref_sub);
            } else {
                let sub = &b - &a;
                let ref_sub = ref_b - ref_a;
                assert_eq!(sub, ref_sub);
            }
        }
    }
}
