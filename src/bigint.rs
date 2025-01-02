use num_bigint::BigUint;
use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
};

type Limb = u64;
type WideLimb = u128;

/// A little endian representation of a non-negative integer
#[derive(Clone, Debug, Default)]
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

// Copied from https://github.com/RustCrypto/crypto-bigint/blob/f9f2e4aec43b87ebb5595e35b28eab45d74d9886/src/primitives.rs#L20
/// Computes `lhs + rhs + carry`, returning the result along with the new carry (0, 1, or 2).
#[inline(always)]
pub const fn adc(lhs: Limb, rhs: Limb, carry: Limb) -> (Limb, Limb) {
    let a = lhs as WideLimb;
    let b = rhs as WideLimb;
    let carry = carry as WideLimb;
    let ret = a + b + carry;
    (ret as Limb, (ret >> Limb::BITS) as Limb)
}

// Copied from https://github.com/RustCrypto/crypto-bigint/blob/f9f2e4aec43b87ebb5595e35b28eab45d74d9886/src/primitives.rs#L39C1-L39C86
/// Computes `self - (rhs + borrow)`, returning the result along with the new borrow.
#[inline(always)]
pub(crate) const fn sbb(lhs: Limb, rhs: Limb, borrow: Limb) -> (Limb, Limb) {
    let a = lhs as WideLimb;
    let b = rhs as WideLimb;
    let borrow = (borrow >> (Limb::BITS - 1)) as WideLimb;
    let ret = a.wrapping_sub(b + borrow);
    (ret as Limb, (ret >> Limb::BITS) as Limb)
}

impl SimpleBigint {
    /// Returns a bigint representing 0 that has the given number of limbs
    pub(crate) fn zero(num_limbs: usize) -> Self {
        SimpleBigint(vec![0; num_limbs])
    }

    /// Returns a bigint representing 2^pow
    pub(crate) fn twopow(pow: u32) -> Self {
        // The number of leading zeros for this power of two representation
        let num_zero_limbs = (pow / Limb::BITS) as usize;
        // Calculate the most significant limb
        let remaining_shift = pow % Limb::BITS;
        let last_limb = 1 << remaining_shift;

        // Construct the bigint
        let mut out = Vec::with_capacity(num_zero_limbs + 1);
        out.extend(core::iter::repeat(0).take(num_zero_limbs));
        out.push(last_limb);
        SimpleBigint(out)
    }

    pub(crate) fn set_bit(&mut self, bit: u64, value: bool) {
        let value = Choice::from(value as u8);
        // Find the limb and bit index
        let limb_idx = (bit / Limb::BITS as u64) as usize;
        let bit_idx = (bit % Limb::BITS as u64) as usize;

        // If the bit is beyond the highest limb, add limbs
        if limb_idx >= self.0.len() {
            let num_limbs_to_extend = limb_idx - self.0.len();
            self.0
                .extend(core::iter::repeat(0).take(num_limbs_to_extend));
        }

        // Compute the new limb for when value is 0 or 1
        let newlimb_when_true = self.0[limb_idx] | (1 << bit_idx);
        let newlimb_when_false = self.0[limb_idx] & !(1 << bit_idx);

        // Assign the new limb based on the value
        self.0[limb_idx].conditional_assign(&newlimb_when_true, value);
        self.0[limb_idx].conditional_assign(&newlimb_when_false, !value);
    }

    pub(crate) fn get_bit(&self, bit: u64) -> bool {
        // Find the limb and bit index
        let limb_idx = (bit / Limb::BITS as u64) as usize;
        let bit_idx = (bit % Limb::BITS as u64) as usize;

        assert!(
            limb_idx < self.0.len(),
            "tried to retreive bit that doesn't exist"
        );

        // Return true iff the bitmask on the specified limb is nonzero
        let bitmask = 1 << bit_idx;
        self.0[limb_idx] & bitmask != 0
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

    pub(crate) fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        assert_eq!(a.num_limbs(), b.num_limbs());

        SimpleBigint(
            a.0.iter()
                .zip(b.0.iter())
                .map(|(a, b)| Limb::conditional_select(a, b, choice))
                .collect(),
        )
    }

    pub(crate) fn conditional_assign(&mut self, b: &Self, choice: Choice) {
        assert_eq!(self.num_limbs(), b.num_limbs());

        self.0
            .iter_mut()
            .zip(b.0.iter())
            .for_each(|(a, b)| a.conditional_assign(b, choice));
    }

    pub(crate) fn as_biguint(&self) -> BigUint {
        // Convert to u32 representation first
        BigUint::from_slice(&self.u32_limbs().collect::<Vec<_>>())
    }

    /// Returns a little-endian iterator of the u128 limbs representing this bigint
    pub(crate) fn u128_limbs(&self) -> impl ExactSizeIterator<Item = u128> + '_ {
        // This only works when limbs are 64 bits
        assert_eq!(Limb::BITS, 64);

        self.0.chunks(2).map(|c| {
            let lo = c[0] as u128;
            let hi = c.get(1).copied().unwrap_or(0) as u128;
            lo | (hi << 64)
        })
    }

    /// Returns a little-endian iterator of the u64 limbs representing this bigint
    pub(crate) fn u64_limbs(&self) -> impl ExactSizeIterator<Item = u64> + '_ {
        // This only works when limbs are u64
        assert_eq!(Limb::BITS, 64);
        self.0.iter().copied()
    }

    /// Returns a little-endian iterator of the u32 limbs representing this bigint
    pub(crate) fn u32_limbs(&self) -> impl Iterator<Item = u32> + '_ {
        // This only works when limbs are u64
        assert_eq!(Limb::BITS, 64);
        self.0.iter().flat_map(|&x| {
            let hi = (x >> 32) as u32;
            let lo = x as u32;
            [lo, hi]
        })
    }

    /// Returns a little-endian iterator of the u8 limbs representing this bigint
    pub(crate) fn to_bytes_le(&self) -> impl Iterator<Item = u8> + '_ {
        self.0.iter().flat_map(|&x| x.to_le_bytes())
    }

    pub(crate) fn from_bytes_le(bytes: &[u8]) -> Self {
        let limb_bytes = Limb::BITS as usize / 8;
        let mut num_limbs = bytes.len() / limb_bytes;
        if bytes.len() % limb_bytes != 0 {
            num_limbs += 1;
        }

        // Convert each chunk of bytes into a limb, then push the limb
        let mut out = Vec::with_capacity(num_limbs);
        for c in bytes.chunks(limb_bytes) {
            let mut buf = [0u8; Limb::BITS as usize / 8];
            (&mut buf[..c.len()]).copy_from_slice(c);
            let limb = Limb::from_le_bytes(buf);
            out.push(limb);
        }

        SimpleBigint(out)
    }

    /// Returns a reversed iterator over the limbs of this bigint and the other bigint, padding the
    /// shorter one with 0s.
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

impl<'a> core::ops::Add<&'a SimpleBigint> for &'a SimpleBigint {
    type Output = SimpleBigint;

    fn add(self, rhs: &'a SimpleBigint) -> Self::Output {
        // Use add_assign
        let mut tmp = self.clone();
        tmp += rhs;
        tmp
    }
}

impl<'a> core::ops::AddAssign<&'a SimpleBigint> for SimpleBigint {
    fn add_assign(&mut self, rhs: &'a SimpleBigint) {
        // Extend self to be the length of max(lhs, rhs), plus 1 to handle overflow
        let new_num_limbs = core::cmp::max(self.num_limbs(), rhs.num_limbs()) + 1;
        self.0
            .extend(core::iter::repeat(0).take(new_num_limbs - self.num_limbs()));

        // Add and propagate the carry. Extend the RHS by 1 limb so that the final carry gets added
        // into the LHS
        let mut carry = 0;
        for (l, r) in self
            .0
            .iter_mut()
            .zip(rhs.0.iter().chain(core::iter::once(&0)))
        {
            let (sum, new_carry) = adc(*l, *r, carry);
            *l = sum;
            carry = new_carry;
        }
    }
}

impl core::ops::AddAssign<u64> for SimpleBigint {
    fn add_assign(&mut self, rhs: u64) {
        // Add a limb in case this addition overflows
        self.0.push(0);

        // Add rhs to the least significant limb and carry it up
        let mut carry = rhs;
        for limb in self.0.iter_mut() {
            let (new_limb, new_carry) = limb.overflowing_add(carry as Limb);
            *limb = new_limb;
            carry = new_carry as u64;
        }

        // Sanity check: we cannot have overflown
        debug_assert!(carry == 0);
    }
}

impl<'a> core::ops::Mul<&'a SimpleBigint> for &'a SimpleBigint {
    type Output = SimpleBigint;

    fn mul(self, rhs: Self) -> Self::Output {
        let lhs_len = self.num_limbs();
        let mut out = vec![0; lhs_len + rhs.num_limbs()];

        // Go through the RHS and multiply each limb by the LHS
        for (i, &rhs_limb) in rhs.0.iter().enumerate() {
            let mut carry = 0;
            for j in 0..lhs_len {
                let (new_limb, new_carry) = mac(out[i + j], self.0[j], rhs_limb, carry);
                out[i + j] = new_limb;
                carry = new_carry;
            }
            out[i + lhs_len] = carry;
        }

        SimpleBigint(out)
    }
}

impl<'a> core::ops::Sub<&'a SimpleBigint> for &'a SimpleBigint {
    type Output = SimpleBigint;

    fn sub(self, rhs: &'a SimpleBigint) -> SimpleBigint {
        // Use sub_assign
        let mut tmp = self.clone();
        tmp -= rhs;
        tmp
    }
}

// Copied from https://github.com/RustCrypto/crypto-bigint/blob/f9f2e4aec43b87ebb5595e35b28eab45d74d9886/src/uint/sub.rs#L11
impl<'a> core::ops::SubAssign<&'a SimpleBigint> for SimpleBigint {
    fn sub_assign(&mut self, rhs: &'a SimpleBigint) {
        let mut borrow = 0;
        self.0
            .iter_mut()
            .zip(rhs.0.iter().chain(core::iter::repeat(&0)))
            .for_each(|(left, &right)| {
                let (w, b) = sbb(*left, right, borrow);
                borrow = b;
                *left = w;
            });

        assert_eq!(borrow, 0, "attempted to subtract with underflow");
    }
}

impl<'a> core::ops::Not for &'a SimpleBigint {
    type Output = SimpleBigint;

    fn not(self) -> Self::Output {
        SimpleBigint(self.0.iter().map(|&x| !x).collect())
    }
}

impl<'a> core::ops::Shr<u32> for &'a SimpleBigint {
    type Output = SimpleBigint;

    fn shr(self, rhs: u32) -> Self::Output {
        // Use shr_assign
        let mut tmp = self.clone();
        tmp >>= rhs;
        tmp
    }
}

impl<'a> core::ops::ShrAssign<u32> for SimpleBigint {
    fn shr_assign(&mut self, rhs: u32) {
        // We get rid of the rhs/BITS lowest limbs
        let new_lowest_limb = (rhs / Limb::BITS) as usize;

        let remaining_shift = rhs % Limb::BITS;
        // This covers all the bits that are shifted away
        let lower_bitmask = (Limb::from(1u8) << remaining_shift) - 1;

        // Now we just have to do a smaller shift for the remaining limbs
        let mut this_limb = self.0[new_lowest_limb];
        for i in 0..self.0.len() - new_lowest_limb {
            let next_limb = self.0.get(i + new_lowest_limb + 1).copied().unwrap_or(0);

            // Get the bits that will be shifted away from the limb above
            let bits_from_next_limb = next_limb & lower_bitmask;
            // Shift this limb
            let mut new_limb = this_limb >> remaining_shift;
            // Add in the bits from the limba above
            new_limb |= bits_from_next_limb << ((Limb::BITS - remaining_shift) % Limb::BITS);

            self.0[i] = new_limb;
            this_limb = next_limb;
        }

        self.0.truncate(self.0.len() - new_lowest_limb);
    }
}

impl From<u64> for SimpleBigint {
    fn from(value: u64) -> Self {
        // This only works when limbs are 64 bits
        assert_eq!(Limb::BITS, 64);
        SimpleBigint(vec![value])
    }
}

impl From<u128> for SimpleBigint {
    fn from(value: u128) -> Self {
        // This only works when limbs are 64 bits
        assert_eq!(Limb::BITS, 64);
        let lo = value as u64;
        let hi = (value >> 64) as u64;
        SimpleBigint(vec![lo, hi])
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
    use rand::{thread_rng, Rng};

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

        for _ in 0..200 {
            let a = rand_biguint(&mut rng);
            let b = rand_biguint(&mut rng);
            let prod = &a * &b;

            let ref_a = a.as_biguint();
            let ref_b = b.as_biguint();
            let ref_prod = &ref_a * &ref_b;

            assert_eq!(prod, ref_prod, "{ref_a} * {ref_b}");
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
            let shrassign = {
                let mut tmp = a.clone();
                tmp >>= shift_size;
                tmp
            };

            let ref_a = a.as_biguint();
            let ref_shr = ref_a >> shift_size;

            assert_eq!(shr, ref_shr);
            assert_eq!(shrassign.0, shr.0, "{:x?} != {:x?}", shrassign.0, shr.0);
            assert_eq!(shrassign, ref_shr);
        }
    }

    #[test]
    fn get_bit() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let a = rand_biguint(&mut rng);
            let ref_a = a.as_biguint();
            if a.0.len() < 1 {
                continue;
            }
            let bit_idx = rng.gen_range(0..Limb::BITS as u64 * a.0.len() as u64);

            assert_eq!(a.get_bit(bit_idx), ref_a.bit(bit_idx));
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

            let bit_idx = rng.gen_range(0..Limb::BITS as u64 * a.0.len() as u64);
            let value = rng.gen_bool(0.5);

            a.set_bit(bit_idx, value);
            ref_a.set_bit(bit_idx, value);

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
    fn add() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let mut a = rand_biguint(&mut rng);
            let b: u64 = rng.gen();

            let mut ref_a = a.as_biguint();

            // Check that adding a u64 to a is correct
            a += b;
            ref_a += b;
            assert_eq!(a, ref_a);

            // Now check that adding a SimpleBigint is correct
            let a = rand_biguint(&mut rng);
            let b = rand_biguint(&mut rng);

            let ref_a = a.as_biguint();
            let ref_b = b.as_biguint();

            assert_eq!(&a + &b, ref_a + ref_b);
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

    #[test]
    fn twopow() {
        let mut rng = thread_rng();

        for _ in 0..100 {
            // Restrict the range so it's bigger than a u16 but not so crazy big that it slows down
            // the BigUint calculation
            let pow = rng.gen_range(0u32..70000);
            let a = SimpleBigint::twopow(pow);
            let ref_a = BigUint::from(1u8) << pow;

            assert_eq!(a, ref_a);
        }
    }
}
