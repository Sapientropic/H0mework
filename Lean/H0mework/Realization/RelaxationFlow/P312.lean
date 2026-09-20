import H0mework.Arithmetic.PrimeShadow.P311

/-!
# Proposition 312: integer-depth sigma relaxation

P311 packaged the natural-number iteration image as the arithmetic carrier.
The next layer of the sigma-relaxation foundation is directed consolidation
depth: positive depth is forward relaxation, negative depth is the inverse
noisy-OR step.

The clean coordinate is again the residual keep-rate.  For a signed depth
`z : ℤ`, define

`iteratedRateInt σ z = 1 - (1 - σ)^z`.

Then serial noisy-OR composition is exactly integer addition.  On
`0 < σ < 1`, the map from integer depths to rates is faithful, giving an image
carrier equivalent to `ℤ`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Signed effective rates -/

/-- The effective rate for a signed integer depth.  Negative depths use the
inverse residual power. -/
def iteratedRateInt (σ : K) (z : ℤ) : K :=
  1 - (1 - σ) ^ z

/-- THEOREM 1: the residual keep-rate at signed depth `z` is `(1-σ)^z`. -/
theorem keep_iteratedRateInt (σ : K) (z : ℤ) :
    1 - iteratedRateInt σ z = (1 - σ) ^ z := by
  unfold iteratedRateInt
  ring

/-- THEOREM 2: zero signed depth is the no-op rate. -/
@[simp] theorem iteratedRateInt_zero (σ : K) :
    iteratedRateInt σ 0 = 0 := by
  simp [iteratedRateInt]

/-- THEOREM 3: signed depth `1` is the original base rate. -/
@[simp] theorem iteratedRateInt_one (σ : K) :
    iteratedRateInt σ 1 = σ := by
  simp [iteratedRateInt]

/-- THEOREM 4: signed depth extends the natural-number iteration formula. -/
theorem iteratedRateInt_natCast (σ : K) (n : ℕ) :
    iteratedRateInt σ (n : ℤ) = iteratedRate σ n := by
  simp [iteratedRateInt, iteratedRate, zpow_natCast]

/-- THEOREM 5: serial noisy-OR composition is addition of signed depths. -/
theorem iteratedRateInt_add
    {σ : K} (hσ : σ ≠ 1) (z w : ℤ) :
    iteratedRateInt σ (z + w) =
      satOrField (iteratedRateInt σ z) (iteratedRateInt σ w) := by
  have hkeep : 1 - σ ≠ 0 := by
    intro h
    exact hσ (sub_eq_zero.mp h).symm
  unfold iteratedRateInt satOrField
  rw [zpow_add₀ hkeep]
  ring

/-- THEOREM 6: a signed depth and its negative compose to the no-op rate. -/
theorem satOr_iteratedRateInt_neg
    {σ : K} (hσ : σ ≠ 1) (z : ℤ) :
    satOrField (iteratedRateInt σ z) (iteratedRateInt σ (-z)) = 0 := by
  have h := iteratedRateInt_add (σ := σ) hσ z (-z)
  simpa using h.symm

/-- Signed-depth effective rates never hit the absorbing rate when
`σ ≠ 1`. -/
theorem iteratedRateInt_ne_one_of_ne_one
    {σ : K} (hσ : σ ≠ 1) (z : ℤ) :
    iteratedRateInt σ z ≠ 1 := by
  have hkeep : 1 - σ ≠ 0 := by
    intro h
    exact hσ (sub_eq_zero.mp h).symm
  intro h
  have hz : (1 - σ) ^ z = 0 := by
    have hk := keep_iteratedRateInt σ z
    rw [h] at hk
    simpa using hk.symm
  exact (zpow_ne_zero z hkeep) hz

/-- A signed-depth effective rate bundled as a non-absorbing noisy-OR rate. -/
def iteratedIntNonAbsorbingRate
    (σ : K) (hσ : σ ≠ 1) (z : ℤ) :
    NonAbsorbingRate (α := K) :=
  ⟨iteratedRateInt σ z, iteratedRateInt_ne_one_of_ne_one hσ z⟩

@[simp] theorem iteratedIntNonAbsorbingRate_val
    (σ : K) (hσ : σ ≠ 1) (z : ℤ) :
    (iteratedIntNonAbsorbingRate σ hσ z).1 = iteratedRateInt σ z := rfl

/-- THEOREM 7: integer-depth rates multiply in the non-absorbing noisy-OR
group by adding signed depths. -/
theorem iteratedIntNonAbsorbingRate_add
    (σ : K) (hσ : σ ≠ 1) (z w : ℤ) :
    iteratedIntNonAbsorbingRate σ hσ (z + w) =
      iteratedIntNonAbsorbingRate σ hσ z *
        iteratedIntNonAbsorbingRate σ hσ w := by
  ext
  exact iteratedRateInt_add hσ z w

/-- THEOREM 8: signed depth `0` maps to the noisy-OR group identity. -/
@[simp] theorem iteratedIntNonAbsorbingRate_zero
    (σ : K) (hσ : σ ≠ 1) :
    iteratedIntNonAbsorbingRate σ hσ 0 = 1 := by
  ext
  simp [iteratedIntNonAbsorbingRate]

/-- THEOREM 9: signed depth `1` maps to the original base rate. -/
@[simp] theorem iteratedIntNonAbsorbingRate_one_val
    (σ : K) (hσ : σ ≠ 1) :
    (iteratedIntNonAbsorbingRate σ hσ 1).1 = σ := by
  simp [iteratedIntNonAbsorbingRate]

/-- THEOREM 10: integer depths form a monoid hom into the non-absorbing
noisy-OR rate group.  Multiplication in `Multiplicative ℤ` is addition of
ordinary signed depths. -/
def iteratedRateIntMonoidHom
    (σ : K) (hσ : σ ≠ 1) :
    Multiplicative ℤ →* NonAbsorbingRate (α := K) where
  toFun z := iteratedIntNonAbsorbingRate σ hσ z.toAdd
  map_one' := by
    ext
    simp [iteratedIntNonAbsorbingRate]
  map_mul' := by
    intro z w
    ext
    exact iteratedRateInt_add hσ z.toAdd w.toAdd

@[simp] theorem iteratedRateIntMonoidHom_apply
    (σ : K) (hσ : σ ≠ 1) (z : Multiplicative ℤ) :
    (iteratedRateIntMonoidHom σ hσ z).1 =
      iteratedRateInt σ z.toAdd := rfl

/-- THEOREM 11: signed-depth hom multiplication is exactly serial noisy-OR on
values. -/
theorem iteratedRateIntMonoidHom_map_mul_val
    (σ : K) (hσ : σ ≠ 1) (z w : Multiplicative ℤ) :
    ((iteratedRateIntMonoidHom σ hσ (z * w)).1 : K) =
      satOrField
        (iteratedRateIntMonoidHom σ hσ z).1
        (iteratedRateIntMonoidHom σ hσ w).1 := by
  change iteratedRateInt σ (z.toAdd + w.toAdd) =
    satOrField (iteratedRateInt σ z.toAdd) (iteratedRateInt σ w.toAdd)
  exact iteratedRateInt_add hσ z.toAdd w.toAdd

/-! ## The signed-depth image carrier -/

/-- The image of signed integer depths inside the sigma carrier. -/
def SigmaIntegerDepthImage (σ : K) : Type _ :=
  { r : K // ∃ z : ℤ, r = iteratedRateInt σ z }

namespace SigmaIntegerDepthImage

/-- The image point corresponding to a signed depth. -/
def ofInt (σ : K) (z : ℤ) : SigmaIntegerDepthImage σ :=
  ⟨iteratedRateInt σ z, ⟨z, rfl⟩⟩

/-- A chosen signed depth for an image point. -/
def depth {σ : K} (r : SigmaIntegerDepthImage σ) : ℤ :=
  Classical.choose r.2

/-- The chosen depth represents the image point. -/
theorem val_eq_iteratedRateInt_depth
    {σ : K} (r : SigmaIntegerDepthImage σ) :
    r.1 = iteratedRateInt σ (depth r) :=
  Classical.choose_spec r.2

/-- Every image point is the `ofInt` point of its chosen depth. -/
theorem ofInt_depth_eq
    {σ : K} (r : SigmaIntegerDepthImage σ) :
    ofInt σ (depth r) = r := by
  apply Subtype.ext
  exact (val_eq_iteratedRateInt_depth r).symm

/-- On `0 < σ < 1`, signed-depth effective rates are injective in the integer
depth. -/
theorem ofInt_injective_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Function.Injective (ofInt σ) := by
  intro z w h
  have hval : iteratedRateInt σ z = iteratedRateInt σ w :=
    congrArg Subtype.val h
  have hpows : (1 - σ) ^ z = (1 - σ) ^ w := by
    calc
      (1 - σ) ^ z = 1 - iteratedRateInt σ z :=
        (keep_iteratedRateInt σ z).symm
      _ = 1 - iteratedRateInt σ w := by rw [hval]
      _ = (1 - σ) ^ w := keep_iteratedRateInt σ w
  have hkeep_pos : 0 < 1 - σ := sub_pos.mpr hσ1
  have hkeep_ne_one : (1 - σ) ≠ 1 := by nlinarith
  exact zpow_right_injective₀ hkeep_pos hkeep_ne_one hpows

/-- On `0 < σ < 1`, the chosen depth of `ofInt z` is `z`. -/
theorem depth_ofInt_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) (z : ℤ) :
    depth (ofInt σ z) = z := by
  apply ofInt_injective_of_mem_Ioo hσ0 hσ1
  exact ofInt_depth_eq (ofInt σ z)

/-- The signed-depth image is equivalent to `ℤ` on `0 < σ < 1`. -/
def equivIntOfMemIoo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaIntegerDepthImage σ ≃ ℤ where
  toFun r := depth r
  invFun z := ofInt σ z
  left_inv := ofInt_depth_eq
  right_inv := depth_ofInt_of_mem_Ioo hσ0 hσ1

/-- Addition on the signed-depth image, transported from `ℤ`. -/
def add {σ : K} (x y : SigmaIntegerDepthImage σ) : SigmaIntegerDepthImage σ :=
  ofInt σ (depth x + depth y)

/-- The image zero point. -/
def zero (σ : K) : SigmaIntegerDepthImage σ :=
  ofInt σ 0

/-- THEOREM 12: image addition is serial `satOr` on signed-depth rates. -/
theorem add_val_eq_satOr
    {σ : K} (hσ : σ ≠ 1) (x y : SigmaIntegerDepthImage σ) :
    (add x y).1 = satOrField x.1 y.1 := by
  calc
    (add x y).1 = iteratedRateInt σ (depth x + depth y) := rfl
    _ = satOrField (iteratedRateInt σ (depth x))
        (iteratedRateInt σ (depth y)) := iteratedRateInt_add hσ (depth x) (depth y)
    _ = satOrField x.1 y.1 := by
      rw [← val_eq_iteratedRateInt_depth x,
        ← val_eq_iteratedRateInt_depth y]

/-- THEOREM 13: named signed-depth points add by integer addition. -/
theorem add_ofInt_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) (z w : ℤ) :
    add (ofInt σ z) (ofInt σ w) = ofInt σ (z + w) := by
  simp [add, depth_ofInt_of_mem_Ioo hσ0 hσ1]

/-- THEOREM 14: image addition reflects exactly integer addition. -/
theorem add_eq_ofInt_iff_add_eq_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {z w u : ℤ} :
    add (ofInt σ z) (ofInt σ w) = ofInt σ u ↔ z + w = u := by
  constructor
  · intro h
    apply ofInt_injective_of_mem_Ioo hσ0 hσ1
    calc
      ofInt σ (z + w) = add (ofInt σ z) (ofInt σ w) :=
        (add_ofInt_of_mem_Ioo hσ0 hσ1 z w).symm
      _ = ofInt σ u := h
  · intro h
    rw [← h]
    exact add_ofInt_of_mem_Ioo hσ0 hσ1 z w

/-- THEOREM 15: image addition is associative. -/
theorem add_assoc_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y z : SigmaIntegerDepthImage σ) :
    add (add x y) z = add x (add y z) := by
  rw [← ofInt_depth_eq x, ← ofInt_depth_eq y, ← ofInt_depth_eq z]
  simp [add, depth_ofInt_of_mem_Ioo hσ0 hσ1, add_assoc]

/-- THEOREM 16: image addition is commutative. -/
theorem add_comm_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y : SigmaIntegerDepthImage σ) :
    add x y = add y x := by
  rw [← ofInt_depth_eq x, ← ofInt_depth_eq y]
  simp [add, depth_ofInt_of_mem_Ioo hσ0 hσ1, add_comm]

/-- THEOREM 17: zero is a left identity for signed-depth image addition. -/
theorem zero_add_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x : SigmaIntegerDepthImage σ) :
    add (zero σ) x = x := by
  rw [← ofInt_depth_eq x]
  simp [add, zero, depth_ofInt_of_mem_Ioo hσ0 hσ1]

/-- THEOREM 18: every signed-depth image point has an additive inverse. -/
theorem add_left_neg_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x : SigmaIntegerDepthImage σ) :
    add (ofInt σ (-(depth x))) x = zero σ := by
  rw [← ofInt_depth_eq x]
  simp [add, zero, depth_ofInt_of_mem_Ioo hσ0 hσ1]

/-- A compact certificate for the integer-depth layer. -/
structure IntegerDepthImageCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  carrier_equiv_int :
    SigmaIntegerDepthImage σ ≃ ℤ
  signed_add_is_satOr :
    ∀ x y : SigmaIntegerDepthImage σ,
      (add x y).1 = satOrField x.1 y.1
  add_reflects_int :
    ∀ z w u : ℤ,
      add (ofInt σ z) (ofInt σ w) = ofInt σ u ↔ z + w = u
  add_assoc :
    ∀ x y z : SigmaIntegerDepthImage σ, add (add x y) z = add x (add y z)
  add_comm :
    ∀ x y : SigmaIntegerDepthImage σ, add x y = add y x
  zero_add :
    ∀ x : SigmaIntegerDepthImage σ, add (zero σ) x = x
  add_left_neg :
    ∀ x : SigmaIntegerDepthImage σ, add (ofInt σ (-(depth x))) x = zero σ
  monoid_hom :
    Multiplicative ℤ →* NonAbsorbingRate (α := K)
  monoid_hom_apply :
    ∀ z : Multiplicative ℤ,
      (monoid_hom z).1 = iteratedRateInt σ z.toAdd

/-- THEOREM 19: the canonical integer-depth certificate on `0 < σ < 1`. -/
def integerDepthImageCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    IntegerDepthImageCertificate σ hσ0 hσ1 where
  carrier_equiv_int := equivIntOfMemIoo hσ0 hσ1
  signed_add_is_satOr := add_val_eq_satOr (ne_of_lt hσ1)
  add_reflects_int := by
    intro z w u
    exact add_eq_ofInt_iff_add_eq_of_mem_Ioo hσ0 hσ1
  add_assoc := add_assoc_of_mem_Ioo hσ0 hσ1
  add_comm := add_comm_of_mem_Ioo hσ0 hσ1
  zero_add := zero_add_of_mem_Ioo hσ0 hσ1
  add_left_neg := add_left_neg_of_mem_Ioo hσ0 hσ1
  monoid_hom := iteratedRateIntMonoidHom σ (ne_of_lt hσ1)
  monoid_hom_apply := iteratedRateIntMonoidHom_apply σ (ne_of_lt hσ1)

end SigmaIntegerDepthImage

end AffineRelaxation
end SaturationMonoid
