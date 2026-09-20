import H0mework.Realization.RelaxationFlow.P312
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition 313: real-depth sigma relaxation

P312 extended the iteration image from natural depths to signed integer
depths.  The next layer is the continuous depth carrier.  For a real depth
`t : ℝ`, use the same residual coordinate:

`iteratedRateReal σ t = 1 - (1 - σ)^t`.

When `0 < σ < 1`, the residual base `1 - σ` is positive and not `1`, so real
power is injective in the exponent.  Thus the sigma image is equivalent to
`ℝ`; serial noisy-OR composition is exactly addition of real depths.

Boundary: this is the continuous-depth algebraic carrier.  It is not a
physical time-scale producer, not an RG flow, and not a proof that a runtime
reducer exposes real-valued depths without a mechanism-faithfulness certificate.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

/-! ## Real-depth effective rates -/

/-- The effective rate for a real-valued depth. -/
def iteratedRateReal (σ t : ℝ) : ℝ :=
  1 - (1 - σ) ^ t

/-- THEOREM 1: the residual keep-rate at real depth `t` is `(1-σ)^t`. -/
theorem keep_iteratedRateReal (σ t : ℝ) :
    1 - iteratedRateReal σ t = (1 - σ) ^ t := by
  unfold iteratedRateReal
  ring

/-- THEOREM 2: zero real depth is the no-op rate. -/
@[simp] theorem iteratedRateReal_zero (σ : ℝ) :
    iteratedRateReal σ 0 = 0 := by
  simp [iteratedRateReal]

/-- THEOREM 3: real depth `1` is the original base rate. -/
@[simp] theorem iteratedRateReal_one (σ : ℝ) :
    iteratedRateReal σ 1 = σ := by
  simp [iteratedRateReal]

/-- THEOREM 4: real depth extends the signed integer-depth formula. -/
theorem iteratedRateReal_intCast
    (σ : ℝ) (z : ℤ) :
    iteratedRateReal σ (z : ℝ) = iteratedRateInt σ z := by
  simp [iteratedRateReal, iteratedRateInt, Real.rpow_intCast]

/-- THEOREM 5: serial noisy-OR composition is addition of real depths. -/
theorem iteratedRateReal_add
    {σ : ℝ} (hkeep : 0 < 1 - σ) (t u : ℝ) :
    iteratedRateReal σ (t + u) =
      satOrField (iteratedRateReal σ t) (iteratedRateReal σ u) := by
  unfold iteratedRateReal satOrField
  rw [Real.rpow_add hkeep]
  ring

/-- THEOREM 6: a real depth and its negative compose to the no-op rate. -/
theorem satOr_iteratedRateReal_neg
    {σ : ℝ} (hkeep : 0 < 1 - σ) (t : ℝ) :
    satOrField (iteratedRateReal σ t) (iteratedRateReal σ (-t)) = 0 := by
  have h := iteratedRateReal_add (σ := σ) hkeep t (-t)
  simpa using h.symm

/-- Real-depth effective rates never hit the absorbing rate when the residual
base is positive. -/
theorem iteratedRateReal_ne_one_of_keep_pos
    {σ : ℝ} (hkeep : 0 < 1 - σ) (t : ℝ) :
    iteratedRateReal σ t ≠ 1 := by
  intro h
  have hz : (1 - σ) ^ t = 0 := by
    have hk := keep_iteratedRateReal σ t
    rw [h] at hk
    simpa using hk.symm
  exact (Real.rpow_pos_of_pos hkeep t).ne' hz

/-- A real-depth effective rate bundled as a non-absorbing noisy-OR rate. -/
def iteratedRealNonAbsorbingRate
    (σ : ℝ) (hkeep : 0 < 1 - σ) (t : ℝ) :
    NonAbsorbingRate (α := ℝ) :=
  ⟨iteratedRateReal σ t, iteratedRateReal_ne_one_of_keep_pos hkeep t⟩

@[simp] theorem iteratedRealNonAbsorbingRate_val
    (σ : ℝ) (hkeep : 0 < 1 - σ) (t : ℝ) :
    (iteratedRealNonAbsorbingRate σ hkeep t).1 = iteratedRateReal σ t := rfl

/-- THEOREM 7: real-depth rates multiply in the non-absorbing noisy-OR group
by adding real depths. -/
theorem iteratedRealNonAbsorbingRate_add
    (σ : ℝ) (hkeep : 0 < 1 - σ) (t u : ℝ) :
    iteratedRealNonAbsorbingRate σ hkeep (t + u) =
      iteratedRealNonAbsorbingRate σ hkeep t *
        iteratedRealNonAbsorbingRate σ hkeep u := by
  ext
  exact iteratedRateReal_add hkeep t u

/-- THEOREM 8: real depth `0` maps to the noisy-OR group identity. -/
@[simp] theorem iteratedRealNonAbsorbingRate_zero
    (σ : ℝ) (hkeep : 0 < 1 - σ) :
    iteratedRealNonAbsorbingRate σ hkeep 0 = 1 := by
  ext
  simp [iteratedRealNonAbsorbingRate]

/-- THEOREM 9: real depths form a monoid hom into the non-absorbing noisy-OR
rate group.  Multiplication in `Multiplicative ℝ` is addition of ordinary
real depths. -/
def iteratedRateRealMonoidHom
    (σ : ℝ) (hkeep : 0 < 1 - σ) :
    Multiplicative ℝ →* NonAbsorbingRate (α := ℝ) where
  toFun t := iteratedRealNonAbsorbingRate σ hkeep t.toAdd
  map_one' := by
    ext
    simp [iteratedRealNonAbsorbingRate]
  map_mul' := by
    intro t u
    ext
    exact iteratedRateReal_add hkeep t.toAdd u.toAdd

@[simp] theorem iteratedRateRealMonoidHom_apply
    (σ : ℝ) (hkeep : 0 < 1 - σ) (t : Multiplicative ℝ) :
    (iteratedRateRealMonoidHom σ hkeep t).1 =
      iteratedRateReal σ t.toAdd := rfl

/-- THEOREM 10: real-depth hom multiplication is exactly serial noisy-OR on
values. -/
theorem iteratedRateRealMonoidHom_map_mul_val
    (σ : ℝ) (hkeep : 0 < 1 - σ) (t u : Multiplicative ℝ) :
    ((iteratedRateRealMonoidHom σ hkeep (t * u)).1 : ℝ) =
      satOrField
        (iteratedRateRealMonoidHom σ hkeep t).1
        (iteratedRateRealMonoidHom σ hkeep u).1 := by
  change iteratedRateReal σ (t.toAdd + u.toAdd) =
    satOrField (iteratedRateReal σ t.toAdd) (iteratedRateReal σ u.toAdd)
  exact iteratedRateReal_add hkeep t.toAdd u.toAdd

/-! ## The real-depth image carrier -/

/-- The image of real depths inside the sigma carrier. -/
def SigmaRealDepthImage (σ : ℝ) : Type :=
  { r : ℝ // ∃ t : ℝ, r = iteratedRateReal σ t }

namespace SigmaRealDepthImage

/-- The image point corresponding to a real depth. -/
def ofReal (σ t : ℝ) : SigmaRealDepthImage σ :=
  ⟨iteratedRateReal σ t, ⟨t, rfl⟩⟩

/-- A chosen real depth for an image point. -/
def depth {σ : ℝ} (r : SigmaRealDepthImage σ) : ℝ :=
  Classical.choose r.2

/-- The chosen depth represents the image point. -/
theorem val_eq_iteratedRateReal_depth
    {σ : ℝ} (r : SigmaRealDepthImage σ) :
    r.1 = iteratedRateReal σ (depth r) :=
  Classical.choose_spec r.2

/-- Every image point is the `ofReal` point of its chosen depth. -/
theorem ofReal_depth_eq
    {σ : ℝ} (r : SigmaRealDepthImage σ) :
    ofReal σ (depth r) = r := by
  apply Subtype.ext
  exact (val_eq_iteratedRateReal_depth r).symm

/-- On `0 < σ < 1`, real-depth effective rates are injective in the depth. -/
theorem ofReal_injective_of_mem_Ioo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Function.Injective (ofReal σ) := by
  intro t u h
  have hval : iteratedRateReal σ t = iteratedRateReal σ u :=
    congrArg Subtype.val h
  have hpows : (1 - σ) ^ t = (1 - σ) ^ u := by
    calc
      (1 - σ) ^ t = 1 - iteratedRateReal σ t :=
        (keep_iteratedRateReal σ t).symm
      _ = 1 - iteratedRateReal σ u := by rw [hval]
      _ = (1 - σ) ^ u := keep_iteratedRateReal σ u
  have hkeep_pos : 0 < 1 - σ := sub_pos.mpr hσ1
  have hkeep_ne_one : 1 - σ ≠ 1 := by nlinarith
  exact (Real.rpow_right_inj hkeep_pos hkeep_ne_one).mp hpows

/-- On `0 < σ < 1`, the chosen depth of `ofReal t` is `t`. -/
theorem depth_ofReal_of_mem_Ioo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    depth (ofReal σ t) = t := by
  apply ofReal_injective_of_mem_Ioo hσ0 hσ1
  exact ofReal_depth_eq (ofReal σ t)

/-- The real-depth image is equivalent to `ℝ` on `0 < σ < 1`. -/
def equivRealOfMemIoo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaRealDepthImage σ ≃ ℝ where
  toFun r := depth r
  invFun t := ofReal σ t
  left_inv := ofReal_depth_eq
  right_inv := depth_ofReal_of_mem_Ioo hσ0 hσ1

/-- Addition on the real-depth image, transported from `ℝ`. -/
def add {σ : ℝ} (x y : SigmaRealDepthImage σ) : SigmaRealDepthImage σ :=
  ofReal σ (depth x + depth y)

/-- The image zero point. -/
def zero (σ : ℝ) : SigmaRealDepthImage σ :=
  ofReal σ 0

/-- THEOREM 11: image addition is serial `satOr` on real-depth rates. -/
theorem add_val_eq_satOr
    {σ : ℝ} (hkeep : 0 < 1 - σ) (x y : SigmaRealDepthImage σ) :
    (add x y).1 = satOrField x.1 y.1 := by
  calc
    (add x y).1 = iteratedRateReal σ (depth x + depth y) := rfl
    _ = satOrField (iteratedRateReal σ (depth x))
        (iteratedRateReal σ (depth y)) := iteratedRateReal_add hkeep (depth x) (depth y)
    _ = satOrField x.1 y.1 := by
      rw [← val_eq_iteratedRateReal_depth x,
        ← val_eq_iteratedRateReal_depth y]

/-- THEOREM 12: named real-depth points add by real addition. -/
theorem add_ofReal_of_mem_Ioo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t u : ℝ) :
    add (ofReal σ t) (ofReal σ u) = ofReal σ (t + u) := by
  simp [add, depth_ofReal_of_mem_Ioo hσ0 hσ1]

/-- THEOREM 13: image addition reflects exactly real addition. -/
theorem add_eq_ofReal_iff_add_eq_of_mem_Ioo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t u v : ℝ} :
    add (ofReal σ t) (ofReal σ u) = ofReal σ v ↔ t + u = v := by
  constructor
  · intro h
    apply ofReal_injective_of_mem_Ioo hσ0 hσ1
    calc
      ofReal σ (t + u) = add (ofReal σ t) (ofReal σ u) :=
        (add_ofReal_of_mem_Ioo hσ0 hσ1 t u).symm
      _ = ofReal σ v := h
  · intro h
    rw [← h]
    exact add_ofReal_of_mem_Ioo hσ0 hσ1 t u

/-- THEOREM 14: image addition is associative. -/
theorem add_assoc_of_mem_Ioo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y z : SigmaRealDepthImage σ) :
    add (add x y) z = add x (add y z) := by
  rw [← ofReal_depth_eq x, ← ofReal_depth_eq y, ← ofReal_depth_eq z]
  simp [add, depth_ofReal_of_mem_Ioo hσ0 hσ1, add_assoc]

/-- THEOREM 15: image addition is commutative. -/
theorem add_comm_of_mem_Ioo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x y : SigmaRealDepthImage σ) :
    add x y = add y x := by
  rw [← ofReal_depth_eq x, ← ofReal_depth_eq y]
  simp [add, depth_ofReal_of_mem_Ioo hσ0 hσ1, add_comm]

/-- THEOREM 16: zero is a left identity for real-depth image addition. -/
theorem zero_add_of_mem_Ioo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x : SigmaRealDepthImage σ) :
    add (zero σ) x = x := by
  rw [← ofReal_depth_eq x]
  simp [add, zero, depth_ofReal_of_mem_Ioo hσ0 hσ1]

/-- THEOREM 17: every real-depth image point has an additive inverse. -/
theorem add_left_neg_of_mem_Ioo
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x : SigmaRealDepthImage σ) :
    add (ofReal σ (-(depth x))) x = zero σ := by
  rw [← ofReal_depth_eq x]
  simp [add, zero, depth_ofReal_of_mem_Ioo hσ0 hσ1]

/-- A compact certificate for the real-depth layer. -/
structure RealDepthImageCertificate
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  carrier_equiv_real :
    SigmaRealDepthImage σ ≃ ℝ
  real_add_is_satOr :
    ∀ x y : SigmaRealDepthImage σ,
      (add x y).1 = satOrField x.1 y.1
  add_reflects_real :
    ∀ t u v : ℝ,
      add (ofReal σ t) (ofReal σ u) = ofReal σ v ↔ t + u = v
  add_assoc :
    ∀ x y z : SigmaRealDepthImage σ, add (add x y) z = add x (add y z)
  add_comm :
    ∀ x y : SigmaRealDepthImage σ, add x y = add y x
  zero_add :
    ∀ x : SigmaRealDepthImage σ, add (zero σ) x = x
  add_left_neg :
    ∀ x : SigmaRealDepthImage σ, add (ofReal σ (-(depth x))) x = zero σ
  monoid_hom :
    Multiplicative ℝ →* NonAbsorbingRate (α := ℝ)
  monoid_hom_apply :
    ∀ t : Multiplicative ℝ,
      (monoid_hom t).1 = iteratedRateReal σ t.toAdd

/-- THEOREM 18: the canonical real-depth certificate on `0 < σ < 1`. -/
def realDepthImageCertificate
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    RealDepthImageCertificate σ hσ0 hσ1 where
  carrier_equiv_real := equivRealOfMemIoo hσ0 hσ1
  real_add_is_satOr := add_val_eq_satOr (sub_pos.mpr hσ1)
  add_reflects_real := by
    intro t u v
    exact add_eq_ofReal_iff_add_eq_of_mem_Ioo hσ0 hσ1
  add_assoc := add_assoc_of_mem_Ioo hσ0 hσ1
  add_comm := add_comm_of_mem_Ioo hσ0 hσ1
  zero_add := zero_add_of_mem_Ioo hσ0 hσ1
  add_left_neg := add_left_neg_of_mem_Ioo hσ0 hσ1
  monoid_hom := iteratedRateRealMonoidHom σ (sub_pos.mpr hσ1)
  monoid_hom_apply := iteratedRateRealMonoidHom_apply σ (sub_pos.mpr hσ1)

end SigmaRealDepthImage

end AffineRelaxation
end SaturationMonoid
