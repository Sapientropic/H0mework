import H0mework.Realization.QuerySupport.P224

/-!
# Proposition 225: target-general affine relaxation

`Basic.lean` proves the saturation bump

  `h -> h + sigma * (1 - h)`,

which is relaxation toward the distinguished target `1`.  The unification note
uses the target-general scalar equation

  `x -> x + sigma * (target - x)`.

This file proves the scalar algebra behind that generalization.  It does not
formalize complex analytic continuation, vector/tensor carriers, or any physics
claim.  It only closes the ordered-field / real-metric target-general
relaxation law.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Target-general relaxation over a field -/

/-- Relax `x` by rate `sigma` toward an arbitrary `target`. -/
def relaxTo {alpha : Type*} [Field alpha] (target sigma x : alpha) : alpha :=
  x + sigma * (target - x)

/-- Convex-combination form of target-general relaxation. -/
lemma relaxTo_eq_convex
    {alpha : Type*} [Field alpha] (target sigma x : alpha) :
    relaxTo target sigma x = (1 - sigma) * x + sigma * target := by
  unfold relaxTo
  ring

/-- Residual-to-target form: relaxation multiplies the remaining residual by
`1 - sigma`. -/
lemma target_sub_relaxTo
    {alpha : Type*} [Field alpha] (target sigma x : alpha) :
    target - relaxTo target sigma x = (1 - sigma) * (target - x) := by
  unfold relaxTo
  ring

/-- The target-general law reduces to `bumpSatField` at target `1`. -/
theorem relaxTo_one_eq_bumpSatField
    {alpha : Type*} [Field alpha] (sigma x : alpha) :
    relaxTo 1 sigma x = bumpSatField x sigma := by
  rw [relaxTo_eq_convex, bumpSatField_eq]
  ring

/-! ## Noisy-OR composition still governs rates -/

/-- Noisy-OR composition is associative over any field carrier. -/
theorem satOrField_assoc_general
    {alpha : Type*} [Field alpha] (sigma1 sigma2 sigma3 : alpha) :
    satOrField (satOrField sigma1 sigma2) sigma3 =
      satOrField sigma1 (satOrField sigma2 sigma3) := by
  unfold satOrField
  ring

/-- Noisy-OR composition is commutative over any field carrier. -/
theorem satOrField_comm_general
    {alpha : Type*} [Field alpha] (sigma1 sigma2 : alpha) :
    satOrField sigma1 sigma2 = satOrField sigma2 sigma1 := by
  unfold satOrField
  ring

/-- Zero is the no-op rate over any field carrier. -/
theorem satOrField_zero_right_general
    {alpha : Type*} [Field alpha] (sigma : alpha) :
    satOrField sigma 0 = sigma := by
  unfold satOrField
  ring

/-- One is the absorbing rate over any field carrier. -/
theorem satOrField_one_right_general
    {alpha : Type*} [Field alpha] (sigma : alpha) :
    satOrField sigma 1 = 1 := by
  unfold satOrField
  ring

/-- Two relaxations toward the same target compose as one relaxation whose rate
is the noisy-OR of the two rates. -/
theorem relaxTo_compose
    {alpha : Type*} [Field alpha] (target x sigma1 sigma2 : alpha) :
    relaxTo target sigma2 (relaxTo target sigma1 x) =
      relaxTo target (satOrField sigma1 sigma2) x := by
  unfold relaxTo satOrField
  ring

/-- Relaxation order is irrelevant when both steps share the same target. -/
theorem relaxTo_compose_comm
    {alpha : Type*} [Field alpha] (target x sigma1 sigma2 : alpha) :
    relaxTo target sigma2 (relaxTo target sigma1 x) =
      relaxTo target sigma1 (relaxTo target sigma2 x) := by
  unfold relaxTo
  ring

/-- Three same-target relaxations associate through noisy-OR rate composition.
-/
theorem relaxTo_compose_assoc
    {alpha : Type*} [Field alpha]
    (target x sigma1 sigma2 sigma3 : alpha) :
    relaxTo target sigma3 (relaxTo target sigma2 (relaxTo target sigma1 x)) =
      relaxTo target (satOrField sigma1 (satOrField sigma2 sigma3)) x := by
  unfold relaxTo satOrField
  ring

/-- Rate `0` is a no-op relaxation. -/
theorem relaxTo_zero
    {alpha : Type*} [Field alpha] (target x : alpha) :
    relaxTo target 0 x = x := by
  unfold relaxTo
  ring

/-- Rate `1` jumps directly to the target. -/
theorem relaxTo_one
    {alpha : Type*} [Field alpha] (target x : alpha) :
    relaxTo target 1 x = target := by
  unfold relaxTo
  ring

/-- The target itself is an absorbing state for every rate. -/
theorem relaxTo_target_absorbing
    {alpha : Type*} [Field alpha] (target sigma : alpha) :
    relaxTo target sigma target = target := by
  unfold relaxTo
  ring

/-! ## Runtime interval preservation over ordered fields -/

/-- Relaxing between two points in `[lo, hi]` with a rate in `[0, 1]` stays in
`[lo, hi]`. -/
theorem relaxTo_mem_Icc
    {alpha : Type*} [Field alpha] [LinearOrder alpha] [IsStrictOrderedRing alpha]
    (lo hi target sigma x : alpha)
    (hx0 : lo <= x) (hx1 : x <= hi)
    (ht0 : lo <= target) (ht1 : target <= hi)
    (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    lo <= relaxTo target sigma x ∧ relaxTo target sigma x <= hi := by
  rw [relaxTo_eq_convex]
  constructor
  · have hres_nonneg : 0 <= 1 - sigma := by nlinarith
    have hleft_x : (1 - sigma) * lo <= (1 - sigma) * x :=
      mul_le_mul_of_nonneg_left hx0 hres_nonneg
    have hleft_t : sigma * lo <= sigma * target :=
      mul_le_mul_of_nonneg_left ht0 hs0
    nlinarith
  · have hres_nonneg : 0 <= 1 - sigma := by nlinarith
    have hright_x : (1 - sigma) * x <= (1 - sigma) * hi :=
      mul_le_mul_of_nonneg_left hx1 hres_nonneg
    have hright_t : sigma * target <= sigma * hi :=
      mul_le_mul_of_nonneg_left ht1 hs0
    nlinarith

/-! ## Real metric contraction facts -/

/-- Two target-general relaxation outputs are separated by `|1 - sigma|` times
the original separation. -/
theorem dist_relaxTo_real (target sigma x y : ℝ) :
    dist (relaxTo target sigma x) (relaxTo target sigma y) =
      |1 - sigma| * dist x y := by
  simp [Real.dist_eq, relaxTo_eq_convex]
  have h :
      (1 - sigma) * x - (1 - sigma) * y =
          (1 - sigma) * (x - y) := by
    ring
  rw [h, abs_mul]

/-- Distance to the target contracts by `|1 - sigma|`. -/
theorem dist_relaxTo_target_real (target sigma x : ℝ) :
    dist (relaxTo target sigma x) target =
      |1 - sigma| * dist x target := by
  calc
    dist (relaxTo target sigma x) target =
        dist (relaxTo target sigma x) (relaxTo target sigma target) := by
          rw [relaxTo_target_absorbing]
    _ = |1 - sigma| * dist x target := dist_relaxTo_real target sigma x target

/-- For rates in `[0, 1]`, the real relaxation map is Lipschitz with constant
`1 - sigma`. -/
theorem lipschitzWith_relaxTo_real
    (target sigma : ℝ) (hs1 : sigma <= 1) :
    LipschitzWith (Real.toNNReal (1 - sigma))
      (fun x : ℝ => relaxTo target sigma x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_relaxTo_real]
  have hres_nonneg : 0 <= 1 - sigma := by linarith
  rw [abs_of_nonneg hres_nonneg]
  simp [Real.toNNReal_of_nonneg hres_nonneg]

/-- The target-general real relaxation map is continuous. -/
theorem continuous_relaxTo_real (target sigma : ℝ) :
    Continuous (fun x : ℝ => relaxTo target sigma x) := by
  unfold relaxTo
  continuity

/-!
  Summary:
  - `X -> X + sigma * (Target - X)` has the same noisy-OR rate law as
    `bumpSat`.
  - Target `1` recovers `bumpSatField`.
  - On ordered fields, `[lo, hi]` is preserved under rates in `[0, 1]`.
  - On `ℝ`, the map is Lipschitz/continuous and contracts distances by
    `|1 - sigma|`.

  Boundary:
  - This is scalar field/ordered-field/real-metric algebra only.  Complex,
    vector, tensor, gauge, and standard-model readings remain separate routes.
-/


end

end AffineRelaxation
end SaturationMonoid
