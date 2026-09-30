import H0mework.Chemistry.LAlanineTrueTubeWhole.ErrorParameters
import H0mework.Chemistry.LAlanineTrueTube.TraceSignedField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeError

open SourceGaussianModel ContinuousGradient ContinuousParameterMap TrueTubeSource TrueTubeTrace
open TrueTubeError TrueTubeWholeActual Set
open scoped NNReal
noncomputable section

attribute [local irreducible] parameterMap parameterJacobian sourceGradient

def signedFinite (d : Direction) (p : BandPoint) (t : ℝ) : Point :=
  finiteTrajectory (zeroTimeParameters p.val) ((sign d : ℝ) * t)

def signedFiniteVelocity (d : Direction) (p : BandPoint) (t : ℝ) : Point :=
  (sign d : ℝ) • finiteVelocity (zeroTimeParameters p.val) ((sign d : ℝ) * t)

theorem signedFinite_hasDerivAt (d : Direction) (p : BandPoint) (t : ℝ) :
    HasDerivAt (signedFinite d p) (signedFiniteVelocity d p t) t := by
  unfold signedFinite signedFiniteVelocity
  convert! (finiteTrajectory_hasDerivAt (zeroTimeParameters p.val) ((sign d : ℝ) * t)).scomp t
    ((hasDerivAt_id t).const_mul (sign d : ℝ)) using 1
  simp only [mul_one]

theorem signed_time_inside (d : Direction) (t : ℝ) (time : t ∈ Icc (0 : ℝ) (1 / 2)) :
    (sign d : ℝ) * t ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
  fin_cases d
  · change (sign (0 : Direction) : ℝ) * t ∈ _
    rw [TrueTubeChecks.directions.1, Rat.cast_neg, Rat.cast_one, neg_one_mul]
    constructor <;> linarith [time.1, time.2]
  · change (sign (1 : Direction) : ℝ) * t ∈ _
    rw [TrueTubeChecks.directions.2, Rat.cast_one, one_mul]
    exact ⟨by linarith [time.1], time.2⟩

theorem signedFinite_starts (d : Direction) (p : BandPoint) :
    signedFinite d p 0 = initialMap 0 4 p.val := by
  simp only [signedFinite, mul_zero, finiteTrajectory_same_initial]

theorem signed_defect_norm_le (d : Direction) (p : BandPoint) (t : ℝ)
    (time : t ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖signedFiniteVelocity d p t - signedGradient (sign d) (signedFinite d p t)‖ ≤
      (wholeDefectBound : ℝ) := by
  have unit : |(sign d : ℝ)| = 1 := by exact_mod_cast (TrueTubeChecks.direction_units d).1
  simpa only [signedFiniteVelocity, signedFinite, signedGradient, ← smul_sub, norm_smul,
    Real.norm_eq_abs, unit, one_mul] using
    finite_defect_norm_le p ((sign d : ℝ) * t) (signed_time_inside d t time)

/-- The original finite-map defect is generated above; the comparison input is an actual path law. -/
theorem compare_signed (d : Direction) (p : BandPoint) (region : Set Point) (K : ℝ≥0)
    (lipschitz : LipschitzOnWith K (signedGradient (sign d)) region)
    (finiteInside : ∀ t ∈ Ico (0 : ℝ) (1 / 2), signedFinite d p t ∈ region)
    (actual : ℝ → Point)
    (evolves : IsIntegralCurveOn actual (fun _ => signedGradient (sign d)) (Icc (0 : ℝ) (1 / 2)))
    (actualInside : ∀ t ∈ Ico (0 : ℝ) (1 / 2), actual t ∈ region)
    (starts : actual 0 = initialMap 0 4 p.val) :
    ∀ t ∈ Icc (0 : ℝ) (1 / 2), dist (signedFinite d p t) (actual t) ≤
      gronwallBound 0 K wholeDefectBound t := by
  have comparison := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun _ => signedGradient (sign d)) (s := fun _ => region)
    (f' := signedFiniteVelocity d p) (g' := fun t => signedGradient (sign d) (actual t))
    (δ := 0) (εf := (wholeDefectBound : ℝ)) (εg := 0)
    (fun _ _ => lipschitz)
    (show Continuous (signedFinite d p) from
      (show Differentiable ℝ (signedFinite d p) from
        fun t => (signedFinite_hasDerivAt d p t).differentiableAt).continuous).continuousOn
    (fun t _ => (signedFinite_hasDerivAt d p t).hasDerivWithinAt)
    (fun t ht => by rw [dist_eq_norm]; exact signed_defect_norm_le d p t (Ico_subset_Icc_self ht))
    finiteInside evolves.continuousOn
    (fun t ht => (evolves t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun _ _ => by simp only [dist_self, le_refl]) actualInside
    (by rw [signedFinite_starts, starts, dist_self])
  simpa only [add_zero, sub_zero] using comparison

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeError
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
