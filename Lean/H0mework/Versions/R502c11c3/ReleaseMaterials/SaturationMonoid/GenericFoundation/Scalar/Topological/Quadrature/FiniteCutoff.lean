import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Topological.Quadrature.CutoffPair
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Topological.ConservativePort.Transfer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedQuadrature

open Filter SourceGeneratedCompressedUnitaryDefectPort.Feedback
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Doubling the actual cutoff uses a fixed dilation and the original change
of amplitude. Both coefficients stay inside the convergence disk. -/
def cutoffInverse (action : E →ₗᵢ[ℂ] E) (ratio : ℝ) : E →L[ℂ] E :=
  geometric action.toContinuousLinearMap (ratio : ℂ)

omit [CompleteSpace E] in
private theorem action_bound (action : E →ₗᵢ[ℂ] E) :
    ‖action.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [LinearIsometry.coe_toContinuousLinearMap, action.norm_map, one_mul]

private theorem cutoff_inverse_action (action : E →ₗᵢ[ℂ] E) (ratio : ℝ)
    (small : ‖ratio‖ < 1) (x : E) :
    cutoffInverse action ratio (x-ratio • action x) = x := by
  have disk : ‖(ratio : ℂ)‖ < 1 := by
    rwa [Complex.norm_real]
  symm
  apply eq_geometric_of_solve action.toContinuousLinearMap (action_bound action) disk
  rw [LinearIsometry.coe_toContinuousLinearMap, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- An intertwiner transports the complete cutoff inverse. -/
theorem cutoff_inverse_intertwines {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (action : E →ₗᵢ[ℂ] E) (moved : F →ₗᵢ[ℂ] F)
    (map : E →L[ℂ] F) (commutes : ∀ x, map (action x) = moved (map x))
    (ratio : ℝ) (small : ‖ratio‖ < 1) (x : E) :
    map (cutoffInverse action ratio x) = cutoffInverse moved ratio (map x) := by
  have disk : ‖(ratio : ℂ)‖ < 1 := by
    rwa [Complex.norm_real]
  apply eq_geometric_of_solve moved.toContinuousLinearMap (action_bound moved) disk
  have solved := congrArg map (geometric_solve action.toContinuousLinearMap (action_bound action) disk x)
  rw [map_sub, map_smul, LinearIsometry.coe_toContinuousLinearMap, commutes] at solved
  exact solved

/-- First and second asymptotic coordinates of adjacent count differences.
The change of cutoff acts before taking the difference. -/
def finiteCutoffLeading (action : E →ₗᵢ[ℂ] E) (ratio : ℝ) (difference : Nat → E) (m : Nat) : E :=
  cutoffInverse action ratio (difference m)

def finiteCutoffVelocity (action : E →ₗᵢ[ℂ] E) (ratio : ℝ) (difference : Nat → E) (m : Nat) : E :=
  cutoffInverse action (ratio/2) (cutoffPair difference m)

/-- Only differences at consecutive doubled cutoffs are observed. The
unknown full limit cancels, and the two remaining coordinates have explicit inverses. -/
theorem finite_cutoff_coordinates (action : E →ₗᵢ[ℂ] E) (ratio : ℝ)
    (small : ‖ratio‖ < 1) {tail difference : Nat → E} {leading velocity : E}
    (observed : ∀ m, difference m = tail m-ratio • action (tail (doubledCut m)))
    (leadingRead : Tendsto tail atTop (𝓝 leading))
    (velocityRead : Tendsto (fun m : Nat => ((m : ℝ)+1) • (tail m-leading)) atTop (𝓝 velocity)) :
    Tendsto (fun m => (finiteCutoffLeading action ratio difference m,
      finiteCutoffVelocity action ratio difference m)) atTop (𝓝 (leading,velocity)) := by
  let acted := action.toContinuousLinearMap.restrictScalars ℝ
  have next := leadingRead.comp doubledCut_tendsto
  have differenceLeading : Tendsto difference atTop (𝓝 (leading-ratio • action leading)) := by
    have moved := leadingRead.sub (((acted.continuous.tendsto _).comp next).const_smul ratio)
    apply moved.congr'
    exact Eventually.of_forall (fun m => (observed m).symm)
  have differenceVelocity : Tendsto (fun m : Nat => ((m : ℝ)+1) •
      (difference m-(leading-ratio • action leading))) atTop (𝓝 (velocity-(ratio/2) • action velocity)) := by
    have nextSlope := velocityRead.comp doubledCut_tendsto
    have moved := velocityRead.sub (((acted.continuous.tendsto _).comp nextSlope).const_smul (ratio/2))
    apply moved.congr'
    filter_upwards with m
    let n : ℝ := (m : ℝ)+1
    have double : ((doubledCut m : ℕ) : ℝ)+1 = 2*n := by
      unfold doubledCut n
      push_cast
      ring
    rw [Function.comp_apply, Function.comp_apply, double, observed]
    let x := tail m
    let y := tail (doubledCut m)
    change n • (x-leading) - (ratio/2) • acted ((2*n) • (y-leading)) =
      n • ((x-ratio • acted y)-(leading-ratio • acted leading))
    rw [map_smul, map_sub]
    simp only [smul_sub, smul_smul]
    module
  have smallHalf : ‖ratio/2‖ < 1 := by
    rw [norm_div, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have first := ((cutoffInverse action ratio).continuous.tendsto _).comp differenceLeading
  have second := ((cutoffInverse action (ratio/2)).continuous.tendsto _).comp
    (cutoff_pair_tendsto differenceVelocity)
  rw [cutoff_inverse_action action ratio small] at first
  rw [cutoff_inverse_action action (ratio/2) smallHalf] at second
  exact first.prodMk_nhds second

end SourceGeneratedQuadrature
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
