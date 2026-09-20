import H0mework.Physics.CoframeVariation.CoframeLocalVariation
import H0mework.Physics.Coframe.SynchronizedRadialCoframeHomogeneity

/-! Conformal coframe trace of the authoritative form-native action. The
three gauge blocks have zero trace for arbitrary fields. The source scalar
contact and the actual Dirac equation can consequently determine the gravity
trace without computing a new connection Hessian. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material

open Filter
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineMatterCovariantDerivativeAffine
open StageNineScalarLocalSpinDensity
open StageNineSynchronizedRadialCoframeHomogeneity

open scoped ContDiff

noncomputable section

local instance : NormedAddCommGroup LorentzianCoframe :=
  inferInstanceAs (NormedAddCommGroup (Fin 4 → Fin 4 → ℝ))
local instance : NormedSpace ℝ LorentzianCoframe :=
  inferInstanceAs (NormedSpace ℝ (Fin 4 → Fin 4 → ℝ))

private theorem coframeRadialLine_hasDerivAt (coframe : LorentzianCoframe) :
    HasDerivAt (fun scalar : ℝ => coframe + scalar • coframe) coframe 0 := by
  apply hasDerivAt_pi.mpr
  intro row
  apply hasDerivAt_pi.mpr
  intro column
  change HasDerivAt
    (fun scalar : ℝ => coframe row column + scalar * coframe row column)
    (coframe row column) 0
  have differentiable : DifferentiableAt ℝ
      (fun scalar : ℝ => coframe row column + scalar * coframe row column)
      0 := by fun_prop
  have derivative := differentiable.hasDerivAt
  have productDerivative :
      deriv (fun scalar : ℝ => scalar * coframe row column) 0 =
        coframe row column := by simp
  simpa only [deriv_const_add, productDerivative] using derivative

theorem diracDualFormNativeCoframeGaugeDensity_smul
    (source : SmoothUnifiedSource) (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    diracDualFormNativeCoframeGaugeDensity source field (scalar • field.coframe) =
      diracDualFormNativeCoframeGaugeDensity source field field.coframe := by
  unfold diracDualFormNativeCoframeGaugeDensity
    generatedFormNativeGaugeDensityAtBoundary gaugeConstitutiveOperatorAtBoundary
  simp only [withCoframe]
  rw [coframeGaugeSpacetimeHodgeLinear_smul_of_nondegenerate scalar nonzero
    field.coframe nondegenerate]

theorem diracDualFormNativeCoframeGaugeEulerCovector_trace_zero
    (source : SmoothUnifiedSource) (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    diracDualFormNativeCoframeGaugeEulerCovector source field field.coframe = 0 := by
  let line := fun scalar : ℝ => field.coframe + scalar • field.coframe
  have lineDerivative : HasDerivAt line field.coframe 0 :=
    coframeRadialLine_hasDerivAt field.coframe
  have densityDerivative : HasFDerivAt
      (diracDualFormNativeCoframeGaugeDensity source field)
      (diracDualFormNativeCoframeGaugeEulerCovector source field) (line 0) := by
    simpa [line] using
      diracDualFormNativeCoframeGaugeDensity_hasFDerivAt source field nondegenerate
  have evaluated := densityDerivative.comp_hasDerivAt (0 : ℝ) lineDerivative
  have nonzero : ∀ᶠ scalar : ℝ in nhds 0, 1 + scalar ≠ 0 := by
    exact (continuousAt_const.add continuousAt_id).eventually_ne
      (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have constant :
      (fun scalar => diracDualFormNativeCoframeGaugeDensity source field
          (line scalar)) =ᶠ[nhds 0]
        (fun _ => diracDualFormNativeCoframeGaugeDensity source field field.coframe) := by
    filter_upwards [nonzero] with scalar hs
    rw [show line scalar = (1 + scalar) • field.coframe by
      dsimp [line]
      module]
    exact diracDualFormNativeCoframeGaugeDensity_smul source field nondegenerate
      (1 + scalar) hs
  have constantDerivative :=
    (hasDerivAt_const (0 : ℝ)
      (diracDualFormNativeCoframeGaugeDensity source field field.coframe)
      ).congr_of_eventuallyEq constant
  exact evaluated.unique constantDerivative

theorem diracDualFormNativeCoframeEulerCovector_trace_eq_matter_sub_reaction
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    diracDualFormNativeCoframeEulerCovector source point field field.coframe =
      diracDualFormNativeCoframeMatterEulerCovector source point field field.coframe -
        StageNineFormNativeCoframeLocalVariation.formNativeCoframeConstraintReaction
          field field.coframe := by
  rw [diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
    source point field nondegenerate]
  rw [diracDualFormNativeCoframeGaugeEulerCovector_trace_zero source field nondegenerate,
    zero_add]

theorem generatedContinuumMatterKineticVector_coframe_smul
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    generatedContinuumMatterKineticVector source 0 point
        (withCoframe field (scalar • field.coframe)) =
      ((scalar⁻¹ : ℝ) : ℂ) • generatedContinuumMatterKineticVector source 0 point field := by
  have gamma (direction : LorentzianIndex) :
      inverseCoframeDiracGamma
        { coframe := scalar • field.coframe, derivative := 0 } direction =
      ((scalar⁻¹ : ℝ) : ℂ) • inverseCoframeDiracGamma
        { coframe := field.coframe, derivative := 0 } direction := by
    unfold inverseCoframeDiracGamma
    rw [matrix_inv_smul_of_nondegenerate scalar nonzero field.coframe nondegenerate]
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Finset.smul_sum, smul_smul]
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, gamma, coframeDiracMatrixMatterAction_smul_matrix]
  rw [← Finset.smul_sum, smul_comm]

theorem generatedDensitizedContinuumMatterKineticDensity_coframe_smul
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    generatedDensitizedContinuumMatterKineticDensity source 0 point
        (withCoframe field (scalar • field.coframe)) =
      scalar ^ 3 * generatedDensitizedContinuumMatterKineticDensity source 0 point field := by
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [generatedVolumeDensity_withCoframe_smul,
    generatedContinuumMatterKineticVector_coframe_smul source point field
      nondegenerate scalar nonzero]
  simp only [withCoframe, map_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

theorem diracDualFormNativeCoframeMatterDensity_radial_zero
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (scalarDerivativeZero : field.scalarCovariantDerivative = 0)
    (potentialZero : generatedScalarPotential source 0 point field.scalar = 0)
    (kineticZero : generatedDensitizedContinuumMatterKineticDensity source 0 point field = 0)
    (yukawaZero : generatedContinuumDiracDualYukawaVector source 0 point field = 0)
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    diracDualFormNativeCoframeMatterDensity source point field
      (scalar • field.coframe) = 0 := by
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [generatedDensitizedContinuumMatterKineticDensity_coframe_smul source point field
    nondegenerate scalar nonzero, kineticZero, mul_zero]
  have scalarZero : generatedDensitizedContinuumScalarDensity source 0 point
      (withCoframe field (scalar • field.coframe)) = 0 := by
    unfold generatedDensitizedContinuumScalarDensity generatedScalarKineticDensity
    simp only [withCoframe, scalarDerivativeZero, potentialZero]
    simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]
  rw [scalarZero]
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
  rw [show generatedContinuumDiracDualYukawaVector source 0 point
      (withCoframe field (scalar • field.coframe)) = 0 from yukawaZero]
  simp

theorem diracDualFormNativeCoframeMatterEulerCovector_trace_zero_of_radialMaterial
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (scalarDerivativeZero : field.scalarCovariantDerivative = 0)
    (potentialZero : generatedScalarPotential source 0 point field.scalar = 0)
    (kineticZero : generatedDensitizedContinuumMatterKineticDensity source 0 point field = 0)
    (yukawaZero : generatedContinuumDiracDualYukawaVector source 0 point field = 0) :
    diracDualFormNativeCoframeMatterEulerCovector source point field field.coframe = 0 := by
  let line := fun scalar : ℝ => field.coframe + scalar • field.coframe
  have densityDerivative : HasFDerivAt
      (diracDualFormNativeCoframeMatterDensity source point field)
      (diracDualFormNativeCoframeMatterEulerCovector source point field) (line 0) := by
    simpa [line] using
      diracDualFormNativeCoframeMatterDensity_hasFDerivAt source point field nondegenerate
  have evaluated := densityDerivative.comp_hasDerivAt (0 : ℝ)
    (coframeRadialLine_hasDerivAt field.coframe)
  have nonzero : ∀ᶠ scalar : ℝ in nhds 0, 1 + scalar ≠ 0 :=
    (continuousAt_const.add continuousAt_id).eventually_ne
      (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have zero :
      (fun scalar => diracDualFormNativeCoframeMatterDensity source point field
          (line scalar)) =ᶠ[nhds 0] (fun _ => 0) := by
    filter_upwards [nonzero] with scalar hs
    rw [show line scalar = (1 + scalar) • field.coframe by
      dsimp [line]
      module]
    exact diracDualFormNativeCoframeMatterDensity_radial_zero source point field
      nondegenerate scalarDerivativeZero potentialZero kineticZero yukawaZero
      (1 + scalar) hs
  exact evaluated.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq zero)

end
end SaturationMonoid.PhysicsCore.Stage9C.Material
