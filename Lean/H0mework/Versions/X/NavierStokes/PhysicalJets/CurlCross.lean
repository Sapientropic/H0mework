import H0mework.NavierStokes.SourceAction.SpatialOperators
import H0mework.Versions.X.NavierStokes.ResolvedAction.ResolvedNonlinearReadout

set_option autoImplicit false
open scoped BigOperators ContDiff

namespace SaturationMonoid.NavierStokes.NativeFluidCurlCross

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientPhysicalCompiler

noncomputable section

def crossValue (left right : PhysicalSpace) : PhysicalSpace :=
  WithLp.toLp 2 ![left 1 * right 2 - left 2 * right 1,
    left 2 * right 0 - left 0 * right 2, left 0 * right 1 - left 1 * right 0]

def crossRight (left : PhysicalSpace) : PhysicalSpace →L[ℝ] PhysicalSpace :=
  ({ toFun := crossValue left
     map_add' := by intro first second; ext output; fin_cases output <;> simp [crossValue] <;> ring
     map_smul' := by intro scalar right; ext output; fin_cases output <;> simp [crossValue] <;> ring
    } : PhysicalSpace →ₗ[ℝ] PhysicalSpace).toContinuousLinearMap

def crossCLM : PhysicalSpace →L[ℝ] PhysicalSpace →L[ℝ] PhysicalSpace :=
  ({ toFun := crossRight
     map_add' := by
       intro first second
       apply ContinuousLinearMap.ext
       intro right
       ext output
       fin_cases output <;> simp [crossRight, crossValue] <;> ring
     map_smul' := by
       intro scalar left
       apply ContinuousLinearMap.ext
       intro right
       ext output
       fin_cases output <;> simp [crossRight, crossValue] <;> ring
    } : PhysicalSpace →ₗ[ℝ] PhysicalSpace →L[ℝ] PhysicalSpace).toContinuousLinearMap

def cross (left right : PhysicalSpace → PhysicalSpace) (space : PhysicalSpace) : PhysicalSpace :=
  crossCLM (left space) (right space)

theorem cross_contDiff (left right : PhysicalSpace → PhysicalSpace)
    (leftSmooth : ContDiff ℝ ∞ left) (rightSmooth : ContDiff ℝ ∞ right) :
    ContDiff ℝ ∞ (cross left right) :=
  (crossCLM.contDiff.comp leftSmooth).clm_apply rightSmooth

theorem cross_fderiv (left right : PhysicalSpace → PhysicalSpace) (space increment : PhysicalSpace)
    (leftDiff : DifferentiableAt ℝ left space) (rightDiff : DifferentiableAt ℝ right space) :
    fderiv ℝ (cross left right) space increment =
      crossValue (fderiv ℝ left space increment) (right space) +
        crossValue (left space) (fderiv ℝ right space increment) := by
  have written := (crossCLM.hasFDerivAt.comp space leftDiff.hasFDerivAt).clm_apply rightDiff.hasFDerivAt
  have actual := congrArg (fun derivative => derivative increment) written.fderiv
  change fderiv ℝ (cross left right) space increment =
    crossValue (left space) (fderiv ℝ right space increment) +
      crossValue (fderiv ℝ left space increment) (right space) at actual
  exact actual.trans (add_comm _ _)

private theorem apply_coordinates (derivative : PhysicalSpace →L[ℝ] PhysicalSpace)
    (value : PhysicalSpace) (output : Coordinate) :
    derivative value output = ∑ direction : Coordinate, value direction * derivative (EuclideanSpace.single direction 1) output := by
  rw [← (EuclideanSpace.basisFun Coordinate ℝ).sum_repr value, map_sum]
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, PiLp.single_apply,
    mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]

theorem curl_cross (left right : PhysicalSpace → PhysicalSpace) (space : PhysicalSpace)
    (leftDiff : DifferentiableAt ℝ left space) (rightDiff : DifferentiableAt ℝ right space) :
    vorticityField (cross left right) space =
      fderiv ℝ left space (right space) - fderiv ℝ right space (left space) +
        velocityDivergence right space • left space - velocityDivergence left space • right space := by
  rw [vorticityField_apply]
  simp_rw [cross_fderiv left right space _ leftDiff rightDiff]
  ext output
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
  rw [apply_coordinates (fderiv ℝ left space) (right space) output,
    apply_coordinates (fderiv ℝ right space) (left space) output]
  fin_cases output <;>
    simp [crossValue, velocityDivergence, velocityDivergenceReadout,
      velocityDivergenceReadoutLinear, Fin.sum_univ_three] <;> ring

theorem source_vorticity_divergence (source : RawVorticityFourierSource) :
    velocityDivergence (physicalVorticity source) = 0 := by
  rw [physicalVorticity, velocityDivergence_finiteRealComplexFourierField]
  funext space
  apply Finset.sum_eq_zero
  intro wave _
  have transverse := generatedVorticityCoefficient_transverse source wave
  simp [fourierDivergenceCoefficient, transverse, realComplexScalarFourierMode]

theorem source_nonlinear_curl (source : RawVorticityFourierSource) :
    -vorticityAdvection (physicalVelocity source) + vortexStretching (physicalVelocity source) =
      vorticityField (cross (physicalVelocity source) (physicalVorticity source)) := by
  funext space
  rw [curl_cross _ _ space ((physicalVelocity_contDiff source).differentiable (by simp) space)
    ((physicalVorticity_contDiff source).differentiable (by simp) space),
    source_vorticity_divergence, velocityDivergence_physicalVelocity_eq_zero]
  simp only [Pi.zero_apply, zero_smul, add_zero, sub_zero, Pi.add_apply, Pi.neg_apply,
    vorticityAdvection, vortexStretching, vorticityField_physicalVelocity]
  abel

theorem cross_restrict (left right : PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint → PhysicalSpace)
    (time : ℝ) :
    cross (NativeFluidSpatialOperators.restrict left time) (NativeFluidSpatialOperators.restrict right time) =
      NativeFluidSpatialOperators.restrict (PhysicsCore.Stage9CU.Fluid.cross left right) time := rfl

theorem curl_cross_restrict (left right : PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint → PhysicalSpace)
    (leftSmooth : ContDiff ℝ ∞ left) (rightSmooth : ContDiff ℝ ∞ right) (time : ℝ) :
    vorticityField (cross (NativeFluidSpatialOperators.restrict left time) (NativeFluidSpatialOperators.restrict right time)) =
      NativeFluidSpatialOperators.restrict (PhysicsCore.Stage9CU.Fluid.curl (PhysicsCore.Stage9CU.Fluid.cross left right)) time := by
  rw [cross_restrict]
  exact NativeFluidSpatialOperators.curl_restrict _ (PhysicsCore.Stage9CU.Fluid.cross_contDiff leftSmooth rightSmooth) time

end
end SaturationMonoid.NavierStokes.NativeFluidCurlCross
