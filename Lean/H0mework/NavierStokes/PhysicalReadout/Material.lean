import H0mework.NavierStokes.PhysicalReadout.TimeAction
import H0mework.NavierStokes.SourceReadout.Material

set_option autoImplicit false
open scoped Matrix ENNReal

namespace SaturationMonoid.NavierStokes.NativePhysicalMaterial

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open PhysicsCore PhysicsCore.Stage9CU.Fluid
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair StageNineFullDiracAdjointMaterial
open NativePhysicalFourier NativePhysicalSource NativePhysicalTimeAction

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Both material coordinates are dependent evaluations of the same complete physical field. -/
def primal (field : PhysicalField) (point : Torus) :=
  InitialLift.matter (fun direction => field point direction)

def dual (field : PhysicalField) (point : Torus) :=
  InitialLift.dual (fun direction => field point direction)

theorem paired (field : PhysicalField) (point : Torus) :
    FullDiracAdjointPaired (primal field point) (dual field point) :=
  InitialLift.fullAdjointPaired _

theorem primalCoefficients_memLp (field : PhysicalField) (spin : Fin 4) (color : Fin 2) :
    MemLp (fun point => InitialLift.coefficients (fun direction => field point direction) spin color)
      2 (volume : Measure Torus) := by
  have each (direction : Fin 3) : MemLp (fun point => (field point direction : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp' (memLp_piLp_iff.mp (Lp.memLp field) direction)
  simp only [div_eq_mul_inv, InitialLift.coefficients]
  fin_cases spin <;> fin_cases color
  · exact MemLp.zero
  · exact MemLp.zero
  · exact MemLp.zero
  · exact MemLp.zero
  · exact (memLp_const (1 : ℂ)).add ((each 2).mul_const (4 : ℂ)⁻¹)
  · exact ((each 0).sub ((each 1).const_mul Complex.I)).mul_const (4 : ℂ)⁻¹
  · exact ((each 0).add ((each 1).const_mul Complex.I)).mul_const (4 : ℂ)⁻¹
  · exact (memLp_const (1 : ℂ)).sub ((each 2).mul_const (4 : ℂ)⁻¹)

theorem dualCoefficients_memLp (field : PhysicalField) (spin : Fin 4) (color : Fin 2) :
    MemLp (fun point => InitialLift.dualCoefficients (fun direction => field point direction) spin color)
      2 (volume : Measure Torus) := by
  have each (direction : Fin 3) : MemLp (fun point => (field point direction : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp' (memLp_piLp_iff.mp (Lp.memLp field) direction)
  simp only [div_eq_mul_inv, InitialLift.dualCoefficients]
  fin_cases spin <;> fin_cases color
  · exact (memLp_const (1 : ℂ)).add ((each 2).mul_const (4 : ℂ)⁻¹)
  · exact ((each 0).add ((each 1).const_mul Complex.I)).mul_const (4 : ℂ)⁻¹
  · exact ((each 0).sub ((each 1).const_mul Complex.I)).mul_const (4 : ℂ)⁻¹
  · exact (memLp_const (1 : ℂ)).sub ((each 2).mul_const (4 : ℂ)⁻¹)
  · exact MemLp.zero
  · exact MemLp.zero
  · exact MemLp.zero
  · exact MemLp.zero

def current (field : PhysicalField) (direction : Fin 4) (point : Torus) : ℝ :=
  (dual field point (diracMatrixMatterAction (diracGamma direction) (primal field point))).re

theorem spatialCurrent_eq (field : PhysicalField) (direction : Fin 3) (point : Torus) :
    current field direction.succ point = field point direction :=
  InitialLift.spatialCurrent_eq _ _

theorem temporalCurrent_eq (field : PhysicalField) (point : Torus) :
    current field 0 point = 2 + ‖field point‖ ^ 2 / 8 := by
  rw [current, dual, primal, InitialLift.temporalCurrent_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem temporalCurrent_integrable (field : PhysicalField) :
    Integrable (current field 0) (volume : Measure Torus) := by
  change Integrable (fun point => current field 0 point) volume
  simp_rw [temporalCurrent_eq]
  exact (integrable_const 2).add ((Lp.memLp field).norm.integrable_sq.div_const 8)

theorem temporalCurrent_integral (field : PhysicalField) :
    (∫ point, current field 0 point) = 2 + ‖field‖ ^ 2 / 8 := by
  simp_rw [temporalCurrent_eq]
  rw [integral_add (integrable_const 2) ((Lp.memLp field).norm.integrable_sq.div_const 8),
    integral_div, ← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, integral_const, probReal_univ, one_smul]

/-- The canonical time current reads the original physical kinetic account exactly. -/
theorem source_temporalCurrent_integral (velocity : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality velocity) :
    (∫ point, current (realField velocity) 0 point) = 2 + wholeVorticityEuclideanMass velocity / 8 := by
  rw [temporalCurrent_integral, realField_norm_sq velocity reality]

/-- The actual whole source acceleration differentiates the integrated paired current. -/
theorem temporalCurrent_integral_hasDerivAt
    {path : ℝ → PhysicalField} {tangent : PhysicalField} {time : ℝ}
    (derivative : HasDerivAt path tangent time) :
    HasDerivAt (fun actual => ∫ point, current (path actual) 0 point)
      (inner ℝ (path time) tangent / 4) time := by
  simp_rw [temporalCurrent_integral]
  have square := derivative.norm_sq
  convert (square.div_const 8).const_add 2 using 1 <;> first | rfl | ring

theorem receipt_temporalCurrent_ae_hasDerivAt
    {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ∀ᵐ time : ℝ, time ∈ Set.uIcc (0 : ℝ) T →
      HasDerivAt (fun actual => ∫ point, current (physicalPrimitive receipt actual) 0 point)
        (inner ℝ (physicalPrimitive receipt time) (physicalTangent receipt time) / 4) time := by
  filter_upwards [physicalPrimitive_ae_hasDerivAt receipt] with time derivative inside
  exact temporalCurrent_integral_hasDerivAt (derivative inside)

end
end SaturationMonoid.NavierStokes.NativePhysicalMaterial
