import H0mework.Physics.SourceFamily.Consumer
import H0mework.Physics.SourceGauge.Current
import H0mework.Physics.SourceDirac.Material

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Qualification

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineGlobalBundle
open StageNineCClassicalWorldAcceptance StageNineConnectionSectorSourceBalance
open StageNineDynamicBreakingVacuum StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariationDensity
open StageNineMatterCovariantDerivativeAffine StageNineFormNativeMatterSpinThreeForm
open StageNineTopologicalLorentzThreeFormDuality StageNineMatterVariation
open StageNineGravityBianchi Stage9C.Reduction Stage9C.Material.SpinPair
open Stage9C.Dynamics.Homogeneous SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorBreakingYukawa Gauge

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _

theorem lorentz_admissible (step : ℕ) : GravityConnectionLorentzAdmissible (fieldAt step) :=
  algebraicCartanReduction_lorentzAdmissible (sourceAt step) (seedAt step) (seed_nondegenerate step)

theorem scalar_source_contact (step : ℕ) :
    DynamicScalarSourceContactAtOrigin (sourceAt step) (fieldAt step) := by
  unfold DynamicScalarSourceContactAtOrigin
  rw [field_scalar, generatedLocalVacuumCoordinates, generatedScalarFrame,
    generatedTransition_normalized, scalarCoordinateAction_one]

theorem vacuum_base_retained (step : ℕ) :
    sourceGeneratedVacuumBase (sourceAt step) = sourceGeneratedVacuumBase positiveSmoothUnifiedSource := by
  apply scalarCoordinateEquiv.injective
  change sourceGeneratedVacuumCoordinates (sourceAt step) =
    sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [vacuum_retained, Runtime.source_eq]

theorem gravity_curvature (step : ℕ) (point : BasePoint) :
    holonomicGravityCurvature (fieldAt step) point = homogeneousCurvature spinScale :=
  homogeneousCurvature_actual (fieldAt step) spinScale (Dirac.field_gravityConnection step) point

theorem gravity_curvature_nonzero (step : ℕ) (point : BasePoint) :
    holonomicGravityCurvature (fieldAt step) point ≠ 0 := by
  intro zero
  have entry := congrArg (fun curvature => curvature (3 : Fin 6) (3 : Fin 6)) zero
  rw [gravity_curvature, homogeneousCurvature_components, spinScale_sq] at entry
  norm_num at entry

private def currentProbe : P286GaugeOneForm :=
  fun direction => p286CoordinateEquiv (gaugePotential 1 direction)

theorem matter_current_value (step : ℕ) (point : BasePoint) :
    p286MatterCurrentCoefficient (sourceAt step) (fieldAt step) currentProbe point =
      6 * clock step * spinScale := by
  rw [matter_current]
  have component (index : Fin 3) :
      p286CoordinateEquiv.symm (currentProbe index.succ) = sourceColorP286Generator index := by
    unfold currentProbe
    rw [p286CoordinateEquiv.symm_apply_apply]
    fin_cases index <;> simp [gaugePotential]
  simp_rw [component, sourceColorP286Generator_pairing_self]
  norm_num
  ring

theorem matter_current_nonzero (step : ℕ) (point : BasePoint) :
    MatterCurrentNonzeroAt (sourceAt step) (fieldAt step) point := by
  refine ⟨currentProbe, ?_⟩
  rw [matter_current_value]
  exact ne_of_gt (mul_pos (mul_pos (by norm_num) (clock_pos step)) spinScale_pos)

theorem matter_spin_value (step : ℕ) (point : BasePoint) :
    lorentzMatterSpinSourceCoefficient (sourceAt step) (fieldAt step)
      (loweredLorentzBivectorOneFormCoordinate 1 3) point = -2 * clock step * spinScale := by
  have generated := homogeneousSpinField_coefficient (clock step) spinScale (clock_pos step)
    (upper step point) (lower step point) (upperDual step point) (lowerDual step point)
    (upperDual_lower step point) (lowerDual_upper step point) point 1 3
  have identity : lorentzMatterSpinSourceCoefficient (sourceAt step) (fieldAt step)
      (loweredLorentzBivectorOneFormCoordinate 1 3) point =
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 point
        (homogeneousSpinField (clock step) (upper step point) (lower step point)
          (upperDual step point) (lowerDual step point))
        (loweredLorentzBivectorOneFormCoordinate 1 3) := by
    unfold lorentzMatterSpinSourceCoefficient formNativeLorentzMatterFirstCoefficient
      matterGaugeConnectionFirstVariationDensity matterGaugeConnectionVariationVector matterGaugeKineticSum
      matterCovariantDerivativeFirstVariationDensity matterCovariantDerivativeVariationVector
      matterCovariantDerivativeKineticSum
    simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
      toContinuumPointField, field_coframe, field_matter, field_dual,
      homogeneousSpinField, generatedVolumeDensity]
    rfl
  rw [identity, generated]
  change clock step * (-2 * spinScale) = -2 * clock step * spinScale
  ring

theorem matter_spin_nonzero (step : ℕ) (point : BasePoint) :
    MatterSpinNonzeroAt (sourceAt step) (fieldAt step) point := by
  refine ⟨loweredLorentzBivectorOneFormCoordinate 1 3, ?_⟩
  rw [matter_spin_value]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt (clock_pos step))) (ne_of_gt spinScale_pos)

theorem physical_sectors (step : ℕ) :
    SimultaneousSixPhysicalSectorNonzero (sourceAt step) (fieldAt step) where
  gravityCurvature := ⟨0, gravity_curvature_nonzero step 0⟩
  p286GaugeCurvature := ⟨0, field_curvature_nonzero step 0⟩
  breakingVacuum := by
    rw [vacuum_base_retained]
    exact positive_sourceGeneratedVacuumBase_nonzero
  yukawaMass := by
    rw [vacuum_base_retained]
    exact Stage9C.Material.firstAssemblyCartanActual_sourceYukawaMass_nonzero
  matterCurrent := ⟨0, matter_current_nonzero step 0⟩
  stressOrSpin := ⟨0, Or.inr (matter_spin_nonzero step 0)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Qualification
