import H0mework.Versions.R2.Physics.SpinPair.GaugeEquation
import H0mework.Versions.R2.Physics.Homogeneous.CartanActual

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineCClassicalWorldAcceptance StageNineConnectionSectorSourceBalance
open StageNineDynamicBreakingVacuum StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariationDensity
open StageNineMatterCovariantDerivativeAffine StageNineFormNativeMatterSpinThreeForm
open StageNineTopologicalLorentzThreeFormDuality StageNineMatterVariation
open Stage9C.Dynamics.Homogeneous
open SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem actual_gravityCurvature_nonzero (point : BasePoint) :
    holonomicGravityCurvature actual point ≠ 0 := by
  intro zero
  have entry := congrArg (fun curvature => curvature (3 : Fin 6) (3 : Fin 6)) zero
  rw [actual_gravityCurvature, homogeneousCurvature_components, spinScale_sq] at entry
  norm_num at entry

theorem sourceColorP286Generator_nonzero (index : Fin 3) : sourceColorP286Generator index ≠ 0 := by
  intro zero
  have value := sourceColorP286Generator_pairing_self index
  rw [zero] at value
  norm_num [p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing] at value

theorem actual_gaugeCurvature_nonzero (point : BasePoint) :
    holonomicGaugeCurvature actual point ≠ 0 := by
  intro zero
  have entry := congrArg (fun curvature => curvature (3 : Fin 6)) zero
  rw [actual_gaugeCurvature] at entry
  change -(gaugeScale^2) • sourceColorP286Generator 0 = 0 at entry
  have scalar : -(gaugeScale^2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (ne_of_gt gaugeScale_pos))
  exact sourceColorP286Generator_nonzero 0 ((smul_eq_zero.mp entry).resolve_left scalar)

private def currentProbe : P286GaugeOneForm :=
  fun direction => p286CoordinateEquiv (gaugePotential 1 direction)

theorem actual_matterCurrent_value (point : BasePoint) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource actual currentProbe point =
      6*lapse*spinScale := by
  rw [actual_p286MatterCurrent]
  have component (index : Fin 3) :
      p286CoordinateEquiv.symm (currentProbe index.succ) = sourceColorP286Generator index := by
    unfold currentProbe
    rw [p286CoordinateEquiv.symm_apply_apply]
    fin_cases index <;> simp [gaugePotential]
  simp_rw [component, sourceColorP286Generator_pairing_self]
  norm_num
  ring

theorem actual_matterCurrentNonzeroAt (point : BasePoint) :
    MatterCurrentNonzeroAt positiveSmoothUnifiedSource actual point := by
  refine ⟨currentProbe, ?_⟩
  rw [actual_matterCurrent_value]
  exact ne_of_gt (mul_pos (mul_pos (by norm_num) lapse_pos) spinScale_pos)

theorem actual_matterSpin_value (point : BasePoint) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource actual
      (loweredLorentzBivectorOneFormCoordinate 1 3) point = -2*lapse*spinScale := by
  have generated := homogeneousSpinField_coefficient lapse spinScale lapse_pos
    (upperPhase point) (lowerPhase point) (upperDualPhase point) (lowerDualPhase point)
    (upperDual_lower_product point) (lowerDual_upper_product point) point 1 3
  have identity : lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource actual
      (loweredLorentzBivectorOneFormCoordinate 1 3) point =
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 point
        (homogeneousSpinField lapse (upperPhase point) (lowerPhase point)
          (upperDualPhase point) (lowerDualPhase point))
        (loweredLorentzBivectorOneFormCoordinate 1 3) := by
    unfold lorentzMatterSpinSourceCoefficient formNativeLorentzMatterFirstCoefficient
      matterGaugeConnectionFirstVariationDensity matterGaugeConnectionVariationVector matterGaugeKineticSum
      matterCovariantDerivativeFirstVariationDensity matterCovariantDerivativeVariationVector
      matterCovariantDerivativeKineticSum
    simp only [toContinuumPointField, actual_coframe, actual_matter, actual_conjugateMatter,
      homogeneousSpinField, generatedVolumeDensity]
    rfl
  rw [identity, generated]
  change lapse * (-2*spinScale) = -2*lapse*spinScale
  ring

theorem actual_matterSpinNonzeroAt (point : BasePoint) :
    MatterSpinNonzeroAt positiveSmoothUnifiedSource actual point := by
  refine ⟨loweredLorentzBivectorOneFormCoordinate 1 3, ?_⟩
  rw [actual_matterSpin_value]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt lapse_pos)) (ne_of_gt spinScale_pos)

theorem actual_sixPhysicalSectors :
    SimultaneousSixPhysicalSectorNonzero positiveSmoothUnifiedSource actual where
  gravityCurvature := ⟨0, actual_gravityCurvature_nonzero 0⟩
  p286GaugeCurvature := ⟨0, actual_gaugeCurvature_nonzero 0⟩
  breakingVacuum := positive_sourceGeneratedVacuumBase_nonzero
  yukawaMass := firstAssemblyCartanActual_sourceYukawaMass_nonzero
  matterCurrent := ⟨0, actual_matterCurrentNonzeroAt 0⟩
  stressOrSpin := ⟨0, Or.inr (actual_matterSpinNonzeroAt 0)⟩

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
