import H0mework.Versions.R2.Physics.YangMillsAction.FlatRestriction
import H0mework.Versions.R2.Physics.RootRuntime.RuntimeOccurrence
import H0mework.Versions.R2.Physics.SpinPair.Qualification

/-! The same Stage-10 occurrence supplies a nonzero connection to the pure
restriction. All its gauge curvature survives the removal of charged fields. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Flat

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDynamicBreakingVacuum

noncomputable section

def sourceConnection : P286ConnectionField := Stage10.Runtime.configuration.gaugeConnection

theorem source_curvature_preserved (point : BasePoint) :
    holonomicGaugeCurvature (configuration sourceConnection) point =
      holonomicGaugeCurvature Stage10.Runtime.configuration point := rfl

theorem source_curvature_nonzero (point : BasePoint) :
    holonomicGaugeCurvature (configuration sourceConnection) point ≠ 0 := by
  rw [source_curvature_preserved, Stage10.Runtime.configuration_eq]
  exact Stage9C.Material.SpinPair.actual_gaugeCurvature_nonzero point

theorem source_auxiliary_nonzero (point : BasePoint) :
    (configuration sourceConnection).gaugeAuxiliary point ≠ 0 := by
  change formNativeP286GaugeEliminatedAuxiliaryAtBoundary
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) coframe
    (holonomicGaugeCurvature (primitive sourceConnection) point) ≠ 0
  exact (formNativeP286GaugeEliminatedAuxiliaryAtBoundary_eq_zero_iff _ _
    (Stage9C.Material.SpinPair.actual_nondegenerate 0) _).not.mpr
      (source_curvature_nonzero point)

theorem source_flat_pure_gauge (point : BasePoint) :
    holonomicGravityCurvature (configuration sourceConnection) point = 0 ∧
    holonomicGaugeCurvature (configuration sourceConnection) point ≠ 0 ∧
    (configuration sourceConnection).gaugeAuxiliary point ≠ 0 ∧
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField (configuration sourceConnection) point) ∧
    formNativePhysicalChargedGaugeCurrentThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration sourceConnection) point) = 0 :=
  ⟨gravity_curvature_zero sourceConnection point, source_curvature_nonzero point,
    source_auxiliary_nonzero point, auxiliary_equation sourceConnection point,
    charged_current_zero sourceConnection point⟩

theorem source_action_readback (region : Set BasePoint) :
    (∫ point in region,
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
        (toContinuumPointField (configuration sourceConnection) point) +
        |coframe.det| * generatedScalarPotential positiveSmoothUnifiedSource 0 point 0) =
      actionOn region sourceConnection := action_from_mother region sourceConnection

end
end SaturationMonoid.PhysicsCore.YangMills.Flat
