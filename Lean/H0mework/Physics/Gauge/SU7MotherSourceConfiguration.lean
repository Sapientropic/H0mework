import H0mework.Physics.Gauge.SU7MotherOffBlockRegression

/-!
# Canonical source-generated SU(7) mother configuration

The canonical output uses the source-generated noncommuting mother connection,
source-generated auxiliary fields, and zero constitutive multiplier.  Its
three normalized curvature readouts reproduce the Stage-5 source curvature,
its full cross-block penalty vanishes, and its action value equals the Stage-5
source action.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherSourceConfiguration

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7MotherGaugeAction
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open NonseparableGravityGaugeSourceAction
open NonseparableMasterActionVariations
open NonzeroSourceGaugeStationaryConfiguration

noncomputable section

@[simp] theorem motherColorCoordinate_zero :
    motherColorCoordinate (0 : SU7MotherLieMatrix) = 0 := by
  simp [motherColorCoordinate]

@[simp] theorem motherWeakCoordinate_zero :
    motherWeakCoordinate (0 : SU7MotherLieMatrix) = 0 := by
  simp [motherWeakCoordinate]

@[simp] theorem motherHyperchargeCoordinate_zero :
    motherHyperchargeCoordinate (0 : SU7MotherLieMatrix) = 0 := by
  simp [motherHyperchargeCoordinate]

def sourceGeneratedMotherGaugeConfiguration
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    SU7MotherGaugeConfiguration where
  connection := sourceMotherConnection source
  auxiliary := fun pair =>
    liftSectorValue
      (sourceGaugeAuxiliary source boundary.strongCouplingSquared pair)
      (sourceGaugeAuxiliary source boundary.weakCouplingSquared pair)
      (sourceGaugeAuxiliary source boundary.hyperchargeCouplingSquared pair)
  constitutiveMultiplier := fun _ => 0

@[simp] theorem sourceMother_colorCoordinate
    (source : Source) (pair : Fin 6) :
    motherColorCoordinate (motherCurvature (sourceMotherConnection source) pair) =
      sourceGaugeCurvature source pair := by
  rw [sourceMotherCurvature_eq_target]
  simp [motherColorCoordinate, sourceP286TargetCurvature, realScaleP286,
    canonicalP286Generator, p286LieBlockEmbed, rawP286LieBlock,
    colorCartanGenerator, colorCartanRaw]

@[simp] theorem sourceMother_weakCoordinate
    (source : Source) (pair : Fin 6) :
    motherWeakCoordinate (motherCurvature (sourceMotherConnection source) pair) =
      sourceGaugeCurvature source pair := by
  rw [sourceMotherCurvature_eq_target]
  simp [motherWeakCoordinate, sourceP286TargetCurvature, realScaleP286,
    canonicalP286Generator, p286LieBlockEmbed, rawP286LieBlock,
    weakHyperchargeLieBlock, weakCartanGenerator, weakCartanRaw]

@[simp] theorem sourceMother_hyperchargeCoordinate
    (source : Source) (pair : Fin 6) :
    motherHyperchargeCoordinate
        (motherCurvature (sourceMotherConnection source) pair) =
      sourceGaugeCurvature source pair := by
  rw [sourceMotherCurvature_eq_target]
  simp [motherHyperchargeCoordinate, sourceP286TargetCurvature,
    realScaleP286, canonicalP286Generator, p286LieBlockEmbed,
    rawP286LieBlock, weakHyperchargeLieBlock, hyperchargeLieBlock,
    scalarLieBlock, realScaleHypercharge, hyperchargeGenerator,
    hyperPlusIndex]

@[simp] theorem project_sourceGeneratedMotherGaugeConfiguration
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    projectMotherGaugeConfiguration
        (sourceGeneratedMotherGaugeConfiguration source boundary) =
      sourceStandardModelGaugeConfiguration source boundary := by
  simp [projectMotherGaugeConfiguration,
    sourceGeneratedMotherGaugeConfiguration,
    sourceStandardModelGaugeConfiguration, sourceGaugeSectorConfiguration]
  funext pair
  rfl

@[simp] theorem sourceGeneratedMother_breakingPenalty_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    motherBreakingPenalty
        (sourceGeneratedMotherGaugeConfiguration source boundary) = 0 := by
  simp [motherBreakingPenalty, sourceGeneratedMotherGaugeConfiguration,
    sourceMotherConnection, liftSectorValue]

def sourceGeneratedMotherUnifiedConfiguration
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    SU7MotherUnifiedConfiguration where
  gravity := (sourceNonseparableConfiguration source boundary).gravity
  gauge := sourceGeneratedMotherGaugeConfiguration source boundary

theorem sourceGeneratedMother_action_eq_stageFive
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    motherMasterAction source (motherBoundaryOfStageFive boundary)
        (sourceGeneratedMotherUnifiedConfiguration source boundary) =
      nonseparableMasterAction source boundary
        (sourceNonseparableConfiguration source boundary) := by
  simp [motherMasterAction, nonseparableMasterAction,
    sourceGeneratedMotherUnifiedConfiguration,
    sourceNonseparableConfiguration]

end
end SaturationMonoid.PhysicsCore.SU7MotherSourceConfiguration
