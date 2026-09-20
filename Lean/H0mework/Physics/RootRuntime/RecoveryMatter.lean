import H0mework.Physics.RootRuntime.RecoverySource
import H0mework.Physics.QuantumCompatibility.Mass

/-! Exact common readouts connect the earlier joint scalar, mass and mixing
to the current actual. The old finite matter jet is not substituted for the
current field; its internal representation acts on the actual field itself. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Recovery

open StageNineHolonomicField StageNineDynamicBreakingVacuum
open ProofFreeRicherAnholonomicSource SU7MotherLieAlgebra SU7ExteriorMatterRepresentation
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open DiracExteriorMatterAction DiracCliffordRepresentation
open SU7GravityGaugeMatterJointCredential

noncomputable section

def vacuum (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :=
  scalarCoordinateEquiv.symm (configuration.scalar point)

def mass (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :=
  exteriorYukawaMassMap (vacuum configuration point)

def mixing (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :=
  finiteGenerationMassMatrixOfScalar (vacuum configuration point)

structure MatterRecovery (configuration : StageNineHolonomicConfiguration)
    (earlier : StageEightGravityGaugeMatterCredential Runtime.source.stageEight stageSix) : Prop where
  internalAction : ∀ point element spin,
    diracExteriorMatterGaugeRepresentation element (configuration.matter point) spin =
      earlier.matterRepresentation element (configuration.matter point spin)
  scalar : ∀ point, vacuum configuration point = earlier.jointBreakingScalar
  fullMass : ∀ point, mass configuration point = earlier.generatedMassMap
  finiteMixing : ∀ point, mixing configuration point = earlier.generatedMixing

theorem currentMatter : MatterRecovery Runtime.configuration stageEight := by
  have scalar : ∀ point, vacuum Runtime.configuration point = stageEight.jointBreakingScalar := by
    intro point
    rw [Runtime.configuration_eq]
    exact (Stage9DEF.Compatibility.actualVacuum_stageEight point).trans
      stageEight.jointBreakingScalar_eq_generated.symm
  refine ⟨?_, scalar, ?_, ?_⟩
  · intro point element spin
    rw [stageEight.matterRepresentation_eq_actual]
    rfl
  · intro point
    rw [mass, scalar, stageEight.jointBreakingScalar_eq_matterConfiguration]
    exact stageEight.generatedMassMap_eq_matterConfiguration.symm
  · intro point
    rw [mixing, scalar, stageEight.jointBreakingScalar_eq_matterConfiguration]
    exact stageEight.generatedMixing_eq_matterConfiguration.symm

end
end SaturationMonoid.PhysicsCore.Stage10.Recovery
