import H0mework.Physics.RootRuntime.Seal

/-! An independent consumer reads the whole physical acceptance, eliminates
the competing exclusive-path block and consumes the following original
inquiry. Empirical measurements are a separate, explicitly recorded input. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Runtime

open StageNineHolonomicField StageNineCClassicalWorldAcceptance
open Stage9DEF.State Stage9DEF.Dynamics

noncomputable section

def nextConfiguration := Stage9DEF.Runtime.configurationAt 10

theorem stageTenClosed :
    Nonempty StageTenPhysicalRootClosure ∧
    ZeroUnregisteredPhysicalAuthorityReceipt ∧
    ClassicalWorldAcceptance source configuration ∧
    SimultaneousSixPhysicalSectorNonzero source configuration ∧
    ClassicalWorldAcceptance source nextConfiguration ∧
    Prediction.JointPrediction ∧
    ¬ (∀ slot : Fin 5, Prediction.nextWeight slot =
      Stage9DEF.Observation.exclusiveWeight (Prediction.jointPoint slot)) ∧
    SameOccurrenceActivation := by
  let closure := stageTenPhysicalRootClosure
  refine ⟨⟨closure⟩, closure.authority, closure.classical,
    closure.classical.simultaneousSixPhysicalSectorNonzero, ?_,
    closure.predictionLock, ?_, closure.activation⟩
  · have same : nextConfiguration = configuration :=
      (Stage9DEF.Runtime.configurationAt_eq_actual 10).trans configuration_eq.symm
    rw [same]
    exact closure.classical
  · intro exclusive
    have equal := (closure.predictionLock.1 2).symm.trans
      ((exclusive 2).trans (closure.predictionLock.2.1 2))
    change (0 : ℝ) = 1 / 2 at equal
    norm_num at equal

end
end SaturationMonoid.PhysicsCore.Stage10.Runtime
