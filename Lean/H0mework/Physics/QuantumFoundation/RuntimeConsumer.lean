import H0mework.Physics.QuantumFoundation.Credential

/-! An independent consumer of the complete Stage-9 credential reads both
the nontrivial classical world and a different quantum response in the
following native occurrence. The original whole-ledger evolution is retained. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G.Runtime

open StageNineHolonomicField StageNineCClassicalWorldAcceptance
open Stage9DEF.State Stage9DEF.Dynamics

noncomputable section

def nextConfiguration := Stage9DEF.Runtime.configurationAt 7

/-- Complete theory output, unique admitted actual, nonzero physics and the
next observable response are read from one generated credential. -/
theorem stageNineClosed :
    Nonempty SourceGeneratedContinuousQuantumUnifiedTheoryCredential ∧
    (∃! actual, LawfulClassicalActual actual ∧ ClassicalWorldAcceptance source actual) ∧
    SimultaneousSixPhysicalSectorNonzero source configuration ∧
    ClassicalWorldAcceptance source nextConfiguration ∧
    (vectorEvaluation (tick.answer 0) (sourceEffect 0).matrix).re = 1 ∧
    (vectorEvaluation
      (nextTick.answer (timeDisplacement Stage9DEF.Observation.darkTime))
      (sourceEffect 0).matrix).re = 0 ∧
    SameOccurrenceActivation := by
  let theory := sourceGeneratedContinuousQuantumUnifiedTheoryCredential
  refine ⟨⟨theory⟩,
    ⟨configuration, ⟨theory.admitted, theory.classical⟩,
      fun alternative admitted => theory.uniqueActual alternative admitted.1⟩,
    theory.classical.simultaneousSixPhysicalSectorNonzero, ?_,
    theory.actualInterference.1, theory.predictionLock.1, theory.sameOccurrence⟩
  have retained : nextConfiguration = configuration :=
    (Stage9DEF.Runtime.configurationAt_eq_actual 7).trans theory.actualGenerated.symm
  rw [retained]
  exact theory.classical

end
end SaturationMonoid.PhysicsCore.Stage9G.Runtime
