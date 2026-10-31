import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Memory.Source.SourceGeneratedActualRelationRoleReflexiveRing
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.Proposition130

/-!
# Canonical reflexive memory of the actual relation cycle

The role-native ring has the literal actual-cycle cochain as its generated
read/write phase.  P130 therefore produces canonical one-atom reflexive
memory and recollectable potential.  P45 forces every sound-and-complete
presentation back to that support while retaining its arbitrary-seven-case
classification no-go.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingActualRelationCycleReflexiveMemory

noncomputable section

open Lifecycle Universal Relations
open M14EssentialAccessRelationFixture
open M14ProofCarryingActualRelationThreeCycleResidual
open M14SourceGeneratedActualRelationRoleReflexiveRing

abbrev ActualRelationRoleRingAt (base : Nat) :=
  actualRelationRoleReflexiveRingAt base

/-- P130 directly consumes the role-generated nonzero residual. -/
theorem actualRelationRoleRing_p130_reflexiveMemory
    (base : Nat) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        (ActualRelationRoleRingAt base).generatedInteractionPhase ∧
      ∃ index,
        ReflexiveMemoryProduction
          ((ActualRelationRoleRingAt base).edgeReflexiveQuery index)
          ((ActualRelationRoleRingAt base).base
            ((ActualRelationRoleRingAt base).next index))
          ReflexiveMemoryAtom.observationChanged := by
  apply (ActualRelationRoleRingAt base
    ).generatedResidual_nonzero_h1_and_edgeReflexiveMemoryProduction
  rw [actualRelationRoleReflexiveRing_generatedResidual_eq_three]
  norm_num

/-- P130's corrected P51 reading of the same residual. -/
theorem actualRelationRoleRing_p130_recollectablePotential
    (base : Nat) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        (ActualRelationRoleRingAt base).generatedInteractionPhase ∧
      ∃ index,
        RecollectableMemoryPotential
          (reflexiveRecollectionAct
            ((ActualRelationRoleRingAt base).edgeReflexiveQuery index))
          ((ActualRelationRoleRingAt base).base
            ((ActualRelationRoleRingAt base).next index)) := by
  apply (ActualRelationRoleRingAt base
    ).generatedResidual_nonzero_h1_and_edgeRecollectablePotential
  rw [actualRelationRoleReflexiveRing_generatedResidual_eq_three]
  norm_num

/-- Every actual selected edge, not only an existentially chosen edge,
produces the canonical P45 memory atom. -/
theorem actualRelationRoleReflexiveMemoryAt
    (base : Nat) (index : ThreeCycleTime) :
    ReflexiveMemoryProduction
      ((ActualRelationRoleRingAt base).edgeReflexiveQuery index)
      ((ActualRelationRoleRingAt base).base
        ((ActualRelationRoleRingAt base).next index))
      ReflexiveMemoryAtom.observationChanged := by
  apply ((ActualRelationRoleRingAt base
    ).edgeReadChanged_iff_edgeReflexiveMemoryProduction index).mp
  apply ((ActualRelationRoleRingAt base
    ).generatedInteractionPhase_edge_nonzero_iff_readChanged index).mp
  rw [actualRelationRoleReflexiveRing_generatedInteractionPhase_eq]
  change actualRelationCycleCochain base index (threeCycleNext index) ≠ 0
  rw [actualRelationCycleCochain_selectedEdge]
  norm_num

/-- The same deterministic edge has recollectable P51 memory potential. -/
theorem actualRelationRoleRecollectablePotentialAt
    (base : Nat) (index : ThreeCycleTime) :
    RecollectableMemoryPotential
      (reflexiveRecollectionAct
        ((ActualRelationRoleRingAt base).edgeReflexiveQuery index))
      ((ActualRelationRoleRingAt base).base
        ((ActualRelationRoleRingAt base).next index)) := by
  apply ((ActualRelationRoleRingAt base
    ).edgeReadChanged_iff_edgeRecollectablePotential index).mp
  apply ((ActualRelationRoleRingAt base
    ).generatedInteractionPhase_edge_nonzero_iff_readChanged index).mp
  rw [actualRelationRoleReflexiveRing_generatedInteractionPhase_eq]
  change actualRelationCycleCochain base index (threeCycleNext index) ≠ 0
  rw [actualRelationCycleCochain_selectedEdge]
  norm_num

/-- P130's H¹ output is the literal P116/P117 cycle cochain. -/
theorem actualRelationRoleRing_p130_h1_exact (base : Nat) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime Int)
      (actualRelationCycleCochain base) := by
  rw [← actualRelationRoleReflexiveRing_generatedInteractionPhase_eq]
  exact (actualRelationRoleRing_p130_reflexiveMemory base).1

/-- P45: every sound-and-complete presentation decodes exactly the selected
edge's canonical reflexive-memory support. -/
theorem actualRelationRoleMemoryPresentation_unique_support
    (base : Nat) (index : ThreeCycleTime)
    {O : Type*}
    (presentation : ReflexiveMemoryPresentation
      ((ActualRelationRoleRingAt base).edgeReflexiveQuery index) O) :
    presentation.decodes
        (presentation.classify
          ((ActualRelationRoleRingAt base).base
            ((ActualRelationRoleRingAt base).next index)))
        ReflexiveMemoryAtom.observationChanged ↔
      ReflexiveMemoryProduction
        ((ActualRelationRoleRingAt base).edgeReflexiveQuery index)
        ((ActualRelationRoleRingAt base).base
          ((ActualRelationRoleRingAt base).next index))
        ReflexiveMemoryAtom.observationChanged :=
  reflexiveMemoryPresentation_unique_support _ presentation _ _

/-- P45: two arbitrary presentations of the same actual edge have identical
decoded support. -/
theorem actualRelationRoleMemoryPresentations_equivalent
    (base : Nat) (index : ThreeCycleTime)
    {O₁ O₂ : Type*}
    (first : ReflexiveMemoryPresentation
      ((ActualRelationRoleRingAt base).edgeReflexiveQuery index) O₁)
    (second : ReflexiveMemoryPresentation
      ((ActualRelationRoleRingAt base).edgeReflexiveQuery index) O₂) :
    first.decodes
        (first.classify
          ((ActualRelationRoleRingAt base).base
            ((ActualRelationRoleRingAt base).next index)))
        ReflexiveMemoryAtom.observationChanged ↔
      second.decodes
        (second.classify
          ((ActualRelationRoleRingAt base).base
            ((ActualRelationRoleRingAt base).next index)))
        ReflexiveMemoryAtom.observationChanged :=
  reflexiveMemoryPresentations_equivalent _ first second _ _

/-- Ring-specific form of P45's boundary: the forced one-atom support cannot
be identified with an arbitrary seven-case predicate family. -/
theorem actualRelationRoleRing_no_unconditional_arbitraryP_memory_equiv
    (base : Nat) :
    ¬ (∀ P : CSafePredicates EssentialAccessRole,
      ∀ index : ThreeCycleTime,
        ReflexiveLambdaObstruction
            ((ActualRelationRoleRingAt base).edgeReflexiveQuery index)
            ((ActualRelationRoleRingAt base).base
              ((ActualRelationRoleRingAt base).next index)) ↔
          ∃ memory,
            MemoryProduction P
              ((ActualRelationRoleRingAt base).base
                ((ActualRelationRoleRingAt base).next index)) memory) := by
  intro claimed
  have obstruction :
      ReflexiveLambdaObstruction
        ((ActualRelationRoleRingAt base).edgeReflexiveQuery .t0)
        ((ActualRelationRoleRingAt base).base
          ((ActualRelationRoleRingAt base).next .t0)) :=
    actualRelationRoleReflexiveMemoryAt base .t0
  rcases (claimed (allSafePredicates EssentialAccessRole) .t0).mp obstruction
      with ⟨memory, produced⟩
  exact allSafe_memoryProduction_false _ memory produced

/-- Universe-stable core consumed by whole-runtime certificates.  The fully
universe-polymorphic presentation theorems remain separate public consumers
below; they are not stored inside a runtime record. -/
theorem actualRelationCycleReflexiveMemoryCore_directConsumer (base : Nat) :
    type_of% (actualRelationRoleReflexiveRing_directConsumer base) ∧
      type_of% (actualRelationRoleRing_p130_reflexiveMemory base) ∧
      type_of% (actualRelationRoleRing_p130_recollectablePotential base) ∧
      (∀ index : ThreeCycleTime,
        type_of% (actualRelationRoleReflexiveMemoryAt base index)) ∧
      (∀ index : ThreeCycleTime,
        type_of% (actualRelationRoleRecollectablePotentialAt base index)) ∧
      type_of%
        (actualRelationRoleRing_no_unconditional_arbitraryP_memory_equiv base) ∧
      type_of% no_unconditional_reflexive_memory_equiv_for_arbitrary_P :=
  ⟨actualRelationRoleReflexiveRing_directConsumer base,
    actualRelationRoleRing_p130_reflexiveMemory base,
    actualRelationRoleRing_p130_recollectablePotential base,
    actualRelationRoleReflexiveMemoryAt base,
    actualRelationRoleRecollectablePotentialAt base,
    actualRelationRoleRing_no_unconditional_arbitraryP_memory_equiv base,
    no_unconditional_reflexive_memory_equiv_for_arbitrary_P⟩

theorem actualRelationCycleReflexiveMemory_directConsumer (base : Nat) :
    type_of% (actualRelationRoleReflexiveRing_directConsumer base) ∧
      type_of% (actualRelationRoleRing_p130_reflexiveMemory base) ∧
      type_of% (actualRelationRoleRing_p130_recollectablePotential base) ∧
      (∀ index : ThreeCycleTime,
        type_of% (actualRelationRoleReflexiveMemoryAt base index)) ∧
      (∀ index : ThreeCycleTime,
        type_of% (actualRelationRoleRecollectablePotentialAt base index)) ∧
      (∀ index : ThreeCycleTime, ∀ {O : Type*},
        ∀ presentation : ReflexiveMemoryPresentation
          ((ActualRelationRoleRingAt base).edgeReflexiveQuery index) O,
          type_of% (actualRelationRoleMemoryPresentation_unique_support
            base index presentation)) ∧
      (∀ index : ThreeCycleTime, ∀ {O₁ O₂ : Type*},
        ∀ first : ReflexiveMemoryPresentation
            ((ActualRelationRoleRingAt base).edgeReflexiveQuery index) O₁,
          ∀ second : ReflexiveMemoryPresentation
            ((ActualRelationRoleRingAt base).edgeReflexiveQuery index) O₂,
            type_of% (actualRelationRoleMemoryPresentations_equivalent
              base index first second)) ∧
      type_of%
        (actualRelationRoleRing_no_unconditional_arbitraryP_memory_equiv base) ∧
      type_of% no_unconditional_reflexive_memory_equiv_for_arbitrary_P :=
  ⟨actualRelationRoleReflexiveRing_directConsumer base,
    actualRelationRoleRing_p130_reflexiveMemory base,
    actualRelationRoleRing_p130_recollectablePotential base,
    actualRelationRoleReflexiveMemoryAt base,
    actualRelationRoleRecollectablePotentialAt base,
    fun _index _O presentation =>
      actualRelationRoleMemoryPresentation_unique_support base _ presentation,
    fun _index _O₁ _O₂ first second =>
      actualRelationRoleMemoryPresentations_equivalent base _ first second,
    actualRelationRoleRing_no_unconditional_arbitraryP_memory_equiv base,
    no_unconditional_reflexive_memory_equiv_for_arbitrary_P⟩

end
end M14ProofCarryingActualRelationCycleReflexiveMemory
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationCycleReflexiveMemory.actualRelationRoleRing_p130_reflexiveMemory
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationCycleReflexiveMemory.actualRelationRoleReflexiveMemoryAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationCycleReflexiveMemory.actualRelationRoleRecollectablePotentialAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationCycleReflexiveMemory.actualRelationRoleMemoryPresentation_unique_support
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationCycleReflexiveMemory.actualRelationCycleReflexiveMemoryCore_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationCycleReflexiveMemory.actualRelationCycleReflexiveMemory_directConsumer
