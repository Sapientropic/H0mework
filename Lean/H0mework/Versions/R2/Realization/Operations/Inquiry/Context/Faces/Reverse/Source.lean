import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Fibre

/-! The actual successor trace generates a complete next-evaluation fibre.
Its retained proof tree supplies the reverse target without a chosen quotient
representative; the complete old/effect pair remains the recovery carrier. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Reverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationLogic
open SourceOperationLogic.FibreLift SourceGeneratedScalarDifferentialResidual
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)
variable (state : runtime.State)

def oldWord : Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  relationMap (R := ℤ) (readEnv runtime source state) (relationWords runtime source state)

def nextWord : Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  relationMap (R := ℤ) (readEnv runtime source state.tick.nextState)
    (nextTrace runtime source state).relationWords

private theorem generated_fibre : q (nextEvaluation runtime source state)
    (oldWord runtime source state + nextWord runtime source state) =
      q (nextEvaluation runtime source state)
        ((actualMorphism runtime source state).sourceMap (oldWord runtime source state)) := by
  apply (q_eq_iff _ _ _).mpr
  rw [LinearMap.mem_ker]
  change evaluation (R := ℤ) (readEnv runtime source state.tick.nextState)
    ((oldWord runtime source state + nextWord runtime source state) - oldWord runtime source state) = 0
  rw [add_sub_cancel_left]
  exact (nextTrace runtime source state).relation_old (R := ℤ)

def target : Fibre (nextEvaluation runtime source state)
    (q (nextEvaluation runtime source state)
      ((actualMorphism runtime source state).sourceMap (oldWord runtime source state))) :=
  ⟨oldWord runtime source state + nextWord runtime source state, generated_fibre runtime source state⟩

def reverse := liftingResidual (actualMorphism runtime source state)
  (oldWord runtime source state) (target runtime source state)

theorem reverse_recover : recover runtime source state (reverse runtime source state) =
    pairInventory runtime source state (nextWord runtime source state) := by
  apply (recover_liftingResidual runtime source state (oldWord runtime source state)
    (target runtime source state)).trans
  change pairInventory runtime source state
    ((oldWord runtime source state + nextWord runtime source state) - oldWord runtime source state) = _
  rw [add_sub_cancel_left]

theorem source_boundary : nextWord runtime source state =
    Finsupp.single (raw runtime source state).expression 1 -
      Finsupp.single (.const ((raw runtime source state).expression.eval (readEnv runtime source state.tick.nextState))) 1 :=
  (nextTrace runtime source state).relation_boundary

def retainedTarget : ExistsEvidence (nextEvaluation runtime source state)
    (fun word => {programme : RelationIndex ℤ (readEnv runtime source state.tick.nextState) sort →₀ ℤ //
      relationMap (R := ℤ) (readEnv runtime source state.tick.nextState) programme = word})
    (q (nextEvaluation runtime source state) (nextWord runtime source state)) :=
  retainEvidence (nextEvaluation runtime source state)
    ⟨(nextTrace runtime source state).relationWords, rfl⟩

end SourceOperationInquiry.Context.Faces.Reverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
