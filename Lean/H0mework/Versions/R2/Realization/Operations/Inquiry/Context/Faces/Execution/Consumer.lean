import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Source

/-! The original occurrence executes its retained word in the existing
owner-free source root. The independent normal read retains the full pair
and recovers the exact reverse fibre residual without an inverse premise. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarInventoryLift SourceOperationLogic SourceOperationLogic.FibreLift
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (initialRuntime runtimeCurrent initial action mathEntry whole)
export RootGeneratedDebtActivationJointSource.OwnerFree (tick_math)
namespace Consumer
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value trace value_source paid_history originalMaterial original_material)
end Consumer
end O

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)
variable (state : runtime.State)
variable (word : Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

abbrev reader (_occurrence : (current runtime state).current.root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (current runtime state).current.visit.current) := pairRaw runtime source state word

def initialRuntime := O.initialRuntime (current runtime state).current.root
  (current runtime state).current.visit.current (reader runtime source state word)

def value : PhysicalValue sort × PhysicalValue sort := O.Consumer.value
  (current runtime state).current.root (current runtime state).current.visit.current (reader runtime source state word)

theorem actual_tick : O.runtimeCurrent (current runtime state).current.root
    (current runtime state).current.visit.current (reader runtime source state word)
      (initialRuntime runtime source state word).tick.next =
    RootGeneratedDebtActivationJointSource.OwnerFree.nextState (current runtime state).current.root
      (current runtime state).current.visit.current (reader runtime source state word)
      (O.initial (current runtime state).current.root (current runtime state).current.visit.current
        (reader runtime source state word)) := O.tick_math _ _ _ _

theorem actual_whole : HEq (initialRuntime runtime source state word).tick.generated.wholeLedgerWriteBack
    ((RootGeneratedDebtActivationJointSource.OwnerFree.compiler (current runtime state).current.root
      (current runtime state).current.visit.current (reader runtime source state word)).compile
        (RootGeneratedDebtActivationJointSource.OwnerFree.emitted (current runtime state).current.root
          (current runtime state).current.visit.current (reader runtime source state word)
          (O.initial (current runtime state).current.root (current runtime state).current.visit.current
            (reader runtime source state word)))) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.tick_ledger _ _ _ _

theorem value_pair : value runtime source state word = pairInventory runtime source state word :=
  (O.Consumer.value_source (current runtime state).current.root
    (current runtime state).current.visit.current (reader runtime source state word)).trans
      (pair_raw_eval runtime source state word)

theorem trace_cost : (O.Consumer.trace (current runtime state).current.root
    (current runtime state).current.visit.current (reader runtime source state word)).length =
      remaining (pairRaw runtime source state word).expression :=
  O.Consumer.paid_history _ _ _

theorem original_occurrence : O.Consumer.originalMaterial (current runtime state).current.root
    (current runtime state).current.visit.current (reader runtime source state word) =
      ⟨(current runtime state).current.root.emitted (current runtime state).current.visit.current,
        (current runtime state).current.root.generatedLedgerAt (current runtime state).current.visit.current,
        (current runtime state).current.root.generatedPatchAt (current runtime state).current.visit.current,
        (current runtime state).current.root.source.restructuringSource.compiler.certifyRestructuring
          ((current runtime state).current.root.emitted (current runtime state).current.visit.current)⟩ :=
  O.Consumer.original_material _ _ _

theorem value_recovered
    (target : Fibre (nextEvaluation runtime source state)
      (q (nextEvaluation runtime source state) ((actualMorphism runtime source state).sourceMap word))) :
    value runtime source state (target.val - word) =
      recover runtime source state (liftingResidual (actualMorphism runtime source state) word target) :=
  (value_pair runtime source state (target.val - word)).trans
    (recover_liftingResidual runtime source state word target).symm

end SourceOperationInquiry.Context.Faces.Execution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
