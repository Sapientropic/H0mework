import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Programme
import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Consumer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Consumer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Registered

open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDirect

noncomputable section

namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree
  (Raw raw facade initialRuntime runtimeCurrent)
end OF

abbrev runtime (depth : Nat) := ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt depth
abbrev old (depth : Nat) := (runtime depth).current.root.toAuthoritativeRoot
abbrev origin (depth : Nat) := (runtime depth).current.visit.current
abbrev Occurrence (depth : Nat) :=
  (old depth).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (origin depth)
abbrev index (depth : Nat) := ParticleWaveFockOccurrenceResponsibilityRuntime.scanIndex (origin depth)
abbrev active (depth : Nat) := (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeActive depth).down
abbrev actor (depth : Nat) := ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeUnitSelectedActorPayload depth
abbrev source (depth : Nat) (occurrence : Occurrence depth) := sourceAt (index depth) (active depth) occurrence
abbrev Point (depth : Nat) := PointAt (Occurrence := Occurrence depth) (index depth) (active depth)
abbrev Value (depth : Nat) := Calculation.Value (Occurrence := Occurrence depth) (index depth) (active depth)

/-- The emitted occurrence supplies the source split and every primitive action.
No completed actor or disposition enters the registered raw reader. -/
def reader (depth : Nat) (occurrence : Occurrence depth) :
    OF.Raw (Value := Value depth) (Var := Var) (sort := Unit.unit) :=
  ⟨sourceEnvironment (index depth) (active depth) occurrence,
    sourceProgramme (index depth) (active depth) occurrence⟩

abbrev calculatedValue (depth : Nat) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value (old depth) (origin depth) (reader depth)

theorem calculated_value (depth : Nat) : calculatedValue depth =
    Finsupp.single (⟨(runtime depth).emittedOccurrence,
      .completed (actor depth).rooted.outcome⟩ : Point depth) 1 := by
  apply (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source
    (old depth) (origin depth) (reader depth)).trans
  change (sourceProgramme (index depth) (active depth) (runtime depth).emittedOccurrence).eval
    (sourceEnvironment (index depth) (active depth) (runtime depth).emittedOccurrence) = _
  rw [sourceProgramme_eval]
  exact congrArg (fun outcome => Finsupp.single
    (⟨(runtime depth).emittedOccurrence, .completed outcome⟩ : Point depth) (1 : ℤ))
    (actor depth).rooted.outcome_eq.symm

/-- The generated value is consumed by the original independent actuality
consumer, preserving either source-selected chronological outcome. -/
theorem consumes_original_disposition (depth : Nat) :
    (∃ reached : ReachedAt (actor depth).rooted.rootSource.source,
      calculatedValue depth = Finsupp.single
        (⟨(runtime depth).emittedOccurrence, .completed (.inl reached)⟩ : Point depth) 1 ∧
      ∃ generated : PrimePairActualitySettlementAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) = .settlement generated) ∨
    (∃ exhausted : ExhaustedAt (actor depth).rooted.rootSource.source,
      calculatedValue depth = Finsupp.single
        (⟨(runtime depth).emittedOccurrence, .completed (.inr exhausted)⟩ : Point depth) 1 ∧
      ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) = .obstruction generated) := by
  rcases runtime_actor_consumes_original_disposition depth with
    ⟨reached, actual, settled, disposition⟩ | ⟨exhausted, actual, blocked, disposition⟩
  · left
    refine ⟨reached, ?_, settled, disposition⟩
    rw [calculated_value, actual]
    rfl
  · right
    refine ⟨exhausted, ?_, blocked, disposition⟩
    rw [calculated_value, actual]
    rfl

/-- Syntax steps pay the existing mathematical debt. An already-completed
actor remains a completed value; this syntax budget is not an actor-event count. -/
def activeContinuation (depth : Nat)
    (count : Fin (SourceOperationExecution.remaining
      (OF.raw (old depth) (origin depth) (reader depth)).expression)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activeContinuation
    (old depth) (origin depth) (reader depth) count

theorem installed_trace (depth : Nat) :
    (actor depth).rooted.programmeTrace =
      sourceTrace (index depth) (active depth) (runtime depth).emittedOccurrence := rfl

def actualEnvironment (depth : Nat) : SourceOperationEffects.Env (Value depth) Var :=
  fun sort name => action (index depth) (active depth)
    ((OF.raw (old depth) (origin depth) (reader depth)).environment sort name)

def actualIncrement (depth : Nat) : SourceOperationEffects.Env (Value depth) Var :=
  actualEnvironment depth - (OF.raw (old depth) (origin depth) (reader depth)).environment

/-- The original emitted source's actual pulse supplies the update consumed by
the existing paid relation, inverse-fibre and cochain laws. -/
theorem relation_receipt (depth : Nat) :
    (type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.relation_boundary
      (R := ℤ) (old depth) (origin depth) (reader depth))) ∧
    (type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.relation_old
      (R := ℤ) (old depth) (origin depth) (reader depth))) ∧
    (type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.updated_inverse_fibre
      (R := ℤ) (old depth) (origin depth) (reader depth) (actualIncrement depth))) ∧
    (type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.relation_cochain
      (R := ℤ) (old depth) (origin depth) (reader depth) (actualIncrement depth))) :=
  ⟨RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.relation_boundary
      (R := ℤ) (old depth) (origin depth) (reader depth),
    RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.relation_old
      (R := ℤ) (old depth) (origin depth) (reader depth),
    RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.updated_inverse_fibre
      (R := ℤ) (old depth) (origin depth) (reader depth) (actualIncrement depth),
    RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.relation_cochain
      (R := ℤ) (old depth) (origin depth) (reader depth) (actualIncrement depth)⟩

theorem receipt (depth : Nat) :
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (old depth) (origin depth) (reader depth)).length =
        sourceFuel (source depth (runtime depth).emittedOccurrence) + 1 ∧
    (type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.original_material
      (old depth) (origin depth) (reader depth))) ∧
    (type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.target_factorizes
      (old depth) (origin depth) (reader depth))) ∧
    (type_of% (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeUnitSelectedActor_keeps_occurrence_ledger_next depth)) ∧
    (type_of% (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeUnitSelectedActorPayload_eq_tickProjection depth)) ∧
    (type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.wellFounded
      (old depth) (origin depth) (reader depth))) := by
  refine ⟨?_, RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.original_material
    (old depth) (origin depth) (reader depth),
    RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.target_factorizes
      (old depth) (origin depth) (reader depth),
    ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeUnitSelectedActor_keeps_occurrence_ledger_next depth,
    ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeUnitSelectedActorPayload_eq_tickProjection depth,
    RootGeneratedDebtActivationJointSource.OwnerFree.Payment.wellFounded
      (old depth) (origin depth) (reader depth)⟩
  exact (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history
    (old depth) (origin depth) (reader depth)).trans
      (sourceProgramme_budget (index depth) (active depth) (runtime depth).emittedOccurrence)

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Registered
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
