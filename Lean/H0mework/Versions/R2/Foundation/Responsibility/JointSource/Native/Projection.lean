import H0mework.Foundation.Responsibility.JointSource.Native.Compiler
import H0mework.Versions.R2.Foundation.Authority.SourceProjectionInventory

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (program : Program lower)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)

def originalOccurrence {current : Current registered}
    (occurrence : (source program registered).toRootSource.actual.OccurrenceAt current) :
    lower.source.source.toRootSource.actual.OccurrenceAt current.1 := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact lower.emitted current.1

structure MathReadout where
  state : SourceOperationExecutionDebt.State registered.input.environment registered.input.expression
  action : SourceOperationExecutionDebt.Settlement state ⊕
    GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) state
  value : Value sort

def mathReadout (current : Current registered) : MathReadout registered where
  state := current.2.state
  action := mathAction current.2
  value := current.2.state.1.eval registered.input.environment

/-- Every old projection is pulled back from the same original occurrence;
its classifier, complete payload fibre and inactive receipt remain intact. -/
def projectionLaw (old : SourceNativeProjectionLaw lower.source) :
    SourceNativeProjectionLaw (ledgerSource program registered) where
  Projection := old.Projection ⊕ PUnit
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl original => old.ActiveAt original (originalOccurrence program registered occurrence)
    | .inr _ => PUnit
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl original => old.InactiveAt original (originalOccurrence program registered occurrence)
    | .inr _ => PEmpty
  classify := fun projection {_current} occurrence =>
    match projection with
    | .inl original => old.classify original (originalOccurrence program registered occurrence)
    | .inr _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence active =>
    match projection with
    | .inl original => old.PayloadAt original (originalOccurrence program registered occurrence) active
    | .inr _ => MathReadout registered
  project := fun projection {current} occurrence active =>
    match projection with
    | .inl original => old.project original (originalOccurrence program registered occurrence) active
    | .inr _ => mathReadout registered current

theorem original_projection_outcome (old : SourceNativeProjectionLaw lower.source)
    {current : Current registered}
    (occurrence : (source program registered).toRootSource.actual.OccurrenceAt current)
    (projection : old.Projection) :
    HEq ((projectionLaw program registered old).outcomeAt (.inl projection) occurrence)
      (old.outcomeAt projection (originalOccurrence program registered occurrence)) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [projectionLaw]
  cases old.classify projection (originalOccurrence program registered occurrence) <;> rfl

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
