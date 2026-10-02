import H0mework.Foundation.Responsibility.JointSource.Idle
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Registration.Source
import H0mework.Realization.Audit.DebtFirstWrite

/-! The actual occurrence supplies the complete raw expression and environment.
Its dependent executor generates a fresh mathematical bearer without selecting
an old row. Physical support stays fixed during this calculation. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree
open SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
abbrev Raw := Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort)
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))

def raw := reader (old.emitted origin)
abbrev law := Idle.law (raw old origin reader).environment (raw old origin reader).expression
abbrev World := ExtendedNetwork N (law old origin reader)
abbrev Current := SourceOperationExecutionDebt.State (raw old origin reader).environment (raw old origin reader).expression
def support := old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted origin)
def supportAt (state : Current old origin reader) : (World old origin reader).Support :=
  ⟨support old origin, some state⟩
def initial := SourceOperationExecutionDebt.initial (raw old origin reader).environment (raw old origin reader).expression

def action (state : Current old origin reader) : SourceOperationExecutionDebt.Settlement state ⊕
    GeneratedStepAt (law old origin reader) state :=
  SourceOperationExecutionDebt.generate (raw old origin reader).environment (raw old origin reader).expression state

def targetOf (state : Current old origin reader)
    (selected : SourceOperationExecutionDebt.Settlement state ⊕ GeneratedStepAt (law old origin reader) state) :
    Current old origin reader :=
  match selected with
  | .inl _ => state
  | .inr paid => paid.1

def nextState (state : Current old origin reader) := targetOf old origin reader state (action old origin reader state)

def vocabulary : Vocabulary.{u} where
  Current := Current old origin reader
  Anchor := V.Anchor
  Incidence := V.Incidence
  Lineage := V.Lineage
  anchorAt := fun _ => V.anchorAt origin
  incidenceAt := fun _ => V.incidenceAt origin
  lineageAt := fun _ => V.lineageAt origin
  NativeWriteAt := fun state => GeneratedStepAt (law old origin reader) state
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun state => SourceOperationExecutionDebt.Settlement state
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := Sigma.fst
  relationTarget := PEmpty.elim
  continuedTarget := fun {state} _ => state
  redirectTarget := PEmpty.elim

inductive EventAt : (vocabulary old origin reader).Current → (World old origin reader).Support → Type u
  | generated (state : Current old origin reader) : EventAt state (supportAt old origin reader state)

def eventAlgebra : SourceNativeEventAlgebra (World old origin reader) (vocabulary old origin reader) where
  EventAt := EventAt old origin reader
  compile := by
    intro state target event
    cases event
    exact match action old origin reader state with
      | .inl settled => .continuedTransport settled
      | .inr paid => .nativeWrite paid
  AffectedInventoryAt := fun _ => Option (old.toLedgerRoot.source.source.law.AffectedInventoryAt (old.emitted origin).2)
  affectedInventoryPresentation := by
    intro state target event
    cases event
    exact activeInventoryPresentation (law := law old origin reader) state
      (old.toLedgerRoot.source.source.law.affectedInventoryPresentation (old.emitted origin).2)
  anchorKey := old.toLedgerRoot.source.source.law.anchorKey
  incidenceKey := old.toLedgerRoot.source.source.law.incidenceKey
  lineageKey := old.toLedgerRoot.source.source.law.lineageKey
  anchor_commutes := by
    intro state target event
    cases event
    exact old.toLedgerRoot.source.source.law.anchor_commutes (old.emitted origin).2
  incidence_commutes := by
    intro state target event
    cases event
    exact old.toLedgerRoot.source.source.law.incidence_commutes (old.emitted origin).2
  lineage_commutes := by
    intro state target event
    cases event
    exact old.toLedgerRoot.source.source.law.lineage_commutes (old.emitted origin).2

def source : SourceNativeSource (World old origin reader) (vocabulary old origin reader) where
  initial := initial old origin reader
  law := eventAlgebra old origin reader

def emitted (state : Current old origin reader) : (source old origin reader).toRootSource.actual.OccurrenceAt state :=
  ⟨supportAt old origin reader state, .generated state⟩

def wholeOf (state : Current old origin reader)
    (selected : SourceOperationExecutionDebt.Settlement state ⊕ GeneratedStepAt (law old origin reader) state) :
    LedgerWriteEvolutionAt (World old origin reader) ⟨supportAt old origin reader state⟩
      ⟨supportAt old origin reader (targetOf old origin reader state selected)⟩ :=
  match selected with
  | .inl settled => transportLedgerEvolution (support old origin) (Idle.identityTransport state settled)
  | .inr paid => stepLedgerEvolution (support old origin) paid.2

def whole (state : Current old origin reader) := wholeOf old origin reader state (action old origin reader state)

def mathEntry (state : Current old origin reader) := debtEntry (N := N) (law := law old origin reader) (support old origin) state

theorem destination_math (state : Current old origin reader) :
    ((whole old origin reader state).destination (mathEntry old origin reader state)).1 =
      mathEntry old origin reader (nextState old origin reader state) := by
  unfold whole nextState
  generalize action old origin reader state = selected
  cases selected <;> rfl

theorem origin_math (state : Current old origin reader) :
    ((whole old origin reader state).origin (mathEntry old origin reader (nextState old origin reader state))).1 =
      mathEntry old origin reader state := by
  unfold whole nextState
  generalize action old origin reader state = selected
  cases selected <;> rfl

theorem whole_origin_destination (state : Current old origin reader)
    (entry : OpenResponsibilityAt (World old origin reader) (supportAt old origin reader state)) :
    ((whole old origin reader state).origin ((whole old origin reader state).destination entry).1).1 = entry := by
  unfold whole
  dsimp only [nextState] at *
  generalize action old origin reader state = selected at *
  cases selected with
  | inl settled => exact transportLedgerEvolution_origin_destination (support old origin) (Idle.identityTransport state settled) entry
  | inr paid => exact stepLedgerEvolution_origin_destination (support old origin) paid.2 entry

theorem whole_destination_origin (state : Current old origin reader)
    (entry : OpenResponsibilityAt (World old origin reader) (supportAt old origin reader (nextState old origin reader state))) :
    ((whole old origin reader state).destination ((whole old origin reader state).origin entry).1).1 = entry := by
  revert entry
  unfold whole nextState
  generalize action old origin reader state = selected
  intro entry
  cases selected with
  | inl settled => exact transportLedgerEvolution_destination_origin (support old origin) (Idle.identityTransport state settled) entry
  | inr paid => exact stepLedgerEvolution_destination_origin (support old origin) paid.2 entry

end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
