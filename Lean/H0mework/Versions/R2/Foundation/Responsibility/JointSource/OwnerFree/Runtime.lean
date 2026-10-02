import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Authority
import H0mework.Versions.R2.Foundation.Runtime.Activation
import H0mework.Versions.R2.Foundation.Inquiry.Protocol

/-! The existing canonical runtime consumes this source's mathematical
successors. Exact finite histories distinguish visits to a settled state. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree
open SourceOperationEffects DebtActivationWorld DebtActivationLedger RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))

theorem next_eq (state : Current old origin reader) :
    ((ledgerRoot old origin reader).toRoot.evolutionAt state).nextCurrent? = some (nextState old origin reader state) := by
  change (match action old origin reader state with
    | .inl settled => EvolutionAt.continuedTransport (V := vocabulary old origin reader) settled
    | .inr paid => EvolutionAt.nativeWrite (V := vocabulary old origin reader) paid).nextCurrent? = _
  unfold nextState targetOf
  cases action old origin reader state <;> rfl

def finiteVisit : Nat → RootVisit (ledgerRoot old origin reader).toRoot
  | 0 => (ledgerRoot old origin reader).toRoot.initialVisit
  | depth + 1 => (finiteVisit depth).next (next_eq old origin reader _)

def temporalVisit (depth : Nat) := SourceNativeTemporalVisitAt.finite (finiteVisit old origin reader depth)

private theorem generated_next {W : WorldRelationNetwork.{u}} {L : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure W L)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (root.emitted visit.current)
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current)) :
    root.generatedNextCurrentAt visit = ⟨L, root.toAuthoritativeRoot, visit.next successor.next_eq⟩ := by
  generalize same : root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current = generated at successor ⊢
  cases generated with
  | nativeWrite write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_nativeWriteBranch visit write structural target evolution same successor.next_eq
  | relationWrite write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_relationWriteBranch visit write structural target evolution same successor.next_eq
  | continuedTransport write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_continuedTransportBranch visit write structural target evolution same successor.next_eq
  | borromeanRedirect write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_borromeanRedirectBranch visit write structural target evolution same successor.next_eq
  | faithfulTerminal terminal structural evolution => exact nomatch successor

private theorem next_visit_unique {W : WorldRelationNetwork.{u}} {L : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure W L} (visit : SourceNativeTemporalVisitAt root)
    {first second : L.Current}
    (left : (root.toRoot.evolutionAt visit.current).nextCurrent? = some first)
    (right : (root.toRoot.evolutionAt visit.current).nextCurrent? = some second) :
    visit.next left = visit.next right := by
  have targets := Option.some.inj (left.symm.trans right)
  cases targets
  rfl

def sourceSuccessor (state : Current old origin reader) : SourceNativeLedgerGeneratedSuccessorAt
    ((ledgerRoot old origin reader).emitted state) ((ledgerRoot old origin reader).generatedLedgerAt state) :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? ((ledgerRoot old origin reader).generatedLedgerAt state)).get (by
    cases (ledgerRoot old origin reader).generatedLedgerAt state with
    | nativeWrite => rfl
    | relationWrite => rfl
    | continuedTransport => rfl
    | borromeanRedirect => rfl
    | faithfulTerminal impossible => exact nomatch impossible)

private def temporalDepth (current : SourceNativeLivingRootCurrentAt (World old origin reader)) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem visit_depth (depth : Nat) :
    temporalDepth old origin reader ⟨vocabulary old origin reader, livingRoot old origin reader,
      temporalVisit old origin reader depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      change some (ProductiveFiniteRootHistoryAt.causalDepth (finiteVisit old origin reader depth).history + 1) = some (depth + 1)
      exact congrArg some (congrArg (fun count => count + 1) (Option.some.inj prior))

def process : SourceNativeLivingRootProcess (World old origin reader) where
  State := ULift.{u, 0} Nat
  stateAt := fun depth => ⟨vocabulary old origin reader, livingRoot old origin reader, temporalVisit old origin reader depth.down⟩
  stateAt_injective := by
    intro first second same
    have depths := congrArg (temporalDepth old origin reader) same
    rw [visit_depth old origin reader first.down, visit_depth old origin reader second.down] at depths
    have values := Option.some.inj depths
    cases first
    cases second
    cases values
    rfl
  initial := ⟨0⟩
  successorAt := fun depth => ⟨⟨depth.down + 1⟩, by
    have step := sourceSuccessor old origin reader (finiteVisit old origin reader depth.down).current
    have next := generated_next (livingRoot old origin reader) (temporalVisit old origin reader depth.down) step
    rw [next]
    change (⟨vocabulary old origin reader, (livingRoot old origin reader).toAuthoritativeRoot,
      (temporalVisit old origin reader depth.down).next (next_eq old origin reader _)⟩ : SourceNativeAuthoritativeRootCurrentAt _) = _
    exact congrArg (fun arrived => (⟨vocabulary old origin reader,
      (livingRoot old origin reader).toAuthoritativeRoot, arrived⟩ : SourceNativeAuthoritativeRootCurrentAt _))
        (next_visit_unique (temporalVisit old origin reader depth.down) (next_eq old origin reader _) step.next_eq), by
      cases (livingRoot old origin reader).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (temporalVisit old origin reader depth.down).current <;> first | exact True.intro | exact HEq.rfl⟩

abbrev Runtime := LivingRuntimeState (process old origin reader)
def initialRuntime : Runtime old origin reader := LivingRuntimeState.initial (process old origin reader)
def runtimeCurrent (runtime : Runtime old origin reader) := (finiteVisit old origin reader runtime.state.down).current

def facade : SourceNativeLivingRuntimeFacade (World old origin reader) where
  process := process old origin reader
  FaceAt := fun runtime => runtime.current.root.toAuthoritativeRoot.source.projectionLaw.Projection
  componentAt := fun runtime _ => runtime.current.root.toAuthoritativeRoot.source.projectionLaw
  installationAt := fun _ _ => .refl _
  projectionAt := fun _ face => face

def rawFace (runtime : Runtime old origin reader) : SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (baseInstallation old origin reader).embed (.inr false)
  active := PUnit.unit
  classifier_eq := rfl

def mathFace (runtime : Runtime old origin reader) : SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (baseInstallation old origin reader).embed (.inr true)
  active := PUnit.unit
  classifier_eq := rfl

def originalFace (runtime : Runtime old origin reader) : SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (originalInstallation old origin reader).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def observationFace (runtime : Runtime old origin reader) : SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (observationInstallation old origin reader).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem tick_math (runtime : Runtime old origin reader) :
    runtimeCurrent old origin reader runtime.tick.next = nextState old origin reader (runtimeCurrent old origin reader runtime) := rfl

theorem tick_ledger (runtime : Runtime old origin reader) : HEq runtime.tick.generated.wholeLedgerWriteBack
    ((compiler old origin reader).compile (emitted old origin reader (runtimeCurrent old origin reader runtime))) := HEq.rfl

def tickCertificate (runtime : Runtime old origin reader) : SourceNativeLedgerRestructuringCertificationAt
    (restructuringLaw old origin reader) ((compiler old origin reader).compile
      (emitted old origin reader (runtimeCurrent old origin reader runtime))) :=
  runtime.current.root.toAuthoritativeRoot.source.restructuringSource.compiler.certifyRestructuring runtime.tick.generated.occurrence

end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
