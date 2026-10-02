import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Authority
import H0mework.Versions.R2.Foundation.Runtime.Activation
import H0mework.Versions.R2.Foundation.Inquiry.Protocol

/-! The existing finite-visit registry consumes this fixed packet source root.
Its causal history distinguishes repeated visits even when ledger size changes. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Restructuring
open SourceOperationEffects DebtActivationWorld DebtActivationLedger CompilerFromPacketSourceLaw RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)
variable (packetAt : (current : V.Current) → Packet old.toLedgerRoot current)

def finiteVisit : Nat → RootVisit (ledgerRoot registered packetAt).toRoot
  | 0 => (ledgerRoot registered packetAt).toRoot.initialVisit
  | depth + 1 => (finiteVisit depth).next rfl

def temporalVisit (depth : Nat) : SourceNativeTemporalVisitAt (ledgerRoot registered packetAt) :=
  .finite (finiteVisit old registered packetAt depth)

private def temporalDepth (current : SourceNativeLivingRootCurrentAt (World registered)) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none


private theorem visit_depth (depth : Nat) :
    temporalDepth old registered ⟨JointV registered packetAt, livingRoot old registered packetAt,
      temporalVisit old registered packetAt depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      change some (ProductiveFiniteRootHistoryAt.causalDepth
        (finiteVisit old registered packetAt depth).history + 1) = some (depth + 1)
      have oldDepth : ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit old registered packetAt depth).history = depth := Option.some.inj prior
      exact congrArg some (congrArg (fun count => count + 1) oldDepth)

def process : SourceNativeLivingRootProcess (World registered) where
  State := ULift.{u, 0} Nat
  stateAt := fun depth => ⟨JointV registered packetAt, livingRoot old registered packetAt,
    temporalVisit old registered packetAt depth.down⟩
  stateAt_injective := by
    intro first second same
    have depths := congrArg (temporalDepth old registered) same
    rw [visit_depth old registered packetAt first.down, visit_depth old registered packetAt second.down] at depths
    have values : first.down = second.down := Option.some.inj depths
    cases first
    cases second
    cases values
    rfl
  initial := ⟨0⟩
  successorAt := fun depth => ⟨⟨depth.down + 1⟩, by rfl, by rfl⟩

abbrev Runtime := LivingRuntimeState (process old registered packetAt)

def initialRuntime : Runtime old registered packetAt := LivingRuntimeState.initial (process old registered packetAt)

def runtimeCurrent (runtime : Runtime old registered packetAt) : Current registered :=
  (finiteVisit old registered packetAt runtime.state.down).current

def facade : SourceNativeLivingRuntimeFacade (World registered) where
  process := process old registered packetAt
  FaceAt := fun runtime => runtime.current.root.toAuthoritativeRoot.source.projectionLaw.Projection
  componentAt := fun runtime _ => runtime.current.root.toAuthoritativeRoot.source.projectionLaw
  installationAt := fun _ _ => .refl _
  projectionAt := fun _ face => face

def rawFace (runtime : Runtime old registered packetAt) :
    SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (rawInstallation old registered packetAt).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def completeFace (runtime : Runtime old registered packetAt) :
    SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (completeInstallation old registered packetAt).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def mathFace (runtime : Runtime old registered packetAt) :
    SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (oldInstallation old registered packetAt).embed (.inr PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

def observationFace (runtime : Runtime old registered packetAt) :
    SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (observationInstallation old registered packetAt).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem tick_ledger (runtime : Runtime old registered packetAt) :
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((compiler registered packetAt).compile (emitted registered packetAt (runtimeCurrent old registered packetAt runtime))) :=
  HEq.rfl

theorem tick_patch (runtime : Runtime old registered packetAt) :
    HEq runtime.tick.generated.currentPatch
      ((compiler registered packetAt).compilePatch (emitted registered packetAt (runtimeCurrent old registered packetAt runtime))) :=
  HEq.rfl

def tickCertificate (runtime : Runtime old registered packetAt) :
    ExactLedgerRestructuringCertificationAt (law old registered packetAt)
      (emitted registered packetAt (runtimeCurrent old registered packetAt runtime))
      (patch registered packetAt (runtimeCurrent old registered packetAt runtime)).toLedgerWriteEvolution :=
  runtime.current.root.toAuthoritativeRoot.source.restructuringSource.compiler.certifyRestructuring
    runtime.tick.generated.occurrence

def tickSplitConsumer (runtime : Runtime old registered packetAt)
    (left right : OpenResponsibilityAt (World registered)
      (supportAt registered (targetCurrent registered packetAt (runtimeCurrent old registered packetAt runtime))))
    (same : ((patch registered packetAt (runtimeCurrent old registered packetAt runtime)).toLedgerWriteEvolution.origin left).1 =
      ((patch registered packetAt (runtimeCurrent old registered packetAt runtime)).toLedgerWriteEvolution.origin right).1) :
    PLift (left = right) ⊕
      (Σ coverage : SourceNativeSplitCoverageAt (law old registered packetAt)
        (emitted registered packetAt (runtimeCurrent old registered packetAt runtime))
        (patch registered packetAt (runtimeCurrent old registered packetAt runtime)).toLedgerWriteEvolution left right same,
        DescendantFamily (Native.Restructuring.vocabulary old registered) coverage.receipt.sourceEvent
          ((law old registered packetAt).obligationAt (emitted registered packetAt (runtimeCurrent old registered packetAt runtime))
            ((patch registered packetAt (runtimeCurrent old registered packetAt runtime)).toLedgerWriteEvolution.origin left).1)
          coverage.receipt.children) :=
  match (tickCertificate old registered packetAt runtime).split left right same with
  | .identity equality => .inl ⟨equality⟩
  | .split coverage => .inr ⟨coverage, coverage.descendantFamily⟩

def tickMergeConsumer (runtime : Runtime old registered packetAt)
    (left right : OpenResponsibilityAt (World registered) (supportAt registered (runtimeCurrent old registered packetAt runtime)))
    (same : ((patch registered packetAt (runtimeCurrent old registered packetAt runtime)).toLedgerWriteEvolution.destination left).1 =
      ((patch registered packetAt (runtimeCurrent old registered packetAt runtime)).toLedgerWriteEvolution.destination right).1) :
    PLift (left = right) ⊕
      (Σ coverage : SourceNativeMergeCoverageAt (law old registered packetAt)
        (emitted registered packetAt (runtimeCurrent old registered packetAt runtime))
        (patch registered packetAt (runtimeCurrent old registered packetAt runtime)).toLedgerWriteEvolution left right same,
        (parent : (Native.Restructuring.vocabulary old registered).Obligation) → parent ∈ coverage.receipt.parents →
          (Native.Restructuring.vocabulary old registered).LocalDischargePreservedAt coverage.receipt.sourceEvent
            parent.content coverage.receipt.target.content) :=
  match (tickCertificate old registered packetAt runtime).merge left right same with
  | .identity equality => .inl ⟨equality⟩
  | .merge coverage => .inr ⟨coverage, fun _ member => coverage.receipt.every_parent_retains_localDischarge member⟩

theorem tick_next (runtime : Runtime old registered packetAt) :
    runtimeCurrent old registered packetAt runtime.tick.next =
      targetCurrent registered packetAt (runtimeCurrent old registered packetAt runtime) := rfl

theorem tick_math (runtime : Runtime old registered packetAt) :
    (runtimeCurrent old registered packetAt runtime.tick.next).2.state =
      mathTarget (runtimeCurrent old registered packetAt runtime).2 :=
  math_next registered packetAt (runtimeCurrent old registered packetAt runtime)

theorem tick_original_next (runtime : Runtime old registered packetAt) :
    (old.toLedgerRoot.source.source.toRootSource.actual.compile
      (old.emitted (runtimeCurrent old registered packetAt runtime).1)).nextCurrent? =
      some (runtimeCurrent old registered packetAt runtime.tick.next).1 :=
  CompilerFromPacketSourceLaw.original_next registered packetAt (runtimeCurrent old registered packetAt runtime)

def tickSuccessor (runtime : Runtime old registered packetAt) :
    SourceNativeLedgerGeneratedSuccessorAt runtime.tick.generated.occurrence runtime.tick.generated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? runtime.tick.generated.wholeLedgerWriteBack).get (by rfl)

theorem tick_full_destination (runtime : Runtime old registered packetAt) :
    (tickSuccessor old registered packetAt runtime).ledgerEvolution.destination =
      (whole registered packetAt (runtimeCurrent old registered packetAt runtime)).destination :=
  congrArg LedgerWriteEvolutionAt.destination (patch_fold registered packetAt (runtimeCurrent old registered packetAt runtime))

theorem tick_original_projection (runtime : Runtime old registered packetAt)
    (projection : old.source.projectionLaw.Projection) :
    HEq (runtime.tick.generated.projectionOutcome
      ((oldInstallation old registered packetAt).embed (.inl projection)))
      (old.source.projectionLaw.outcomeAt projection (old.emitted (runtimeCurrent old registered packetAt runtime).1)) :=
  old_projection_outcome old registered packetAt
    (emitted registered packetAt (runtimeCurrent old registered packetAt runtime)) projection

theorem facade_tick_factorizes (runtime : Runtime old registered packetAt)
    (face : (facade old registered packetAt).FaceAt runtime) :
    HEq ((facade old registered packetAt).readoutAt runtime face)
      (runtime.tick.generated.projectionOutcome face) ∧
      runtime.tick.nextCurrent = (process old registered packetAt).stateAt
        ((process old registered packetAt).successor runtime.state) := by
  have actual := (facade old registered packetAt).readoutAt_factorizes runtime face
  exact ⟨actual.2.2.2.1, actual.2.2.2.2⟩

end RootGeneratedDebtActivationJointSource.Successor.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
