import H0mework.Foundation.Ledger.Restructuring

/-!
# Source-native ledger restructuring focused regression

The positive fixture installs an injective identity ledger under a
restructuring vocabulary whose split and merge coverage fibres are empty.
Every repeated origin/destination is therefore classified by literal entry
identity.

The negative fixture uses the same source occurrence with a weak amplifier.
Its pairwise ledger maps are total, but its repeated origin and destination
would require split and merge receipts whose coverage fibres are empty.  It
cannot obtain restructuring authority.  Independently, the ledger's default
zero budget cannot be cloned by installing a richer split vocabulary: the
root split authority itself now requires a strict child debit.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace SourceNativeLedgerRestructuringRegression

open ConstructiveRoot

/-! ## One constructive source and complete Boolean ledger -/

def network : WorldRelationNetwork where
  Support := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  Responsibility := Bool
  Claim := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  OpenAt := fun _ _ => Unit
  openClaimAt := fun _ => ()
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => Unit
  obstructionClaim := fun _ => ()
  SemanticChangeAt := fun _ _ _ => Unit
  DispositionAt := fun _ _ => Unit

abbrev N := network

theorem networkOpenAtSubsingleton
    (support : N.Support) (responsibility : N.Responsibility) :
    Subsingleton (N.OpenAt support responsibility) where
  allEq := by
    intro left right
    cases left
    cases right
    rfl

def rootVocabulary : ConstructiveRoot.Vocabulary where
  Current := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun _ => ()
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := rootVocabulary

def inventoryPresentation :
    ConstructivePresentation Bool (OpenResponsibilityAt N ()) where
  forward := fun responsibility => ⟨responsibility, ()⟩
  backward := Sigma.fst
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, openAt⟩
    cases openAt
    rfl

def sourceLaw : SourceNativeEventAlgebra N V where
  EventAt := fun _ _ => Unit
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun _ => Bool
  affectedInventoryPresentation := fun _ => inventoryPresentation
  anchorKey := fun _ => ()
  incidenceKey := fun _ => ()
  lineageKey := fun _ => ()
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl

def source : SourceNativeSource N V where
  initial := ()
  law := sourceLaw

def emitted : (current : V.Current) →
    source.toRootSource.actual.OccurrenceAt current :=
  fun _ => ⟨(), ()⟩

abbrev ledger : CompleteLiveLedgerAt N := ⟨()⟩

def falseEntry : ledger.Entry := ⟨false, ()⟩

def trueEntry : ledger.Entry := ⟨true, ()⟩

def identityEvolution : LedgerWriteEvolutionAt N ledger ledger :=
  .identity ledger

/-- Pairwise totality alone permits this one-to-many and many-to-one map. -/
def weakAmplifier : LedgerWriteEvolutionAt N ledger ledger where
  destination := fun _ =>
    ⟨falseEntry, .transferred () rfl rfl (Nat.le_refl _)⟩
  origin := fun _ =>
    ⟨falseEntry, .transferred () rfl rfl (Nat.le_refl _)⟩

structure ExactPairTransition (sourceEntry targetEntry : Bool) : Type where
  equality : sourceEntry = targetEntry

def ledgerCompiler : SourceNativeLedgerCompiler source where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact ExactPairTransition sourceEntry.1 targetEntry.1
  exact_incidence := fun _ => ()
  exact_lineage := fun _ => rfl
  writeRowSource := LedgerWriteRowSourceAt.empty source (by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact ExactPairTransition sourceEntry.1 targetEntry.1)
  terminalRowSource := LedgerTerminalRowSourceAt.empty source
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases current
    cases support
    cases event
    exact .nativeWrite () rfl ⟨(), ()⟩ identityEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases current
    cases support
    cases event
    exact ⟨FiniteGeneratedLedgerWritePatchAt.identity
      (LedgerWriteRowSourceAt.empty source (by
        intro current occurrence targetSupport sourceEntry targetEntry
        exact ExactPairTransition sourceEntry.1 targetEntry.1))
      ⟨(), ()⟩, rfl⟩

/-! ## Exact lifecycle presentation and restructuring authority -/

def responsibilityVocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Unit
  Content := Bool
  Residual := Unit
  Bearer := Unit
  ProtectedInterest := Unit
  Scope := Unit
  Lineage := Unit
  Incidence := Unit
  SourceObservation := ComplementObservation.canonicalComplementPair
  sourceAnchor := fun _ => MinimalRegistrableSourceAnchor.canonical () ()
  sourceIncidence := fun _ => ()
  ObstructionAt := fun _ => Unit
  demandContent := fun _ => false
  demandResidual := fun _ => ()
  CommitmentAt := fun _ _ => Unit
  MandateOriginAt := fun _ _ => Unit
  AcceptedTaskAt := fun _ _ => Unit
  ActiveDependencyAt := fun _ _ => Unit
  ProtectedRiskAt := fun _ _ => Unit
  AdmissionAuthorityAt := fun _ _ => Unit
  AcceptedAt := fun _ _ _ => Unit
  StandingMandateAt := fun _ _ _ => Unit
  DischargeJurisdiction := fun _ _ => Unit
  ProgressAt := fun _ _ _ _ => Unit
  MaintenanceAt := fun _ _ _ => Unit
  TypedDeferAt := fun _ _ _ => Unit
  ScopeNarrowingAt := fun _ _ _ => Unit
  TransferAcceptedAt := fun _ _ _ _ => Unit
  FulfilledAt := fun _ _ _ => Unit
  WaivedAt := fun _ _ _ => Unit
  InvalidatedAt := fun _ _ _ => Unit
  AbandonedAt := fun _ _ _ => Unit
  ImpossibleResidueAcceptedAt := fun _ _ _ => Unit
  SupersessionAt := fun _ _ _ _ _ _ _ => Unit
  ReopenAt := fun _ _ _ _ _ _ _ => Unit
  JurisdictionEndedAt := fun _ _ _ => Unit
  ConsentRevokedAt := fun _ _ _ => Unit
  CapacityReleasedAt := fun _ _ _ => Unit
  UpperRouteAt := fun _ _ _ => Unit
  NextActorSignal := Unit
  AgeSignal := Unit
  TransferOfferSignal := Unit

abbrev ResponsibilityV := responsibilityVocabulary

def payload (content : Bool) : NativeAdmissionPayload ResponsibilityV where
  sourceEvent := ()
  content := content
  residual := ()
  bearer := ()
  beneficiary := ()
  scope := ()
  lineage := ()
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

/-- Coverage is intentionally unavailable.  An identity branch needs none;
an actual split or merge cannot fabricate it. -/
def noCoverageVocabulary : RestructuringVocabulary where
  base := ResponsibilityV
  DescendantAt := fun _ _ _ _ _ => Unit
  SplitCoverageAt := fun _ _ _ => PEmpty
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun _ _ _ => Unit
  RenameAt := fun _ _ _ => Unit

def obligationAt
    {support : N.Support} (entry : OpenResponsibilityAt N support) :
    noCoverageVocabulary.Obligation :=
  (payload entry.1).toObligation

theorem obligationAt_responsibilityKey
    {support : N.Support} (entry : OpenResponsibilityAt N support) :
    (obligationAt entry).content = entry.1 :=
  rfl

theorem obligationAt_injective
    {support : N.Support} : Function.Injective
      (obligationAt (support := support)) := by
  rintro ⟨left, leftOpen⟩ ⟨right, rightOpen⟩ obligation_eq
  have content_eq : left = right :=
    congrArg AdmittedObligation.content obligation_eq
  cases content_eq
  cases leftOpen
  cases rightOpen
  rfl

def restructuringLaw : SourceNativeLedgerRestructuringLaw source where
  vocabulary := noCoverageVocabulary
  sourceEventAt := fun _ => ()
  obligationAt := by
    intro current occurrence support entry
    exact obligationAt entry
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := fun _ => ()
  lineageKey := fun _ => ()
  responsibility_commutes := by
    intro current occurrence support entry
    exact obligationAt_responsibilityKey entry
  anchor_commutes := by
    intro current occurrence support entry
    rfl
  incidence_commutes := by
    intro current occurrence support entry
    rfl
  lineage_commutes := by
    intro current occurrence support entry
    rfl
  obligationAt_injective := by
    intro current occurrence support left right equality
    exact obligationAt_injective equality

/-- The identity compiler classifies aliases by literal entry equality; it
does not ask the empty coverage families for a receipt. -/
def identityRestructuringCertification
    (occurrence : source.toRootSource.actual.OccurrenceAt ()) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases support
  cases event
  exact {
    split := fun _ _ origin_eq => .identity origin_eq
    merge := fun _ _ destination_eq => .identity destination_eq
  }

def restructuringCompiler : SourceNativeRestructuringLedgerCompiler source where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := identityRestructuringCertification

def restructuringSource : SourceNativeRestructuringLedgerSource N V where
  source := source
  compiler := restructuringCompiler

/-! The certification is part of the source compiler itself.  No later root
wrapper or pair-query court is needed to read it. -/

/-- The exact source compiler uses identity in both directions despite empty
split and merge coverage fibres. -/
theorem injective_identity_branch_needs_no_coverage :
    (restructuringCompiler.certifyRestructuring (emitted ())).split
        falseEntry falseEntry rfl = .identity rfl ∧
      (restructuringCompiler.certifyRestructuring (emitted ())).merge
        trueEntry trueEntry rfl = .identity rfl :=
  ⟨rfl, rfl⟩

theorem weak_amplifier_split_cannot_be_certified :
    IsEmpty (SourceNativeSplitClassificationAt restructuringLaw
      (emitted ()) weakAmplifier falseEntry trueEntry rfl) where
  false classification := by
    cases classification with
    | identity target_eq =>
        exact Bool.noConfusion (congrArg Sigma.fst target_eq)
    | split coverage =>
        exact PEmpty.elim coverage.receipt.coverage

/-- Even if a domain replaces the empty receipt vocabulary, this zero-budget
root cannot certify a split.  Receipt richness cannot refill the live row. -/
theorem zero_budget_split_authority_is_empty :
    IsEmpty (SourceNativeSplitCoverageAt restructuringLaw
      (emitted ()) weakAmplifier falseEntry trueEntry rfl) where
  false coverage := by
    have positive := coverage.parentProgressBudget_positive
    exact Nat.not_lt_zero _ positive

theorem weak_amplifier_merge_cannot_be_certified :
    IsEmpty (SourceNativeMergeClassificationAt restructuringLaw
      (emitted ()) weakAmplifier falseEntry trueEntry rfl) where
  false classification := by
    cases classification with
    | identity source_eq =>
        exact Bool.noConfusion (congrArg Sigma.fst source_eq)
    | merge coverage =>
        exact PEmpty.elim coverage.receipt.coverage

/-- The weak amplifier has neither a legal split nor a legal merge
classification, hence cannot become a restructuring-aware compiler image. -/
theorem weak_amplifier_cannot_acquire_restructuring_authority :
    IsEmpty (ExactLedgerRestructuringCertificationAt restructuringLaw
      (emitted ()) weakAmplifier) where
  false certification :=
    weak_amplifier_split_cannot_be_certified.false <|
      certification.split falseEntry trueEntry rfl

/-- The identity-only adapter exposes only the occurrence-indexed,
injective restructuring law.  Its `PUnit` implementation vocabulary and raw
admitted-obligation helper cannot be used as detached lifecycle mouths. -/
theorem identity_only_raw_admission_mouths_are_private : True := by
  fail_if_success
    exact identityOnlyWorldLedgerRestructuringVocabulary N ()
  fail_if_success
    exact identityOnlyWorldLedgerObligationAt () falseEntry
  trivial

/-- The public identity adapter may present an already open row, but its
commitment and discharge receipts contain exactly that row's `OpenAt`
witness rather than a free inhabited token. -/
theorem identity_only_admission_is_exact_open_row :
    let law := identityOnlyWorldLedgerRestructuringLaw source ()
      networkOpenAtSubsingleton
    Nonempty
        (ConstructivePresentation
          (law.vocabulary.base.CommitmentAt () false)
          (N.OpenAt () false)) ∧
      Nonempty
        (ConstructivePresentation
          (law.vocabulary.base.DischargeJurisdiction false ())
          (N.OpenAt () false)) := by
  dsimp only
  exact
    ⟨⟨identityOnlyWorldLedgerCommitmentPresentation source ()
        networkOpenAtSubsingleton () false⟩,
      ⟨identityOnlyWorldLedgerDischargePresentation source ()
        networkOpenAtSubsingleton () false⟩⟩

end SourceNativeLedgerRestructuringRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
