import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLedger

/-! The source's finite instruction inventory refines the inherited programme
responsibility.  This uses the existing lifecycle split receipt and the
existing world ledger.  Its structural custodian is the inherited root row;
economic parties are generated separately by the original programme face.
There is no terminal or financial discharge in this refinement vocabulary. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRestructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot ComplementObservation
open ProgrammeWorld ProgrammeSource ProgrammeLedger

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)

abbrev lifecycle : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := (N input).Support
  Content := (N input).Responsibility
  Residual := Nat
  Bearer := Unit
  ProtectedInterest := (N input).Claim
  Scope := Unit
  Lineage := (N input).Lineage
  Incidence := (N input).Incidence
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun _ => MinimalRegistrableSourceAnchor.canonical () ()
  sourceIncidence := (N input).incidenceAt
  ObstructionAt := fun _ => PEmpty
  demandContent := fun impossible => impossible.elim
  demandResidual := fun impossible => impossible.elim
  CommitmentAt := fun _ _ => PEmpty
  MandateOriginAt := fun support row => (N input).OpenAt support row
  AcceptedTaskAt := fun _ _ => PEmpty
  ActiveDependencyAt := fun _ _ => PEmpty
  ProtectedRiskAt := fun _ _ => PEmpty
  AdmissionAuthorityAt := fun _ _ => Unit
  AcceptedAt := fun _ _ _ => PEmpty
  StandingMandateAt := fun _ _ _ => Unit
  DischargeJurisdiction := fun _ _ => Unit
  ProgressAt := fun _ _ _ _ => PEmpty
  MaintenanceAt := fun _ _ _ => PEmpty
  TypedDeferAt := fun _ _ _ => PEmpty
  ScopeNarrowingAt := fun _ _ _ => PEmpty
  TransferAcceptedAt := fun _ _ _ _ => PEmpty
  FulfilledAt := fun _ _ _ => PEmpty
  WaivedAt := fun _ _ _ => PEmpty
  InvalidatedAt := fun _ _ _ => PEmpty
  AbandonedAt := fun _ _ _ => PEmpty
  ImpossibleResidueAcceptedAt := fun _ _ _ => PEmpty
  SupersessionAt := fun _ _ _ _ _ _ _ => PEmpty
  ReopenAt := fun _ _ _ _ _ _ _ => PEmpty
  JurisdictionEndedAt := fun _ _ _ => PEmpty
  ConsentRevokedAt := fun _ _ _ => PEmpty
  CapacityReleasedAt := fun _ _ _ => PEmpty
  UpperRouteAt := fun _ _ _ => PEmpty
  NextActorSignal := PEmpty
  AgeSignal := PEmpty
  TransferOfferSignal := PEmpty

def admission {support : (N input).Support}
    (entry : OpenResponsibilityAt (N input) support) :
    NativeAdmissionPayload (lifecycle input) where
  sourceEvent := support
  content := entry.1
  residual := entry.progressBudget
  bearer := ()
  beneficiary := entry.claim
  scope := ()
  lineage := ()
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .standingMandate entry.2
  authority := ()
  assumption := .mandated ()
  dischargeJurisdiction := ()

def obligation {support : (N input).Support}
    (entry : OpenResponsibilityAt (N input) support) :
    AdmittedObligation (lifecycle input) := (admission input entry).toObligation

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem open_subsingleton (support : (N input).Support) (row : (N input).Responsibility) :
    Subsingleton ((N input).OpenAt support row) := by
  cases support <;> cases row <;>
    first | exact (inferInstance : Subsingleton Unit) | exact (inferInstance : Subsingleton PEmpty)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem obligation_injective {support : (N input).Support} :
    Function.Injective (obligation input (support := support)) := by
  rintro ⟨left, leftOpen⟩ ⟨right, rightOpen⟩ same
  have rows : left = right := congrArg AdmittedObligation.content same
  cases rows
  have witnesses := (open_subsingleton input support left).elim leftOpen rightOpen
  cases witnesses
  rfl

abbrev restructuringVocabulary : RestructuringVocabulary where
  base := lifecycle input
  DescendantAt := fun support parentIncidence parent childIncidence child =>
    PLift (support = .bootstrap ∧ parentIncidence = true ∧ childIncidence = true ∧
      parent = .inherited ∧ child ∈ childRows input)
  SplitCoverageAt := fun support parent children =>
    PLift (support = .bootstrap ∧ parent = .inherited ∧ children = childRows input)
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun support parent child =>
    PLift (support = .bootstrap ∧ parent = .inherited ∧ child ∈ childRows input)
  RenameAt := fun _ before after => PLift (before = after)

def restructuringLaw : SourceNativeLedgerRestructuringLaw (ProgrammeSource.source input) where
  vocabulary := restructuringVocabulary input
  sourceEventAt := fun occurrence => occurrence.1
  obligationAt := fun {_} _ {_} entry => obligation input entry
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by intro current occurrence support entry; rfl
  anchor_commutes := by intro current occurrence support entry; rfl
  incidence_commutes := by intro current occurrence support entry; rfl
  lineage_commutes := by intro current occurrence support entry; rfl
  obligationAt_injective := by intro current occurrence support; exact obligation_injective input

def firstChildren : List (restructuringVocabulary input).Obligation :=
  (childRows input).map fun row => obligation input (targetEntry input .bootstrap row)

theorem firstChildren_content :
    (firstChildren input).map AdmittedObligation.content = childRows input := by
  change ((childRows input).map fun row =>
    obligation input (targetEntry input .bootstrap row)).map AdmittedObligation.content = _
  rw [List.map_map]
  exact List.map_id (childRows input)

theorem firstChildren_nonempty : firstChildren input ≠ [] := by
  exact List.cons_ne_nil _ _

theorem child_content_mem (child : (restructuringVocabulary input).Obligation)
    (member : child ∈ firstChildren input) : child.content ∈ childRows input := by
  rw [← firstChildren_content input]
  exact List.mem_map.mpr ⟨child, member, rfl⟩

theorem child_incidence (child : (restructuringVocabulary input).Obligation)
    (member : child ∈ firstChildren input) : child.sourceIncidence = true := by
  obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
  rfl

def firstReceipt (parent : OpenResponsibilityAt (N input) .bootstrap)
    (isParent : parent.1 = .inherited) :
    SplitReceipt (restructuringVocabulary input) (obligation input parent) where
  sourceEvent := .bootstrap
  sourceOwnership := ⟨rfl, rfl⟩
  children := firstChildren input
  children_nonempty := firstChildren_nonempty input
  coverage := ⟨rfl, isParent, firstChildren_content input⟩
  descendant := fun child member =>
    ⟨rfl, rfl, child_incidence input child member, isParent,
      child_content_mem input child member⟩
  anchorTransport := fun child member => {
    toFun := id
    injective := Function.injective_id
    map_identity := by
      obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
      rfl
    map_complement := fun _ => rfl
    scope_eq := Subsingleton.elim _ _
    lineage_eq := Subsingleton.elim (α := Unit) _ _ }
  lineage := fun _ _ => Subsingleton.elim (α := Unit) _ _
  localDischarge := fun child member =>
    ⟨rfl, isParent, child_content_mem input child member⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRestructuring
