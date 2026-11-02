import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Ledger

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {generatedSource : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue generatedSource.snapshot} {all : Candidates generatedSource catalogue} {owner : Ready all}
  (made : Generated owner) (index : Index prepared) (first : First made)

noncomputable section

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source made index first) :=
  identityOnlyWorldLedgerRestructuringLaw (source made index first) () (open_subsingleton made index)

def restructuringSource : SourceNativeRestructuringLedgerSource (N made index) (V made index) where
  source := source made index first
  compiler := {
    ledgerCompiler := ledgerCompiler made index first
    restructuringLaw := restructuringLaw made index first
    certifyRestructuring := by
      intro tick occurrence
      cases occurrence_eq_emitted made index first occurrence
      exact ExactLedgerRestructuringCertificationAt.ofInjective
        (origin_injective made index first tick) (destination_injective made index first tick) }

variable (component : SourceNativeProjectionLaw (oldRoot made index).toAuthoritativeRoot.toLedgerRoot.source)

def parentRoot := (oldRoot made index).withProjectionCoface component

def parentOccurrence (tick : Nat) := (parentRoot made index component).emitted (oldCurrent made index tick)

inductive OwnProjection | ledger | computation
abbrev Projection := (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.Projection ⊕ OwnProjection

def ActiveAt (projection : Projection made index component) {tick : Nat}
    (_occurrence : (source made index first).toRootSource.actual.OccurrenceAt tick) : Type :=
  match projection with
  | .inl old => PLift (BaseAdvance made tick) × (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.ActiveAt old (parentOccurrence made index component tick)
  | .inr _ => Unit

def InactiveAt (projection : Projection made index component) {tick : Nat}
    (_occurrence : (source made index first).toRootSource.actual.OccurrenceAt tick) : Type :=
  match projection with
  | .inl old => (PLift (BaseAdvance made tick) × (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.InactiveAt old (parentOccurrence made index component tick)) ⊕ PLift (¬ BaseAdvance made tick)
  | .inr _ => PEmpty

def classify (projection : Projection made index component) {tick : Nat}
    (occurrence : (source made index first).toRootSource.actual.OccurrenceAt tick) :
    ActiveAt made index first component projection occurrence ⊕ InactiveAt made index first component projection occurrence :=
  match projection with
  | .inl old =>
      if enabled : BaseAdvance made tick then
        match (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.classify old (parentOccurrence made index component tick) with
        | .inl active => .inl ⟨⟨enabled⟩,active⟩
        | .inr inactive => .inr (.inl ⟨⟨enabled⟩,inactive⟩)
      else .inr (.inr ⟨enabled⟩)
  | .inr _ => .inl ()

def projectionLaw : SourceNativeProjectionLaw (ledgerSource made index first) where
  Projection := Projection made index component
  ActiveAt := ActiveAt made index first component
  InactiveAt := InactiveAt made index first component
  classify := classify made index first component
  PayloadAt := fun projection {tick} occurrence active => match projection with
    | .inl old => (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.PayloadAt old (parentOccurrence made index component tick) active.2
    | .inr .ledger => SourceNativeLedgerEvolutionAt (source made index first) occurrence
    | .inr .computation => Book made
  project := fun projection {tick} occurrence active => match projection with
    | .inl old => (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.project old (parentOccurrence made index component tick) active.2
    | .inr .ledger => (ledgerCompiler made index first).compile occurrence
    | .inr .computation => generate made

def authoritySource : SourceNativeAuthoritySource (N made index) (V made index) where
  restructuringSource := restructuringSource made index first
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource made index first)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic (N made index)
  projectionLaw := projectionLaw made index first component

def livingRoot : SourceNativeLivingRootClosure (N made index) (V made index) where
  source := {
    base := authoritySource made index first component
    terminalHandoff := (authoritySource made index first component).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emitted made index first
  compiler_commutes := fun _ => rfl

def initialVisit := SourceNativeTemporalVisitAt.finite
  (livingRoot made index first component).toAuthoritativeRoot.toRoot.initialVisit

def initialGenerated := (livingRoot made index first component).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
  (initialVisit made index first component)

def initialBornEntry := debtEntry (N := ProgrammeSource.N (oldInput made index)) (law := law owner)
  (supportAt made index 0).1 (state made 0)

def initialBornRow : (initialGenerated made index first component).GeneratedEntryRowAt (initialBornEntry made index) :=
  ((initialGenerated made index first component).canonicalGeneratedEntryRow? (initialBornEntry made index)).get (by rfl)

def initialOldRow (entry : OpenResponsibilityAt (ProgrammeSource.N (oldInput made index)) (supportAt made index 0).1) :
    (initialGenerated made index first component).GeneratedEntryRowAt
      (oldEntry (law := law owner) (state? := some (state made 0)) entry) :=
  ((initialGenerated made index first component).canonicalGeneratedEntryRow?
    (oldEntry (law := law owner) (state? := some (state made 0)) entry)).get (by rfl)

def bornAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (livingRoot made index first component)
    (initialVisit made index first component) (initialBornEntry made index) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow (livingRoot made index first component)
    (initialBornEntry made index) (initialBornRow made index first component)

def answerAndNext := (livingRoot made index first component).generatedCausalEntryAnswerAndNextAt
  (initialVisit made index first component) (initialBornEntry made index) (bornAuthority made index first component)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt (initialGenerated made index first component).occurrence
    (initialGenerated made index first component).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (initialGenerated made index first component).wholeLedgerWriteBack).get (by rfl)

theorem canonical_born_entry_is_the_source_admission :
    initialBornEntry made index = (first.write index).initialEntry := rfl

theorem canonical_first_state_is_the_actual_paid_target : state made 1 = first.event.target := by
  change (execute owner (position made 1) (initial owner)).endpoint = _
  have one : position made 1 = 1 := by have positive := first.nonempty;dsimp only [position];omega
  rw [one]
  rfl

include first in
theorem canonical_first_write_strictly_spends_the_born_budget :
    (entryAt made index 1 0).progressBudget < (initialBornEntry made index).progressBudget := by
  exact (law owner).step_budget_lt (paidStep made 0 first.nonempty)

theorem inherited_projection_is_literal (projection : (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.Projection)
    (tick : Nat) (enabled : BaseAdvance made tick) (active : (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.ActiveAt projection (parentOccurrence made index component tick)) :
    HEq ((projectionLaw made index first component).project (.inl projection) (emitted made index first tick) ⟨⟨enabled⟩,active⟩)
      ((parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.project projection (parentOccurrence made index component tick) active) := HEq.rfl

def bookkeeping_inactive (projection : (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.Projection)
    (tick : Nat) (disabled : ¬ BaseAdvance made tick) :
    InactiveAt made index first component (.inl projection) (emitted made index first tick) := .inr ⟨disabled⟩

theorem old_face_is_inactive_during_bookkeeping
    (projection : (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.Projection)
    (tick : Nat) (disabled : ¬ BaseAdvance made tick) :
    classify made index first component (.inl projection) (emitted made index first tick) =
      .inr (bookkeeping_inactive made index first component projection tick disabled) := by
  simp only [classify,dif_neg disabled,bookkeeping_inactive]

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical
