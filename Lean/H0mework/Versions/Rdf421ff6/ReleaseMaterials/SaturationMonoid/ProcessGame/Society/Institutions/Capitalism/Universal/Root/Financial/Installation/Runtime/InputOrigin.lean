import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Ingress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Input.Runtime

/-! The first query is the original registered full-input germ.  The next
query starts at its literal macro target; accounting is not attached to an
arbitrary bare engine or to a reconstructed body result. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def datum : InputSource.Datum Party Good Port Technology Instrument := ⟨fun _ => .programme input⟩

variable (oldVisit : OldVisit) (sourceIndex boundary : Nat)

def inputPresentation := InputSource.presentation (datum input) oldVisit sourceIndex boundary

def inputQuery : (inputPresentation input oldVisit sourceIndex boundary).Query :=
  InputSource.germAt (datum input)
    ((InputSource.root (datum input)).emitted
      (InputSource.visit (datum input) oldVisit sourceIndex boundary).current)

omit [DecidableEq Port] in
theorem input_query_unique (candidate : (inputPresentation input oldVisit sourceIndex boundary).Query) :
    candidate = inputQuery input oldVisit sourceIndex boundary :=
  InputSource.germ_unique (datum input) _ candidate

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem selected_input (positive : 0 < ProgrammeSource.registrationSize input) :
    InputSource.selectedInput (datum input) oldVisit sourceIndex boundary = some ⟨input, positive⟩ := by
  simp only [InputSource.selectedInput, InputSource.chosenInput, InputSource.germAt, datum, dif_pos positive]

omit [DecidableEq Port] in
theorem input_entry_card : erasedEntryCard (inputPresentation input oldVisit sourceIndex boundary).erase = 1 := by
  let source := inputPresentation input oldVisit sourceIndex boundary
  let Carrier := OpenResponsibilityAt source.N source.state.base.support
  let canonical : Carrier := source.state.base.entryAt (inputQuery input oldVisit sourceIndex boundary)
  have singleton : Subsingleton Carrier := by
    constructor
    rintro ⟨left, leftOpen⟩ ⟨right, rightOpen⟩
    cases left
    cases right
    have same : leftOpen = rightOpen := by
      cases leftOpen
      cases rightOpen
      rfl
    cases same
    rfl
  let : Unique Carrier := ⟨⟨canonical⟩, fun other => singleton.elim other canonical⟩
  change Nat.card Carrier = 1
  exact Nat.card_unique

theorem input_successor_valid (positive : 0 < ProgrammeSource.registrationSize input)
    (query : (inputPresentation input oldVisit sourceIndex boundary).Query) :
    (ingressPresentation input 1).erase =
        (RootInquiryProcessNode.answered (inputPresentation input oldVisit sourceIndex boundary) query).erase ∧
      (RootInquiryProcessNode.active (inputPresentation input oldVisit sourceIndex boundary)).PreservesGeneratedLivingLawAt
        query (.active (ingressPresentation input 1)) := by
  have unique := input_query_unique input oldVisit sourceIndex boundary query
  cases unique
  have original := ((InputSource.process (datum input) oldVisit sourceIndex boundary).successorAt
    .source (inputQuery input oldVisit sourceIndex boundary)).property
  change (InputSource.targetPresentation (datum input) oldVisit sourceIndex boundary 2).erase =
      (RootInquiryProcessNode.answered (inputPresentation input oldVisit sourceIndex boundary)
        (inputQuery input oldVisit sourceIndex boundary)).erase ∧
    (RootInquiryProcessNode.active (inputPresentation input oldVisit sourceIndex boundary)).PreservesGeneratedLivingLawAt
      (inputQuery input oldVisit sourceIndex boundary)
      (.active (InputSource.targetPresentation (datum input) oldVisit sourceIndex boundary 2)) at original
  rw [InputSource.targetPresentation, selected_input input oldVisit sourceIndex boundary positive] at original
  exact original

theorem input_ne_ingress :
    (inputPresentation input oldVisit sourceIndex boundary).erase ≠ (ingressPresentation input 1).erase := by
  intro same
  have cards := congrArg erasedEntryCard same
  rw [input_entry_card] at cards
  have lower := programme_entry_lower input (ProgrammeHistory.visitAt input 2).current
  change 2 ≤ erasedEntryCard (ingressPresentation input 1).erase at lower
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
