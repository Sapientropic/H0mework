import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Input.Compilation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Inquiry.State

/-! The source-selected programme and the inherited legacy branch share one
registry.  Both continue on the literal root returned by their U8 consumer;
the first macro successor is visit two, after the actual first body. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource

namespace Legacy
export M14SourceGeneratedPostSettlementObserverSubmissionU8
  (revisedPresentationAt processAt RuntimeState)
end Legacy

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (datum : Datum Party Good Port Technology Instrument)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

abbrev InputChoice :=
  Option { raw : RawInput Party Good Port Technology Instrument // 0 < (ProgrammeSource.registrationSize raw) }

def branchPresentation (choice : InputChoice (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (index : Nat) : RootInquiryStatePresentation :=
  match choice with
  | none => Legacy.revisedPresentationAt oldVisit sourceIndex (boundary + 1) index
  | some raw => ProgrammeInquiry.presentationAt raw.val index

def targetPresentation (index : Nat) : RootInquiryStatePresentation :=
  branchPresentation oldVisit sourceIndex boundary
    (selectedInput datum oldVisit sourceIndex boundary) index

def branchQuery (choice : InputChoice (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (index : Nat) :
    (RootInquiryProcessNode.active (branchPresentation oldVisit sourceIndex boundary choice index)).Query := by
  cases choice <;> exact PUnit.unit

theorem branchQuery_unique (choice : InputChoice (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument)) (index : Nat)
    (candidate : (RootInquiryProcessNode.active
      (branchPresentation oldVisit sourceIndex boundary choice index)).Query) :
    candidate = branchQuery oldVisit sourceIndex boundary choice index := by
  cases choice <;> cases candidate <;> rfl

theorem branch_erase_injective (choice : InputChoice (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Function.Injective
    (fun index => (branchPresentation oldVisit sourceIndex boundary choice index).erase) := by
  intro left right same
  cases choice with
  | none =>
      have stateSame := (Legacy.processAt oldVisit sourceIndex (boundary + 1)).erase_injective
        (left := M14SourceGeneratedPostSettlementObserverSubmissionU8.RuntimeState.revised left)
        (right := M14SourceGeneratedPostSettlementObserverSubmissionU8.RuntimeState.revised right)
        rfl rfl same
      exact M14SourceGeneratedPostSettlementObserverSubmissionU8.RuntimeState.revised.inj stateSame
  | some raw => exact ProgrammeInquiry.presentation_erase_injective raw.val same

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource
