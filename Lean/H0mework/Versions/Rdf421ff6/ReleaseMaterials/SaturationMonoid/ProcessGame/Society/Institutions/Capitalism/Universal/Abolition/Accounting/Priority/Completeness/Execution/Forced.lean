import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)

def presentation := Refusal.Installation.presentation claim (Source.native claim frame) (Source.word claim frame)

def nextFrame := Refusal.Action.nextFrame claim (Source.native claim frame) (Source.word claim frame)

def actualReply := Refusal.Source.readReply claim (Source.native claim frame) (Source.word claim frame)

/-- The installed mechanism consumes its root's compiled word. There is no
external adoption, capital-consent or target-state argument. -/
theorem source_selection_controls_the_actual_action :
    Refusal.RefusalInstalledAt claim (Source.native claim frame) (Source.word claim frame) :=
  Refusal.the_original_root_returns_refusal_liability_and_no_capital_renewal_authority
    claim (Source.native claim frame) (Source.word claim frame)

theorem the_actual_answer_and_next_have_one_original_root :
    (RootInquiryProcessNode.answered (presentation claim frame) PUnit.unit).erase =
      (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
        ⟨(nextFrame claim frame).V,(nextFrame claim frame).root.toAuthoritativeRoot,
          (nextFrame claim frame).visit⟩⟩ : AnyAuthoritativeRootCurrent) :=
  (source_selection_controls_the_actual_action claim frame).actual_next

theorem the_current_source_and_its_chosen_word_control_the_actual_next :
    Abolition.Accounting.Root.Reentry.Frame.state claim (nextFrame claim frame) =
      Responsibility.Family.State.advance claim
        (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw
        (Root.Gate.executableWord claim (Source.native claim frame) (Source.word claim frame)) := by
  unfold nextFrame
  rw [Refusal.the_liability_is_read_on_the_same_actual_next_row,Source.state_eq]
  rfl

def nextCalculationFace : SourceNativeRootSemanticFaceAt
    (nextFrame claim frame).root (nextFrame claim frame).visit where
  projection := Abolition.Accounting.Root.Reentry.inquiryOldProjection claim
    (Refusal.Source.native claim (Source.native claim frame) (Source.word claim frame))
    (Root.Gate.executableWord claim (Source.native claim frame) (Source.word claim frame))
    (.inherited (.inherited (.inherited (.inherited (Source.face claim frame).projection))))
  active := (Source.face claim frame).active
  classifier_eq := (Source.face claim frame).classifier_eq

theorem selection_and_every_resource_inspection_remain_visible_on_the_same_next :
    HEq (nextCalculationFace claim frame).rootRead (Source.read claim frame) := HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution
