import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Installation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer.State

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Consumer

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

abbrev claim := Responsibility.Consumer.familyClaim

def firstFrame := ofSource claim Root.Consumer.input Root.Consumer.native Root.Consumer.visit
  Responsibility.Consumer.paidPrefixThenRejected 1

def secondWord : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.transfer 2 0 [(.material,1)]⟩]

def secondFrame := Installation.successor claim firstFrame secondWord

def thirdFrame := Installation.successor claim secondFrame Responsibility.Consumer.nominalMatrixWord

theorem the_first_frame_reads_the_already_observed_residual :
    Frame.state claim firstFrame = Responsibility.Family.State.advance claim Responsibility.Consumer.matrixActive
      Control.Scenario.openLaw Responsibility.Consumer.paidPrefixThenRejected := by
  unfold firstFrame
  rw [ofSource_observed,Root.Consumer.the_actual_input_has_the_same_rooted_material_interpretation]

theorem the_second_frame_reads_the_real_next_payment :
    Frame.state claim secondFrame = Responsibility.Family.State.advance claim
      (Responsibility.Family.State.advance claim Responsibility.Consumer.matrixActive
        Control.Scenario.openLaw Responsibility.Consumer.paidPrefixThenRejected) Control.Scenario.openLaw secondWord := by
  unfold secondFrame
  rw [Installation.successor_reads_the_actual_updated_row,the_first_frame_reads_the_already_observed_residual]
  rfl

theorem the_third_frame_keeps_the_same_cursor_and_original_debt :
    Frame.state claim thirdFrame = Responsibility.Family.State.advance claim
      (Responsibility.Family.State.advance claim
        (Responsibility.Family.State.advance claim Responsibility.Consumer.matrixActive
          Control.Scenario.openLaw Responsibility.Consumer.paidPrefixThenRejected) Control.Scenario.openLaw secondWord)
      Control.Scenario.openLaw Responsibility.Consumer.nominalMatrixWord := by
  unfold thirdFrame
  rw [Installation.successor_reads_the_actual_updated_row,the_second_frame_reads_the_real_next_payment]
  rfl

set_option maxHeartbeats 2400000 in
theorem repeated_actual_reentry_consumes_seven_then_six_without_refill_or_iou_erasure :
    (Frame.state claim firstFrame).remaining (0,.material) = 7 ∧
      (Frame.state claim secondFrame).remaining (0,.material) = 6 ∧
      (Frame.state claim thirdFrame).remaining (0,.material) = 6 := by
  rw [the_first_frame_reads_the_already_observed_residual,the_second_frame_reads_the_real_next_payment,
    the_third_frame_keeps_the_same_cursor_and_original_debt]
  decide +kernel

theorem the_second_actual_query_really_selects_sequential_action :
    type_of% (Installation.actual_process_resolution claim firstFrame secondWord) :=
  Installation.actual_process_resolution claim firstFrame secondWord

theorem every_successive_native_row_keeps_the_same_original_source_key :
    secondFrame.row.1 = .inr (Responsibility.Family.activationLaw claim).debtId ∧
      thirdFrame.row.1 = .inr (Responsibility.Family.activationLaw claim).debtId :=
  ⟨secondFrame.rowKey,thirdFrame.rowKey⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Consumer
