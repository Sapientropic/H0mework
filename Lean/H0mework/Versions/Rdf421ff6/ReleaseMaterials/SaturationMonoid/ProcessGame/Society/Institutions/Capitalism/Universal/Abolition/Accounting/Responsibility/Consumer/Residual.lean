import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer.Matrix

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer

open Source.Program
open Innovation

noncomputable section

def nominalMatrixWord : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.issue () 0 2 100⟩]

def foreignMatrixWord : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.transfer 1 0 [(.material,8)]⟩]

def selfMatrixWord : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.transfer 2 2 [(.material,1)]⟩]

def presentMatrixWord : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.present⟩]

def materialOnlyWord : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.revise 2 2⟩] ++
    List.replicate 4 ⟨0,[],false,[],.produce 2⟩ ++
    [⟨0,[],false,[],.transfer 2 0 [(.material,8)]⟩,
     ⟨0,[],false,[],.transfer 2 1 [(.material,5)]⟩]

def paidPrefixThenRejected : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.transfer 2 0 [(.material,1)]⟩,
   ⟨0,[],false,[],.transfer 2 0 [(.material,1000)]⟩]

set_option maxHeartbeats 2400000 in
theorem a_new_iou_and_foreign_funding_cannot_move_the_original_material_cursor :
    (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw nominalMatrixWord).raw.stock 0 .material =
        matrixActive.raw.stock 0 .material ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw foreignMatrixWord).raw.stock 0 .material =
        matrixActive.raw.stock 0 .material ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw nominalMatrixWord).remaining (0,.material) = 8 ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw foreignMatrixWord).remaining (0,.material) = 8 := by
  decide +kernel

set_option maxHeartbeats 2400000 in
theorem self_transfer_and_approval_do_not_settle_original_harms :
    (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw selfMatrixWord).remaining (2,.material) = 5 ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw presentMatrixWord).remaining (0,.material) = 8 ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw presentMatrixWord).remaining (0,.result) = 2 := by
  decide +kernel

set_option maxHeartbeats 2400000 in
theorem global_production_cannot_pay_another_original_beneficiary_without_delivery :
    (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw materialOnlyWord).remaining (0,.material) = 0 ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw materialOnlyWord).remaining (1,.material) = 0 ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw materialOnlyWord).remaining (2,.material) = 0 ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw materialOnlyWord).remaining (0,.result) = 2 ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw materialOnlyWord).remaining (1,.result) = 1 := by
  decide +kernel

set_option maxHeartbeats 2400000 in
theorem a_later_rejection_cannot_charge_again_for_the_original_real_paid_prefix :
    (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw paidPrefixThenRejected).remaining (0,.material) = 7 ∧
      (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw paidPrefixThenRejected).raw.stock 0 .material =
        matrixActive.raw.stock 0 .material + 1 := by decide +kernel

theorem even_the_paid_matrix_has_no_whole_society_terminal_authority :
    (Family.activationLaw familyClaim).SupportTerminalAt matrixPaid → False := by
  intro terminal
  exact nomatch terminal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer
