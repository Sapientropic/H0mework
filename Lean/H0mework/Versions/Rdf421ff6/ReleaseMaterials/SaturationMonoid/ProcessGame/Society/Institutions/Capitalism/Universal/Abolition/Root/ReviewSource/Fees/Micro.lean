import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Code.Independent
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Execution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def feeInput := Physical.receive current (.primitive code.request)
def feeTarget := Physical.next (feeInput current code)

local notation "before" => Physical.stateAt input depth count prefixLimit renewalLimit current.past
local notation "after" => Physical.stateAt input depth count prefixLimit renewalLimit (Physical.Cursor.past (feeTarget current code))

/-- The actual primitive compiler supplies the payment or its original
rejection for every Input, independently of task-source adapter shape. -/
theorem the_original_primitive_fee_has_its_source_generated_effect :
    match Review.attempt input.law code.request code.scope (before).raw with
    | .inl paid =>
        (after).raw = paid.microNext ∧
        (after).raw.stock code.scope.payer code.scope.good + code.scope.amount =
          (before).raw.stock code.scope.payer code.scope.good ∧
        (after).raw.claims = (before).raw.claims ∧
        (after).raw.clock = (before).raw.clock ∧
        (after).raw.round = (before).raw.round
    | .inr _obstruction =>
        after = before ∧ ¬ input.law.Valid (before).raw code.request := by
  have step := Physical.consumed_input_generates_its_own_after input depth count prefixLimit renewalLimit (feeInput current code)
  change after = Compile.next input depth count prefixLimit renewalLimit before (.primitive code.request) at step
  cases produced : Review.attempt input.law code.request code.scope (before).raw with
  | inl paid =>
      have accepted := paid.accepted
      have next : (after).raw = paid.microNext := by
        rw [step]
        simp only [Compile.next, Compile.compile, Actual.inspectPrimitive, dif_pos accepted,
          Compile.Result.next, Actual.Command.next, Actual.primitiveNext, Review.PaymentAt.microNext]
      refine ⟨next, ?_, ?_, ?_, ?_⟩
      · rw [next]
        exact paid.micro_stock_balance code.scope
      · rw [next]
        exact paid.micro_claims_unchanged code.scope
      · rw [next]
        exact paid.micro_clock_and_round.1
      · rw [next]
        exact paid.micro_clock_and_round.2
  | inr obstruction =>
      have rejected := obstruction.request_is_actually_rejected
      refine ⟨?_, rejected⟩
      rw [step]
      simp only [Compile.next, Compile.compile, Actual.inspectPrimitive, dif_neg rejected, Compile.Result.next]

theorem the_original_fee_item_survives_acceptance_and_rejection :
    (Physical.execution input depth count prefixLimit renewalLimit (feeInput current code)).items =
      [⟨0, (before).raw, code.request⟩] := by
  change (Compile.execution input depth count prefixLimit renewalLimit before (.primitive code.request)).items = _
  cases produced : Actual.inspectPrimitive input before code.request <;>
    simp only [Compile.execution, Compile.compile, produced, Compile.Result.execution,
      Compile.Result.requests, Actual.Command.requests, Compile.refusalRequests, RawLaw.execute]

theorem a_real_fee_microstep_keeps_the_original_period_clock :
    (after).raw.clock = (before).raw.clock ∧ (after).raw.round = (before).raw.round := by
  have actual := the_original_primitive_fee_has_its_source_generated_effect
    input depth count prefixLimit renewalLimit current code
  cases produced : Review.attempt input.law code.request code.scope (before).raw with
  | inl paid => rw [produced] at actual; exact actual.2.2.2
  | inr obstruction => rw [produced] at actual; rw [actual.1]; exact ⟨rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees.the_original_primitive_fee_has_its_source_generated_effect
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees.the_original_fee_item_survives_acceptance_and_rejection
