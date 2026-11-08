import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Effect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (request : Request Party Good Port Technology Instrument)

theorem primitive_requests_are_the_original_payload :
    requests input depth count prefixLimit renewalLimit current (.primitive request) = [request] := by
  cases observed : Actual.inspectPrimitive input current request <;>
    simp only [requests, compile, observed, Result.requests, refusalRequests, Actual.Command.requests]

theorem primitive_after_is_the_original_guarded_step :
    (next input depth count prefixLimit renewalLimit current (.primitive request)).raw = input.law.step current.raw request := by
  cases observed : Actual.inspectPrimitive input current request with
  | accepted legal => simp only [next, compile, observed, Result.next, Actual.Command.next, Actual.primitiveNext]
  | refused failed =>
      simp only [next, compile, observed, Result.next, RawLaw.step, if_neg failed]

theorem primitive_guarded_financial_delta (instrument : Instrument) (debtor creditor : Party) :
    (next input depth count prefixLimit renewalLimit current (.primitive request)).raw.claims instrument debtor creditor =
      current.raw.claims instrument debtor creditor + input.law.actualClaimDelta current.raw request instrument debtor creditor := by
  rw [primitive_after_is_the_original_guarded_step]
  exact input.law.step_financial_balance current.raw request instrument debtor creditor

theorem invalid_input_is_a_typed_refusal (failed : ¬ input.law.Valid current.raw request) :
    ∃ refusal, compile input depth count prefixLimit renewalLimit current (.primitive request) = .refused refusal := by
  cases observed : Actual.inspectPrimitive input current request with
  | accepted legal => exact (failed legal).elim
  | refused failure => exact ⟨.invalid request failure, by simp only [compile, observed]⟩

theorem invalid_input_preserves_the_complete_current (failed : ¬ input.law.Valid current.raw request) :
    next input depth count prefixLimit renewalLimit current (.primitive request) = current := by
  obtain ⟨refusal, generated⟩ := invalid_input_is_a_typed_refusal input depth count prefixLimit renewalLimit current request failed
  unfold next
  rw [generated]
  rfl

#print axioms primitive_requests_are_the_original_payload
#print axioms primitive_guarded_financial_delta
#print axioms invalid_input_preserves_the_complete_current

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile
