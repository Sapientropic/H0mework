import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Compiler

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

def refusalRequests : {raw : RawInput Party Good Port Technology Instrument} →
    RefusalAt input depth count prefixLimit renewalLimit current raw → RawEvent Party Good Port Technology Instrument
  | _, .invalid request _ => [request]
  | _, .blocked _ _ => []
  | _, .busy _ _ _ _ => []
  | _, .batch _ _ => []
  | _, .migration _ _ => []
  | _, .reviewStopped => []
  | _, .reviewBusy _ _ _ _ => []

namespace Result
variable {raw : RawInput Party Good Port Technology Instrument}

def next : Result input depth count prefixLimit renewalLimit current raw →
    Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  | .accepted checked => checked.command.next input depth count prefixLimit renewalLimit current
  | .refused _ => current

def requests : Result input depth count prefixLimit renewalLimit current raw → RawEvent Party Good Port Technology Instrument
  | .accepted checked => checked.command.requests input depth count prefixLimit renewalLimit current
  | .refused reason => refusalRequests input depth count prefixLimit renewalLimit current reason

def execution (result : Result input depth count prefixLimit renewalLimit current raw) :=
  input.law.execute current.raw 0 (result.requests input depth count prefixLimit renewalLimit current)

def isAccepted : Result input depth count prefixLimit renewalLimit current raw → Bool
  | .accepted _ => true
  | .refused _ => false

theorem refusal_preserves_the_complete_current
    (reason : RefusalAt input depth count prefixLimit renewalLimit current raw) :
    (Result.refused reason).next input depth count prefixLimit renewalLimit current = current := rfl

theorem invalid_request_is_retained_as_a_real_zero_effect_item
    (request : Request Party Good Port Technology Instrument) (failed : ¬ input.law.Valid current.raw request) :
    let result := Result.refused (RefusalAt.invalid (input := input) (depth := depth) (count := count)
      (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) (current := current) request failed)
    (result.execution input depth count prefixLimit renewalLimit current).items = [⟨0, current.raw, request⟩] ∧
      (result.execution input depth count prefixLimit renewalLimit current).final = current.raw := by
  refine ⟨rfl, ?_⟩
  change input.law.step current.raw request = current.raw
  simp only [RawLaw.step, if_neg failed]

theorem whole_material_balance (result : Result input depth count prefixLimit renewalLimit current raw)
    (person : Party) (good : Good) :
    (result.next input depth count prefixLimit renewalLimit current).raw.stock person good +
        input.law.totalDebit (result.execution input depth count prefixLimit renewalLimit current).items person good =
      current.raw.stock person good +
        input.law.totalCredit (result.execution input depth count prefixLimit renewalLimit current).items person good := by
  cases result with
  | accepted checked => exact Actual.command_whole_material_balance input depth count prefixLimit renewalLimit current checked.command person good
  | refused reason =>
      cases reason with
      | blocked obstruction source => rfl
      | busy submission operation notBoundary source => rfl
      | invalid request failed =>
          have balance := input.law.execute_material_balance current.raw 0 [request] person good
          have same : input.law.step current.raw request = current.raw := by simp only [RawLaw.step, if_neg failed]
          simpa only [execution, requests, refusalRequests, next, RawLaw.execute, same] using balance
      | batch word issue => rfl
      | migration pair issue => rfl
      | reviewStopped => rfl
      | reviewBusy code operation notBoundary source => rfl

end Result

def next (raw : RawInput Party Good Port Technology Instrument) :=
  (compile input depth count prefixLimit renewalLimit current raw).next input depth count prefixLimit renewalLimit current

def requests (raw : RawInput Party Good Port Technology Instrument) :=
  (compile input depth count prefixLimit renewalLimit current raw).requests input depth count prefixLimit renewalLimit current

def execution (raw : RawInput Party Good Port Technology Instrument) :=
  (compile input depth count prefixLimit renewalLimit current raw).execution input depth count prefixLimit renewalLimit current

theorem stopped_review_is_a_typed_no_write_answer :
    next input depth count prefixLimit renewalLimit current .stopReview = current ∧
    (execution input depth count prefixLimit renewalLimit current .stopReview).items = [] ∧
    (compile input depth count prefixLimit renewalLimit current .stopReview).isAccepted = false :=
  ⟨rfl, rfl, rfl⟩

theorem compiled_requests_are_exactly_interpreted (raw : RawInput Party Good Port Technology Instrument) :
    (execution input depth count prefixLimit renewalLimit current raw).items.map ExecutionItem.request =
      requests input depth count prefixLimit renewalLimit current raw :=
  input.law.inventory_requests_exact current.raw 0 _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile
