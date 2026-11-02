import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair.Requests

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

namespace AttemptAt

variable {current : RawCurrent Party Good Technology Instrument}
  {focus : Focus (Party := Party) (Good := Good) (Port := Port)}
  {remaining : List (Request Party Good Port Technology Instrument)}
  (attempt : AttemptAt input depth count current focus remaining)

def actualItem : ExecutionItem Party Good Port Technology Instrument := ⟨0, current, attempt.request⟩
def execution := input.law.execute current 0 [attempt.request]
def after := input.law.step current attempt.request

inductive Verdict : Type
  | accepted (paid : input.law.Valid current attempt.request)
  | refused (failure : ¬ input.law.Valid current attempt.request)

def verdict : attempt.Verdict input :=
  if paid : input.law.Valid current attempt.request then .accepted paid else .refused paid

theorem requested_word_is_actual :
    (attempt.execution input).items = [attempt.actualItem input] ∧
      (attempt.execution input).final = attempt.after input := ⟨rfl, rfl⟩

theorem original_request_is_not_rewritten : ∃ request ∈ remaining,
    attempt.request = request ∧ attempt.request.signer = request.signer ∧
      attempt.request.gates = request.gates ∧ attempt.request.consents = request.consents :=
  ⟨attempt.request, attempt.original, rfl, rfl, rfl, rfl⟩

theorem microstep_keeps_original_debt_and_period :
    (attempt.after input).claims = current.claims ∧ (attempt.after input).clock = current.clock ∧
      (attempt.after input).round = current.round := by
  refine ⟨(relevant_is_nonfinancial input depth count current focus attempt.request attempt.relevant).step_claims input.law current _, ?_⟩
  unfold after RawLaw.step
  split <;> exact ⟨rfl, rfl⟩

theorem whole_material_balance (person : Party) (good : Good) :
    (attempt.after input).stock person good + flowAt (input.law.actualDebit current attempt.request) person good =
      current.stock person good + flowAt (input.law.actualCredit current attempt.request) person good :=
  input.law.material_step_balance current attempt.request person good

theorem refusal_is_original_and_has_no_effect (failure : ¬ input.law.Valid current attempt.request) :
    attempt.actualItem input ∈ (attempt.execution input).items ∧
      ¬ input.law.Valid (attempt.actualItem input).before (attempt.actualItem input).request ∧
      attempt.after input = current := by
  refine ⟨List.mem_cons_self, failure, ?_⟩
  simp only [after, RawLaw.step, if_neg failure]

def reassess (prefixLimit renewalLimit : Nat) :=
  Material.Migration.compileMigration input (Migration.origin input depth count) (attempt.after input)
    (Migration.cohort input depth count) prefixLimit renewalLimit

theorem reassessment_keeps_original_floor_context (prefixLimit renewalLimit : Nat) :
    attempt.reassess input depth count prefixLimit renewalLimit =
      Material.Migration.compileMigration input (Migration.origin input depth count) (attempt.execution input).final
        (Migration.cohort input depth count) prefixLimit renewalLimit := rfl

end AttemptAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair
