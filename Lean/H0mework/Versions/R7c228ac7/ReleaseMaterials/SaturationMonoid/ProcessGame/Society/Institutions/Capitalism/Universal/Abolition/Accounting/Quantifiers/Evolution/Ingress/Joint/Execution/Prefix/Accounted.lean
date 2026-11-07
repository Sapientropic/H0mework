import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

private theorem original_cursor_is_accounting
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat) :
    (originalCursor input depth count).phase = .accounting := by
  unfold originalCursor original
  rw [Financial.Installation.Runtime.frames_cursor]
  cases count <;> rfl

variable {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

theorem an_accounted_original_cause_cannot_execute_a_second_fresh_body :
    ¬ Financial.Installation.Cursor.FreshBody seed.input (originalCursor seed.input seed.depth seed.count) := by
  intro fresh
  unfold Financial.Installation.Cursor.FreshBody at fresh
  rw [original_cursor_is_accounting] at fresh
  simp only [reduceCtorEq,false_or] at fresh
  have accounted := seed.origin.accounted
  change Financial.Installation.Cursor.pending seed.input (originalCursor seed.input seed.depth seed.count) = [] at accounted
  have positive := Financial.Installation.Cursor.capacity_positive seed.input (originalCursor seed.input seed.depth seed.count)
  have lengthZero := congrArg List.length accounted
  simp only [Financial.Installation.Cursor.pending,Financial.Installation.Cursor.currentPending,
    fresh.1,List.drop_zero,List.length_append,List.length_nil] at lengthZero
  unfold Financial.Installation.Cursor.capacity at positive
  omega

theorem the_actual_registered_cut_contains_no_historical_repayment_period :
    cutPast seed.input seed.depth seed.count = [] :=
  if_neg (an_accounted_original_cause_cannot_execute_a_second_fresh_body seed)

theorem the_accounted_financial_successor_retains_the_literal_original_raw :
    sourceRaw seed.input seed.depth seed.count = originalRaw seed.input seed.depth seed.count := by
  unfold sourceRaw
  rw [Financial.Installation.Cursor.physical_next_of_bookkeeping seed.input _
    (an_accounted_original_cause_cannot_execute_a_second_fresh_body seed)]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix
