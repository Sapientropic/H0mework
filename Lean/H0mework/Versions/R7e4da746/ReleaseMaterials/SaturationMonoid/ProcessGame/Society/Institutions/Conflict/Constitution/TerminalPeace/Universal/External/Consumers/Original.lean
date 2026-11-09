import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion.Root
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Frontier

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.OriginalSource

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_append)
open Completion (Phase anchor generated)
open ExposureGuard (stop)
open Renewal (Interleaving)

noncomputable section

abbrev Current := AnyAuthoritativeRootCurrent × ℚ
abbrev Write := AnyAuthoritativeRootCurrent × List Original.Item

abbrev Policy := Interleaving anchor

def physicalClock : Phase → ℚ
  | .loss => Original.cut.raw.clock
  | .secured => Settlement.physicalCut.raw.clock
  | .delivered => (endAt Original.seed (Settlement.protectedPast ++ [Settlement.payerInput])).raw.clock
  | .accounted => Settlement.settledCut.raw.clock
  | .living visit => visit.ready.val.native.raw.clock

def currentAt (policy : Policy) (visit : Nat) : Current :=
  let phase := generated policy visit
  (phase.whole, physicalClock phase)

def actualItems (policy : Policy) : Phase → List Original.Item
  | .loss => Boundary.Actual.items Original.cut stop
  | .secured => Boundary.Actual.items Settlement.physicalCut Settlement.payerInput
  | .delivered => Boundary.Actual.items (endAt Original.seed (Settlement.protectedPast ++ [Settlement.payerInput])) none
  | .accounted => Completion.peace.val.items
  | .living prior => (policy.next prior).ready.val.items

/-- The native event projection uses the actual whole successor and
complete material inventory, including empty inventory on refusal. -/
def writeAt (policy : Policy) (visit : Nat) : Write :=
  ((generated policy (visit + 1)).whole, actualItems policy (generated policy visit))

private theorem prior_to_settlement_clock (policy : Policy) :
    (currentAt policy 0).2 ≤ (currentAt policy 1).2 ∧
    (currentAt policy 1).2 ≤ (currentAt policy 2).2 ∧
    (currentAt policy 2).2 ≤ (currentAt policy 3).2 ∧
    (currentAt policy 3).2 ≤ (currentAt policy 4).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Original.cut.raw.clock ≤ Settlement.physicalCut.raw.clock
    rw [Original.cut_raw, Settlement.protected_stock]
  · change Settlement.physicalCut.raw.clock ≤
      (endAt Original.seed (Settlement.protectedPast ++ [Settlement.payerInput])).raw.clock
    rw [endAt_append]
    exact Quantities.Execution.the_actual_script_never_runs_the_clock_backwards _ _
  · change (endAt Original.seed (Settlement.protectedPast ++ [Settlement.payerInput])).raw.clock ≤
      (endAt Original.seed ((Settlement.protectedPast ++ [Settlement.payerInput]) ++ [none])).raw.clock
    rw [endAt_append Original.seed (Settlement.protectedPast ++ [Settlement.payerInput]) [none]]
    exact Quantities.Execution.the_actual_script_never_runs_the_clock_backwards _ _
  · change Settlement.settledCut.raw.clock ≤ Completion.peace.val.native.raw.clock
    rw [Settlement.settled_raw, Completion.the_first_peace_write_reads_the_paid_current]
    decide +kernel

private theorem clock_mono (policy : Policy) : Monotone (Prod.snd ∘ currentAt policy) := by
  apply monotone_nat_of_le_succ
  intro visit
  by_cases early : visit < 4
  · have clock := prior_to_settlement_clock policy
    have cases : visit = 0 ∨ visit = 1 ∨ visit = 2 ∨ visit = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact clock.1
    · exact clock.2.1
    · exact clock.2.2.1
    · exact clock.2.2.2
  · let n := visit - 4
    have atTail : visit = n + 4 := by omega
    change (currentAt policy visit).2 ≤ (currentAt policy (visit + 1)).2
    rw [atTail, show n + 4 + 1 = n + 1 + 4 by omega]
    unfold currentAt
    rw [Completion.the_generated_future_replays_the_original_compiler,
      Completion.the_generated_future_replays_the_original_compiler]
    exact policy.next_clock_mono (policy.run Completion.peace n)

private theorem native_cofinal (policy : Policy) (bound : ℚ) :
    ∃ visit, bound < (currentAt policy visit).2 := by
  obtain ⟨cut, _, past⟩ := policy.every_run_is_clock_cofinal_after_every_cut Completion.peace 0 bound
  refine ⟨cut + 4, ?_⟩
  unfold currentAt
  rw [Completion.the_generated_future_replays_the_original_compiler]
  exact past

def NoActualDamage (effect : Option Write) : Prop :=
  match effect with
  | none => True
  | some write => ∀ item ∈ write.2, ∀ key,
      Reparation.loss Supply.physical Original.community item key = 0

theorem a_factored_external_write_cannot_reopen_the_war
    (policy : Policy) (external : Trace Current Write)
    (factor : external.Factors (currentAt policy) (writeAt policy) external.ordinal)
    (visit : Nat) (after : 4 ≤ external.ordinal visit) :
    NoActualDamage (external.effect visit) := by
  unfold NoActualDamage
  cases observed : external.effect visit with
  | none => trivial
  | some write =>
    rw [factor.writes visit write observed]
    let n := external.ordinal visit - 4
    have atTail : external.ordinal visit = n + 4 := by omega
    rw [atTail]
    unfold writeAt
    rw [Completion.the_generated_future_replays_the_original_compiler policy n]
    exact policy.next_has_no_damage (policy.run Completion.peace n)

theorem every_exact_external_future_has_the_same_peace_cut
    (policy : Policy) (external : Trace Current Write)
    (starts : external.current 0 = currentAt policy 0)
    (checks : ∀ visit, external.Check (currentAt policy) (writeAt policy) visit) :
    (∀ bound, ∃ visit, bound < (external.current visit).2) ↔
      ((∃! factor, external.Factors (currentAt policy) (writeAt policy) factor) ∧
      (∀ cut, ∃! visit, external.FirstAt cut visit) ∧
      (∃! visit, external.FirstAt 4 visit ∧
        external.current visit = (Completion.peace.val.state.resident.erase, 5)) ∧
      ∀ start bound, ∃ visit ≥ start, bound < (external.current visit).2) := by
  have factor := external.factor_of_checks (currentAt policy) (writeAt policy) starts checks
  constructor
  · intro time
    have progress := external.progress_of_clock_cofinal Prod.snd factor (clock_mono policy) time
    have all := external.progress_iff_every_original_cut_has_unique_first_visit.mp progress
    have peaceful : currentAt policy 4 = (Completion.peace.val.state.resident.erase, 5) := by
      apply Prod.ext
      · rfl
      · change Completion.peace.val.native.raw.clock = 5
        exact congrArg (fun raw : Original.Raw => raw.clock) Completion.the_first_peace_write_reads_the_paid_current
    obtain ⟨visit, first, unique⟩ := all 4
    exact ⟨(external.exact_local_checks_iff_unique_factor _ _).mp ⟨starts, checks⟩, all,
      ⟨visit, ⟨first, (factor.reads visit).trans (by rw [first.1, peaceful])⟩, fun other same => unique other same.1⟩,
      external.clock_cofinal_after_each_visit_of_progress Prod.snd factor
        (clock_mono policy) (native_cofinal policy) progress⟩
  · rintro ⟨_, _, _, time⟩ bound
    obtain ⟨visit, _, later⟩ := time 0 bound
    exact ⟨visit, later⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.OriginalSource
