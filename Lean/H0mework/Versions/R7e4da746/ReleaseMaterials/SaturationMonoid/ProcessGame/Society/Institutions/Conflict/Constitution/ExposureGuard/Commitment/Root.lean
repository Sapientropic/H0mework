import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Actions
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Timing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Withdrawal
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal.Safety

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append inventory inventory_append)

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community] {Observation : Type u}

local notation "M" => State Party Technology
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

theorem every_reserved_visit_keeps_the_original_mandate_released
    (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed) (word : Word)
    (rival : Scheduler Party Good Port M Instrument) (person : Party) (approved : Certified prior answers word)
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed prior.history).raw) (tick : Nat) :
    Civil.Mandate.Released (endAt seed (visitAt prior answers word rival person approved tick).history).raw := by
  rw [visitAt_history, endAt_append]
  have members (item : ExecutionItem Party Good Port M Instrument)
      (listed : item ∈ inventory (endAt seed prior.history) (word.take tick)) :
      item ∈ inventory (endAt seed prior.history) word := by
    have full := List.mem_append_left (inventory (endAt (endAt seed prior.history) (word.take tick)) (word.drop tick)) listed
    rwa [← inventory_append, List.take_append_drop] at full
  exact an_actual_no_grant_word_keeps_the_original_mandate_released _ _ (installed.along prior.history)
    released (fun item listed => approved.admitted.original_authority item (members item listed))
    (fun item listed => approved.admitted.no_grants item (members item listed))

variable (policy : Cofinal.ObservationPolicy Party Good Port (State Party Technology) Instrument Observation)
  (answers : OwnerAnswers seed) (opening : PaidVisit seed community anchor)
  (interleaving : Option (Cofinal.RivalPolicy Party Good Port (State Party Technology) Instrument))

omit [DecidableEq Technology] in
/-- The recursive read of the original histories is exactly the writer
that consumes a priority phase and then the actual guarded rival visits. -/
theorem each_cofinal_round_is_the_same_reserved_original_dispatch
    (rival : Scheduler Party Good Port M Instrument) (person : Party) (round : Nat) :
    let prior := Cofinal.runAgainst policy answers interleaving opening round
    Cofinal.runAgainst policy answers interleaving opening (round + 1) =
      (execute prior answers rival person (Cofinal.candidate policy prior)).elim (fun _ => prior)
        (Cofinal.rivalVisit answers interleaving round) := by
  let prior := Cofinal.runAgainst policy answers interleaving opening round
  have same : Cofinal.step policy answers prior =
      execute prior answers rival person (Cofinal.candidate policy prior) := by
    unfold Cofinal.step
    cases checked : Cofinal.check policy answers prior with
    | inl issue =>
      unfold execute
      rw [show inspectPlan prior answers (Cofinal.candidate policy prior) = .inl issue from checked]
    | inr approved =>
      exact (execute_writes_the_certified_literal_word prior answers rival person _ approved.down).symm
  exact (Cofinal.runAgainst_succ policy answers interleaving opening round).trans
    (congrArg (fun choice => choice.elim (fun _ => prior) (Cofinal.rivalVisit answers interleaving round)) same)

omit interleaving in
/-- Fix the observed policy and its source renewal law before admitting
any adaptive coalition. Each accepted body takes priority and then gives
the same written visit to the guarded rival segment. -/
theorem paid_cofinal_peace_uses_the_original_priority_at_every_round
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed opening.history).raw)
    (person : Party) (exposed : person ∈ bearers seed community anchor)
    (minimum : Good → ℚ) (quantum : ℚ) (positive : 0 < quantum)
    (supply : Cofinal.LocalSupply (community := community) (anchor := anchor) policy answers
      (Cofinal.StockReserve person minimum) quantum)
    (initial : Cofinal.StockReserve person minimum (endAt seed opening.history))
    (count : Nat → Word → Nat) (choose : Nat → Nat → Word → Input) :
    let actual : Option (Cofinal.RivalPolicy Party Good Port M Instrument) := some ⟨person, count, choose⟩
    Cofinal.CofinalRun policy answers actual opening ∧
      ∀ round,
        let prior := Cofinal.runAgainst policy answers actual opening round
        Civil.Mandate.Released (endAt seed prior.history).raw ∧
          (∀ loss ∈ Reparation.Actual.originalLosses seed community prior.history,
            ∃ balance row, prior.state.read row = .inr (loss, balance)) ∧
          ∀ rival : Scheduler Party Good Port M Instrument,
            ∃ approved : Certified prior answers (Cofinal.candidate policy prior),
              let paid := advancePaid prior answers (Cofinal.candidate policy prior) approved.due
              execute prior answers rival person (Cofinal.candidate policy prior) = .inr paid ∧
                Cofinal.runAgainst policy answers actual opening (round + 1) =
                  Cofinal.rivalVisit answers actual round paid := by
  let actual : Option (Cofinal.RivalPolicy Party Good Port M Instrument) := some ⟨person, count, choose⟩
  obtain ⟨live, retained⟩ := Cofinal.an_independent_renewing_stock_forces_paid_cofinal_peace
    (policy := policy) (answers := answers) (opening := opening)
    installed released person exposed minimum quantum positive supply initial count choose
  refine ⟨live, fun round => ?_⟩
  let prior := Cofinal.runAgainst policy answers actual opening round
  obtain ⟨stillReleased, rows⟩ := retained round
  obtain ⟨approved, verified⟩ := live.1 round
  refine ⟨stillReleased, rows, fun rival => ⟨approved.down, ?_, ?_⟩⟩
  · exact execute_writes_the_certified_literal_word prior answers rival person _ approved.down
  · exact Cofinal.an_accepted_round_writes_its_exact_original_word policy answers actual opening round verified

omit policy interleaving [DecidableEq Technology] in
theorem no_cofinal_observation_policy_iff_each_has_an_actual_counterhistory (person : Party) :
    (¬ ∃ strategy : Cofinal.ObservationPolicy Party Good Port M Instrument Observation,
      ∀ (count : Nat → Word → Nat) (choose : Nat → Nat → Word → Input),
        Cofinal.CofinalRun strategy answers (some ⟨person, count, choose⟩) opening) ↔
      ∀ strategy : Cofinal.ObservationPolicy Party Good Port M Instrument Observation,
        ∃ (count : Nat → Word → Nat) (choose : Nat → Nat → Word → Input),
          let actual : Option (Cofinal.RivalPolicy Party Good Port M Instrument) := some ⟨person, count, choose⟩
          (∃ round, Cofinal.FirstFailure strategy answers actual opening round) ∨
            (Cofinal.AllPaid strategy answers actual opening ∧ Cofinal.ClockBounded strategy answers actual opening) := by
  classical
  simp only [not_exists, not_forall]
  constructor
  · intro loses strategy
    obtain ⟨count, choose, failed⟩ := loses strategy
    exact ⟨count, choose,
      (Cofinal.failure_or_bounded_iff_not_cofinal strategy answers (some ⟨person, count, choose⟩) opening).mp failed⟩
  · intro counter strategy
    obtain ⟨count, choose, failed⟩ := counter strategy
    exact ⟨count, choose,
      (Cofinal.failure_or_bounded_iff_not_cofinal strategy answers (some ⟨person, count, choose⟩) opening).mpr failed⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
