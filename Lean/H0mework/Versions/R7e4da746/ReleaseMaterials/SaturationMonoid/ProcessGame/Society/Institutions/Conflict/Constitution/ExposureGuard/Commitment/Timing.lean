import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt remainingNative)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "M" => State Party Technology
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)
  (word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)
  (rival : Scheduler Party Good Port (State Party Technology) Instrument) (person : Party)

/-- Visits and elapsed material time have separate exact completion
bounds. Both are independent of the rival's proposed interleaving. -/
theorem the_literal_commitment_attains_its_exact_original_completion_clock
    (approved : Certified prior answers word) (deadline : ℚ) :
    (∃ tick,
      let reached := visitAt prior answers word rival person approved tick
      reached.history = prior.history ++ word ∧ (endAt seed reached.history).raw.clock ≤ deadline) ↔
        (endAt seed (prior.history ++ word)).raw.clock ≤ deadline := by
  constructor
  · rintro ⟨_, completed, onTime⟩
    rwa [completed] at onTime
  · intro onTime
    have completed := (a_commitment_completes_at_exactly_its_literal_dispatch_count
      prior answers word rival person approved word.length).mpr le_rfl
    refine ⟨word.length, completed, ?_⟩
    rwa [completed]

variable (body : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

theorem initial_native_rank_and_body_length_give_the_sharp_bound
    (approved : Certified prior answers (afterBacklog (endAt seed prior.history) body))
    (tick : Nat) :
    let cut := endAt seed prior.history
    let literal := afterBacklog cut body
    let reached := visitAt prior answers literal rival person approved tick
    reached.history = prior.history ++ literal ↔ remainingNative cut + body.length ≤ tick := by
  dsimp only
  rw [a_commitment_completes_at_exactly_its_literal_dispatch_count, original_backlog_gives_the_exact_dispatch_count]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
