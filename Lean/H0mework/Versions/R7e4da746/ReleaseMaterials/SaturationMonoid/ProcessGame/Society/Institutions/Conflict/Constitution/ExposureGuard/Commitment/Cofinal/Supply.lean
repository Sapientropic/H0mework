import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal.Classification
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Clock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_append)

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {Observation : Type u}
  {seed : Root.Cut Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}

local notation "M" => PublicFunction.Mandate.State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Rival" => RivalPolicy Party Good Port M Instrument

variable (policy : ObservationPolicy Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument Observation)
  (answers : OwnerAnswers seed)
  (interleaving : Option (RivalPolicy Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument))
  (opening : PaidVisit seed community anchor)

local notation "visit" => runAgainst policy answers interleaving opening
local notation "atClock" => clock policy answers interleaving opening

/-- This is a readout of the history already written by the actual
run, including whichever original rival input passed the guard. -/
def actualBatch (round : Nat) : Word :=
  (visit (round + 1)).history.drop (visit round).history.length

theorem the_actual_batch_is_the_exact_new_suffix (round : Nat) :
    (visit round).history ++ actualBatch policy answers interleaving opening round =
      (visit (round + 1)).history := by
  unfold actualBatch
  obtain ⟨tail, original⟩ := every_round_extends_the_exact_original_history policy answers interleaving opening round
  rw [← original, List.drop_left]

private theorem actual_batch_stage (round : Nat) :
    Quantities.Execution.stageAt (endAt seed opening.history)
      (fun index _ => actualBatch policy answers interleaving opening index) round =
        endAt seed (visit round).history := by
  induction round with
  | zero => rfl
  | succ round prior =>
    rw [Quantities.Execution.next_stage_is_the_literal_original_next, prior]
    change endAt (endAt seed (visit round).history)
      (actualBatch policy answers interleaving opening round) = _
    rw [← endAt_append, the_actual_batch_is_the_exact_new_suffix]

theorem a_source_clock_gain_forces_cofinal_paid_visits (quantum : ℚ) (positive : 0 < quantum)
    (paid : AllPaid policy answers interleaving opening)
    (gains : ∀ round, atClock round + quantum ≤ atClock (round + 1)) :
    CofinalRun policy answers interleaving opening := by
  let emitted := fun (round : Nat) (_ : C) => actualBatch policy answers interleaving opening round
  have covered := Quantities.Bounds.Cofinal.a_positive_paid_clock_quantum_crosses_every_physical_horizon
    (endAt seed opening.history) emitted quantum positive (fun round => by
      unfold Quantities.elapsed
      rw [← Quantities.Execution.next_stage_is_the_literal_original_next,
        actual_batch_stage, actual_batch_stage]
      exact le_sub_iff_add_le.mpr (by simpa only [clock, add_comm] using gains round))
  refine ⟨paid, fun horizon => ?_⟩
  obtain ⟨round, reached⟩ := covered (horizon + 1)
  refine ⟨round, (show horizon < horizon + 1 by linarith).trans_le ?_⟩
  unfold clock
  rw [← actual_batch_stage policy answers interleaving opening round]
  exact reached

omit interleaving opening in
/-- One local rule pays the nominated original word, replenishes its
reserve and gains actual time. The same rule is reused at each successor. -/
structure LocalSupply (reserve : C → Prop) (quantum : ℚ) : Prop where
  pays : ∀ prior : PaidVisit seed community anchor, reserve (endAt seed prior.history) →
    Certified prior answers (candidate policy prior)
  replenishes : ∀ prior : PaidVisit seed community anchor, reserve (endAt seed prior.history) →
    reserve (endAt seed (prior.history ++ candidate policy prior))
  gains : ∀ prior : PaidVisit seed community anchor, reserve (endAt seed prior.history) →
    (endAt seed prior.history).raw.clock + quantum ≤
      (endAt seed (prior.history ++ candidate policy prior)).raw.clock

theorem every_round_retains_the_local_supply (reserve : C → Prop) (quantum : ℚ)
    (law : LocalSupply (community := community) (anchor := anchor) policy answers reserve quantum)
    (initial : reserve (endAt seed opening.history))
    (kept : ∀ round (paid : PaidVisit seed community anchor), reserve (endAt seed paid.history) →
      reserve (endAt seed (rivalVisit answers interleaving round paid).history)) (round : Nat) :
    reserve (endAt seed (visit round).history) := by
  induction round with
  | zero => exact initial
  | succ round inherited =>
    let prior := visit round
    obtain ⟨_, verified⟩ := an_admissible_commitment_is_returned_as_certified prior answers
      (candidate policy prior) (law.pays prior inherited)
    rw [an_accepted_round_writes_its_exact_original_word policy answers interleaving opening round verified]
    exact kept round _ (law.replenishes prior inherited)

theorem cofinal_of_local_supply (reserve : C → Prop) (quantum : ℚ) (positive : 0 < quantum)
    (law : LocalSupply (community := community) (anchor := anchor) policy answers reserve quantum)
    (initial : reserve (endAt seed opening.history))
    (kept : ∀ round (paid : PaidVisit seed community anchor), reserve (endAt seed paid.history) →
      reserve (endAt seed (rivalVisit answers interleaving round paid).history)) :
    CofinalRun policy answers interleaving opening := by
  have supplied := every_round_retains_the_local_supply policy answers interleaving opening
    reserve quantum law initial kept
  apply a_source_clock_gain_forces_cofinal_paid_visits policy answers interleaving opening quantum positive
  · intro round
    exact an_admissible_commitment_is_returned_as_certified _ _ _ (law.pays _ (supplied round))
  · intro round
    let prior := visit round
    obtain ⟨certificate, verified⟩ := an_admissible_commitment_is_returned_as_certified prior answers
      (candidate policy prior) (law.pays prior (supplied round))
    have gain := law.gains prior (supplied round)
    have later := clock_monotone_under_original_extension (seed := seed)
      (rival_visit_extends_the_same_original_history answers interleaving round
        (advancePaid prior answers (candidate policy prior) certificate.down.due))
    unfold clock
    rw [an_accepted_round_writes_its_exact_original_word policy answers interleaving opening round verified]
    exact gain.trans later

def StockReserve (person : Party) (minimum : Good → ℚ) (cut : C) : Prop :=
  ∀ good, minimum good ≤ cut.raw.stock person good

omit policy opening in
theorem a_guarded_rival_preserves_the_named_stock_reserve (person : Party) (minimum : Good → ℚ)
    (exposed : person ∈ bearers seed community anchor)
    (targeted : ∀ rival, interleaving = some rival → rival.refuser = person)
    (round : Nat) (paid : PaidVisit seed community anchor)
    (enough : StockReserve person minimum (endAt seed paid.history)) :
    StockReserve person minimum (endAt seed (rivalVisit answers interleaving round paid).history) := by
  cases interleaving with
  | none => exact enough
  | some rival =>
    have same := targeted rival rfl
    subst person
    have preserved (visited : Nat) :
        StockReserve rival.refuser minimum (endAt seed (rivalRun answers rival round paid visited).history) := by
      induction visited with
      | zero => exact enough
      | succ visited previous =>
        rw [rival_run_reads_the_next_actual_adversary_input]
        let current := rivalRun answers rival round paid visited
        intro good
        exact (previous good).trans (current.a_rival_visit_cannot_reduce_the_stock_of_the_refusing_original_bearer
          answers grantRule (paidProbe seed anchor) (rival.choose round visited current.history)
          rival.refuser exposed good)
    exact preserved (rival.count round paid.history)

theorem cofinal_of_independent_stock_renewal (person : Party) (minimum : Good → ℚ)
    (exposed : person ∈ bearers seed community anchor)
    (targeted : ∀ rival, interleaving = some rival → rival.refuser = person)
    (quantum : ℚ) (positive : 0 < quantum)
    (law : LocalSupply (community := community) (anchor := anchor) policy answers (StockReserve person minimum) quantum)
    (initial : StockReserve person minimum (endAt seed opening.history)) :
    CofinalRun policy answers interleaving opening :=
  cofinal_of_local_supply policy answers interleaving opening _ quantum positive law initial
    (a_guarded_rival_preserves_the_named_stock_reserve answers interleaving person minimum exposed targeted)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal
