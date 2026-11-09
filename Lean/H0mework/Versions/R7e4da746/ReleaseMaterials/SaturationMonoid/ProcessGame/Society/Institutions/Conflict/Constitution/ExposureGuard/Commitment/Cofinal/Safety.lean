import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal.Supply

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append inventory)

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Technology] [DecidableEq Community] {Observation : Type u}
  {seed : Root.Cut Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "M" => State Party Technology
local notation "Rival" => RivalPolicy Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument

variable (answers : OwnerAnswers seed)
  (interleaving : Option (RivalPolicy Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument))

theorem the_guarded_rival_visit_keeps_original_release
    (installed : Emergency.Installed seed base scope)
    (exposed : ∀ rival, interleaving = some rival → rival.refuser ∈ bearers seed community anchor)
    (round : Nat) (paid : PaidVisit seed community anchor)
    (released : Civil.Mandate.Released (endAt seed paid.history).raw) :
    Civil.Mandate.Released (endAt seed (rivalVisit answers interleaving round paid).history).raw := by
  cases interleaving with
  | none => exact released
  | some rival =>
    have kept (visited : Nat) :
        Civil.Mandate.Released (endAt seed (rivalRun answers rival round paid visited).history).raw := by
      induction visited with
      | zero => exact released
      | succ visited previous =>
        rw [rival_run_reads_the_next_actual_adversary_input]
        let current := rivalRun answers rival round paid visited
        let selected := current.verdict (withhold answers rival.refuser) grantRule (paidProbe seed anchor)
          (rival.choose round visited current.history)
        change Civil.Mandate.Released (endAt seed (current.history ++ selected.emitted)).raw
        rw [endAt_append]
        have noGrant (item : Item) (listed : item ∈ inventory (endAt seed current.history) selected.emitted) :
            ¬ Grants item.request := by
          intro granted
          obtain ⟨actual, _, position, _, signed⟩ := selected.a_written_grant_reads_each_original_bearer
            (List.mem_append_left _ (exposed rival rfl)) item listed granted
          rw [withholding_uses_the_original_personal_lane] at signed
          cases signed
        exact an_actual_no_grant_word_keeps_the_original_mandate_released _ _ (installed.along current.history)
          previous selected.the_original_selected_word_has_source_authority noGrant
    exact kept (rival.count round paid.history)

variable (policy : ObservationPolicy Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument Observation)
  (opening : PaidVisit seed community anchor)

theorem every_actual_round_keeps_the_original_mandate_released
    (installed : Emergency.Installed seed base scope)
    (exposed : ∀ rival, interleaving = some rival → rival.refuser ∈ bearers seed community anchor)
    (released : Civil.Mandate.Released (endAt seed opening.history).raw) (round : Nat) :
    Civil.Mandate.Released (endAt seed (runAgainst policy answers interleaving opening round).history).raw := by
  induction round with
  | zero => exact released
  | succ round priorReleased =>
    let prior := runAgainst policy answers interleaving opening round
    cases verdict : check policy answers prior with
    | inl issue =>
      rw [a_refused_round_keeps_its_exact_original_visit policy answers interleaving opening round ⟨issue, verdict⟩]
      exact priorReleased
    | inr accepted =>
      rw [an_accepted_round_writes_its_exact_original_word policy answers interleaving opening round verdict]
      apply the_guarded_rival_visit_keeps_original_release _ _ installed exposed
      change Civil.Mandate.Released (endAt seed (prior.history ++ candidate policy prior)).raw
      rw [endAt_append]
      exact an_actual_no_grant_word_keeps_the_original_mandate_released _ _ (installed.along prior.history)
        priorReleased accepted.down.admitted.original_authority accepted.down.admitted.no_grants

omit interleaving in
theorem an_independent_renewing_stock_forces_paid_cofinal_peace
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed opening.history).raw)
    (person : Party) (exposed : person ∈ bearers seed community anchor)
    (minimum : Good → ℚ) (quantum : ℚ) (positive : 0 < quantum)
    (law : LocalSupply (community := community) (anchor := anchor) policy answers (StockReserve person minimum) quantum)
    (initial : StockReserve person minimum (endAt seed opening.history)) :
    ∀ (count : Nat → Reparation.Actual.Script Party Good Port M Instrument → Nat)
      (choose : Nat → Nat → Reparation.Actual.Script Party Good Port M Instrument →
        Reparation.Actual.Input Party Good Port M Instrument),
      let adversary : Option Rival := some ⟨person, count, choose⟩
      CofinalRun policy answers adversary opening ∧
        ∀ round, let reached := runAgainst policy answers adversary opening round
          Civil.Mandate.Released (endAt seed reached.history).raw ∧
            ∀ loss ∈ Reparation.Actual.originalLosses seed community reached.history,
              ∃ balance row, reached.state.read row = .inr (loss, balance) := by
  intro count choose
  let rival : Rival := ⟨person, count, choose⟩
  have original (other : Rival) (same : some rival = some other) : other.refuser = person := by
    rw [← Option.some.inj same]
  refine ⟨cofinal_of_independent_stock_renewal policy answers (some rival) opening person minimum
    exposed original quantum positive law initial, fun round => ?_⟩
  let reached := runAgainst policy answers (some rival) opening round
  exact ⟨every_actual_round_keeps_the_original_mandate_released answers (some rival) policy opening
    installed (fun other same => (original other same).symm ▸ exposed) released round,
    reached.every_original_loss_has_an_exact_live_row⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal
