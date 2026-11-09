import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Effect
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Accumulation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Exit.AutonomousProduction (executed_items_retime retimed)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin current : RawCurrent Party Good Technology Instrument}
  {roster : List Party} {word : RawEvent Party Good Port Technology Instrument}
  (paid : Period input origin current roster word)
  (timing : input.law.TimeIndependent) (reserveLaw : input.law.ReserveInsensitive)

include paid timing reserveLaw

private theorem own_after_paid_reserve_and_clock
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (clock : ℚ) (round : Nat) :
    ∀ item ∈ input.law.rawItems ((current.addReserve reserve).retime clock round) word,
      OwnItem input.law roster item := by
  have expanded := executed_items_addReserve input reserveLaw current reserve nonnegative 0 word
    (fun item original => (paid.own item original).valid)
  have later := executed_items_retime input.law timing (current.addReserve reserve) clock round 0 word
  intro item present
  unfold RawLaw.rawItems at present
  rw [later, expanded] at present
  obtain ⟨enlarged, enlargedPresent, rfl⟩ := List.mem_map.mp present
  obtain ⟨original, originalPresent, rfl⟩ := List.mem_map.mp enlargedPresent
  have owned := paid.own original originalPresent
  exact ⟨owned.operation, owned.member, owned.noConsent,
    (input.law.valid_retime timing _ clock round _).mpr
      (input.law.valid_addReserve reserveLaw _ reserve nonnegative _ owned.valid)⟩

private theorem current_needs_after_paid_reserve_and_clock
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (clock : ℚ) (round : Nat) :
    let before := (current.addReserve reserve).retime clock round
    OriginalNeedFloor input before before roster word := by
  dsimp only
  simpa only [OriginalNeedFloor, originalRequirements, timing.necessities, timing.maintenance,
    reserveLaw.necessities, reserveLaw.maintenance, actualUse_retime input timing,
    actualUse_addReserve input reserveLaw current reserve nonnegative word (fun item original => (paid.own item original).valid)]
    using paid.currentFloor

/-- The available surplus is a readout of the original paid material
legs. Local law covariance transports those legs and each original need. -/
theorem Period.replay
    (accumulating : Balance.FiniteChecks .accumulating input.law current word)
    (quantum : ℚ) (positive : 0 < quantum)
    (sourceClock : ∀ (reserve : Party → Good → ℚ), (∀ person good, 0 ≤ reserve person good) →
      ∀ clock round, quantum ≤ input.law.duration ((current.addReserve reserve).retime clock round))
    (n : Nat) :
    let reached := (repeatPeriod input current word).currentAt n
    Period input origin reached roster word ∧
      (∀ person good, reached.stock person good =
        current.stock person good + (n : ℚ) * Balance.gain input.law current word person good) ∧
      reached.claims = current.claims ∧ reached.technology = current.technology ∧
      quantum ≤ input.law.duration reached ∧
      Balance.FiniteChecks .accumulating input.law reached word := by
  let gain := Balance.gain input.law current word
  let reached := (repeatPeriod input current word).currentAt n
  have actual := Balance.checked_productive_period input.law current word accumulating
  have accepted := fun item original => (paid.own item original).valid
  have resource := productive_period_exact_resources input timing reserveLaw current word gain actual.2 actual.1 accepted
  obtain ⟨clock, round, exactState⟩ := generated_current_has_only_paid_accumulation input timing reserveLaw
    current word gain actual.2 actual.1 accepted n
  let reserve := accumulatedReserve gain n
  have nonnegative := accumulatedReserve_nonnegative gain actual.2 n
  have owns : ∀ item ∈ input.law.rawItems reached word, OwnItem input.law roster item := by
    change ∀ item ∈ input.law.rawItems ((repeatPeriod input current word).currentAt n) word, _
    rw [exactState]
    exact own_after_paid_reserve_and_clock paid timing reserveLaw reserve nonnegative clock round
  have lives : OriginalNeedFloor input reached reached roster word := by
    unfold reached
    rw [exactState]
    exact current_needs_after_paid_reserve_and_clock paid timing reserveLaw reserve nonnegative clock round
  have regenerated : Balance.FiniteChecks .accumulating input.law reached word := by
    refine ⟨accumulating.1, ?_⟩
    intro cell _
    change input.law.totalDebit (input.law.rawItems reached word) cell.1 cell.2 ≤
      input.law.totalCredit (input.law.rawItems reached word) cell.1 cell.2
    have conserved := input.law.actual_next_material_balance reached word cell.1 cell.2
    have renewed : reached.stock cell.1 cell.2 ≤ (input.law.next reached word).stock cell.1 cell.2 := by
      change ((repeatPeriod input current word).currentAt n).stock cell.1 cell.2 ≤
        ((repeatPeriod input current word).currentAt (n + 1)).stock cell.1 cell.2
      rw [(resource n).1, (resource (n + 1)).1, Nat.cast_succ]
      linarith only [actual.2 cell.1 cell.2]
    linarith only [conserved, renewed]
  have advances : quantum ≤ input.law.duration reached := by
    unfold reached
    rw [exactState]
    exact sourceClock reserve nonnegative clock round
  exact ⟨⟨owns, productive_period_keeps_original_need_floor input timing reserveLaw current word gain actual.2
    origin roster actual.1 accepted paid.originalFloor n, lives, positive.trans_le advances⟩,
    (resource n).1, (resource n).2.1, (resource n).2.2, advances, regenerated⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply
