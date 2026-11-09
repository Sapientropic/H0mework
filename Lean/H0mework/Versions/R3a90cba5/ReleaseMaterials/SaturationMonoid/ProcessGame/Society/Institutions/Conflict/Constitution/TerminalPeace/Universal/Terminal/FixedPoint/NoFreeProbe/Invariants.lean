import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

variable (tariff : Tariff Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (policy : CoalitionPolicy Party Good Port Technology Instrument)

theorem history_succ (n : Nat) :
    (history tariff replies opening policy (n + 1)).1 = (stepAt tariff replies opening policy n).next :=
  rfl

theorem history_keeps_original_accounts (n : Nat) :
    InPeace opening (history tariff replies opening policy n).1 := by
  induction n with
  | zero => exact ⟨rfl, .refl _⟩
  | succ n earlier =>
    rw [history_succ]
    exact ⟨(stepAt tariff replies opening policy n).rows.trans earlier.1,
      earlier.2.trans (stepAt tariff replies opening policy n).keepsPublicTerms⟩

/-- Count the physical clock from any reached cut of the same run. -/
theorem original_clock_lower_bound_from (start elapsed : Nat) :
    (history tariff replies opening policy start).1.physical.raw.clock + (elapsed : ℚ) * quantum ≤
      (history tariff replies opening policy (start + elapsed)).1.physical.raw.clock := by
  induction elapsed with
  | zero => simp
  | succ elapsed earlier =>
    have next := (stepAt tariff replies opening policy (start + elapsed)).clock
    rw [← history_succ] at next
    rw [Nat.cast_succ, ← Nat.add_assoc]
    linarith only [next, earlier]

theorem original_clock_lower_bound (n : Nat) :
    opening.physical.raw.clock + (n : ℚ) * quantum ≤
      (history tariff replies opening policy n).1.physical.raw.clock := by
  change (history tariff replies opening policy 0).1.physical.raw.clock + (n : ℚ) * quantum ≤ _
  simpa only [Nat.zero_add] using original_clock_lower_bound_from tariff replies opening policy 0 n

theorem original_clock_is_strictly_monotone :
    StrictMono (fun n => (history tariff replies opening policy n).1.physical.raw.clock) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [history_succ]
  exact (lt_add_of_pos_right _ opening.recipe.law.positive).trans_le
    (stepAt tariff replies opening policy n).clock

theorem original_clock_is_cofinal (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (history tariff replies opening policy n).1.physical.raw.clock := by
  have positive := opening.recipe.law.positive
  obtain ⟨n, beyond⟩ := exists_nat_gt ((bound - opening.physical.raw.clock) / quantum)
  have passed := (div_lt_iff₀ positive).mp beyond
  have clock := original_clock_lower_bound tariff replies opening policy n
  have crossed : bound < (history tariff replies opening policy n).1.physical.raw.clock := by
    linarith only [clock, passed]
  have later := (original_clock_is_strictly_monotone tariff replies opening policy).monotone
    (le_max_left n start)
  exact ⟨max n start, le_max_right _ _, crossed.trans_le later⟩

private theorem Step.paid_wire_stamp
    {tariff : Tariff Party Good Port Technology Instrument} {replies : Replies Party Good Port Technology Instrument}
    {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}
    (step : Step tariff replies current) {wire : Wire Party Good Port Technology Instrument}
    (used : step.paidWire = some wire) : wire.clock = current.physical.raw.clock := by
  cases step with
  | renewed => simp [Step.paidWire] at used
  | revised => simp [Step.paidWire] at used
  | reviewed submitted signed _ =>
    have same : submitted = wire := Option.some.inj used
    rw [← same]
    exact signed.fresh

/-- A paid submission's literal clock is spent even if a later
admission is run with different tariff or signature inputs. -/
theorem an_actual_paid_wire_cannot_be_replayed
    (futureTariff : Tariff Party Good Port Technology Instrument)
    (futureReplies : Replies Party Good Port Technology Instrument)
    {earlier later : Nat} {wire : Wire Party Good Port Technology Instrument}
    (used : (stepAt tariff replies opening policy earlier).paidWire = some wire)
    (after : earlier < later) :
    checked futureTariff futureReplies (history tariff replies opening policy later).1 wire = none := by
  have stamp := (stepAt tariff replies opening policy earlier).paid_wire_stamp used
  apply an_earlier_stamp_is_rejected
  rw [stamp]
  exact original_clock_is_strictly_monotone tariff replies opening policy after

private theorem Step.material_successor
    {tariff : Tariff Party Good Port Technology Instrument} {replies : Replies Party Good Port Technology Instrument}
    {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}
    (step : Step tariff replies current) : step.round.next.physical = step.next.physical := by
  cases step <;> rfl

/-- The paid assessment write leaves the material successor of its
actual productive round in place. Every due ordinal retains that round's
own needs, independent exit, and damage certificates. -/
theorem every_due_ordinal_pays_needs_and_keeps_exit_and_growth (n : Nat) :
    let before := (history tariff replies opening policy n).1.physical
    let after := (history tariff replies opening policy (n + 1)).1.physical
    let read := (stepAt tariff replies opening policy n).round.visit.read
    read.effect.isAccepted = true ∧ read.effect.next = after ∧
      OriginalNeedFloor read.programme origin before.raw people read.commands ∧
      OriginalNeedFloor read.programme before.raw before.raw people read.commands ∧
      (∀ person ∈ people, ∃ word, Supply.Registered read.programme before.raw word ∧
        Supply.Period read.programme origin before.raw [person] word) ∧
      (∀ item ∈ read.effect.execution.items, ∀ key, Reparation.loss read.programme.law community item key = 0) ∧
      (∃ person good, before.raw.stock person good < after.raw.stock person good) := by
  let step := stepAt tariff replies opening policy n
  have successor : step.round.next.physical = (history tariff replies opening policy (n + 1)).1.physical := by
    rw [history_succ]
    exact step.material_successor
  refine ⟨step.round.realWrite, step.round.physicalNext.trans successor,
    step.round.needs.1, step.round.needs.2, step.round.exit, step.round.noDamage, ?_⟩
  rw [← successor]
  exact step.round.growth

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe
