import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Accounting

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem total_debit_nonnegative (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (person : Party) (good : Good) :
    0 ≤ law.totalDebit items person good := by
  unfold RawLaw.totalDebit
  apply List.sum_nonneg
  intro debit listed
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp listed
  unfold RawLaw.actualDebit
  split
  · rename_i valid
    exact amount_nonnegative _ valid.2.2.2.1 _
  · simp [flowAt, amount]

def repairCredit (origin : C) (exposure repair : Script) (person : Party) (good : Good) : ℚ :=
  let damaged := Execution.endAt origin exposure
  damaged.native.handlerFace.rootRead.totalCredit (Execution.inventory damaged repair) person good

def shortage (origin : C) (exposure repair : Script) (person : Party) (good : Good) : ℚ :=
  origin.raw.stock person good - (Execution.endAt origin (exposure ++ repair)).raw.stock person good

theorem shortage_is_the_original_loss_plus_actual_repair_debits_less_credits
    (origin : C) (exposure repair : Script) (person : Party) (good : Good) :
    let damaged := Execution.endAt origin exposure
    shortage origin exposure repair person good =
      origin.raw.stock person good - damaged.raw.stock person good +
        damaged.native.handlerFace.rootRead.totalDebit (Execution.inventory damaged repair) person good -
        repairCredit origin exposure repair person good := by
  intro damaged
  have balance := (record damaged repair).actualBalance person good
  unfold shortage repairCredit
  rw [Execution.endAt_append]
  change origin.raw.stock person good - (Execution.endAt damaged repair).raw.stock person good = _
  linarith only [balance]

theorem a_repair_credit_ceiling_gives_the_original_shortage_floor
    (origin : C) (exposure repair : Script) (person : Party) (good : Good) (ceiling : ℚ)
    (bounded : repairCredit origin exposure repair person good ≤ ceiling) :
    origin.raw.stock person good - (Execution.endAt origin exposure).raw.stock person good - ceiling ≤
      shortage origin exposure repair person good := by
  let damaged := Execution.endAt origin exposure
  have debit := total_debit_nonnegative damaged.native.handlerFace.rootRead
    (Execution.inventory damaged repair) person good
  have balance := shortage_is_the_original_loss_plus_actual_repair_debits_less_credits
    origin exposure repair person good
  change origin.raw.stock person good - damaged.raw.stock person good - ceiling ≤ _
  linarith only [debit, bounded, balance]

theorem a_positive_shortage_preserves_the_original_named_residual
    (origin : C) (exposure repair : Script) (person : Party) (good : Good)
    (unpaid : 0 < shortage origin exposure repair person good) :
    ∃ loss : Loss origin exposure repair, loss.address = (person, good) ∧
      Recorded origin (exposure ++ repair) := by
  have remaining : (Execution.endAt origin (exposure ++ repair)).raw.stock person good <
      origin.raw.stock person good := sub_pos.mp unpaid
  have original : (person, good) ∈ Execution.materialAddresses origin (exposure ++ repair) := by
    by_contra absent
    have unaffected := Execution.stock_outside_original_effects_is_unchanged origin
      (exposure ++ repair) person good absent
    rw [unaffected] at remaining
    exact (lt_irrefl _) remaining
  exact ⟨⟨(person, good), original, remaining⟩, rfl, record origin _⟩

/-- If the original actual repair credits cannot cover the physical
loss, the same bearer's named residual remains on the complete root. -/
theorem original_repair_credit_below_gap_keeps_its_named_loss
    (origin : C) (exposure repair : Script) (person : Party) (good : Good)
    (short : (Execution.endAt origin exposure).raw.stock person good +
      repairCredit origin exposure repair person good < origin.raw.stock person good) :
    ∃ loss : Loss origin exposure repair, loss.address = (person, good) ∧
      Recorded origin (exposure ++ repair) := by
  apply a_positive_shortage_preserves_the_original_named_residual
  have floor := a_repair_credit_ceiling_gives_the_original_shortage_floor
    origin exposure repair person good (repairCredit origin exposure repair person good) le_rfl
  linarith only [floor, short]

/-- A source-verified uniform credit ceiling rules out repair across all
settled original continuations. The alternatives keep their actual
accounting or the same person's original physical shortfall. -/
theorem every_original_continuation_retains_an_unrepairable_loss_under_the_source_credit_ceiling
    (origin : C) (exposure : Script) (person : Party) (good : Good) (ceiling : ℚ)
    (uniform : ∀ repair, Settled (Execution.endAt origin exposure) repair →
      repairCredit origin exposure repair person good ≤ ceiling)
    (short : (Execution.endAt origin exposure).raw.stock person good + ceiling < origin.raw.stock person good) :
    ∀ repair, Recorded origin (exposure ++ repair) ∧
      (Nonempty (Obstruction (Execution.endAt origin exposure) repair) ∨
        ∃ loss : Loss origin exposure repair, loss.address = (person, good) ∧
          origin.raw.stock person good - (Execution.endAt origin exposure).raw.stock person good - ceiling ≤
            shortage origin exposure repair person good) := by
  intro repair
  refine ⟨record origin _, ?_⟩
  cases decideAt (Execution.endAt origin exposure) repair with
  | blocked issue => exact Or.inl ⟨issue⟩
  | feasible paid =>
    have bounded : repairCredit origin exposure repair person good ≤ ceiling :=
      uniform repair (settle _ _ paid)
    have uncovered : (Execution.endAt origin exposure).raw.stock person good +
        repairCredit origin exposure repair person good < origin.raw.stock person good := by
      linarith only [bounded, short]
    obtain ⟨loss, same, _⟩ :=
      original_repair_credit_below_gap_keeps_its_named_loss origin exposure repair person good uncovered
    exact Or.inr ⟨loss, same, a_repair_credit_ceiling_gives_the_original_shortage_floor
      origin exposure repair person good ceiling bounded⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
