import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Profile
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Assignment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement

open scoped BigOperators
open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}
  {script : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ids : Finset TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source script)}
  {allocation : Service.Need ids task → Service.Supply source script ids task → ℚ}

local notation "Net" => Service.network source script ids task reserved
local notation "View" => profile source script ids task reserved allocation

/-- Exactly the same accepted debit which determines capacity accounts for
all assigned fragments at this bearer and physical unit. -/
theorem allocation_is_conservative_at_every_original_timed_debit
    (admitted : (Net).Admissible allocation) : (View).Conservative where
  nonnegative := fun line item => (admitted.1 line (item, originalUnit line)).1
  perRow := fun line => (the_original_ordinals_sum_to_the_full_due_allocation admitted line).trans_le
    (admitted.2.1 line)
  perDebit := by
    intro ordinal key
    let item := (Execution.timedAt source script ordinal).1
    let law := source.native.handlerFace.rootRead
    have originalDebit : (View).debit ordinal key = flowAt (law.actualDebit item.before item.request) key.1 key.2 := rfl
    have nonnegative : 0 ≤ (View).debit ordinal key := by
      rw [originalDebit]
      unfold RawLaw.actualDebit
      split
      · rename_i accepted
        exact amount_nonnegative _ accepted.2.2.2.1 _
      · rfl
    by_cases hasGood : key.2 ∈ Service.goods ids task
    · by_cases ownsUse : ∃ bundle : Bundle Good, ∃ purpose : Use,
          item.request.operation = .use key.1 bundle purpose
      · obtain ⟨bundle, purpose, operation⟩ := ownsUse
        let supply : Service.Supply source script ids task := (ordinal, ⟨key.2, hasGood⟩)
        have limited : (Net).capacity supply ≤ (View).debit ordinal key := by
          change (if ordinal ∈ reserved then 0 else Service.paidAmount law item key.2) ≤ _
          by_cases held : ordinal ∈ reserved
          · simpa only [if_pos held] using nonnegative
          · simp only [if_neg held, Service.paidAmount, operation, originalDebit, le_refl]
        apply le_trans _ ((admitted.2.2 supply).trans limited)
        apply Finset.sum_le_sum
        intro line _
        by_cases owns : (View).address line = key
        · rw [if_pos owns]
          have same : originalUnit line = supply.2 := Subtype.ext (congrArg Prod.snd owns)
          change allocation line (ordinal, originalUnit line) ≤ _
          rw [same]
        · exact if_neg owns ▸ (admitted.1 line supply).1
      · have zero : (∑ line, if (View).address line = key then (View).paid line ordinal else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro line _
          by_cases owns : (View).address line = key
          · rw [if_pos owns]
            rcases eq_or_lt_of_le (admitted.1 line (ordinal, originalUnit line)).1 with empty | positive
            · exact empty.symm
            · exfalso
              apply ownsUse
              have used := (a_positive_original_allocation_has_its_original_use admitted line
                (ordinal, originalUnit line) positive).2.2.2.2.2
              change Service.useFor item line.1.spec at used
              cases operation : item.request.operation <;> simp only [Service.useFor, operation] at used
              case use bearer bundle purpose =>
                have person : line.1.spec.bearer = key.1 := congrArg Prod.fst owns
                exact ⟨bundle, purpose, by rw [used.1.trans person]⟩
          · exact if_neg owns
        exact zero.le.trans nonnegative
    · have zero : (∑ line, if (View).address line = key then (View).paid line ordinal else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro line _
        have distinct : (View).address line ≠ key := fun owns =>
          hasGood (congrArg Prod.snd owns ▸ (originalUnit line).property)
        exact if_neg distinct
      exact zero.le.trans nonnegative

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement
