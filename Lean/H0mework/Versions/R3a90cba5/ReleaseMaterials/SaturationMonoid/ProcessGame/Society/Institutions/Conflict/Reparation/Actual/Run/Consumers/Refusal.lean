import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.ActualDamage

set_option autoImplicit false
set_option maxRecDepth 8192

open private physically_executed from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.ActualDamage

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Consumers

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (sourceInput sourceRead)
open Conflict.Reparation.Consumers (actualOrigin withoutLivingPayment levyPast levyInput
  the_actual_assault_leaves_its_living_payment_unfulfilled
  the_rejected_assault_files_its_six_on_the_actual_material_successor)
open Quantities.Execution (primitiveScript)

noncomputable section

abbrev refusedWord := primitiveScript withoutLivingPayment

theorem the_original_approved_material_word_is_refused_at_settlement :
    ∃ checked issue, approval actualOrigin refusedWord = .settlementRefused checked issue := by
  have authority : Conflict.Root.Authorized actualOrigin withoutLivingPayment := by
    unfold Conflict.Root.Authorized
    rw [sourceInput, sourceRead]
    decide +kernel
  have material : SourceAuthority actualOrigin refusedWord := by
    intro item listed
    rw [Quantities.Execution.primitive_inventory physically_executed 0] at listed
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp listed
    exact authority original present
  unfold approval
  split
  · rename_i item original unlicensed _
    exact (unlicensed (material item original)).elim
  · rename_i checked _
    split
    · rename_i issue _
      exact ⟨checked, issue, rfl⟩
    · rename_i settled _
      exact (the_actual_assault_leaves_its_living_payment_unfulfilled settled).elim

def TheRefusedAssaultKeepsItsOriginalVictim : Prop :=
  let written := publish actualOrigin id refusedWord
  (∃ checked issue, written.result = .settlementRefused checked issue) ∧
  ∃ damage : Boundary.Actual.DamageAt (Quantities.Execution.endAt actualOrigin levyPast) levyInput id,
    damage.quantity = 6 ∧ ∃ balance, ∃ row,
      written.next.read row = .inr (⟨levyPast, levyInput, damage⟩, balance)

theorem the_refused_assault_keeps_its_original_victim : TheRefusedAssaultKeepsItsOriginalVictim := by
  obtain ⟨_, damage, amount, _⟩ := the_rejected_assault_files_its_six_on_the_actual_material_successor
  let origin : Occurrence actualOrigin id := ⟨levyPast, levyInput, damage⟩
  have listed : origin ∈ originalLosses actualOrigin id refusedWord := by
    change origin ∈ originalLosses actualOrigin id ((levyPast ++ [levyInput]) ++ [none])
    rw [losses_snoc, losses_snoc]
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨damage, Boundary.Actual.every_actual_debit_is_assessed _, rfl⟩))
  rw [← the_live_ledger_contains_exactly_the_original_losses] at listed
  obtain ⟨⟨same, balance⟩, entry, exactOrigin⟩ := List.mem_map.mp listed
  change same = origin at exactOrigin
  subst same
  refine ⟨the_original_approved_material_word_is_refused_at_settlement, damage, amount, balance, ?_⟩
  exact (run actualOrigin id refusedWord).every_balance_is_a_row_of_the_current _ entry

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Consumers
