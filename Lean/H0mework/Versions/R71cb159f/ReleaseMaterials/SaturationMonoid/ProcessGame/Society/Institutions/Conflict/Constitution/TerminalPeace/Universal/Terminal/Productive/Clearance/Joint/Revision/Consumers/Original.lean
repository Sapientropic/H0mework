import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Run
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Settlement

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt primitiveScript)
open Reparation.Actual
open Reparation.Actual.Allocation (Position originalItem)
open Joint.OriginalExchange
open private transferChannel from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Native
open private one_row base_balance_after_production from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Settlement

noncomputable section

private theorem dueAfterProduction (signs : Bool) :
    dueFor claim (prefixRows loss (personalReplies signs) beforeSale) = 6 := by
  rw [one_row (personalReplies signs) (first_production_is_safe signs)]
  simpa only [dueFor_is_the_keyed_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    if_pos (show loss.key = claim from rfl), add_zero] using base_balance_after_production signs

private theorem nativeFloor : reserveAt loss beforeSale true false = 0 := by
  unfold reserveAt atRaw
  rw [Conflict.Consumers.Evolving.sourceInput]
  decide +kernel

theorem the_original_clearing_reads_the_complete_six_from_new_inventory (signs : Bool) :
    maximumInstallment loss (personalReplies signs) beforeSale claim = 6 := by
  rw [maximumInstallment, dueAfterProduction, materialMargin, nativeFloor, first_production_raw]
  decide +kernel

private theorem beforeSalePays :
    CanInstallment loss replies (reserveAt loss beforeSale) beforeSale false claim
      (maximumInstallment loss replies beforeSale claim) := by
  rw [show maximumInstallment loss replies beforeSale claim = 6 from
    the_original_clearing_reads_the_complete_six_from_new_inventory true]
  refine ⟨by norm_num, le_of_eq (dueAfterProduction true).symm, ?_, ?_⟩
  · rw [nativeFloor, first_production_raw]
    decide +kernel
  · apply transferChannel beforeSale claim 6 first_production_ready (by norm_num)
      (by rw [first_production_raw]; decide +kernel) (by decide) rfl rfl
    intro who site exactItem
    unfold replies personalReplies
    rw [exactItem]
    cases who <;> decide +kernel

private theorem refusal_survives_the_actual_transfer :
    ¬ CanInstallment loss (personalReplies false) (reserveAt loss beforeSale) beforeSale false claim
      (maximumInstallment loss (personalReplies false) beforeSale claim) := by
  rw [the_original_clearing_reads_the_complete_six_from_new_inventory false]
  intro checked
  have enough : 6 ≤ (prefixRaw loss beforeSale).stock claim.2.1 claim.2.2 :=
    (le_add_of_nonneg_left (reserveAt_nonnegative _ _ _ _)).trans checked.stock
  have legal := delivery_has_original_authority checked.channel checked.positive enough
  have single := the_delivery_writes_one_original_item first_production_ready.1 first_production_ready.2 legal
  let site : Position Original.seed (Occurrence.history loss ++ beforeSale) (payment false claim 6) :=
    ⟨0, by rw [single]; decide⟩
  have literal : originalItem Original.seed (Occurrence.history loss ++ beforeSale) (payment false claim 6) site =
      ⟨0, prefixRaw loss beforeSale, paymentRequest false claim 6⟩ := by
    have found : originalItem Original.seed (Occurrence.history loss ++ beforeSale) (payment false claim 6) site ∈
        Boundary.Actual.items (endAt Original.seed (Occurrence.history loss ++ beforeSale)) (payment false claim 6) :=
      List.getElem_mem _
    rw [single] at found
    exact List.mem_singleton.mp found
  have refused : personalReplies false (Occurrence.history loss ++ beforeSale) (payment false claim 6) site claim.1 = false := by
    unfold personalReplies
    rw [literal]
    decide +kernel
  exact Bool.false_ne_true (refused.symm.trans (checked.channel.victim site))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve.OriginalConsumer
