import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Runtime
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.OriginalConsumer

open Capitalism.Universal.Source.Program
open Reparation.Actual (Occurrence)
open Clearance Joint Joint.OriginalExchange Joint.SourceReserve
open private accepted_recipe_has_no_failure sign starts from H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Consumers.Original

noncomputable section

private abbrev tail : Original.Word := installment false claim 6
private abbrev candidate := firstProduction loss [grow] ++ tail

private theorem exact_original_word : candidate = paidPrefix := by
  unfold candidate firstProduction
  rw [original_drain_exact]
  rfl

private def inspected :=
  verifyPrepared loss replies [grow] quiet (menu true) addresses covers tail (picked true) (codeAt true candidate)

private theorem the_original_preflight_accepts :
    ∃ certified, inspected = .ok certified := by
  obtain ⟨opening, _, same, _⟩ := the_original_six_are_paid_before_the_actual_peace_round
  have word : opening.word = candidate := same.trans exact_original_word.symm
  have ready : ReadyEntry loss candidate := word ▸ opening.entry.ready
  have safe : Occurrence.Eligible replies loss candidate := word ▸ opening.entry.eligible
  have debt : WholeCleared loss replies candidate := word ▸ opening.entry.paid
  have inventory : ProtectsNeeds loss candidate :=
    exact_original_word.symm ▸ all_paid_positions_keep_needs _ List.prefix_rfl
  obtain ⟨_, wrote⟩ := first_production_is_written true
  have first : ProductionWrite replies loss (openingDrain loss) [grow] :=
    original_drain_exact.symm ▸ (inspectProduction_passes_iff _ _ _ _).mp ⟨_, wrote⟩
  cases checked : inspected with
  | ok result => exact ⟨result, rfl⟩
  | error issue =>
    exfalso
    cases issue with
    | empty missing => cases missing
    | unproductive missing => exact missing credit_first
    | authority _ refused => exact refused first
    | native _ refused => exact refused first
    | firstInput failed => exact (failed.refutes replies start) first.eligible
    | input failed => exact (failed.refutes replies start) safe
    | stock failed => exact failed.refutes loss inventory
    | work pending => exact pending ready.1
    | review closed => exact closed ready.2
    | debt _ _ actual unpaid => exact unpaid (debt _ actual)
    | unapproved refused => exact refused (sign candidate)
    | pilot wrong => exact wrong (starts candidate)
    | recipe issue => exact accepted_recipe_has_no_failure candidate exact_original_word ready issue

theorem the_verified_original_word_writes_the_same_cleared_ledger :
    ∃ certified, inspected = .ok certified ∧ certified.opening.word = paidPrefix ∧
      Occurrence.Unbounded.ActualWrite replies loss paidPrefix ∧
      (∀ row ∈ certified.opening.entry.current.ledger.stack.balances, row.2.remaining = 0) := by
  obtain ⟨certified, chosen⟩ := the_original_preflight_accepts
  refine ⟨certified, chosen, certified.usesOriginalWord.trans exact_original_word, ?_, certified.opening.fixed.oldPaid⟩
  exact exact_original_word ▸ (certified.the_word_has_the_original_whole_write loss replies [grow] quiet (menu true) tail).1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.OriginalConsumer
