import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialReentry
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open NativeMaterialPotentialSource
abbrev active := LiveJointRepaymentControls.active
abbrev start := LiveJointRepaymentSource.start LiveJointRepaymentControls.old LiveJointRepaymentControls.saved
abbrev stages := LiveJointRepaymentControls.stages
abbrev final := LiveJointRepaymentControls.final
abbrev production := LiveJointRepaymentControls.production
abbrev deliveryRow := LiveJointRepaymentControls.deliveryRow
theorem actualLaw : active.law = law := AtomicWorkControls.materialLaw
theorem actualStocks : ∀ party good, 0 ≤ (EventStep.seed start).current.stock party good := by
  intro party good
  fin_cases party <;> cases good <;> decide +kernel

abbrev actualAccount := NativeMaterialPotentialConsumer.arbitrary_actual_continuations_have_one_telescoping_material_account
  active actualLaw start stages
abbrev actualBudget := NativeMaterialPotentialConsumer.original_stocks_generate_a_uniform_paid_stage_budget
  active actualLaw start stages actualStocks
theorem actual_reproduction_and_repayment_conserve_material_but_delivery_pays_it :
    NativeMaterialPotentialConsumer.cost active production = 0 ∧
      potential production.after.current = potential production.before.current ∧
      NativeMaterialPotentialConsumer.cost active deliveryRow = 2 ∧
      NativeMaterialPotentialConsumer.bill active start stages = 2 ∧
      NativeMaterialPotentialConsumer.charged active (StageTrace.records start stages) = 1 ∧
      potential (EventStep.seed final).current = potential (EventStep.seed start).current - 2 ∧
      (EventStep.seed final).current.claims () 1 2 < (EventStep.seed start).current.claims () 1 2 ∧
      LiveJointRepaymentControls.received.receipts = [AtomicWorkControls.receipt] := by
  and_intros <;> decide +kernel

def charge : RecycledQuorumMaterial.Action := ⟨1,[],.reserve 1,[],.use 1 [(.service,1)] .external⟩
def negative : RecycledQuorumMaterial.Action := ⟨1,[],.reserve 1,[],.use 1 [(.service,-1)] .external⟩
abbrev terminal := (EventStep.seed final).current
abbrev oversized := List.replicate (NativeMaterialPotentialConsumer.capacity active final + 1) charge
theorem source_shortage_and_invalid_input_cannot_mint_the_missing_budget :
    0 < shortfall terminal oversized ∧
      quote negative = -2 ∧ ¬ law.Valid terminal negative ∧
      draw terminal negative = 0 ∧ law.step terminal negative = terminal ∧
      spent (law.rawItems terminal oversized) = 0 ∧
      potential (law.next terminal oversized) = potential terminal := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_,by decide +kernel,by decide +kernel⟩
  exact if_neg (by decide +kernel)

abbrev finalStocks := NativeMaterialPotentialConsumer.arbitrary_continuations_preserve_nonnegative_stock
  active actualLaw start stages actualStocks
abbrev actualShortage := the_generated_shortfall_requires_actual_new_material terminal oversized finalStocks
  source_shortage_and_invalid_input_cannot_mint_the_missing_budget.1
def reentry : LiveRepaymentSource.Snapshot := ⟨active,final⟩
theorem original : reentry.cursor.side = .original := rfl
abbrev everyAdaptiveCrossCodeBudget (control : LiveRepaymentSource.Controller) (count : Nat) :=
  NativeMaterialPotentialReentry.no_control_or_code_expansion_refills_the_actual_stock_budget
    reentry control actualLaw original finalStocks count
abbrev everyAdaptiveCrossCodeAccount (control : LiveRepaymentSource.Controller) (count : Nat) :=
  NativeMaterialPotentialReentry.arbitrary_cross_code_controls_share_one_original_material_account
    reentry control actualLaw original count
abbrev native := StageRuntime.the_final_root_consumes_actual_budget_native_responsibility_ledger_and_next
  LiveJointRepaymentControls.bound start stages AtomicWorkControls.vocabulary
abbrev actualLedger := LiveJointRepaymentControls.actualLedger
abbrev actualDelivery := LiveJointRepaymentControls.actualDelivery
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialControls
