import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualCut

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program Abolition.Accounting.Quantifiers Abolition.Accounting.Quantifiers.Joint
open Abolition.Accounting.Quantifiers.Joint.Consumers.Compact
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material

noncomputable section

local macro "original_source_snapshot" : tactic => `(tactic|
  simp only [Planning.primitiveItems,Planning.primitiveAnalysis,Planning.grossCredits,
    Planning.primitiveAfter,Planning.primitiveReadings,Planning.initialWork,
    Planning.Menu.plantPlan,Planning.Menu.materialPlan,Planning.Menu.productionPrefix,
    Planning.Menu.fundedNeeds,Planning.Menu.fundNeedsFrom,Planning.Menu.needsWord,Planning.Menu.needCells,
    Planning.Menu.bills,Planning.Menu.grossFrom,Planning.Menu.productiveFrom,Planning.Menu.dose,
    Planning.Menu.relevantGoods,Planning.Menu.required,Planning.Menu.recipeNet,Planning.Menu.command,Planning.Menu.settlements,
    Allocation.Kernel.after,Allocation.Kernel.net,Allocation.Kernel.productiveCredit,Allocation.Kernel.gross,
    Allocation.Kernel.reservation,Allocation.Kernel.incoming,Allocation.Kernel.grossCharged,Allocation.room,Allocation.first,
    the_live_interpreter_is_the_same_public_physical_law,shared_raw_readout,shared_productive_scope,shared_gross_scope,
    shared_productive_remaining,shared_gross_remaining,shared_productive_declared,shared_gross_declared,
    live_roster,original_financial_tail,the_productive_gap_is_the_same_sources_real_eighteen.2,
    the_original_productive_row_is_still_active,false_and,if_false,List.foldl_cons,List.foldl_nil])

def settledCut : RawCurrent Bool Bool Unit Unit where
  stock := fun person good => if good then if person then 2 else 0 else if person then 109 else 117
  claims := fun _ _ _ => 0
  technology := ()
  clock := 4
  round := 4

theorem base_raw_is_the_real_settled_cut : base.raw = settledCut := by
  rw [base_raw_is_the_original_default_execution]
  unfold defaultWord
  original_source_snapshot
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
