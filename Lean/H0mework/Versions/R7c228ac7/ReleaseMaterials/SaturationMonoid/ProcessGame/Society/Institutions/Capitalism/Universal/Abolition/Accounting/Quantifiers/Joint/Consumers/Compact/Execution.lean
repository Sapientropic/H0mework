import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Report

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact

open Source.Program

noncomputable section

theorem the_original_productive_row_is_still_active : ¬ Current.productivePaid seed grossClaim shared := by
  intro paid
  have original : (false,false) ∈ Responsibility.Family.positiveScope mechanism past nature response := by decide +kernel
  have zero := paid (false,false) original
  rw [shared_productive_remaining] at zero
  norm_num at zero

local macro "source_snapshot" : tactic => `(tactic|
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
    the_original_productive_row_is_still_active,false_and,if_false,
    List.foldl_cons,List.foldl_nil])

def defaultWord := Planning.Menu.plantPlan seed grossClaim shared true ()

theorem the_default_source_plan_has_all_primitive_resources : Planning.Resources seed grossClaim shared defaultWord := by
  constructor <;> unfold defaultWord <;> source_snapshot <;> decide +kernel

theorem the_default_plan_is_in_the_actual_source_menu : defaultWord ∈ Planning.Menu.plans seed grossClaim shared := by
  rw [Planning.Menu.plans,if_neg (fun paid => the_original_productive_row_is_still_active paid.1)]
  apply List.mem_flatMap.mpr
  refine ⟨true,?_,?_⟩
  · rw [Planning.Menu.operators,if_neg the_original_productive_row_is_still_active,
      the_productive_gap_is_the_same_sources_real_eighteen.2]
    exact List.mem_singleton_self _
  · apply List.mem_map.mpr
    refine ⟨(),?_,rfl⟩
    apply List.mem_dedup.mpr
    have unique : shared.raw.technology = () := Subsingleton.elim _ _
    rw [← unique]
    exact List.mem_cons_self

theorem the_source_generates_its_own_sufficient_plan : Planning.Enough seed grossClaim shared :=
  ⟨defaultWord,the_default_plan_is_in_the_actual_source_menu,the_default_source_plan_has_all_primitive_resources⟩

theorem the_selected_actual_action_clears_both_rows_and_original_needs :
    Planning.ActualSuccess seed grossClaim shared (Planning.selected seed grossClaim shared) :=
  Planning.sufficient_source_resources_force_the_actual_shared_payment seed grossClaim shared
    the_source_generates_its_own_sufficient_plan

def refund136 : RawEvent Bool Bool Bool Unit Unit :=
  [⟨false,[],false,[],.produce true⟩,⟨false,[],false,[],.produce true⟩,
   ⟨false,[],false,[],.transfer true false [(false,136)]⟩,
   ⟨false,[],false,[],.use false [(false,18)] .external⟩] ++
    Planning.Menu.needsWord seed grossClaim shared ++ Planning.Menu.settlements seed

theorem the_136_return_pays_both_rows_after_the_real_eighteen_cost :
    Planning.Resources seed grossClaim shared refund136 := by
  constructor <;> unfold refund136 <;> source_snapshot <;> decide +kernel

theorem the_real_cost_does_not_turn_sufficient_136_into_a_false_residual :
    Planning.ActualSuccess seed grossClaim shared refund136 :=
  Planning.primitive_resources_generate_one_actual_payment_of_both_original_obligations
    seed grossClaim shared refund136 the_136_return_pays_both_rows_after_the_real_eighteen_cost

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact
