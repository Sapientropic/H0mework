import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed.Resources
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Horizon
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Snapshot
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Raw
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Public.Census

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed

open Capitalism.Universal.Source.Program Capitalism.Universal.Root Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting Capitalism.Universal.Abolition.Accounting.Quantifiers Joint
open Capitalism.Universal.Abolition.Root Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

private theorem productive_unpaid : ¬ Joint.Current.productivePaid seed grossClaim shared := by
  intro paid
  have zero := paid (false, false) (by rw [productive_scope]; exact List.mem_singleton_self _)
  rw [productive_balance] at zero
  norm_num at zero

def defaultWord := Planning.Menu.plantPlan seed grossClaim shared true releasedTech

local macro "source_snapshot" : tactic => `(tactic|
  simp only [Planning.primitiveItems,Planning.primitiveAnalysis,Planning.grossCredits,
    Planning.primitiveAfter,Planning.primitiveReadings,Planning.initialWork,
    Planning.Menu.plantPlan,Planning.Menu.materialPlan,Planning.Menu.productionPrefix,
    Planning.Menu.fundedNeeds,Planning.Menu.fundNeedsFrom,Planning.Menu.needsWord,Planning.Menu.needCells,
    Planning.Menu.bills,Planning.Menu.grossFrom,Planning.Menu.productiveFrom,Planning.Menu.dose,
    Planning.Menu.relevantGoods,Planning.Menu.required,Planning.Menu.recipeNet,Planning.Menu.command,Planning.Menu.settlements,
    Allocation.Kernel.after,Allocation.Kernel.net,Allocation.Kernel.productiveCredit,Allocation.Kernel.gross,
    Allocation.Kernel.reservation,Allocation.Kernel.incoming,Allocation.Kernel.grossCharged,Allocation.room,Allocation.first,
    physical_law,shared_raw,productive_scope,gross_scope,productive_balance,gross_balance,
    productive_declared,gross_declared,live_roster,original_financial_tail,productive_gap.2,
    productive_unpaid,false_and,if_false,List.foldl_cons,List.foldl_nil])

private theorem default_resources : Planning.Resources seed grossClaim shared defaultWord := by
  constructor <;> unfold defaultWord <;> source_snapshot <;> decide +kernel

private theorem default_in_menu : defaultWord ∈ Planning.Menu.plans seed grossClaim shared := by
  rw [Planning.Menu.plans, if_neg (fun paid => productive_unpaid paid.1)]
  apply List.mem_flatMap.mpr
  refine ⟨true, ?_, ?_⟩
  · rw [Planning.Menu.operators, if_neg productive_unpaid, productive_gap.2]
    exact List.mem_singleton_self _
  · apply List.mem_map.mpr
    refine ⟨releasedTech, ?_, rfl⟩
    unfold Planning.Menu.technologies
    rw [shared_raw]
    exact List.mem_dedup.mpr List.mem_cons_self

theorem enough : Planning.Enough seed grossClaim shared := ⟨defaultWord, default_in_menu, default_resources⟩

private theorem only_technology : Planning.Menu.technologies seed grossClaim shared = [releasedTech] := by
  unfold Planning.Menu.technologies
  rw [shared_raw]
  decide +kernel

private theorem chosen_is_default : Planning.chosen seed grossClaim shared = defaultWord := by
  have member : Planning.chosen seed grossClaim shared ∈ Planning.Menu.plans seed grossClaim shared := by
    unfold Planning.chosen
    cases Planning.selection seed grossClaim shared with
    | ready word original resources => exact original
    | blocked issues =>
      exact (Planning.failure_inventory_retains_each_original_plan _ _ _ issues
        defaultWord default_in_menu default_resources).elim
  rcases Planning.Menu.every_plan_keeps_the_original_actor_technology_and_financial_tail
    seed grossClaim shared _ member with paid | ⟨actor, original, technology, parameter, same⟩
  · exact (productive_unpaid paid.1).elim
  · rw [Planning.Menu.operators, if_neg productive_unpaid, productive_gap.2] at original
    rw [only_technology] at parameter
    cases List.mem_singleton.mp original
    cases List.mem_singleton.mp parameter
    exact same

theorem selected_is_default : Planning.selected seed grossClaim shared = defaultWord := by
  rw [Planning.sufficient_source_resources_execute_the_whole_selected_programme seed grossClaim shared enough]
  exact chosen_is_default

def nativeOpening := Evolving.Source.initial seed grossClaim enough (fun _ _ => .advance)
def epoch := Evolving.Epoch.Source.initial nativeOpening

theorem epoch_ready : Ready epoch :=
  Evolving.Source.initial_has_no_pending_native_work seed grossClaim enough (fun _ _ => .advance)

theorem epoch_review : ReviewAvailable epoch := by
  unfold ReviewAvailable epoch
  rw [Evolving.Epoch.Source.initial_source_phase_is_read_from_its_own_face]
  trivial

def settledRaw : Raw where
  stock := fun person good => if good then if person then 2 else 0 else if person then 109 else 117
  claims := fun _ _ _ => 0
  technology := releasedTech
  clock := 4
  round := 4

private theorem one_material_hour (word : List Req) :
    ((PublicFunction.physicalLaw active).next snapshot word).clock = settledRaw.clock := by
  change (3 : ℚ) + max 0 1 = 4
  norm_num

private theorem one_material_round (word : List Req) :
    ((PublicFunction.physicalLaw active).next snapshot word).round = settledRaw.round := rfl

theorem epoch_effect : epoch.raw = (PublicFunction.physicalLaw active).next snapshot defaultWord := by
  have actual : epoch.raw = (Runtime.Resumption.paidState seed grossClaim).raw :=
    Runtime.Resumption.the_resumed_live_raw_is_the_same_actual_paid_raw seed grossClaim enough
  rw [actual]
  change (Planning.actualNext seed grossClaim shared).raw = _
  rw [Planning.the_selected_next_is_the_one_original_live_material_next, selected_is_default, physical_law, shared_raw]

private theorem settled_stock : ((PublicFunction.physicalLaw active).next snapshot defaultWord).stock =
    settledRaw.stock := by
  funext person good
  unfold defaultWord
  source_snapshot
  cases person <;> cases good <;> decide +kernel

private theorem settled_claims : ((PublicFunction.physicalLaw active).next snapshot defaultWord).claims =
    settledRaw.claims := by
  funext instrument debtor creditor
  unfold defaultWord
  source_snapshot
  cases instrument
  cases debtor <;> cases creditor <;> decide +kernel

private theorem settled_technology : ((PublicFunction.physicalLaw active).next snapshot defaultWord).technology =
    settledRaw.technology := by
  unfold defaultWord
  source_snapshot
  decide +kernel

attribute [local irreducible] defaultWord Planning.selected Planning.actualNext

theorem epoch_raw : epoch.raw = settledRaw := by
  refine epoch_effect.trans ?_
  apply RawCurrent.ext
  · exact settled_stock
  · exact settled_claims
  · exact settled_technology
  · exact one_material_hour defaultWord
  · exact one_material_round defaultWord

def repair : Req := ⟨true, [], .ordinary false, [], .transfer true false [(true, 1)]⟩

def cut : Conflict.Root.Cut Bool Bool Port Tech Unit := afterNative epoch repair

private theorem repair_valid : (Physical.Public.interpreter epoch.native.input).Valid epoch.raw repair := by
  rw [epoch_raw]
  decide +kernel

def cutRaw := (PublicFunction.physicalLaw active).step settledRaw repair

theorem cut_ready : Ready cut :=
  (two_actual_root_steps_pay_and_consume_the_generated_primitive epoch repair epoch_ready epoch_review rfl repair_valid).1

theorem cut_review : ReviewAvailable cut :=
  afterNative_keeps_the_available_review epoch repair epoch_ready epoch_review rfl repair_valid

theorem cut_input : cut.native.input = input := afterNative_keeps_the_same_original_input epoch repair

theorem cut_raw : cut.raw = cutRaw := by
  rw [cut, (two_actual_root_steps_pay_and_consume_the_generated_primitive
    epoch repair epoch_ready epoch_review rfl repair_valid).2, epoch_raw]
  rfl

theorem installed : Emergency.Installed cut base scope := by
  unfold Emergency.Installed
  rw [cut_input]
  rfl

theorem cut_parameters :
    cut.native.depth = 0 ∧ cut.native.count = 19 ∧ cut.native.prefixLimit = 0 ∧
    cut.native.renewalLimit = 0 ∧ cut.native.oldPast = [] := by
  have first := (queued epoch repair).advance_parameters
  have second := (afterBody epoch repair).advance_parameters
  exact ⟨second.2.1.trans first.2.1, second.2.2.1.trans first.2.2.1,
    second.2.2.2.1.trans first.2.2.2.1, second.2.2.2.2.1.trans first.2.2.2.2.1,
    second.2.2.2.2.2.1.trans first.2.2.2.2.2.1⟩

theorem original_member (person : Bool) :
    person ∈ Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Census.parties cut.native.input
      cut.native.depth cut.native.count cut.native.prefixLimit cut.native.renewalLimit
        (Physical.Prefix.cursor cut.native.oldPast) := by
  rw [cut_input,cut_parameters.1,cut_parameters.2.1,cut_parameters.2.2.1,
    cut_parameters.2.2.2.1,cut_parameters.2.2.2.2]
  cases person <;> decide +kernel

theorem standing (person : Bool) : person ∈ cut.members :=
  Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
    _ _ _ _ _ _ _ person
    (original_member person)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed
