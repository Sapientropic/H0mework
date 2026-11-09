import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Balance
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Horizon
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Snapshot
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Raw
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Native

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Source.Program Capitalism.Universal.Root Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting Capitalism.Universal.Abolition.Accounting.Quantifiers Joint
open Capitalism.Universal.Abolition.Root Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Installed (Port Tech Raw Req releasedTech scope)

noncomputable section

private theorem productive_unpaid : ¬ Joint.Current.productivePaid seed grossClaim shared := by
  intro paid
  have zero := paid (false, false) (by rw [productive_scope]; exact List.mem_singleton_self _)
  rw [productive_balance] at zero
  norm_num at zero

def clearing := Planning.Menu.plantPlan seed grossClaim shared true releasedTech

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
    productive_declared,gross_declared,live_roster,original_financial_tail,original_gap.2,
    productive_unpaid,false_and,if_false,List.foldl_cons,List.foldl_nil])

private theorem resources : Planning.Resources seed grossClaim shared clearing := by
  constructor <;> unfold clearing <;> source_snapshot <;> decide +kernel

private theorem only_technology : Planning.Menu.technologies seed grossClaim shared = [releasedTech] := by
  unfold Planning.Menu.technologies
  rw [shared_raw]
  decide +kernel

private theorem plan_menu : Planning.Menu.plans seed grossClaim shared = [clearing] := by
  rw [Planning.Menu.plans, if_neg (fun paid => productive_unpaid paid.1), Planning.Menu.operators,
    if_neg productive_unpaid, original_gap.2, only_technology]
  rfl

theorem enough : Planning.Enough seed grossClaim shared :=
  ⟨clearing, plan_menu.symm ▸ List.mem_singleton_self _, resources⟩

private theorem selected : Planning.selected seed grossClaim shared = clearing := by
  rw [Planning.sufficient_source_resources_execute_the_whole_selected_programme seed grossClaim shared enough]
  unfold Planning.chosen
  cases Planning.selection seed grossClaim shared with
  | ready word original resources => exact List.mem_singleton.mp (plan_menu ▸ original)
  | blocked issues => exact (Planning.failure_inventory_retains_each_original_plan _ _ _ issues
      clearing (plan_menu.symm ▸ List.mem_singleton_self _) resources).elim

def nativeOpening := Evolving.Source.initial seed grossClaim enough (fun _ _ => .advance)

abbrev C := Conflict.Root.Cut Bool Bool Port Tech Unit

def start : C := Evolving.Epoch.Source.initial nativeOpening

theorem start_ready : Ready start :=
  Evolving.Source.initial_has_no_pending_native_work seed grossClaim enough (fun _ _ => .advance)

theorem start_review : start.control.review = none := by
  unfold start
  rw [Evolving.Epoch.Source.initial_source_phase_is_read_from_its_own_face]
  rfl

theorem start_input : start.native.input = input := rfl

theorem installed : Emergency.Installed start base scope := rfl

def opening : Raw where
  stock := fun person good => if good then if person then 16 else 1 else if person then 108 else 118
  claims := fun _ _ _ => 0
  technology := releasedTech
  clock := 4
  round := 4

private theorem actual_clearing : start.raw = (PublicFunction.physicalLaw law).next snapshot clearing := by
  have actual : start.raw = (Runtime.Resumption.paidState seed grossClaim).raw :=
    Runtime.Resumption.the_resumed_live_raw_is_the_same_actual_paid_raw seed grossClaim enough
  rw [actual]
  change (Planning.actualNext seed grossClaim shared).raw = _
  rw [Planning.the_selected_next_is_the_one_original_live_material_next, selected, physical_law, shared_raw]

private theorem cleared_stock : ((PublicFunction.physicalLaw law).next snapshot clearing).stock = opening.stock := by
  funext person good
  unfold clearing
  source_snapshot
  cases person <;> cases good <;> decide +kernel

private theorem cleared_claims : ((PublicFunction.physicalLaw law).next snapshot clearing).claims = opening.claims := by
  funext code debtor creditor
  unfold clearing
  source_snapshot
  cases code
  cases debtor <;> cases creditor <;> decide +kernel

private theorem cleared_technology : ((PublicFunction.physicalLaw law).next snapshot clearing).technology =
    opening.technology := by
  unfold clearing
  source_snapshot
  decide +kernel

private theorem material_hour (word : List Req) :
    ((PublicFunction.physicalLaw law).next snapshot word).clock = opening.clock := by
  change (3 : ℚ) + max 0 1 = 4
  norm_num

attribute [local irreducible] clearing Planning.selected Planning.actualNext

theorem start_raw : start.raw = opening := by
  refine actual_clearing.trans ?_
  apply RawCurrent.ext
  · exact cleared_stock
  · exact cleared_claims
  · exact cleared_technology
  · exact material_hour clearing
  · rfl

theorem every_person_originally_stands (person : Bool) :
    person ∈ Capitalism.Universal.Abolition.Root.Actual.members start.native.input start.native.depth start.native.count := by
  change person ∈ Capitalism.Universal.Abolition.Root.Actual.members input 0 count
  cases person <;> decide +kernel

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
