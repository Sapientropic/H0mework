import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.LegacyReadings
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Initial
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Read
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Raw

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers

open Source.Program Innovation Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers
open Quantifiers.Joint

noncomputable section

def oldPayment := Planning.Menu.plantPlan seed grossClaim shared true ()

theorem original_positive_scope :
    (false,false) ∈ Responsibility.Family.positiveScope mechanism CompactSource.past nature CompactSource.response := by
  decide +kernel

private theorem stillOpen : ¬ Current.productivePaid seed grossClaim shared := by
  intro complete
  have unpaid : shared.productive (false,false) = 18 := by decide +kernel
  have paid := complete (false,false) original_positive_scope
  rw [unpaid] at paid
  norm_num at paid

theorem original_menu : oldPayment ∈ Planning.Menu.plans seed grossClaim shared := by
  rw [Planning.Menu.plans, if_neg (fun complete => stillOpen complete.1)]
  apply List.mem_flatMap.mpr
  refine ⟨true, ?_, ?_⟩
  · rw [Planning.Menu.operators, if_neg stillOpen]
    decide +kernel
  · apply List.mem_map.mpr
    refine ⟨(), ?_, rfl⟩
    apply List.mem_dedup.mpr
    have unique : shared.raw.technology = () := Subsingleton.elim _ _
    rw [← unique]
    exact List.mem_cons_self

private theorem live_law : actualLaw seed = PublicFunction.physicalLaw law := rfl

local macro "old_reads" : tactic => `(tactic|
  simp only [Planning.primitiveItems, Planning.primitiveAnalysis, Planning.grossCredits,
    Planning.primitiveAfter, Planning.primitiveReadings, Planning.initialWork,
    Planning.Menu.plantPlan, Planning.Menu.materialPlan, Planning.Menu.productionPrefix,
    Planning.Menu.fundedNeeds, Planning.Menu.fundNeedsFrom, Planning.Menu.needsWord, Planning.Menu.needCells,
    Planning.Menu.bills, Planning.Menu.grossFrom, Planning.Menu.productiveFrom, Planning.Menu.dose,
    Planning.Menu.relevantGoods, Planning.Menu.required, Planning.Menu.recipeNet, Planning.Menu.command,
    Planning.Menu.settlements, Allocation.Kernel.after, Allocation.Kernel.net, Allocation.Kernel.productiveCredit,
    Allocation.Kernel.gross, Allocation.Kernel.reservation, Allocation.Kernel.incoming,
    Allocation.Kernel.grossCharged, Allocation.room, Allocation.first, live_law, shared_raw, productive_scope,
    gross_scope, productive_remaining, gross_remaining, productive_declared, gross_declared, live_roster,
    original_financial_tail, cohort, stillOpen, false_and, if_false, List.foldl_cons, List.foldl_nil])

set_option maxHeartbeats 2500000 in
theorem old_payment_is_funded : Planning.Resources seed grossClaim shared oldPayment := by
  constructor <;> unfold oldPayment <;> old_reads <;> decide +kernel

theorem enough : Planning.Enough seed grossClaim shared :=
  ⟨oldPayment, original_menu, old_payment_is_funded⟩

def nativeSource := Evolving.Source.initial seed grossClaim enough (fun _ _ => .advance)
def source := Evolving.Epoch.Source.initial nativeSource

theorem source_is_ready : ¬ Public.Inquiry.HasWork source.native.frame source.native.actual.actual :=
  Evolving.Source.initial_has_no_pending_native_work seed grossClaim enough (fun _ _ => .advance)

theorem source_raw :
    source.raw = (Evolution.Ingress.Joint.Material.Runtime.Resumption.paidState seed grossClaim).raw :=
  (Evolving.Epoch.Source.initial_raw_is_the_original_live_raw nativeSource).trans
    (Evolution.Ingress.Joint.Material.Runtime.Resumption.the_resumed_live_raw_is_the_same_actual_paid_raw
      seed grossClaim enough)

theorem selected_is_the_original_paid_word : Planning.selected seed grossClaim shared = oldPayment := by
  rw [Planning.sufficient_source_resources_execute_the_whole_selected_programme _ _ _ enough]
  have menu : Planning.Menu.plans seed grossClaim shared = [oldPayment] := by
    rw [Planning.Menu.plans, if_neg (fun paid => stillOpen paid.1), Planning.Menu.operators,
      if_neg stillOpen, cohort]
    have technologies : Planning.Menu.technologies seed grossClaim shared = [()] := by
      unfold Planning.Menu.technologies
      rw [show shared.raw.technology = () from Subsingleton.elim _ _]
      decide +kernel
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, technologies]
    rfl
  unfold Planning.chosen
  cases chosen : Planning.selection seed grossClaim shared with
  | ready word listed _ => exact List.mem_singleton.mp (menu ▸ listed)
  | blocked issues =>
    exact (Planning.failure_inventory_retains_each_original_plan _ _ _ issues
      oldPayment original_menu old_payment_is_funded).elim

theorem source_is_the_original_paid_material_cut :
    source.raw = (PublicFunction.physicalLaw law).next Quantifiers.Joint.Consumers.Compact.physicalSnapshot oldPayment := by
  rw [source_raw]
  change (actualLaw seed).next shared.raw (Planning.selected seed grossClaim shared) = _
  rw [selected_is_the_original_paid_word, live_law, shared_raw]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers
