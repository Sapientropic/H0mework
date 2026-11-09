import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Batch
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.Occurrence
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Restitution
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualReadback
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.SelectedPrimitive

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving
open Quantities.Execution

open private sourceReady sourceReview from
  H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

noncomputable section

abbrev actualOrigin : C := Conflict.Consumers.Evolving.source
def withoutLivingPayment : W := [destroy, levy]
def levyPast : Actual.Script Bool Bool Bool Unit Unit := primitiveScript [destroy]
def levyInput : Actual.Input Bool Bool Bool Unit Unit := some (.primitive levy)

private theorem physically_executed :
    Trace actualOrigin withoutLivingPayment (Conflict.Root.terminal actualOrigin withoutLivingPayment) := by
  have authorized : Conflict.Root.Authorized actualOrigin withoutLivingPayment := by
    unfold Conflict.Root.Authorized
    rw [sourceInput, sourceRead]
    decide +kernel
  exact (pay_checked_primitives actualOrigin _ 0 sourceReady sourceReview (by decide +kernel)
    (fun item present => PublicFunction.valid_physical _ _ _ (authorized item present))).1

theorem the_actual_assault_leaves_its_living_payment_unfulfilled :
    ¬ Quantities.Feasible actualOrigin (primitiveScript withoutLivingPayment) := by
  intro paid
  have floor := (Quantities.Demand.primitive_covers_iff_original_floor physically_executed).mp paid.paid
  have first := (queued Original.source issue).advance_parameters
  have second := (afterBody Original.source issue).advance_parameters
  have original := Innovation.Contribution.Pricing.Consumers.Actual.source_parameters
  have params : actualOrigin.native.depth = 0 ∧ actualOrigin.native.count = 19 ∧
      actualOrigin.native.prefixLimit = 0 ∧ actualOrigin.native.renewalLimit = 0 ∧
      actualOrigin.native.oldPast = [] :=
    ⟨second.2.1.trans (first.2.1.trans original.1),
     second.2.2.1.trans (first.2.2.1.trans original.2.1),
     second.2.2.2.1.trans (first.2.2.2.1.trans original.2.2.1),
     second.2.2.2.2.1.trans (first.2.2.2.2.1.trans original.2.2.2.1),
     second.2.2.2.2.2.1.trans (first.2.2.2.2.2.1.trans original.2.2.2.2)⟩
  have present : false ∈ actualOrigin.members := by
    apply Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
    rw [sourceInput, params.1, params.2.1, params.2.2.1, params.2.2.2.1, params.2.2.2.2]
    decide +kernel
  have listed : (false, .necessity, true, (1 : ℚ)) ∈
      Material.originalRequirements (Public.Scope.checkInput actualOrigin.native.input)
        (Capitalism.Universal.Abolition.Root.Actual.origin actualOrigin.native.input actualOrigin.native.depth
          actualOrigin.native.count) actualOrigin.members := by
    rw [sourceInput, params.1, params.2.1]
    exact List.mem_flatMap.mpr ⟨false, present, by decide +kernel⟩
  have bound := floor _ listed
  change (1 : ℚ) ≤ Material.actualUse (Public.Scope.checkInput actualOrigin.native.input)
    actualOrigin.raw withoutLivingPayment false .necessity true at bound
  rw [sourceInput, sourceRead] at bound
  exact (by decide +kernel : ¬ (1 : ℚ) ≤ Material.actualUse (Public.Scope.checkInput compact)
    oldRaw withoutLivingPayment false .necessity true) bound

private abbrev levyCut := endAt actualOrigin levyPast

private theorem levy_inventory :
    Boundary.Actual.items levyCut levyInput = [⟨0, levyCut.raw, levy⟩] := by
  have trace : Trace levyCut [levy] (Conflict.Root.terminal actualOrigin withoutLivingPayment) :=
    Conflict.Root.trace_after_prefix actualOrigin _ [destroy] [levy] physically_executed
  have ready := trace.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp)
  have checked := trace.every_original_instruction_has_its_actual_guards 0
    ⟨0, levyCut.raw, levy⟩ List.mem_cons_self
  exact (the_selected_primitive_is_paid_by_the_original_root (queued levyCut levy) levy ready.1
    (the_available_review_forwards_the_actual_requested_primitive levyCut levy ready.2)
    checked.2 checked.1).2.2

private theorem exact_levy_loss :
    loss (Boundary.Actual.materialLaw levyCut) id ⟨0, levyCut.raw, levy⟩ address = 6 := by
  have trace := Conflict.Root.trace_before_prefix actualOrigin _ [destroy] [levy] physically_executed
  have raw := trace.raw_is_the_complete_original_execution 0
  change levyCut.raw = _ at raw
  have installed : levyCut.native.input = compact := (endAt_input _ _).trans sourceInput
  rw [Boundary.Actual.materialLaw, installed, raw, sourceInput, sourceRead]
  decide +kernel

def FiledSixOnTheActualNext (damage : Boundary.Actual.DamageAt levyCut levyInput id) : Prop :=
  damage.quantity = 6 ∧
    let written := Actual.materialBatch actualOrigin id levyPast levyInput (Actual.material_ready damage)
    let origin : Actual.Occurrence actualOrigin id := ⟨levyPast, levyInput, damage⟩
    ∃ row, written.read row = .inr (origin, Actual.opening origin)

theorem the_rejected_assault_files_its_six_on_the_actual_material_successor :
    Nonempty (Quantities.Obstruction actualOrigin (primitiveScript withoutLivingPayment)) ∧
    ∃ damage, FiledSixOnTheActualNext damage := by
  refine ⟨(Quantities.infeasible_iff_original_obstruction _ _).mp
    the_actual_assault_leaves_its_living_payment_unfulfilled, ?_⟩
  have present : (⟨0, levyCut.raw, levy⟩ : ExecutionItem Bool Bool Bool Unit Unit) ∈
      Boundary.Actual.items levyCut levyInput := by rw [levy_inventory]; exact List.mem_singleton_self _
  obtain ⟨position, inside, same⟩ := List.getElem_of_mem present
  let damage : Boundary.Actual.DamageAt levyCut levyInput id :=
    ⟨(⟨position, inside⟩, address), by
      change 0 < loss (Boundary.Actual.materialLaw levyCut) id
        ((Boundary.Actual.items levyCut levyInput)[position]'inside) address
      rw [same, exact_levy_loss]
      decide⟩
  have qty : damage.quantity = 6 := by
    change loss (Boundary.Actual.materialLaw levyCut) id
      ((Boundary.Actual.items levyCut levyInput)[position]'inside) address = 6
    rw [same, exact_levy_loss]
  exact ⟨damage, qty, Actual.every_affected_address_is_filed_on_the_same_generated_next _ _ _ _ _ damage⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers
