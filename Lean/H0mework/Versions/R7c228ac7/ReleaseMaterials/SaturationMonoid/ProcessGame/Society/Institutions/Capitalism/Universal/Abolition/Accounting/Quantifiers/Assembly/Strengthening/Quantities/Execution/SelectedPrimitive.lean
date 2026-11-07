import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Drain
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (one_checked_original_primitive_has_one_actual_material_step)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

private theorem selectedPrimitiveResult (source : C) (request : Request Party Good Port Technology Instrument)
    (selected : source.executionRaw = .primitive request) :
    let initial := Evolving.Epoch.Source.originalState source.native
    let actual := Physical.Public.compile source.native.input initial (.primitive request)
    source.physicalResult.execution = actual.execution ∧ source.physicalResult.next = actual.next ∧
      source.physicalResult.isAccepted = actual.isAccepted := by
  intro initial actual
  unfold Evolving.Epoch.Current.physicalResult
  rw [selected]
  unfold Public.Scope.actualResult Public.Scope.selectedCursor
  rw [(Public.Scope.every_nonperiod_proposal_keeps_its_actual_route _ _ _ _ _ _ _ (.primitive request) rfl).1]
  exact ⟨rfl, rfl, rfl⟩

/-- Consume a primitive already selected by the installed source rule.
In an active review the rule can require that very primitive. -/
theorem the_selected_primitive_is_paid_by_the_original_root
    (source : C) (request : Request Party Good Port Technology Instrument)
    (ready : ¬ Pending source) (selected : source.executionRaw = .primitive request)
    (signed : request.consents = [])
    (valid : (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    (next source none).raw = (Physical.Public.interpreter source.native.input).step source.raw request ∧
      source.physicalResult.isAccepted = true ∧ inventory source [none] = [⟨0, source.raw, request⟩] := by
  let initial := Evolving.Epoch.Source.originalState source.native
  let actual := Physical.Public.compile source.native.input initial (.primitive request)
  have routed := selectedPrimitiveResult source request selected
  have paid := one_checked_original_primitive_has_one_actual_material_step source.native.input initial request signed valid
  have readyAt : ¬ Public.Inquiry.HasWork source.native.frame source.native.actual.actual := ready
  have body := Evolving.Epoch.Transition.next_state_reads_the_same_actual_material_target source readyAt
  change source.advance.raw = _ ∧ _ ∧ _
  rw [source.advance_eq_epoch readyAt]
  have raw : actual.next.raw = (Physical.Public.interpreter source.native.input).step source.raw request :=
    congrArg (fun state => state.raw) paid.2.2
  refine ⟨body.trans ((congrArg (fun state => state.raw) routed.2.1).trans raw), routed.2.2.trans paid.1, ?_⟩
  have effective : Optimality.Programme.Epoch.effective source = [.primitive request] := by
    unfold Optimality.Programme.Epoch.effective
    rw [if_neg readyAt, selected,
      (Public.Scope.every_nonperiod_proposal_keeps_its_actual_route _ _ _ _ _ _ _ (.primitive request) rfl).1]
  have stored := effective_inventory source none
  change Optimality.Programme.items source.native.input initial (Optimality.Programme.Epoch.effective source) =
    Optimality.Programme.Epoch.materialItems source at stored
  rw [effective] at stored
  simp only [inventory, List.append_nil]
  change Optimality.Programme.Epoch.materialItems source = _
  rw [← stored]
  change actual.execution.items ++ [] = _
  rw [List.append_nil, paid.2.1]
  rfl

theorem the_selected_refusal_keeps_the_exact_original_material_current
    (source : C) (request : Request Party Good Port Technology Instrument)
    (ready : ¬ Pending source) (selected : source.executionRaw = .primitive request)
    (signed : request.consents = [])
    (invalid : ¬ (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    (next source none).raw = source.raw ∧ source.physicalResult.isAccepted = false := by
  let initial := Evolving.Epoch.Source.originalState source.native
  have failed :
      (Physical.Public.compile source.native.input initial (.primitive request)).next.raw = source.raw ∧
      (Physical.Public.compile source.native.input initial (.primitive request)).isAccepted = false := by
    cases Physical.Public.compile source.native.input initial (.primitive request) with
    | accepted actual exactWord accepted =>
      have same : [request] = actual := Option.some.inj
        ((congrArg some (congrArg List.singleton (Request.resign_self request signed))).symm.trans exactWord)
      subst actual
      exact (invalid (accepted ⟨0, source.raw, request⟩ List.mem_cons_self)).elim
    | refused _ _ _ _ _ => exact ⟨rfl, rfl⟩
    | metadata absent => cases absent
  have readyAt : ¬ Public.Inquiry.HasWork source.native.frame source.native.actual.actual := ready
  have body := Evolving.Epoch.Transition.next_state_reads_the_same_actual_material_target source readyAt
  have routed := selectedPrimitiveResult source request selected
  change source.advance.raw = source.raw ∧ _
  rw [source.advance_eq_epoch readyAt]
  exact ⟨body.trans ((congrArg (fun state => state.raw) routed.2.1).trans failed.1),
    routed.2.2.trans failed.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
