import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment.Repeated

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (R compact)
open Quantities.Execution
open Reparation.Actual.Allocation (Position originalItem)
open ExposureGuard
open private cut_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Source
open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

noncomputable section

abbrev production : R := ⟨true, [], false, [], .produce true⟩
abbrev produceInput : Reparation.Actual.Input Bool Bool Bool Unit Unit := some (.primitive production)
abbrev productionHead : Original.Word := [produceInput, none]

private theorem compact_production_is_legal (raw : Original.Raw) : compact.law.Valid raw production := by
  unfold RawLaw.Valid
  refine ⟨⟨trivial, rfl⟩, ?_, trivial, ?_, ?_, ?_⟩
  · intro port listed
    change port ∈ [true] at listed
    rw [List.mem_singleton.mp listed]
    exact Or.inl rfl
  · intro _ absent
    exact (List.not_mem_nil absent).elim
  · intro item listed
    change item ∈ [((true, false), 18)] at listed
    rw [List.mem_singleton.mp listed]
    norm_num
  · intro _ absent
    exact (List.not_mem_nil absent).elim

variable (past : Original.Word) (ready : Ready (endAt Original.seed past))
  (review : ReviewAvailable (endAt Original.seed past))

private theorem legal_at : (endAt Original.seed past).native.input.law.Valid (endAt Original.seed past).raw production := by
  rw [cut_source past]
  exact compact_production_is_legal _

private theorem physical :
    (Physical.Public.interpreter (endAt Original.seed past).native.input).Valid (endAt Original.seed past).raw production :=
  PublicFunction.valid_physical _ _ _ (legal_at past)

include ready review

theorem the_production_item_is_actual : Boundary.Actual.items (endAt Original.seed past) produceInput =
    [⟨0, (endAt Original.seed past).raw, production⟩] :=
  (the_selected_primitive_is_paid_by_the_original_root
    (queued (endAt Original.seed past) production) production ready
    (the_available_review_forwards_the_actual_requested_primitive _ _ review) rfl (physical past)).2.2

theorem production_accounting_has_no_item : Boundary.Actual.items (endAt Original.seed (past ++ [produceInput])) none = [] := by
  have work := the_actual_body_must_consume_its_original_native_head (endAt Original.seed past) production
    ready review rfl (physical past)
  rw [endAt_append]
  exact Reparation.Transport.native_step_has_no_material_items none work

theorem the_produced_item_at (site : Position Original.seed past produceInput) :
    originalItem Original.seed past produceInput site = ⟨0, (endAt Original.seed past).raw, production⟩ := by
  have actual : originalItem Original.seed past produceInput site ∈ Boundary.Actual.items (endAt Original.seed past) produceInput :=
    List.getElem_mem _
  rw [the_production_item_is_actual past ready review] at actual
  exact List.mem_singleton.mp actual

omit ready review in
private theorem the_production_has_no_debit :
    (Boundary.Actual.materialLaw (endAt Original.seed past)).actualDebit (endAt Original.seed past).raw production = [] := by
  change (Physical.Public.interpreter (endAt Original.seed past).native.input).actualDebit _ _ = _
  rw [cut_source past, RawLaw.actualDebit]
  split <;> rfl

theorem the_material_production_has_no_new_damage :
    Boundary.Actual.damages (endAt Original.seed past) produceInput Original.community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro damage _
  have keys := original_key damage
  rw [show damage.item = originalItem Original.seed past produceInput damage.position from rfl,
    the_produced_item_at past ready review] at keys
  unfold keysAt at keys
  rw [the_production_has_no_debit past] at keys
  exact (List.not_mem_nil keys).elim

theorem the_production_and_accounting_are_eligible (anchor : Original.Word) :
    Occurrence.EligibleFrom Original.community replies anchor past productionHead := by
  refine ⟨⟨⟨?_, ?_⟩, the_material_production_has_no_new_damage past ready review⟩, ?_, trivial⟩
  · intro item listed
    change item ∈ Boundary.Actual.items (endAt Original.seed past) produceInput at listed
    rw [the_production_item_is_actual past ready review] at listed
    rw [List.mem_singleton.mp listed]
    exact legal_at past
  · intro site question asked _
    change question ∈ questions (endAt Original.seed past) (originalItem Original.seed past produceInput site) at asked
    rw [the_produced_item_at past ready review] at asked
    have exactQuestion : questions (endAt Original.seed past) ⟨0, (endAt Original.seed past).raw, production⟩ =
        [(true, .signature)] := by
      unfold questions materialQuestions
      dsimp only
      rw [the_production_has_no_debit past]
      rfl
    rw [exactQuestion, List.mem_singleton] at asked
    rw [asked]
    unfold replies
    rw [the_produced_item_at past ready review]
    rfl
  · have empty := production_accounting_has_no_item past ready review
    exact ⟨no_material_is_admitted _ _ _ _ empty, Boundary.Actual.no_material_write_has_no_damage _ _ _ empty⟩

theorem production_adds_eighteen_to_the_actual_original_inventory (base : ℚ)
    (stock : (endAt Original.seed past).raw = Snapshot 0 base) :
    (endAt Original.seed (past ++ productionHead)).raw = Snapshot 0 (base + 18) ∧
    Ready (endAt Original.seed (past ++ productionHead)) ∧ ReviewAvailable (endAt Original.seed (past ++ productionHead)) := by
  have execution : Trace (endAt Original.seed past) [production] (endAt Original.seed (past ++ productionHead)) ∧
      Ready (endAt Original.seed (past ++ productionHead)) ∧ ReviewAvailable (endAt Original.seed (past ++ productionHead)) := by
    rw [endAt_append]
    apply pay_checked_primitives (endAt Original.seed past) [production] 0 ready review
    · intro request present
      rw [List.mem_singleton.mp present]
    · intro item present
      change item ∈ [⟨0, (endAt Original.seed past).raw, production⟩] at present
      rw [List.mem_singleton.mp present]
      exact physical past
  refine ⟨?_, execution.2⟩
  rw [execution.1.raw_is_the_complete_original_execution 0, cut_source past, stock]
  let interpreter := Physical.Public.interpreter compact
  have lawful : interpreter.Valid (Snapshot 0 base) production := PublicFunction.valid_physical _ _ _ (compact_production_is_legal _)
  change (interpreter.execute (Snapshot 0 base) 0 [production]).final = _
  rw [show (interpreter.execute (Snapshot 0 base) 0 [production]).final = interpreter.step (Snapshot 0 base) production from rfl,
    RawLaw.step, if_pos lawful]
  apply RawCurrent.ext
  · funext person good
    have debit : interpreter.debit (Snapshot 0 base) production = [] := rfl
    have credit : interpreter.credit (Snapshot 0 base) production = [((true, false), 18)] := rfl
    change (Snapshot 0 base).stock person good - flowAt _ person good + flowAt _ person good = _
    rw [debit, credit]
    cases person <;> cases good <;> simp [Snapshot, Original.snapshot, flowAt, amount]
  · rfl
  · rfl
  · rfl
  · rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment.Repeated
