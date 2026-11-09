import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Round
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifePeriod
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Reader

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Innovation.Contribution.Pricing.Consumers.Actual
  (life lifeWord source_parameters source_ready source_review source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair every_original_person_keeps_actual_standing)
open Quantities.Consumers

noncomputable section

abbrev C := Root.Cut Bool Bool Bool Unit Unit
abbrev Period := Window Bool Bool Bool Unit Unit
abbrev Input := Option (Compile.RawInput Bool Bool Bool Unit Unit)
abbrev Move := Script Bool Bool Bool Unit Unit

abbrev initial : Period := Window.at lifeSource
abbrev service : Input := some (.execute lifeWord)
abbrev supplied := Accounting.Quantifiers.Joint.Consumers.Compact.input
abbrev before := Innovation.Contribution.Pricing.Consumers.Actual.quoteCut
abbrev material := Physical.Public.interpreter supplied

private theorem inventory_exact :
    Boundary.Actual.items lifeSource service = material.rawItems before lifeWord := by
  change Quantities.Execution.inventory lifeSource [some (.execute lifeWord)] = _
  rw [Quantities.Execution.a_checked_period_has_the_original_paid_inventory lifeSource lifeWord
    source_ready source_review checked_living_period, source_input_is_the_original_registered_input,
    the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  rfl

private theorem residents_still_stand (person : Bool) :
    person ∈ (initial.nextCut service).members := by
  let target := Quantities.Execution.endAt lifeSource lifePeriod
  obtain ⟨input, depth, count⟩ := Quantities.Execution.the_actual_script_keeps_the_original_reader_indices
    lifeSource lifePeriod
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  change person ∈ Capitalism.Universal.Abolition.Root.Actual.members
    target.native.input target.native.depth target.native.count
  rw [input, depth, count, source_input_is_the_original_registered_input, source_parameters.1, source_parameters.2.1]
  cases person <;> decide +kernel

private theorem no_original_foreign_debit (damage : Boundary.Actual.DamageAt lifeSource service id) : False := by
  have listed := damage.source_item
  rw [inventory_exact] at listed
  have exact : ∀ item ∈ material.rawItems before lifeWord, ∀ victim attacker good : Bool,
      ¬ 0 < Reparation.loss material id item (victim, attacker, good) := by decide +kernel
  have positive := damage.positive
  change 0 < Reparation.loss (Physical.Public.interpreter lifeSource.native.input) id damage.item damage.key at positive
  rw [source_input_is_the_original_registered_input] at positive
  exact exact damage.item listed damage.key.1 damage.key.2.1 damage.key.2.2 positive

private theorem own_requests (request : Request Bool Bool Bool Unit Unit)
    (listed : request ∈ signedRequests service) : OwnSignature lifeSource [] request := by
  refine ⟨every_original_person_keeps_actual_standing _, List.not_mem_nil, ?_⟩
  exact (by decide +kernel : ∀ req ∈ lifeWord, req.consents = []) request listed

private theorem own_inventory (item : ExecutionItem Bool Bool Bool Unit Unit)
    (listed : item ∈ Boundary.Actual.items lifeSource service) : OwnMaterial lifeSource [] item := by
  rw [inventory_exact] at listed
  refine ⟨⟨every_original_person_keeps_actual_standing _, List.not_mem_nil, ?_, ?_⟩, ?_⟩
  · exact (by decide +kernel : ∀ req ∈ material.rawItems before lifeWord, req.request.consents = []) item listed
  · change ∀ entry ∈ (Physical.Public.interpreter lifeSource.native.input).actualDebit item.before item.request,
      0 < entry.2 → entry.1.1 = item.request.signer
    rw [source_input_is_the_original_registered_input]
    exact (by decide +kernel : ∀ original ∈ material.rawItems before lifeWord,
      ∀ entry ∈ material.actualDebit original.before original.request,
        0 < entry.2 → entry.1.1 = original.request.signer) item listed
  · rw [source_input_is_the_original_registered_input]
    exact (by decide +kernel : ∀ original ∈ material.rawItems before lifeWord,
      supplied.law.Valid original.before original.request) item listed

private theorem deadline_exact : (initial.nextCut service).raw.clock = initial.deadline := by
  change (Quantities.Execution.endAt lifeSource lifePeriod).raw.clock = _
  rw [the_original_life_period_pays_its_actual_material_body]
  rfl

private theorem original_needs_are_paid : Quantities.Demand.Covers lifeSource lifePeriod := by
  have actual : Quantities.Execution.inventory lifeSource lifePeriod =
      (Physical.Public.interpreter lifeSource.native.input).rawItems lifeSource.raw lifeWord := by
    change Boundary.Actual.items lifeSource service = _
    rw [inventory_exact, source_input_is_the_original_registered_input,
      the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  apply (Quantities.Demand.covers_iff_original_floor_of_paid_inventory lifePeriod lifeWord
    ExecutionItem.index (by simpa using actual)).mpr
  exact (Quantities.Demand.primitive_covers_iff_original_floor lifeTrace).mp
    the_two_actual_life_payments_write_the_original_ledger.paid

private theorem timely_is_the_actual_paid_amount (cell : Bool × Use × Bool × ℚ) :
    initial.timely [] service cell = Quantities.Demand.delivered lifeSource lifePeriod cell.1 cell.2.1 cell.2.2.1 := by
  have eligible (item : ExecutionItem Bool Bool Bool Unit Unit)
      (listed : item ∈ Boundary.Actual.items lifeSource service) :
      decide (OwnMaterial lifeSource [] item) = true := decide_eq_true (own_inventory item listed)
  unfold Window.timely
  change (if (initial.nextCut service).raw.clock ≤ initial.deadline then
    (((Boundary.Actual.items lifeSource service).filter fun item => decide (OwnMaterial lifeSource [] item)).map
      fun item => flowAt (Optimality.Cost.actualPart lifeSource.native.handlerFace.rootRead
        item.before item.request (.use cell.2.1)) cell.1 cell.2.2.1).sum else 0) + 0 = _
  rw [if_pos deadline_exact.le, add_zero, List.filter_eq_self.mpr eligible,
    Quantities.Demand.delivered_is_from_original_inventory]
  rfl

theorem real_life_service_is_a_safe_paid_round :
    RoundGood lifeSource [] id initial lifePeriod [] := by
  refine ⟨?_, ⟨⟨no_original_foreign_debit, fun person _ => residents_still_stand person,
    fun _ => own_requests, fun _ => own_inventory, fun _ => deadline_exact.le, ?_⟩, trivial⟩, ?_, trivial⟩
  · intro empty
    have original : false ∈ Civil.protectedMembers lifeSource [] :=
      List.mem_filter.mpr ⟨every_original_person_keeps_actual_standing _, rfl⟩
    have resident := Window.includes_current_resident lifeSource [] initial original
    exact List.not_mem_nil (empty ▸ resident)
  · intro _ cell listed
    let cells := Boundary.floorCells lifeSource (initial.residents lifeSource [])
    have same := List.mem_dedup.mp listed
    change cell ∈ cells ++ cells ++ cells at same
    simp only [List.mem_append, or_self] at same
    have original := (List.mem_filter.mp same).1
    rw [timely_is_the_actual_paid_amount]
    exact original_needs_are_paid cell original
  · change lifeSource.raw.clock < ((initial.write service).current).raw.clock
    rw [Window.write_current]
    have paid := the_original_period_advances_one_actual_hour
    unfold Quantities.elapsed at paid
    change (initial.nextCut service).raw.clock - lifeSource.raw.clock = 1 at paid
    linarith

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers
