import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Cycle

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Source.Program Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Installed (Port Raw Req scope liftRequest)
open Quantities

noncomputable section

def noControl : Raw → List Bool := fun _ => []

private theorem request_shape {request : Req} (listed : request ∈ period) :
    request = liftRequest Transition.Handoff.Consumers.Actual.production ∨
    request = liftRequest Transition.Handoff.Consumers.Actual.provision ∨
    request = liftRequest (Transition.Handoff.Consumers.Actual.life false) ∨
    request = liftRequest (Transition.Handoff.Consumers.Actual.life true) ∨
    request = liftRequest Transition.Handoff.Consumers.Actual.service := by
  simpa only [period, Transition.Handoff.Consumers.Actual.period, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] using listed

private theorem original_ordinary_ports (raw : Raw) (request : Req) (listed : request ∈ period) :
    law.operationAllowed raw request = true ∧
      ∀ port ∈ law.requiredPorts raw request, law.allowed raw.technology port request.signer = true := by
  rcases request_shape listed with rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨rfl, ?_⟩
    intro port required
    change port ∈ [Port.ordinary _] at required
    rcases List.mem_singleton.mp required with rfl
    rfl

private theorem the_literal_debits_have_their_own_signers (raw : Raw) (request : Req) (listed : request ∈ period) :
    ∀ entry ∈ material.debit raw request, entry.1.1 = request.signer := by
  rcases request_shape listed with rfl | rfl | rfl | rfl | rfl
  all_goals
    intro entry present
    first
    | exact (List.not_mem_nil present).elim
    | change entry ∈ [_] at present
      rcases List.mem_singleton.mp present with rfl
      rfl

private theorem the_same_debits_need_no_war_title (raw : Raw) (request : Req) (listed : request ∈ period)
    (physical : material.Valid raw request) : MandateExit.TitleFree base scope ⟨0, raw, request⟩ := by
  have permission := original_ordinary_ports (MandateExit.withoutWarTitle raw) request listed
  refine ⟨⟨⟨physical.1.1, permission.1⟩, fun port present => Or.inl (permission.2 port present), ?_⟩, ?_⟩
  · rcases request_shape listed with rfl | rfl | rfl | rfl | rfl <;> exact physical.2.2
  · rcases request_shape listed with rfl | rfl | rfl | rfl | rfl <;> exact id

theorem no_financial_question (item : Item) (listed : item.request ∈ period) :
    financialQuestions item = [] := by
  rcases item with ⟨index, raw, request⟩
  change request ∈ period at listed
  rcases request_shape listed with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem actual_request (n : Nat) (item : Item) (listed : item ∈ Boundary.Actual.items (readyCut (run n)) service) :
    item.request ∈ period := by
  rw [(body_paid (run n) n (stage n)).2] at listed
  have original := List.mem_map_of_mem (f := ExecutionItem.request) listed
  change item.request ∈ ((material.execute (materialAt n) 0 period).items.map ExecutionItem.request) at original
  rw [material.inventory_requests_exact] at original
  exact original

private theorem physical_item (n : Nat) (item : Item) (listed : item ∈ Boundary.Actual.items (readyCut (run n)) service) :
    material.Valid item.before item.request := by
  rw [(body_paid (run n) n (stage n)).2] at listed
  exact ((original_material_guard opening [] n).2.2.1 item listed).1

theorem each_item_lawful (n : Nat) (item : Item) (listed : item ∈ Boundary.Actual.items (readyCut (run n)) service) :
    law.Valid item.before item.request := by
  have physical := physical_item n item listed
  have permission := original_ordinary_ports item.before item.request (actual_request n item listed)
  exact ⟨⟨physical.1.1, permission.1⟩, fun port present => Or.inl (permission.2 port present), physical.2.2⟩

theorem each_item_title_free (n : Nat) (item : Item) (listed : item ∈ Boundary.Actual.items (readyCut (run n)) service) :
    MandateExit.TitleFree base scope item := by
  have free := the_same_debits_need_no_war_title item.before item.request
    (actual_request n item listed) (physical_item n item listed)
  rcases item with ⟨index, raw, request⟩
  exact free

theorem debit_owner (n : Nat) (item : Item) (listed : item ∈ Boundary.Actual.items (readyCut (run n)) service) :
    ∀ entry ∈ (Boundary.Actual.materialLaw (readyCut (run n))).actualDebit item.before item.request,
      entry.1.1 = item.request.signer := by
  have source := (ready_stage (run n) n (stage n)).input
  unfold Boundary.Actual.materialLaw
  rw [source]
  change ∀ entry ∈ material.actualDebit item.before item.request, entry.1.1 = item.request.signer
  rw [RawLaw.actualDebit, if_pos (physical_item n item listed)]
  exact the_literal_debits_have_their_own_signers _ _ (actual_request n item listed)

theorem each_item_is_self_paid (n : Nat) (item : Item)
    (listed : item ∈ Boundary.Actual.items (readyCut (run n)) service) : OwnMaterial (readyCut (run n)) [] item := by
  refine ⟨⟨standing_after n (Execution.drain (run n)) _, List.not_mem_nil,
    original_consents_empty _ (actual_request n item listed), fun entry inside _ => debit_owner n item listed entry inside⟩, ?_⟩
  rw [(ready_stage (run n) n (stage n)).input]
  exact each_item_lawful n item listed

theorem material_has_no_foreign_damage (n : Nat) (damage : Boundary.Actual.DamageAt (readyCut (run n)) service id) : False := by
  let cut := readyCut (run n)
  have actual := damage.actual_foreign_debit
  have controlled := actual.1
  have empty : flowAt ((physical cut).actualDebit damage.item.before damage.item.request) damage.key.1 damage.key.2.2 = 0 := by
    apply amount_zero_of_absent
    intro entry listed address
    have owner := debit_owner n damage.item damage.source_item entry listed
    exact controlled.1 ((congrArg Prod.fst address).symm.trans (owner.trans controlled.2.1))
  have net := nonpositive_actual_debit_is_nonpositive_net_debit cut damage.item damage.key.1 damage.key.2.2 empty.le
  have positive := damage.positive
  unfold Boundary.Actual.DamageAt.quantity Reparation.loss at positive
  rw [if_pos controlled] at positive
  change 0 < max 0 (netDebit cut damage.item damage.key.1 damage.key.2.2) at positive
  rw [max_eq_left net] at positive
  exact (lt_irrefl _ positive)

theorem no_other_bearer_asked (n : Nat) (item : Item)
    (listed : item ∈ Boundary.Actual.items (readyCut (run n)) service) :
    ∀ question ∈ questions (run n) item, question.1 = item.request.signer := by
  have same : physical (run n) = physical (readyCut (run n)) :=
    congrArg Physical.Public.interpreter ((stage n).input.trans (ready_stage (run n) n (stage n)).input.symm)
  intro question asked
  simp only [questions, List.mem_cons, List.mem_append, no_financial_question item (actual_request n item listed),
    List.not_mem_nil, or_false] at asked
  rcases asked with signature | debit
  · exact congrArg Prod.fst signature
  · obtain ⟨entry, original, selected⟩ := List.mem_filterMap.mp debit
    have initial : entry ∈ (physical (run n)).actualDebit item.before item.request := original
    rw [same] at initial
    have own := debit_owner n item listed entry initial
    dsimp only at selected
    split at selected
    · exact (congrArg Prod.fst (Option.some.inj selected)).symm.trans own
    · cases selected

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
