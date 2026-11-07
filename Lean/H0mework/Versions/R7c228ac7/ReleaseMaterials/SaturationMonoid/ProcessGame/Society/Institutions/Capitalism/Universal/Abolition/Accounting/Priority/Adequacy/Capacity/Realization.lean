import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Facts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity

open Source.Program Innovation
open Exit.Necessity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

theorem original_inventory_is_valid
    (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (conditions : Primitive.Conditions law (Primitive.execute law initial 0 word).items) :
    ∀ item ∈ law.rawItems initial word, law.Valid item.before item.request := by
  have same := Primitive.all_primitive_effects_become_the_same_actual_execution law initial 0 word conditions
  intro item member
  rw [RawLaw.rawItems,same] at member
  exact conditions.actual_validity_is_generated item member

omit [DecidableEq Instrument] in
private theorem source_recognized (cohort : List Party) (victims : List (Party × Good))
    (word : RawEvent Party Good Port Technology Instrument)
    (material : ∀ request ∈ word, Responsibility.Family.materialOperation cohort victims request) :
    Responsibility.Family.inspectSource cohort victims word = .accepted material := by
  induction word with
  | nil => rfl
  | cons request rest inherited =>
    simp only [Responsibility.Family.inspectSource,dif_pos (material request List.mem_cons_self)]
    rw [inherited (fun next member => material next (List.mem_cons_of_mem request member))]

omit [DecidableEq Instrument] in
private theorem inventory_recognized (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument))
    (valid : ∀ item ∈ items, law.Valid item.before item.request) :
    Responsibility.inspectMaterial law items = .accepted valid := by
  induction items with
  | nil => rfl
  | cons item rest inherited =>
    simp only [Responsibility.inspectMaterial,dif_pos (valid item List.mem_cons_self)]
    rw [inherited (fun next member => valid next (List.mem_cons_of_mem item member))]

theorem raw_bill_becomes_actual_paid_service
    (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (valid : ∀ item ∈ law.rawItems initial word, law.Valid item.before item.request)
    (actor : Party) (goods : Bundle Good) (purpose : Use) :
    BundlePaid law initial word actor goods purpose ↔ Bill word actor goods purpose := by
  constructor
  · intro paid
    rcases paid with empty | ⟨item,member,_valid,matched⟩
    · exact .inl empty
    · refine .inr ⟨item.request,?_,matched⟩
      have requested : item.request ∈ (law.rawItems initial word).map ExecutionItem.request := List.mem_map.mpr ⟨item,member,rfl⟩
      rwa [RawLaw.rawItems,RawLaw.inventory_requests_exact] at requested
  · intro bill
    rcases bill with empty | ⟨request,member,matched⟩
    · exact .inl empty
    · have requested : request ∈ (law.rawItems initial word).map ExecutionItem.request := by
        rw [RawLaw.rawItems,RawLaw.inventory_requests_exact]
        exact member
      obtain ⟨item,inside,same⟩ := List.mem_map.mp requested
      exact .inr ⟨item,inside,valid item inside,same ▸ matched⟩

variable {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

theorem source_resources_are_recognized_by_the_original_native_attempt
    (conditions : Primitive.Conditions law (Primitive.execute law state.raw 0 word).items)
    (material : ∀ request ∈ word, Responsibility.Family.materialOperation
      (Responsibility.controllerCohort source past nature response)
      (Responsibility.Family.positiveScope source past nature response) request) :
    Responsibility.Family.State.attempt claim state law word =
      .accepted (original_inventory_is_valid law state.raw word conditions) material := by
  unfold Responsibility.Family.State.attempt Responsibility.Family.inspectAttempt
  rw [source_recognized _ _ _ material,inventory_recognized _ _ (original_inventory_is_valid law state.raw word conditions)]

def residual (key : Party × Good) : ℚ := max 0 (state.remaining key - max 0
  (Primitive.net law (Primitive.execute law state.raw 0 word).items key.1 key.2))

theorem primitive_residual_is_the_original_actual_remaining
    (conditions : Primitive.Conditions law (Primitive.execute law state.raw 0 word).items)
    (material : ∀ request ∈ word, Responsibility.Family.materialOperation
      (Responsibility.controllerCohort source past nature response)
      (Responsibility.Family.positiveScope source past nature response) request) (key : Party × Good) :
    (Responsibility.Family.State.advance claim state law word).remaining key = residual claim state law word key := by
  have actual := Primitive.all_primitive_effects_become_the_same_actual_execution law state.raw 0 word conditions
  have balance := Primitive.symbolic_stock_is_exactly_the_original_primitive_net law state.raw 0 word key.1 key.2
  change max 0 (state.remaining key - (Responsibility.Family.State.attempt claim state law word).credit key) = _
  rw [source_resources_are_recognized_by_the_original_native_attempt claim state law word conditions material]
  simp only [Responsibility.Family.Attempt.credit,RawLaw.next,actual,residual]
  congr 2
  congr 1
  linarith

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity
