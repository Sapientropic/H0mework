import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

/-! Uniform functional realization of an original lawful word under the
existing open-admission interpretation.  This computes no new technology,
resources or programme and does not install a migration in the original root. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions

open Source.Program Exit

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

/-- The original legality of the entire trace supplies the authorization
of its open counterpart.  No successful counterpart is a premise. -/
theorem original_authorizes_open_trace (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (legal : ∀ item ∈ (law.execute current index word).items, law.Valid item.before item.request) :
    ∀ item ∈ ((PublicFunction.physicalLaw law).execute current index word).items,
      law.Valid item.before item.request := by
  induction word generalizing current index with
  | nil => simp only [RawLaw.execute, List.not_mem_nil, false_implies, implies_true]
  | cons request tail ih =>
      have front := legal ⟨index, current, request⟩ List.mem_cons_self
      have openFront := PublicFunction.valid_physical law current request front
      have same : (PublicFunction.physicalLaw law).step current request = law.step current request := by
        simp only [RawLaw.step, if_pos openFront, if_pos front]
        rfl
      intro item member
      simp only [RawLaw.execute, List.mem_cons, same] at member
      rcases member with sameItem | later
      · subst item
        exact front
      · exact ih (law.step current request) (index + 1)
          (fun item present => legal item (List.mem_cons_of_mem _ present)) item later

theorem original_generates_open_execution (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (legal : ∀ item ∈ (law.execute current index word).items, law.Valid item.before item.request) :
    (PublicFunction.physicalLaw law).execute current index word = law.execute current index word := by
  have authorized := original_authorizes_open_trace law current index word legal
  exact (PublicFunction.execute_physical_of_authorized law current index word
    (fun item present => PublicFunction.valid_physical law item.before item.request (authorized item present))
    authorized).symm

variable (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (legal : ∀ item ∈ law.rawItems current word, law.Valid item.before item.request)

include legal in
theorem original_items_and_before_states_are_preserved :
    (PublicFunction.physicalLaw law).rawItems current word = law.rawItems current word :=
  congrArg ExecutionResult.items (original_generates_open_execution law current 0 word legal)

include legal in
theorem original_full_next_is_preserved :
    (PublicFunction.physicalLaw law).next current word = law.next current word := by
  unfold RawLaw.next
  rw [original_generates_open_execution law current 0 word legal]
  rfl

include legal in
theorem original_word_is_valid_in_open_interpretation :
    ∀ item ∈ (PublicFunction.physicalLaw law).rawItems current word,
      (PublicFunction.physicalLaw law).Valid item.before item.request := by
  rw [original_items_and_before_states_are_preserved law current word legal]
  exact fun item present => PublicFunction.valid_physical law item.before item.request (legal item present)

include legal in
theorem original_payment_bundle_is_preserved (person : Party) (goods : Bundle Good) (purpose : Use) :
    Necessity.BundlePaid (PublicFunction.physicalLaw law) current word person goods purpose ↔
      Necessity.BundlePaid law current word person goods purpose := by
  constructor
  · rintro (empty | ⟨item, present, _openLegal, matched⟩)
    · exact Or.inl empty
    · rw [original_items_and_before_states_are_preserved law current word legal] at present
      exact Or.inr ⟨item, present, legal item present, matched⟩
  · rintro (empty | ⟨item, present, accepted, matched⟩)
    · exact Or.inl empty
    · exact Or.inr ⟨item,
        (original_items_and_before_states_are_preserved law current word legal).symm ▸ present,
        PublicFunction.valid_physical law item.before item.request accepted, matched⟩

include legal in
theorem original_needs_and_maintenance_are_preserved (members : List Party) :
    Necessity.AllNeedsPaid (PublicFunction.physicalLaw law) current members word ↔
      Necessity.AllNeedsPaid law current members word := by
  constructor <;> intro paid person present
  · exact ⟨(original_payment_bundle_is_preserved law current word legal person _ .necessity).mp (paid person present).1,
      (original_payment_bundle_is_preserved law current word legal person _ .maintenance).mp (paid person present).2⟩
  · exact ⟨(original_payment_bundle_is_preserved law current word legal person _ .necessity).mpr (paid person present).1,
      (original_payment_bundle_is_preserved law current word legal person _ .maintenance).mpr (paid person present).2⟩

include legal in
/-- The existing service-task consumer also sees exactly its old beneficiaries,
bundles and clock window.  A source need cannot be renamed out of this result. -/
theorem original_service_task_is_preserved (task : PublicFunction.PublicTaskSpec Party Good) :
    PublicFunction.ServiceAdequate (PublicFunction.physicalLaw law) current task word ↔
      PublicFunction.ServiceAdequate law current task word := by
  unfold PublicFunction.ServiceAdequate
  rw [original_full_next_is_preserved law current word legal]
  constructor <;> rintro ⟨earliest, deadline, paid⟩
  · exact ⟨earliest, deadline, fun slot present =>
      (original_payment_bundle_is_preserved law current word legal slot.bearer slot.goods slot.purpose).mp
        (paid slot present)⟩
  · exact ⟨earliest, deadline, fun slot present =>
      (original_payment_bundle_is_preserved law current word legal slot.bearer slot.goods slot.purpose).mpr
        (paid slot present)⟩

include legal in
theorem original_operations_are_preserved :
    ((PublicFunction.physicalLaw law).rawItems current word).map (fun item => item.request.operation) =
      (law.rawItems current word).map (fun item => item.request.operation) := by
  rw [original_items_and_before_states_are_preserved law current word legal]

#print axioms original_generates_open_execution
#print axioms original_full_next_is_preserved
#print axioms original_needs_and_maintenance_are_preserved
#print axioms original_service_task_is_preserved

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions
