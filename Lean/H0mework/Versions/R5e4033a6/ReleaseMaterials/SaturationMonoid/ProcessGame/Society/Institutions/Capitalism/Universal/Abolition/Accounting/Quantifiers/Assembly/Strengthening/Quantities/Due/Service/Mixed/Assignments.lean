import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Matching.Full
import Mathlib.Data.List.Dedup

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- Enumerate full assignments by consuming one available ordinal per slot. -/
def assignments (legal : L → R → Bool) : List L → List R → List (Finset (L × R))
  | [], _ => [∅]
  | slot :: later, items =>
      (items.filter (legal slot)).flatMap fun item =>
        (assignments legal later (items.filter fun other => decide (other ≠ item))).map
          fun rest => insert (slot, item) rest

def ExactAssignment (legal : L → R → Bool) (slots : List L) (items : List R)
    (matching : Finset (L × R)) : Prop :=
  matching.image Prod.fst = slots.toFinset ∧
    (∀ edge ∈ matching, edge.2 ∈ items ∧ legal edge.1 edge.2 = true) ∧
    Set.InjOn Prod.fst (matching : Set (L × R)) ∧ Set.InjOn Prod.snd (matching : Set (L × R))

private theorem injective_after_fresh_endpoint {A B : Type*} [DecidableEq A]
    (project : A → B) (candidate : A) (rest : Finset A) (injective : Set.InjOn project (rest : Set A))
    (fresh : ∀ edge ∈ rest, project edge ≠ project candidate) :
    Set.InjOn project ((insert candidate rest : Finset A) : Set A) := by
  have notMember : candidate ∉ (rest : Set A) := fun inside => fresh candidate inside rfl
  rw [Finset.coe_insert, Set.injOn_insert notMember]
  exact ⟨injective, fun ⟨edge, inside, same⟩ => fresh edge inside same⟩

private theorem insert_preserves_exactness (legal : L → R → Bool)
    {slot : L} {later : List L} {item : R} {items : List R}
    {rest : Finset (L × R)} (freshSlot : slot ∉ later)
    (chosen : item ∈ items.filter (legal slot))
    (exactRest : ExactAssignment legal later (items.filter fun other => decide (other ≠ item)) rest) :
    ExactAssignment legal (slot :: later) items (insert (slot, item) rest) := by
  obtain ⟨image, edges, leftInj, rightInj⟩ := exactRest
  refine ⟨by rw [Finset.image_insert, image, List.toFinset_cons], ?_, ?_, ?_⟩
  · intro edge present
    rcases Finset.mem_insert.mp present with rfl | fromRest
    · exact List.mem_filter.mp chosen
    · exact ⟨(List.mem_filter.mp (edges edge fromRest).1).1, (edges edge fromRest).2⟩
  · apply injective_after_fresh_endpoint Prod.fst _ _ leftInj
    intro edge present same
    change edge.1 = slot at same
    apply freshSlot
    apply List.mem_toFinset.mp
    rw [← image, ← same]
    exact Finset.mem_image.mpr ⟨edge, present, rfl⟩
  · apply injective_after_fresh_endpoint Prod.snd _ _ rightInj
    intro edge present
    exact of_decide_eq_true (List.mem_filter.mp (edges edge present).1).2

private theorem erase_preserves_exactness (legal : L → R → Bool)
    {slot : L} {later : List L} {item : R} {items : List R}
    {matching : Finset (L × R)} (freshSlot : slot ∉ later) (selected : (slot, item) ∈ matching)
    (exactFull : ExactAssignment legal (slot :: later) items matching) :
    ExactAssignment legal later (items.filter fun other => decide (other ≠ item)) (matching.erase (slot, item)) := by
  obtain ⟨image, edges, leftInj, rightInj⟩ := exactFull
  have stillOriginal : matching.erase (slot, item) ⊆ matching := Finset.erase_subset _ _
  refine ⟨?_, ?_, leftInj.mono stillOriginal, rightInj.mono stillOriginal⟩
  · ext actual
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨edge, kept, rfl⟩
      have original : edge.1 ∈ (slot :: later).toFinset := by
        rw [← image]
        exact Finset.mem_image.mpr ⟨edge, stillOriginal kept, rfl⟩
      rcases List.mem_cons.mp (List.mem_toFinset.mp original) with same | rest
      · exact (Finset.ne_of_mem_erase kept (leftInj (stillOriginal kept) selected same)).elim
      · exact rest
    · intro rest
      have original : actual ∈ matching.image Prod.fst := by
        rw [image, List.mem_toFinset]
        exact List.mem_cons_of_mem _ rest
      obtain ⟨edge, present, same⟩ := Finset.mem_image.mp original
      refine ⟨edge, Finset.mem_erase.mpr ⟨?_, present⟩, same⟩
      rintro rfl
      change slot = actual at same
      exact freshSlot (same.symm ▸ rest)
  · intro edge kept
    have original := edges edge (stillOriginal kept)
    refine ⟨List.mem_filter.mpr ⟨original.1, decide_eq_true ?_⟩, original.2⟩
    exact fun same => Finset.ne_of_mem_erase kept (rightInj (stillOriginal kept) selected same)

theorem assignments_are_exact (legal : L → R → Bool) (slots : List L) (items : List R)
    (distinct : slots.Nodup) (matching : Finset (L × R)) :
    matching ∈ assignments legal slots items ↔ ExactAssignment legal slots items matching := by
  induction slots generalizing items matching with
  | nil =>
    constructor
    · intro empty
      have same : matching = ∅ := by simpa [assignments] using empty
      subst matching
      simp [ExactAssignment, Set.InjOn]
    · intro exactFull
      have empty : matching = ∅ := Finset.image_eq_empty.mp exactFull.1
      simp [assignments, empty]
  | cons slot later previous =>
    have fresh := (List.nodup_cons.mp distinct).1
    have noDuplicate := (List.nodup_cons.mp distinct).2
    constructor
    · intro found
      obtain ⟨item, eligible, remaining⟩ := List.mem_flatMap.mp found
      obtain ⟨rest, fromRest, rfl⟩ := List.mem_map.mp remaining
      exact insert_preserves_exactness legal fresh eligible ((previous _ noDuplicate _).mp fromRest)
    · intro exactFull
      have slotCovered : slot ∈ matching.image Prod.fst := by
        rw [exactFull.1, List.mem_toFinset]
        exact List.mem_cons_self
      obtain ⟨⟨actual, item⟩, present, same⟩ := Finset.mem_image.mp slotCovered
      change actual = slot at same
      subst actual
      have eligible : item ∈ items.filter (legal slot) := List.mem_filter.mpr (exactFull.2.1 _ present)
      have remaining := erase_preserves_exactness legal fresh present exactFull
      apply List.mem_flatMap.mpr
      refine ⟨item, eligible, List.mem_map.mpr ⟨matching.erase (slot, item), ?_, Finset.insert_erase present⟩⟩
      exact (previous _ noDuplicate _).mpr remaining

open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

def eligibility {L R : Type*} (geom : CanonicalBipartiteFeasibility L R) (slot : L) (item : R) : Bool :=
  @decide (geom.Feasible slot item) (geom.feasibleDecidable slot item)

@[simp] theorem eligibility_eq_true {L R : Type*} (geom : CanonicalBipartiteFeasibility L R)
    (slot : L) (item : R) : eligibility geom slot item = true ↔ geom.Feasible slot item := by
  simp only [eligibility, decide_eq_true_eq]

theorem original_and_full_iff_assignment {L R : Type*} [DecidableEq L] [DecidableEq R]
    (geom : CanonicalBipartiteFeasibility L R) (slots : List L) (items : List R)
    (left : slots.toFinset = geom.leftCarrier) (right : items.toFinset = geom.rightCarrier)
    (matching : Finset (L × R)) :
    (matching ∈ geom.matchings ∧ matching.card = geom.leftCarrier.card) ↔
      ExactAssignment (eligibility geom) slots items matching := by
  classical
  constructor
  · rintro ⟨member, full⟩
    have laws := geom.matching_laws member
    have allowed (edge : L × R) (present : edge ∈ matching) :=
      (geom.mem_edgeCarrier_iff edge).mp (geom.matching_subset_edgeCarrier member present)
    have subset : matching.image Prod.fst ⊆ geom.leftCarrier := by
      intro slot present
      obtain ⟨edge, listed, rfl⟩ := Finset.mem_image.mp present
      exact (allowed edge listed).1
    have count : (matching.image Prod.fst).card = geom.leftCarrier.card :=
      (Finset.card_image_of_injOn laws.1).trans full
    have exactLeft := (Finset.eq_of_subset_of_card_le subset count.ge).trans left.symm
    refine ⟨exactLeft, fun edge listed => ?_, laws.1, laws.2⟩
    have native := allowed edge listed
    exact ⟨List.mem_toFinset.mp (right.symm ▸ native.2.1), (eligibility_eq_true geom _ _).mpr native.2.2⟩
  · rintro ⟨exactLeft, edges, leftInj, rightInj⟩
    constructor
    · unfold CanonicalBipartiteFeasibility.matchings
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, leftInj, rightInj⟩
      intro edge present
      have allowed := edges edge present
      have leftPresent : edge.1 ∈ geom.leftCarrier :=
        exactLeft.trans left ▸ Finset.mem_image.mpr ⟨edge, present, rfl⟩
      exact (geom.mem_edgeCarrier_iff edge).mpr
        ⟨leftPresent, right ▸ List.mem_toFinset.mpr allowed.1, (eligibility_eq_true geom _ _).mp allowed.2⟩
    · rw [← Finset.card_image_of_injOn leftInj, exactLeft, left]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
