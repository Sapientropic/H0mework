import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Classification
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Finite folds of the source's original effect items.  The first positive
quantity is located by a real finite scan, so a scalar deficit returns its
original item and responsibility rather than a freely selected old row. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u v

namespace EffectFold

variable {Item : Type u} {Quantity : Type v} [AddCommMonoid Quantity] [LinearOrder Quantity]
  [IsOrderedCancelAddMonoid Quantity]

def total (items : List Item) (amount : Item → Quantity) : Quantity := (items.map amount).sum

private theorem positive_tail (head : Item) (tail : List Item) (amount : Item → Quantity)
    (positive : 0 < total (head :: tail) amount) (notHead : ¬ 0 < amount head) :
    0 < total tail amount := by
  by_contra notTail
  have bound : amount head + total tail amount ≤ 0 := by
    calc
      amount head + total tail amount ≤ 0 + 0 :=
        add_le_add (le_of_not_gt notHead) (le_of_not_gt notTail)
      _ = 0 := zero_add 0
  exact (not_lt_of_ge bound) positive

def firstPositive (amount : Item → Quantity) : (items : List Item) →
    0 < total items amount → { item : Item // item ∈ items ∧ 0 < amount item }
  | [], positive => False.elim ((lt_irrefl (0 : Quantity)) positive)
  | head :: tail, positive =>
      if atHead : 0 < amount head then ⟨head, List.mem_cons_self, atHead⟩
      else
        let found := firstPositive amount tail (positive_tail head tail amount positive atHead)
        ⟨found.val, List.mem_cons_of_mem head found.property.1, found.property.2⟩

theorem total_nonnegative (items : List Item) (amount : Item → Quantity)
    (nonnegative : ∀ item ∈ items, 0 ≤ amount item) : 0 ≤ total items amount := by
  induction items with
  | nil => exact le_refl 0
  | cons head tail ih =>
      exact add_nonneg (nonnegative head List.mem_cons_self)
        (ih (fun item member => nonnegative item (List.mem_cons_of_mem _ member)))

end EffectFold

namespace ExistingSocietyFace.RawEffectLaw

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource N V} {society : ExistingSocietyFace source}
  {Good Quantity : Type u} [AddCommMonoid Quantity] [LinearOrder Quantity]
  [IsOrderedCancelAddMonoid Quantity]
  (raw : society.RawEffectLaw Good Quantity)
  {current : V.Current} (event : ContinuingEventAt source current)
  (R : society.Relation event → Prop) [DecidablePred R]

def acquired (item : OriginalInventoryItem event) (good : Good) : Quantity :=
  raw.rawAcquired event item good

def dependent (item : OriginalInventoryItem event) (good : Good) : Quantity :=
  match raw.decode event item with
  | some effect => effect.dependentAmount society event R good
  | none => 0

def independent (item : OriginalInventoryItem event) (good : Good) : Quantity :=
  match raw.decode event item with
  | some effect => effect.independentAmount society event R good
  | none => 0

def pending (item : OriginalInventoryItem event) (good : Good) : Quantity :=
  match raw.decode event item with
  | some effect => effect.pendingAmount society event R good
  | none => raw.rawAcquired event item good

omit [IsOrderedCancelAddMonoid Quantity] in
theorem item_partition (item : OriginalInventoryItem event) (good : Good) :
    raw.dependent event R item good + raw.independent event R item good +
        raw.pending event R item good = raw.acquired event item good := by
  unfold dependent independent pending acquired
  cases selected : raw.decode event item with
  | none => simp
  | some effect =>
      rw [← raw.decoded_exact event item effect selected]
      exact effect.partition_exact society event R good

omit [IsOrderedCancelAddMonoid Quantity] in
theorem item_nonnegative (item : OriginalInventoryItem event) (good : Good)
    (nonnegative : 0 ≤ raw.acquired event item good) :
    0 ≤ raw.dependent event R item good ∧ 0 ≤ raw.independent event R item good ∧
      0 ≤ raw.pending event R item good := by
  unfold dependent independent pending
  unfold acquired at nonnegative
  cases selected : raw.decode event item with
  | none => simpa using nonnegative
  | some effect =>
      rw [← raw.decoded_exact event item effect selected] at nonnegative
      exact effect.amounts_nonnegative society event R good nonnegative

omit [IsOrderedCancelAddMonoid Quantity] in
theorem total_partition (items : List (OriginalInventoryItem event)) (good : Good) :
    EffectFold.total items (fun item => raw.dependent event R item good) +
        EffectFold.total items (fun item => raw.independent event R item good) +
        EffectFold.total items (fun item => raw.pending event R item good) =
      EffectFold.total items (fun item => raw.acquired event item good) := by
  induction items with
  | nil => simp [EffectFold.total]
  | cons head tail ih =>
      simp only [EffectFold.total, List.map_cons, List.sum_cons]
      calc
        (raw.dependent event R head good + _) + (raw.independent event R head good + _) +
            (raw.pending event R head good + _) =
          (raw.dependent event R head good + raw.independent event R head good +
            raw.pending event R head good) +
          (EffectFold.total tail (fun item => raw.dependent event R item good) +
            EffectFold.total tail (fun item => raw.independent event R item good) +
            EffectFold.total tail (fun item => raw.pending event R item good)) := by ac_rfl
        _ = _ := by
          rw [raw.item_partition event R head good, ih]
          rfl

theorem positive_dependent_original_item (items : List (OriginalInventoryItem event))
    (good : Good)
    (positive : 0 < EffectFold.total items (fun item => raw.dependent event R item good)) :
    ∃ item ∈ items, ∃ effect : society.AcquisitionEffect event Good Quantity item,
      raw.decode event item = some effect ∧ effect.DependentPath society event R := by
  let found := EffectFold.firstPositive (fun item => raw.dependent event R item good) items positive
  have atItem := found.property.2
  unfold dependent at atItem
  cases selected : raw.decode event found.val with
  | none => simp only [selected] at atItem; exact False.elim ((lt_irrefl (0 : Quantity)) atItem)
  | some effect =>
      simp only [selected] at atItem
      exact ⟨found.val, found.property.1, effect, selected,
        effect.positive_dependent_has_actual_path society event R good atItem⟩

def pendingBearer (items : List (OriginalInventoryItem event)) (good : Good)
    (positive : 0 < EffectFold.total items (fun item => raw.pending event R item good)) :
    OpenResponsibilityAt N (source.source.toRootSource.account.supportOf event.val) :=
  originalRow event
    (EffectFold.firstPositive (fun item => raw.pending event R item good) items positive).val

theorem pendingBearer_original_item (items : List (OriginalInventoryItem event)) (good : Good)
    (positive : 0 < EffectFold.total items (fun item => raw.pending event R item good)) :
    ∃ item ∈ items, raw.pendingBearer event R items good positive = originalRow event item ∧
      0 < raw.pending event R item good := by
  let found := EffectFold.firstPositive (fun item => raw.pending event R item good) items positive
  exact ⟨found.val, found.property.1, rfl, found.property.2⟩

end ExistingSocietyFace.RawEffectLaw

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source
