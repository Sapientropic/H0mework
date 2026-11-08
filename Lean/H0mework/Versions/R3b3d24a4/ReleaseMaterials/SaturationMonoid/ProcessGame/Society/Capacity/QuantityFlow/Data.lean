import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

open scoped BigOperators

/-- A finite material allocation between original demand addresses and
actual supply addresses. The edge bit is computed from the owning law. -/
structure Network (L R : Type*) where
  need : L → ℚ
  capacity : R → ℚ
  allows : L → R → Bool
  need_nonnegative : ∀ slot, 0 ≤ need slot
  capacity_nonnegative : ∀ item, 0 ≤ capacity item

namespace Network

variable {L R : Type*} [Fintype L] [Fintype R]

def rowTotal (allocation : L → R → ℚ) (slot : L) : ℚ := ∑ item, allocation slot item

def columnTotal (allocation : L → R → ℚ) (item : R) : ℚ := ∑ slot, allocation slot item

def total (allocation : L → R → ℚ) : ℚ := ∑ slot, rowTotal allocation slot

def Admissible (network : Network L R) (allocation : L → R → ℚ) : Prop :=
  (∀ slot item, 0 ≤ allocation slot item ∧ (network.allows slot item = false → allocation slot item = 0)) ∧
    (∀ slot, rowTotal allocation slot ≤ network.need slot) ∧
    (∀ item, columnTotal allocation item ≤ network.capacity item)

instance (network : Network L R) (allocation : L → R → ℚ) :
    Decidable (network.Admissible allocation) := by
  unfold Admissible
  infer_instance

theorem zero_is_admissible (network : Network L R) : network.Admissible (fun _ _ => 0) := by
  refine ⟨fun _ _ => ⟨le_rfl, fun _ => rfl⟩, ?_, ?_⟩
  · intro slot
    simpa [rowTotal] using network.need_nonnegative slot
  · intro item
    simpa [columnTotal] using network.capacity_nonnegative item

def demandOf (network : Network L R) (group : Finset L) : ℚ :=
  ∑ slot ∈ group, network.need slot

def supplyOf (network : Network L R) (items : Finset R) : ℚ :=
  ∑ item ∈ items, network.capacity item

def neighbours (network : Network L R) (group : Finset L) : Finset R :=
  Finset.univ.filter fun item => ∃ slot ∈ group, network.allows slot item = true

omit [Fintype L] in
@[simp] theorem mem_neighbours (network : Network L R) (group : Finset L) (item : R) :
    item ∈ network.neighbours group ↔ ∃ slot ∈ group, network.allows slot item = true := by
  simp [neighbours]

def gap (network : Network L R) (group : Finset L) : ℚ :=
  network.demandOf group - network.supplyOf (network.neighbours group)

def cut (network : Network L R) (group : Finset L) : ℚ :=
  network.demandOf Finset.univ - network.gap group

def Complete (network : Network L R) (allocation : L → R → ℚ) : Prop :=
  network.Admissible allocation ∧ ∀ slot, rowTotal allocation slot = network.need slot

end Network

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
