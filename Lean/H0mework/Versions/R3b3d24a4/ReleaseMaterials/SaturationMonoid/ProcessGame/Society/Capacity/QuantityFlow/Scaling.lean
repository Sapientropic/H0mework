import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Cut
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Integral
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

/-- The input denominations determine a finite grid. This grid is used in
the existence proof and need not be enumerated by the certificate producer. -/
def scale (network : Network L R) : ℕ :=
  (∏ slot, (network.need slot).den) * (∏ item, (network.capacity item).den)

theorem scale_positive (network : Network L R) : 0 < network.scale := by
  unfold scale
  exact Nat.mul_pos (CanonicallyOrderedAdd.prod_pos.mpr fun _ _ => Rat.den_pos _)
    (CanonicallyOrderedAdd.prod_pos.mpr fun _ _ => Rat.den_pos _)

private theorem need_den_dvd_scale (network : Network L R) (slot : L) :
    (network.need slot).den ∣ network.scale := by
  unfold scale
  exact (Finset.dvd_prod_of_mem (fun l => (network.need l).den) (Finset.mem_univ slot)).trans
    ⟨_, rfl⟩

private theorem capacity_den_dvd_scale (network : Network L R) (item : R) :
    (network.capacity item).den ∣ network.scale := by
  unfold scale
  exact (Finset.dvd_prod_of_mem (fun r => (network.capacity r).den) (Finset.mem_univ item)).trans
    ⟨_, mul_comm _ _⟩

def scaledAmount (denominator : ℕ) (amount : ℚ) : ℕ :=
  amount.num.toNat * (denominator / amount.den)

theorem scaled_amount_is_exact (denominator : ℕ) (amount : ℚ)
    (positive : 0 < denominator) (nonnegative : 0 ≤ amount) (divides : amount.den ∣ denominator) :
    (scaledAmount denominator amount : ℚ) / (denominator : ℚ) = amount := by
  have denPositive : 0 < (denominator : ℚ) := Nat.cast_pos.mpr positive
  have originalDen : (amount.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr amount.den_ne_zero
  have numNat : (amount.num.toNat : ℤ) = amount.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr nonnegative)
  have numRat : (amount.num.toNat : ℚ) = (amount.num : ℚ) := by
    rw [← Int.cast_natCast, numNat]
  have numEq : (amount.num : ℚ) = amount * (amount.den : ℚ) :=
    (div_eq_iff originalDen).mp amount.num_div_den
  apply (div_eq_iff denPositive.ne').mpr
  unfold scaledAmount
  calc
    ((amount.num.toNat * (denominator / amount.den) : ℕ) : ℚ) =
        (amount.num : ℚ) * ((denominator / amount.den : ℕ) : ℚ) := by rw [Nat.cast_mul, numRat]
    _ = amount * ((amount.den * (denominator / amount.den) : ℕ) : ℚ) := by
      rw [numEq, Nat.cast_mul, mul_assoc]
    _ = amount * (denominator : ℚ) := by rw [Nat.mul_div_cancel' divides]

theorem scaled_need_is_exact (network : Network L R) (slot : L) :
    (scaledAmount network.scale (network.need slot) : ℚ) / (network.scale : ℚ) = network.need slot :=
  scaled_amount_is_exact _ _ network.scale_positive (network.need_nonnegative slot) (network.need_den_dvd_scale slot)

theorem scaled_capacity_is_exact (network : Network L R) (item : R) :
    (scaledAmount network.scale (network.capacity item) : ℚ) / (network.scale : ℚ) =
      network.capacity item :=
  scaled_amount_is_exact _ _ network.scale_positive (network.capacity_nonnegative item)
    (network.capacity_den_dvd_scale item)

def unscale (network : Network L R) (allocation : L → R → ℕ) (slot : L) (item : R) : ℚ :=
  (allocation slot item : ℚ) / (network.scale : ℚ)

private theorem scaled_sum {A : Type*} (denominator : ℕ) (group : Finset A) (counts : A → ℕ) :
    ((∑ a ∈ group, counts a : ℕ) : ℚ) / (denominator : ℚ) =
      ∑ a ∈ group, (counts a : ℚ) / (denominator : ℚ) := by
  rw [Nat.cast_sum, Finset.sum_div]

/-- Every rational network has an attained primal and dual certificate.
The cut proof still bounds every rational allocation off the witness grid. -/
theorem exists_grid_certificate [DecidableEq L] [DecidableEq R] (network : Network L R) :
    ∃ (allocation : L → R → ℕ) (group : Finset L),
      (∀ slot item, allocation slot item ≤ scaledAmount network.scale (network.need slot)) ∧
      network.Admissible (network.unscale allocation) ∧
      total (network.unscale allocation) = network.cut group := by
  let demand := fun slot => scaledAmount network.scale (network.need slot)
  let capacity := fun item => scaledAmount network.scale (network.capacity item)
  obtain ⟨allocation, group, denied, rows, columns, meets⟩ :=
    Integral.exists_allocation_meets_original_cut demand capacity network.allows
  have positive : 0 < (network.scale : ℚ) := Nat.cast_pos.mpr network.scale_positive
  have edges (slot : L) (item : R) : allocation slot item ≤ demand slot := by
    apply le_trans (Finset.single_le_sum (f := allocation slot) (fun _ _ => Nat.zero_le _) (Finset.mem_univ item))
    exact rows slot
  have admissible : network.Admissible (network.unscale allocation) := by
    refine ⟨fun slot item => ⟨div_nonneg (Nat.cast_nonneg _) positive.le, ?_⟩, ?_, ?_⟩
    · intro forbidden
      simp [unscale, denied slot item forbidden]
    · intro slot
      have bound : ((∑ item, allocation slot item : ℕ) : ℚ) ≤ (demand slot : ℚ) := by
        exact_mod_cast rows slot
      have smaller := div_le_div_of_nonneg_right bound positive.le
      rw [scaled_sum] at smaller
      exact smaller.trans_eq (network.scaled_need_is_exact slot)
    · intro item
      have bound : ((∑ slot, allocation slot item : ℕ) : ℚ) ≤ (capacity item : ℚ) := by
        exact_mod_cast columns item
      have smaller := div_le_div_of_nonneg_right bound positive.le
      rw [scaled_sum] at smaller
      exact smaller.trans_eq (network.scaled_capacity_is_exact item)
  have compatible : Integral.neighbours network.allows group = network.neighbours group := by
    ext item
    simp [Integral.neighbours]
  rw [compatible] at meets
  have demandSum (slots : Finset L) :
      ((∑ slot ∈ slots, demand slot : ℕ) : ℚ) / (network.scale : ℚ) = network.demandOf slots := by
    rw [scaled_sum, demandOf]
    exact Finset.sum_congr rfl fun slot _ => network.scaled_need_is_exact slot
  have supplySum (items : Finset R) :
      ((∑ item ∈ items, capacity item : ℕ) : ℚ) / (network.scale : ℚ) = network.supplyOf items := by
    rw [scaled_sum, supplyOf]
    exact Finset.sum_congr rfl fun item _ => network.scaled_capacity_is_exact item
  have allocationSum :
      ((∑ slot, ∑ item, allocation slot item : ℕ) : ℚ) / (network.scale : ℚ) =
        total (network.unscale allocation) := by
    rw [scaled_sum, total]
    exact Finset.sum_congr rfl fun slot _ => scaled_sum network.scale _ (allocation slot)
  have rational :
      ((∑ slot, demand slot : ℕ) : ℚ) +
          ((∑ item ∈ network.neighbours group, capacity item : ℕ) : ℚ) ≤
        ((∑ slot, ∑ item, allocation slot item : ℕ) : ℚ) +
          ((∑ slot ∈ group, demand slot : ℕ) : ℚ) := by
    exact_mod_cast meets
  have lower := div_le_div_of_nonneg_right rational positive.le
  rw [add_div, add_div, demandSum, supplySum, allocationSum, demandSum] at lower
  refine ⟨allocation, group, edges, admissible, le_antisymm
    (network.allocation_is_bounded_by_every_original_cut admissible group) ?_⟩
  unfold cut gap
  linarith only [lower]

theorem exists_certificate [DecidableEq L] [DecidableEq R] (network : Network L R) :
    Nonempty (network.Certificate) := by
  obtain ⟨allocation, group, _, admitted, exactCut⟩ := network.exists_grid_certificate
  exact ⟨⟨network.unscale allocation, group, admitted, exactCut⟩⟩

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network
