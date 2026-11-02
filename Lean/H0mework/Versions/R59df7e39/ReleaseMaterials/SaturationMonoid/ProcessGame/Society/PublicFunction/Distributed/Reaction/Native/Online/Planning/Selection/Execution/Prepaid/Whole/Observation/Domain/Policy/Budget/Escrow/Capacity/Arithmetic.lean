import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Ring.List
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota
open Institutions.Capitalism.Universal.Source.Program

theorem scaled_amount {Good : Type} [DecidableEq Good] (bundle : Bundle Good) (factor : ℚ) (good : Good) :
    amount Good (bundle.map fun entry => (entry.1,factor*entry.2)) good = factor*amount Good bundle good := by
  unfold amount
  simp only [List.map_map,Function.comp_def]
  simpa only [mul_ite,mul_zero] using
    (List.sum_map_mul_left (l := bundle) (r := factor) (f := fun entry => if entry.1 = good then entry.2 else 0))

theorem located_amount {Party Good : Type} [DecidableEq Party] [DecidableEq Good]
    (party : Party) (bundle : Bundle Good) (good : Good) :
    flowAt (locate party bundle) party good = amount Good bundle good := by
  simp [flowAt,locate,amount,List.map_map,Function.comp_def]

structure Item where
  stock : ℚ
  fee : ℚ
  positive : 0 < fee

def Item.limit (item : Item) : Nat := Nat.floor (item.stock/item.fee)

theorem Item.fits_iff (item : Item) (nonnegative : 0 ≤ item.stock) (count : Nat) :
    (count:ℚ)*item.fee ≤ item.stock ↔ count ≤ item.limit := by
  rw [←le_div_iff₀ item.positive]
  exact (Nat.le_floor_iff (div_nonneg nonnegative item.positive.le)).symm

def minimum (first : Nat) : List Nat → Nat
  | [] => first
  | head::tail => min head (minimum first tail)

theorem bounded_iff (first : Nat) (tail : List Nat) (count : Nat) :
    count ≤ minimum first tail ↔ count ≤ first ∧ ∀ limit ∈ tail,count ≤ limit := by
  induction tail with
  | nil => simp [minimum]
  | cons head tail ih =>
      constructor
      · intro bounded
        have both := Nat.le_min.mp bounded
        have previous := ih.mp both.2
        refine ⟨previous.1,?_⟩
        intro limit inside
        rcases List.mem_cons.mp inside with same | later
        · subst limit;exact both.1
        · exact previous.2 limit later
      · rintro ⟨initial,others⟩
        exact Nat.le_min.mpr ⟨others head List.mem_cons_self,ih.mpr ⟨initial,
          fun limit inside => others limit (List.mem_cons_of_mem head inside)⟩⟩

def capacity (first : Item) (tail : List Item) := minimum first.limit (tail.map Item.limit)

theorem capacity_exact (first : Item) (tail : List Item)
    (nonnegative : ∀ item ∈ first::tail,0 ≤ item.stock) (count : Nat) :
    count ≤ capacity first tail ↔ ∀ item ∈ first::tail,(count:ℚ)*item.fee ≤ item.stock := by
  rw [capacity,bounded_iff]
  constructor
  · rintro ⟨bound,others⟩ item inside
    rcases List.mem_cons.mp inside with same | later
    · subst item
      exact (first.fits_iff (nonnegative first List.mem_cons_self) count).mpr bound
    · exact (item.fits_iff (nonnegative item (List.mem_cons_of_mem first later)) count).mpr
        (others item.limit (List.mem_map.mpr ⟨item,later,rfl⟩))
  · intro all
    refine ⟨(first.fits_iff (nonnegative first List.mem_cons_self) count).mp (all first List.mem_cons_self),?_⟩
    intro limit inside
    obtain ⟨item,later,same⟩ := List.mem_map.mp inside
    subst limit
    exact (item.fits_iff (nonnegative item (List.mem_cons_of_mem first later)) count).mp
      (all item (List.mem_cons_of_mem first later))

theorem next_unit_exposes_a_real_stock_shortage (first : Item) (tail : List Item) :
    ∃ item ∈ first::tail,item.stock < ((capacity first tail+1:Nat):ℚ)*item.fee := by
  have selected : ∃ item ∈ first::tail,item.limit = capacity first tail := by
    induction tail with
    | nil => exact ⟨first,List.mem_cons_self,rfl⟩
    | cons head tail ih =>
      by_cases small : head.limit ≤ capacity first tail
      · exact ⟨head,List.mem_cons_of_mem first List.mem_cons_self,Nat.min_eq_left small |>.symm⟩
      · obtain ⟨item,inside,same⟩ := ih
        refine ⟨item,?_,?_⟩
        · rcases List.mem_cons.mp inside with original | later
          · subst item;exact List.mem_cons_self
          · exact List.mem_cons_of_mem first (List.mem_cons_of_mem head later)
        · exact same.trans (Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge small))).symm
  obtain ⟨item,inside,same⟩ := selected
  refine ⟨item,inside,?_⟩
  have bound := Nat.lt_floor_add_one (item.stock/item.fee)
  change item.stock/item.fee < (item.limit:ℚ)+1 at bound
  rw [same] at bound
  exact (div_lt_iff₀ item.positive).mp (by simpa only [Nat.cast_add,Nat.cast_one] using bound)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota
