import H0mework.Arithmetic.GoldbachFourier.Cyclic

/-!
# Natural-window finite Fourier identity

The cyclic theorem in `FiniteFourier` is connected here to the actual natural
window `1 ≤ a < target`.  Modulus `target + 1` contains every endpoint and the
target residue without wrap; residues `0` and `target` receive zero weight.
-/

noncomputable section

open Finset ZMod
open scoped BigOperators ZMod

namespace GoldbachPrimePairTrace

instance goldbachWindowModulusNeZero (target : ℕ) : NeZero (target + 1) :=
  ⟨Nat.succ_ne_zero target⟩

def naturalWindowCyclicWeight
    (weight : ℕ → ℂ) (target : ℕ) : ZMod (target + 1) → ℂ :=
  fun x => if x.val ∈ Finset.Ico 1 target then weight x.val else 0

private theorem target_cast_val (target : ℕ) :
    (target : ZMod (target + 1)).val = target := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (Nat.lt_succ_self target)

private theorem naturalWindowCyclicWeight_pair
    (weight : ℕ → ℂ) (target : ℕ) (x : ZMod (target + 1))
    (hx : x.val ∈ Finset.Ico 1 target) :
    naturalWindowCyclicWeight weight target x *
        naturalWindowCyclicWeight weight target
          ((target : ZMod (target + 1)) - x) =
      weight x.val * weight (target - x.val) := by
  have hxBounds := Finset.mem_Ico.mp hx
  have hxle : x.val ≤ target := Nat.le_of_lt hxBounds.2
  have hrightVal :
      ((target : ZMod (target + 1)) - x).val = target - x.val := by
    calc
      ((target : ZMod (target + 1)) - x).val =
          (target : ZMod (target + 1)).val - x.val := by
        apply ZMod.val_sub
        simpa [target_cast_val] using hxle
      _ = target - x.val := by rw [target_cast_val]
  have hrightMem : target - x.val ∈ Finset.Ico 1 target := by
    rw [Finset.mem_Ico]
    omega
  simp [naturalWindowCyclicWeight, hx, hrightVal, hrightMem]

private theorem sum_zmod_val_eq_sum_range
    (target : ℕ) (f : ℕ → ℂ) :
    (∑ x : ZMod (target + 1), f x.val) =
      ∑ x ∈ Finset.range (target + 1), f x := by
  change (∑ x : Fin (target + 1), f x.val) =
    ∑ x ∈ Finset.range (target + 1), f x
  exact Fin.sum_univ_eq_sum_range f (target + 1)

/-- Summing the cyclic window weight is exactly summing the original weight
over the active natural window. -/
theorem sum_naturalWindowCyclicWeight
    (weight : ℕ → ℂ) (target : ℕ) :
    (∑ x : ZMod (target + 1),
      naturalWindowCyclicWeight weight target x) =
      ∑ x ∈ Finset.Ico 1 target, weight x := by
  calc
    (∑ x : ZMod (target + 1),
        naturalWindowCyclicWeight weight target x) =
        ∑ x ∈ Finset.range (target + 1),
          if x ∈ Finset.Ico 1 target then weight x else 0 := by
      exact sum_zmod_val_eq_sum_range target
        (fun x => if x ∈ Finset.Ico 1 target then weight x else 0)
    _ = ∑ x ∈ Finset.Ico 1 target, weight x := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      · intro x hx
        rfl

theorem naturalWindowCyclicCorrelation_eq_natPairCorrelation
    (weight : ℕ → ℂ) (target : ℕ) :
    cyclicPairCorrelation (naturalWindowCyclicWeight weight target)
        (target : ZMod (target + 1)) =
      natPairCorrelation weight target := by
  rw [cyclicPairCorrelation, natPairCorrelation]
  calc
    (∑ x : ZMod (target + 1),
        naturalWindowCyclicWeight weight target x *
          naturalWindowCyclicWeight weight target
            ((target : ZMod (target + 1)) - x)) =
        ∑ x : ZMod (target + 1),
          if x.val ∈ Finset.Ico 1 target then
            weight x.val * weight (target - x.val)
          else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hactive : x.val ∈ Finset.Ico 1 target
      · rw [if_pos hactive]
        exact naturalWindowCyclicWeight_pair weight target x hactive
      · simp [naturalWindowCyclicWeight, hactive]
    _ = ∑ x ∈ Finset.range (target + 1),
          if x ∈ Finset.Ico 1 target then
            weight x * weight (target - x)
          else 0 := by
      exact sum_zmod_val_eq_sum_range target
        (fun x => if x ∈ Finset.Ico 1 target then
          weight x * weight (target - x) else 0)
    _ = ∑ x ∈ Finset.Ico 1 target,
          weight x * weight (target - x) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      · intro x hx
        rfl

def naturalWindowNoWrapAdapter
    (weight : ℕ → ℂ) (target : ℕ) :
    NaturalCyclicNoWrapAdapter weight target (target + 1) where
  cyclicWeight := naturalWindowCyclicWeight weight target
  correlation_eq :=
    (naturalWindowCyclicCorrelation_eq_natPairCorrelation weight target).symm

/-- Exact finite Fourier coefficient identity for a natural ordered-pair
correlation.  This is the no-wrap specialization of the cyclic DFT theorem. -/
theorem goldbachFiniteFourierCoefficientIdentity
    (weight : ℕ → ℂ) (target : ℕ) :
    natPairCorrelation weight target =
      ((target + 1 : ℕ) : ℂ)⁻¹ *
        ∑ frequency : ZMod (target + 1),
          stdAddChar (frequency * (target : ZMod (target + 1))) *
            (finiteExponentialSum
              (naturalWindowCyclicWeight weight target) frequency) ^ 2 := by
  exact natPairCorrelation_eq_fourierCoefficient_of_noWrap
    (naturalWindowNoWrapAdapter weight target)

end GoldbachPrimePairTrace
