import H0mework.Arithmetic.GoldbachFourier.NaturalWindow

/-!
# Flexible-modulus natural finite Fourier identity

The minimal no-wrap modulus `target + 1` is convenient, but it is not forced.
Every modulus strictly larger than `target` gives the same natural pair
correlation.  Keeping the modulus flexible permits arithmetic alignment, for
example choosing `target + 2` for an even target so that the exact frequency
`1/2` is present on the Fourier grid.

This file changes no endpoint support or pair semantics.  It only generalizes
the already proved natural-to-cyclic transporter.
-/

noncomputable section

open Finset ZMod
open scoped BigOperators ZMod

namespace GoldbachPrimePairTrace

/-- Natural window embedded in any positive cyclic modulus.  Correct
correlation transport additionally requires `target < modulus`. -/
def naturalWindowCyclicWeightAtModulus
    (weight : ℕ → ℂ) (target modulus : ℕ) [NeZero modulus] :
    ZMod modulus → ℂ :=
  fun x => if x.val ∈ Finset.Ico 1 target then weight x.val else 0

private theorem target_cast_val_of_lt
    {target modulus : ℕ} [NeZero modulus]
    (hmodulus : target < modulus) :
    (target : ZMod modulus).val = target := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hmodulus

private theorem naturalWindowCyclicWeightAtModulus_pair
    (weight : ℕ → ℂ) {target modulus : ℕ} [NeZero modulus]
    (hmodulus : target < modulus) (x : ZMod modulus)
    (hx : x.val ∈ Finset.Ico 1 target) :
    naturalWindowCyclicWeightAtModulus weight target modulus x *
        naturalWindowCyclicWeightAtModulus weight target modulus
          ((target : ZMod modulus) - x) =
      weight x.val * weight (target - x.val) := by
  have hxBounds := Finset.mem_Ico.mp hx
  have hxle : x.val ≤ target := Nat.le_of_lt hxBounds.2
  have hrightVal :
      ((target : ZMod modulus) - x).val = target - x.val := by
    calc
      ((target : ZMod modulus) - x).val =
          (target : ZMod modulus).val - x.val := by
        apply ZMod.val_sub
        simpa [target_cast_val_of_lt hmodulus] using hxle
      _ = target - x.val := by
        rw [target_cast_val_of_lt hmodulus]
  have hrightMem : target - x.val ∈ Finset.Ico 1 target := by
    rw [Finset.mem_Ico]
    omega
  simp [naturalWindowCyclicWeightAtModulus, hx, hrightVal, hrightMem]

private theorem sum_zmod_val_eq_sum_range_atModulus
    (modulus : ℕ) [NeZero modulus] (f : ℕ → ℂ) :
    (∑ x : ZMod modulus, f x.val) =
      ∑ x ∈ Finset.range modulus, f x := by
  have hval (x : Fin modulus) :
      ((ZMod.finEquiv modulus) x).val = x.val := by
    cases modulus with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ _ => rfl
  calc
    (∑ x : ZMod modulus, f x.val) =
        ∑ x : Fin modulus, f ((ZMod.finEquiv modulus) x).val :=
      ((ZMod.finEquiv modulus).toEquiv.sum_comp
        (fun x : ZMod modulus => f x.val)).symm
    _ = ∑ x : Fin modulus, f x.val := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [hval]
    _ = ∑ x ∈ Finset.range modulus, f x :=
      Fin.sum_univ_eq_sum_range f modulus

/-- Summing the flexible cyclic weight recovers exactly the active natural
window whenever that window lies below the modulus. -/
theorem sum_naturalWindowCyclicWeightAtModulus
    (weight : ℕ → ℂ) {target modulus : ℕ} [NeZero modulus]
    (hmodulus : target < modulus) :
    (∑ x : ZMod modulus,
      naturalWindowCyclicWeightAtModulus weight target modulus x) =
      ∑ x ∈ Finset.Ico 1 target, weight x := by
  calc
    (∑ x : ZMod modulus,
        naturalWindowCyclicWeightAtModulus weight target modulus x) =
        ∑ x ∈ Finset.range modulus,
          if x ∈ Finset.Ico 1 target then weight x else 0 := by
      exact sum_zmod_val_eq_sum_range_atModulus modulus
        (fun x => if x ∈ Finset.Ico 1 target then weight x else 0)
    _ = ∑ x ∈ Finset.Ico 1 target, weight x := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      · intro x hx
        rfl

/-- The flexible-grid DFT is the expected natural-window exponential sum. -/
theorem finiteExponentialSum_naturalWindowCyclicWeightAtModulus
    (weight : ℕ → ℂ) {target modulus : ℕ} [NeZero modulus]
    (hmodulus : target < modulus) (frequency : ZMod modulus) :
    finiteExponentialSum
        (naturalWindowCyclicWeightAtModulus weight target modulus)
        frequency =
      ∑ n ∈ Finset.Ico 1 target,
        stdAddChar
            (-((n : ZMod modulus) * frequency)) * weight n := by
  rw [finiteExponentialSum, ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    (∑ x : ZMod modulus,
        stdAddChar (-(x * frequency)) *
          naturalWindowCyclicWeightAtModulus
            weight target modulus x) =
        ∑ x : ZMod modulus,
          if x.val ∈ Finset.Ico 1 target then
            stdAddChar (-(x * frequency)) * weight x.val
          else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hactive : x.val ∈ Finset.Ico 1 target
      · simp [naturalWindowCyclicWeightAtModulus, hactive]
      · simp [naturalWindowCyclicWeightAtModulus, hactive]
    _ = ∑ n ∈ Finset.range modulus,
          if n ∈ Finset.Ico 1 target then
            stdAddChar
                (-((n : ZMod modulus) * frequency)) * weight n
          else 0 := by
      simpa only [ZMod.natCast_zmod_val] using
        (sum_zmod_val_eq_sum_range_atModulus modulus
          (fun n => if n ∈ Finset.Ico 1 target then
            stdAddChar (-((n : ZMod modulus) * frequency)) * weight n
          else 0))
    _ = ∑ n ∈ Finset.Ico 1 target,
          stdAddChar
              (-((n : ZMod modulus) * frequency)) * weight n := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      · intro n hn
        rfl

/-- Any modulus strictly above the target has the same no-wrap correlation. -/
theorem naturalWindowCyclicCorrelationAtModulus_eq_natPairCorrelation
    (weight : ℕ → ℂ) {target modulus : ℕ} [NeZero modulus]
    (hmodulus : target < modulus) :
    cyclicPairCorrelation
        (naturalWindowCyclicWeightAtModulus weight target modulus)
        (target : ZMod modulus) =
      natPairCorrelation weight target := by
  rw [cyclicPairCorrelation, natPairCorrelation]
  calc
    (∑ x : ZMod modulus,
        naturalWindowCyclicWeightAtModulus weight target modulus x *
          naturalWindowCyclicWeightAtModulus weight target modulus
            ((target : ZMod modulus) - x)) =
        ∑ x : ZMod modulus,
          if x.val ∈ Finset.Ico 1 target then
            weight x.val * weight (target - x.val)
          else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hactive : x.val ∈ Finset.Ico 1 target
      · rw [if_pos hactive]
        exact naturalWindowCyclicWeightAtModulus_pair
          weight hmodulus x hactive
      · simp [naturalWindowCyclicWeightAtModulus, hactive]
    _ = ∑ x ∈ Finset.range modulus,
          if x ∈ Finset.Ico 1 target then
            weight x * weight (target - x)
          else 0 := by
      exact sum_zmod_val_eq_sum_range_atModulus modulus
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

def naturalWindowNoWrapAdapterAtModulus
    (weight : ℕ → ℂ) {target modulus : ℕ} [NeZero modulus]
    (hmodulus : target < modulus) :
    NaturalCyclicNoWrapAdapter weight target modulus where
  cyclicWeight :=
    naturalWindowCyclicWeightAtModulus weight target modulus
  correlation_eq :=
    (naturalWindowCyclicCorrelationAtModulus_eq_natPairCorrelation
      weight hmodulus).symm

/-- Exact natural finite Fourier identity at any no-wrap modulus. -/
theorem naturalFiniteFourierCoefficientIdentityAtModulus
    (weight : ℕ → ℂ) {target modulus : ℕ} [NeZero modulus]
    (hmodulus : target < modulus) :
    natPairCorrelation weight target =
      (modulus : ℂ)⁻¹ *
        ∑ frequency : ZMod modulus,
          stdAddChar (frequency * (target : ZMod modulus)) *
            (finiteExponentialSum
              (naturalWindowCyclicWeightAtModulus
                weight target modulus) frequency) ^ 2 := by
  exact natPairCorrelation_eq_fourierCoefficient_of_noWrap
    (naturalWindowNoWrapAdapterAtModulus weight hmodulus)

/-! ## Compatibility with the minimal specialization -/

theorem naturalWindowCyclicWeightAtModulus_target_add_one
    (weight : ℕ → ℂ) (target : ℕ) :
    naturalWindowCyclicWeightAtModulus
        weight target (target + 1) =
      naturalWindowCyclicWeight weight target := by
  rfl

end GoldbachPrimePairTrace
