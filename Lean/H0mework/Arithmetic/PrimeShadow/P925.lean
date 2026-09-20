import H0mework.Arithmetic.PrimeShadow.P924

/-!
# Proposition 925: Boolean atomicity checks feed the non-prime SU(7) producer

P924 made the single-cell projection boundary explicit, but its raw cell still
carried proofs of `NatMultiplicativelyAtomic`.  This file lowers that endpoint
input one more executable step:

```text
raw endpoint code + Boolean nontrivial-factor check
  -> NatMultiplicativelyAtomic
  -> P924 non-prime physical branch cell
  -> prime-edge projection
```

The Boolean checker never mentions `Nat.Prime`.  It checks exactly the
multiplicative-atomic condition: the code is at least two and has no divisor
strictly between `1` and itself.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Boolean multiplicative atomicity -/

/-- Does `n` have a nontrivial divisor among `0, ..., n`?

The checked predicate is `2 <= a`, `a < n`, and `a ∣ n`; this is the finite
factor-test form of multiplicative atomicity, not a primality predicate. -/
def natHasNontrivialDivisorCheck (n : ℕ) : Bool :=
  (List.range (n + 1)).any
    (fun a => decide (2 ≤ a ∧ a < n ∧ a ∣ n))

/-- Boolean multiplicative atomicity check. -/
def natMultiplicativelyAtomicCheck (n : ℕ) : Bool :=
  decide (2 ≤ n) && ! natHasNontrivialDivisorCheck n

/-- If the nontrivial-divisor check is false, no nontrivial divisor exists. -/
theorem no_nontrivial_divisor_of_check_false
    {n a : ℕ}
    (hcheck : natHasNontrivialDivisorCheck n = false)
    (ha2 : 2 ≤ a) (halt : a < n) (hdiv : a ∣ n) :
    False := by
  unfold natHasNontrivialDivisorCheck at hcheck
  have hmem : a ∈ List.range (n + 1) := by
    exact List.mem_range.mpr (Nat.lt_trans halt (Nat.lt_succ_self n))
  have hnot_true :
      ¬ decide (2 ≤ a ∧ a < n ∧ a ∣ n) = true :=
    (List.any_eq_false.mp hcheck) a hmem
  exact hnot_true
    (decide_eq_true_eq.mpr ⟨ha2, halt, hdiv⟩)

/-- A successful Boolean atomicity check proves multiplicative atomicity. -/
theorem natMultiplicativelyAtomic_of_check_eq_true
    {n : ℕ}
    (hcheck : natMultiplicativelyAtomicCheck n = true) :
    NatMultiplicativelyAtomic n := by
  unfold natMultiplicativelyAtomicCheck at hcheck
  have h2true : decide (2 ≤ n) = true := by
    by_cases hn2 : 2 ≤ n
    · exact decide_eq_true_eq.mpr hn2
    · have hfalse : decide (2 ≤ n) = false :=
        decide_eq_false_iff_not.mpr hn2
      simp [hfalse] at hcheck
  have hn2 : 2 ≤ n := decide_eq_true_eq.mp h2true
  have hnodiv :
      natHasNontrivialDivisorCheck n = false := by
    have hnot :
        ! natHasNontrivialDivisorCheck n = true := by
      simpa [h2true] using hcheck
    have hnot_true :
        natHasNontrivialDivisorCheck n ≠ true := by
      intro htrue
      simp [htrue] at hnot
    cases hraw : natHasNontrivialDivisorCheck n
    · rfl
    · exact False.elim (hnot_true hraw)
  constructor
  · exact hn2
  · intro a b hfactor
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    · by_cases hb1 : b = 1
      · exact Or.inr hb1
      · have ha0 : a ≠ 0 := by
          intro ha0
          subst a
          simp at hfactor
          omega
        have hb0 : b ≠ 0 := by
          intro hb0
          subst b
          simp at hfactor
          omega
        have ha2 : 2 ≤ a := by omega
        have hb2 : 2 ≤ b := by omega
        have hb1lt : 1 < b := by omega
        have ha_pos : 0 < a := by omega
        have halt_mul : a * 1 < a * b :=
          Nat.mul_lt_mul_of_pos_left hb1lt ha_pos
        have halt : a < n := by
          simpa [Nat.mul_one, hfactor] using halt_mul
        have hdiv : a ∣ n := ⟨b, hfactor⟩
        exact False.elim
          (no_nontrivial_divisor_of_check_false
            hnodiv ha2 halt hdiv)

/-! ## Boolean-checked raw branching cells -/

/-- A raw branching cell whose endpoint codes pass the Boolean atomicity
checker.

This stores neither `Nat.Prime` nor `NatMultiplicativelyAtomic`; it stores the
finite checker results. -/
structure SU7BooleanAtomicRawBranchingCell (n : ℕ) where
  cell : SU7BranchingDecompositionCell n
  left_check :
    natMultiplicativelyAtomicCheck cell.leftWeightCode = true
  right_check :
    natMultiplicativelyAtomicCheck cell.rightWeightCode = true

/-- Boolean endpoint checks generate P923 atomic raw cells. -/
def atomicRawBranchingCell_of_booleanAtomicCell
    {n : ℕ} (x : SU7BooleanAtomicRawBranchingCell n) :
    SU7AtomicRawBranchingCell n where
  cell := x.cell
  left_atomic :=
    natMultiplicativelyAtomic_of_check_eq_true x.left_check
  right_atomic :=
    natMultiplicativelyAtomic_of_check_eq_true x.right_check

/-- Boolean raw cells forget to P923 atomic raw cells. -/
def atomicRawBranchingCells_of_booleanAtomicCells
    {n : ℕ} (xs : List (SU7BooleanAtomicRawBranchingCell n)) :
    List (SU7AtomicRawBranchingCell n) :=
  xs.map atomicRawBranchingCell_of_booleanAtomicCell

/-- Membership in the generated atomic list comes from a Boolean-checked
source cell. -/
theorem exists_booleanCell_of_mem_atomicBooleanList
    {n : ℕ} (xs : List (SU7BooleanAtomicRawBranchingCell n))
    {c : SU7AtomicRawBranchingCell n}
    (hmem : c ∈ atomicRawBranchingCells_of_booleanAtomicCells xs) :
    ∃ x : SU7BooleanAtomicRawBranchingCell n,
      x ∈ xs ∧
        atomicRawBranchingCell_of_booleanAtomicCell x = c := by
  unfold atomicRawBranchingCells_of_booleanAtomicCells at hmem
  exact List.mem_map.mp hmem

/-! ## Boolean checked lists feed P923 -/

/-- A checked raw branch list whose endpoint atomicity is supplied by Boolean
checks. -/
structure SU7BooleanAtomicRawBranchingCheckedCellList (n : ℕ) where
  cells : List (SU7BooleanAtomicRawBranchingCell n)
  startCell : SU7BranchingDecompositionCell n
  start_mem :
    startCell ∈
      (rawBranchingSpectrum_of_certifiedCells
        (certifiedRawBranchingCells_of_atomicRawBranchingCells
          (atomicRawBranchingCells_of_booleanAtomicCells cells))).cells
  maxEnergy : ℕ
  energy_bound :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈
        (rawBranchingSpectrum_of_certifiedCells
          (certifiedRawBranchingCells_of_atomicRawBranchingCells
            (atomicRawBranchingCells_of_booleanAtomicCells cells))).cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy c ≤ maxEnergy
  coverage_check :
    rawBranchingEnergyShellCoverageCheck
      (rawBranchingSpectrum_of_certifiedCells
        (certifiedRawBranchingCells_of_atomicRawBranchingCells
          (atomicRawBranchingCells_of_booleanAtomicCells cells)))
      maxEnergy = true

/-- Boolean checked lists generate P923 atomic checked lists. -/
def atomicCheckedCellList_of_booleanAtomicCheckedCellList
    {n : ℕ} (L : SU7BooleanAtomicRawBranchingCheckedCellList n) :
    SU7AtomicRawBranchingCheckedCellList n where
  cells := atomicRawBranchingCells_of_booleanAtomicCells L.cells
  startCell := L.startCell
  start_mem := L.start_mem
  maxEnergy := L.maxEnergy
  energy_bound := L.energy_bound
  coverage_check := L.coverage_check

/-- A Boolean checked list computes a generated physical zero branch cell via
P923/P924. -/
def generatedPhysicalZeroBranchCell_of_booleanAtomicCheckedCellList
    {n : ℕ} (L : SU7BooleanAtomicRawBranchingCheckedCellList n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_atomicCheckedCellList
    (atomicCheckedCellList_of_booleanAtomicCheckedCellList L)

/-- A Boolean checked list computes a trace-zero prime-edge loop via the
non-prime physical branch-cell projection. -/
def traceZeroPrimeEdgeLoop_of_booleanAtomicCheckedCellList
    {n : ℕ} (L : SU7BooleanAtomicRawBranchingCheckedCellList n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCell_of_booleanAtomicCheckedCellList L)

/-- Every even fiber carries a Boolean-checked atomic raw branch list. -/
def SU7BooleanAtomicRawBranchingCheckedCellListEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7BooleanAtomicRawBranchingCheckedCellList n)

/-- Boolean checked lists produce P923 atomic checked lists on every even
fiber. -/
def atomicCheckedCellListsEveryEvenFiber_of_booleanAtomicCheckedCellLists
    (H : SU7BooleanAtomicRawBranchingCheckedCellListEveryEvenFiber) :
    SU7AtomicRawBranchingCheckedCellListEveryEvenFiber := by
  intro n hn
  exact ⟨atomicCheckedCellList_of_booleanAtomicCheckedCellList
    (Classical.choice (H n hn))⟩

/-- Fiberwise Boolean checked lists give ordinary even Goldbach through
P925 -> P923 -> P922 -> P921. -/
theorem evenGoldbach_of_booleanAtomicCheckedCellLists
    (H : SU7BooleanAtomicRawBranchingCheckedCellListEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_atomicCheckedCellLists
    (atomicCheckedCellListsEveryEvenFiber_of_booleanAtomicCheckedCellLists H)

/-! ## Certificate -/

/-- P925 certificate: finite Boolean atomicity checks feed the non-prime
branch producer. -/
structure SU7BooleanAtomicRawCellProducerCertificate where
  atomicity_check_sound :
    ∀ {n : ℕ},
      natMultiplicativelyAtomicCheck n = true ->
        NatMultiplicativelyAtomic n
  boolean_cell_to_atomic :
    ∀ {n : ℕ}, SU7BooleanAtomicRawBranchingCell n ->
      SU7AtomicRawBranchingCell n
  boolean_checked_to_atomic_checked :
    ∀ {n : ℕ}, SU7BooleanAtomicRawBranchingCheckedCellList n ->
      SU7AtomicRawBranchingCheckedCellList n
  boolean_checked_to_physical_zero :
    ∀ {n : ℕ}, SU7BooleanAtomicRawBranchingCheckedCellList n ->
      SU7GeneratedPhysicalZeroBranchCell n
  every_fiber_to_goldbach :
    SU7BooleanAtomicRawBranchingCheckedCellListEveryEvenFiber ->
      EvenGoldbachStatement

/-- Canonical P925 Boolean atomic raw-cell producer certificate. -/
def su7BooleanAtomicRawCellProducerCertificate :
    SU7BooleanAtomicRawCellProducerCertificate where
  atomicity_check_sound :=
    natMultiplicativelyAtomic_of_check_eq_true
  boolean_cell_to_atomic :=
    atomicRawBranchingCell_of_booleanAtomicCell
  boolean_checked_to_atomic_checked :=
    atomicCheckedCellList_of_booleanAtomicCheckedCellList
  boolean_checked_to_physical_zero :=
    generatedPhysicalZeroBranchCell_of_booleanAtomicCheckedCellList
  every_fiber_to_goldbach :=
    evenGoldbach_of_booleanAtomicCheckedCellLists


end
end StandardModelConstraint
end SaturationMonoid
