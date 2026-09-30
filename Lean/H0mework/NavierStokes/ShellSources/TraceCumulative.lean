import Mathlib.Data.Finsupp.BigOperators
import H0mework.NavierStokes.ShellSources.Path

/-!
# Cumulative coefficient traces along generated integer-shell paths

This module compiles every successful source-owned integer-shell receipt into
a finite coefficient trace on
`IntegerWavevector × Coordinate`.  The trace contains
the complete nonlinear coefficient row on the selected whole shell.

For every finite `GeneratedIntegerShellReachable` path, the source itself
generates the chronological trace list.  Its supports are pairwise disjoint,
each trace is nonzero, and the endpoint coefficient carrier is the initial
carrier plus their cumulative sum.  Consequently the squared coefficient
norm, integer-shell moment, and viscosity-weighted shell moment satisfy exact
finite Pythagorean identities.

These are algebraic write-back identities for the generated source grammar.
They do not identify occurrence count with physical time and do not provide
an amplitude-decay, time-occupancy, or Navier--Stokes continuation estimate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative

open scoped BigOperators Function

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientStretchingOutputCarrier
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath

noncomputable section

/-! ## The finite whole-coefficient carrier -/

/-- One flattened Fourier-wave/vector-coordinate slot. -/
abbrev IntegerShellCoefficientCoordinate :=
  IntegerWavevector × Coordinate

/-- Finite complex coefficients on the flattened wave-coordinate carrier. -/
abbrev IntegerShellCoefficientCarrier :=
  IntegerShellCoefficientCoordinate →₀ ℂ

/--
The complete finite generated vorticity coefficient table of one source,
flattened over wave-coordinate slots.
-/
def generatedCoefficientCarrier
    (source : RawVorticityFourierSource) :
    IntegerShellCoefficientCarrier :=
  ∑ wave ∈ generatedSupport source,
    ∑ coordinate : Coordinate,
      Finsupp.single (wave, coordinate)
        (generatedVorticityCoefficient source wave coordinate)

@[simp] theorem generatedCoefficientCarrier_apply
    (source : RawVorticityFourierSource)
    (index : IntegerShellCoefficientCoordinate) :
    generatedCoefficientCarrier source index =
      generatedVorticityCoefficient source index.1 index.2 := by
  classical
  rcases index with ⟨wave, coordinate⟩
  by_cases waveMem : wave ∈ generatedSupport source
  · rw [generatedCoefficientCarrier,
      Finsupp.finsetSum_apply,
      Finset.sum_eq_single wave]
    · simp [Finsupp.finsetSum_apply,
        Finsupp.single_apply]
    · intro other _ otherNe
      simp [Finsupp.finsetSum_apply, otherNe]
    · intro waveNotMem
      exact (waveNotMem waveMem).elim
  · have coefficientZero :
        generatedVorticityCoefficient source wave = 0 :=
      generatedVorticityCoefficient_eq_zero_of_not_mem
        source waveMem
    rw [coefficientZero]
    rw [generatedCoefficientCarrier,
      Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro other otherMem
    have otherNe : other ≠ wave := by
      intro equality
      subst other
      exact waveMem otherMem
    simp [Finsupp.finsetSum_apply, otherNe]

private theorem generatedVorticityCoefficient_eq_zero_of_not_live
    (source : RawVorticityFourierSource)
    {wave : IntegerWavevector}
    (notLive : wave ∉ generatedLiveVorticityModes source) :
    generatedVorticityCoefficient source wave = 0 := by
  by_cases waveMem : wave ∈ generatedSupport source
  · by_contra coefficientNonzero
    exact notLive
      ((mem_generatedLiveVorticityModes_iff source wave).mpr
        ⟨waveMem, coefficientNonzero⟩)
  · exact
      generatedVorticityCoefficient_eq_zero_of_not_mem
        source waveMem

/-! ## One source-generated whole-shell trace -/

/--
Finite coefficient trace written by one whole-shell extension.  This
definition is a transporter for an explicit source and shell; source
ownership and nonzeroness enter only through `GeneratedIntegerShellReceipt`.
-/
def generatedIntegerShellTrace
    (source : RawVorticityFourierSource)
    (shellSq : ℤ) :
    IntegerShellCoefficientCarrier :=
  ∑ wave ∈ generatedOuterNonlinearShellModes source shellSq,
    ∑ coordinate : Coordinate,
      Finsupp.single (wave, coordinate)
        (generatedVorticityNonlinearCoefficientAt source wave coordinate)

@[simp] theorem generatedIntegerShellTrace_apply
    (source : RawVorticityFourierSource)
    (shellSq : ℤ)
    (index : IntegerShellCoefficientCoordinate) :
    generatedIntegerShellTrace source shellSq index =
      if index.1 ∈
          generatedOuterNonlinearShellModes source shellSq
      then
        generatedVorticityNonlinearCoefficientAt
          source index.1 index.2
      else 0 := by
  classical
  rcases index with ⟨wave, coordinate⟩
  by_cases waveMem :
      wave ∈ generatedOuterNonlinearShellModes source shellSq
  · rw [generatedIntegerShellTrace,
      Finsupp.finsetSum_apply,
      Finset.sum_eq_single wave]
    · simp [Finsupp.finsetSum_apply,
        Finsupp.single_apply, waveMem]
    · intro other _ otherNe
      simp [Finsupp.finsetSum_apply, otherNe]
    · intro waveNotMem
      exact (waveNotMem waveMem).elim
  · rw [generatedIntegerShellTrace,
      Finsupp.finsetSum_apply]
    rw [if_neg waveMem]
    apply Finset.sum_eq_zero
    intro other otherMem
    have otherNe : other ≠ wave := by
      intro equality
      subst other
      exact waveMem otherMem
    simp [Finsupp.finsetSum_apply, otherNe]

/--
The support of a whole-shell trace consists exactly of the nonzero flattened
coordinates of the generated nonlinear rows.
-/
theorem mem_generatedIntegerShellTrace_support_iff
    (source : RawVorticityFourierSource)
    (shellSq : ℤ)
    (index : IntegerShellCoefficientCoordinate) :
    index ∈ (generatedIntegerShellTrace source shellSq).support ↔
      index.1 ∈
          generatedOuterNonlinearShellModes source shellSq ∧
        generatedVorticityNonlinearCoefficientAt
            source index.1 index.2 ≠
          0 := by
  classical
  rw [Finsupp.mem_support_iff, generatedIntegerShellTrace_apply]
  by_cases waveMem :
      index.1 ∈ generatedOuterNonlinearShellModes source shellSq
  · simp [waveMem]
  · simp [waveMem]

/-- Wave projection of the nonzero flattened support. -/
def coefficientWaveSupport
    (carrier : IntegerShellCoefficientCarrier) :
    Finset IntegerWavevector :=
  carrier.support.image Prod.fst

theorem generatedIntegerShellTrace_waveSupport
    (source : RawVorticityFourierSource)
    (shellSq : ℤ) :
    coefficientWaveSupport
        (generatedIntegerShellTrace source shellSq) =
      generatedOuterNonlinearShellModes source shellSq := by
  classical
  ext wave
  constructor
  · intro waveMem
    rcases Finset.mem_image.mp waveMem with
      ⟨index, indexMem, indexWave⟩
    rw [← indexWave]
    exact
      (mem_generatedIntegerShellTrace_support_iff
        source shellSq index).mp indexMem |>.1
  · intro waveMem
    have nonlinearNonzero :
        generatedVorticityNonlinearCoefficientAt source wave ≠ 0 := by
      have outerMem :
          wave ∈ generatedActiveOuterNonlinearModes source :=
        ((mem_generatedOuterNonlinearShellModes_iff
          source shellSq wave).mp waveMem).1
      unfold generatedActiveOuterNonlinearModes at outerMem
      split at outerMem
      · simp at outerMem
      · exact
          (Finset.mem_filter.mp outerMem).2.2.2.2
    have coordinateExists :
        ∃ coordinate : Coordinate,
          generatedVorticityNonlinearCoefficientAt
              source wave coordinate ≠
            0 := by
      by_contra noCoordinate
      apply nonlinearNonzero
      funext coordinate
      by_contra coordinateNonzero
      exact noCoordinate ⟨coordinate, coordinateNonzero⟩
    rcases coordinateExists with
      ⟨coordinate, coordinateNonzero⟩
    exact
      Finset.mem_image.mpr
        ⟨(wave, coordinate),
          (mem_generatedIntegerShellTrace_support_iff
            source shellSq (wave, coordinate)).mpr
            ⟨waveMem, coordinateNonzero⟩,
          rfl⟩

/-- Finite whole-shell trace carried by this literal source response. -/
def generatedIntegerShellReceiptTrace
    (receipt : GeneratedIntegerShellReceipt) :
    IntegerShellCoefficientCarrier :=
  generatedIntegerShellTrace
    receipt.current receipt.selectedShellSq

@[simp] theorem generatedIntegerShellReceiptTrace_apply
    (receipt : GeneratedIntegerShellReceipt)
    (index : IntegerShellCoefficientCoordinate) :
    generatedIntegerShellReceiptTrace receipt index =
      if index.1 ∈ receipt.wholeShellModes
      then
        generatedVorticityNonlinearCoefficientAt
          receipt.current index.1 index.2
      else 0 :=
  generatedIntegerShellTrace_apply
    receipt.current receipt.selectedShellSq index

/-- The wave support of a literal receipt is exactly its complete selected
whole shell. -/
theorem coefficientTrace_waveSupport
    (receipt : GeneratedIntegerShellReceipt) :
    coefficientWaveSupport
        (generatedIntegerShellReceiptTrace receipt) =
      receipt.wholeShellModes :=
  generatedIntegerShellTrace_waveSupport
    receipt.current receipt.selectedShellSq

/-- Every successful source receipt writes a nonzero finite coefficient
trace.  Nonzeroness is generated by its inhabited active shell. -/
theorem coefficientTrace_ne_zero
    (receipt : GeneratedIntegerShellReceipt) :
    generatedIntegerShellReceiptTrace receipt ≠ 0 := by
  intro traceZero
  have waveSupportEmpty :
      coefficientWaveSupport
          (generatedIntegerShellReceiptTrace receipt) = ∅ := by
    rw [traceZero]
    rfl
  rw [coefficientTrace_waveSupport receipt] at waveSupportEmpty
  exact
    (Finset.nonempty_iff_ne_empty.mp
      receipt.wholeShellModes_nonempty)
      waveSupportEmpty

/-- Every supported coordinate of a receipt lies on its exact selected
integer shell. -/
theorem shellSq_of_mem_coefficientTrace_support
    (receipt : GeneratedIntegerShellReceipt)
    {index : IntegerShellCoefficientCoordinate}
    (indexMem :
      index ∈
        (generatedIntegerShellReceiptTrace receipt).support) :
    integerWaveShellSq index.1 = receipt.selectedShellSq := by
  have waveMem :
      index.1 ∈ receipt.wholeShellModes :=
    (mem_generatedIntegerShellTrace_support_iff
      receipt.current receipt.selectedShellSq index).mp
      indexMem |>.1
  exact
    ((mem_generatedOuterNonlinearShellModes_iff
      receipt.current receipt.selectedShellSq index.1).mp
      waveMem).2

/-- One generated response updates the complete finite coefficient carrier
by adding exactly its source-owned whole-shell trace. -/
theorem coefficientCarrier_next
    (receipt : GeneratedIntegerShellReceipt) :
    generatedCoefficientCarrier receipt.next =
      generatedCoefficientCarrier receipt.current +
        generatedIntegerShellReceiptTrace receipt := by
  rw [receipt.next_eq_extension]
  apply Finsupp.ext
  intro index
  simp only [generatedCoefficientCarrier_apply,
    generatedCoefficientCarrier_apply,
    Finsupp.add_apply,
    generatedIntegerShellReceiptTrace_apply,
    generatedVorticityCoefficient_extendByGeneratedNonlinearShell,
    generatedNonlinearShellWriteRow]
  by_cases waveMem : index.1 ∈ receipt.wholeShellModes
  · have notLive :
        index.1 ∉
          generatedLiveVorticityModes receipt.current := by
      intro live
      exact
        Finset.disjoint_left.mp
          receipt.liveModes_disjoint_wholeShell
          live waveMem
    have shellMem :
        index.1 ∈
          generatedOuterNonlinearShellModes
            receipt.current receipt.selectedShellSq := by
      simpa [GeneratedIntegerShellReceipt.wholeShellModes]
        using waveMem
    have oldZero :
        generatedVorticityCoefficient
            receipt.current index.1 =
          0 :=
      generatedVorticityCoefficient_eq_zero_of_not_live
        receipt.current notLive
    simp [waveMem, shellMem, oldZero]
  · have notShell :
        index.1 ∉
          generatedOuterNonlinearShellModes
            receipt.current receipt.selectedShellSq := by
      simpa [GeneratedIntegerShellReceipt.wholeShellModes]
        using waveMem
    simp [waveMem, notShell]

/-! ## Orthogonality and exact finite quadratic ledgers -/

/-- Finite Hermitian coefficient pairing. -/
def coefficientCarrierInner
    (left right : IntegerShellCoefficientCarrier) : ℂ :=
  left.sum fun index coefficient =>
    starRingEnd ℂ coefficient * right index

/-- Sum of complex squared moduli over the finite flattened support. -/
def coefficientCarrierNormSq
    (carrier : IntegerShellCoefficientCarrier) : ℝ :=
  ∑ index ∈ carrier.support, Complex.normSq (carrier index)

/-- Integer-shell-weighted squared coefficient norm. -/
def integerShellWeightedNormSq
    (carrier : IntegerShellCoefficientCarrier) : ℝ :=
  ∑ index ∈ carrier.support,
    (integerWaveShellSq index.1 : ℝ) *
      Complex.normSq (carrier index)

/-- Viscosity-weighted integer-shell moment. -/
def viscosityWeightedNormSq
    (ν : ℝ)
    (carrier : IntegerShellCoefficientCarrier) : ℝ :=
  ν * integerShellWeightedNormSq carrier

theorem coefficientCarrierNormSq_nonneg
    (carrier : IntegerShellCoefficientCarrier) :
    0 ≤ coefficientCarrierNormSq carrier := by
  exact
    Finset.sum_nonneg fun _ _ =>
      Complex.normSq_nonneg _

theorem coefficientCarrierNormSq_eq_zero_iff
    (carrier : IntegerShellCoefficientCarrier) :
    coefficientCarrierNormSq carrier = 0 ↔ carrier = 0 := by
  constructor
  · intro normZero
    apply Finsupp.ext
    intro index
    by_cases indexMem : index ∈ carrier.support
    · have coordinateNormZero :
          Complex.normSq (carrier index) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Complex.normSq_nonneg _)).mp
            normZero index indexMem
      exact Complex.normSq_eq_zero.mp coordinateNormZero
    · exact Finsupp.notMem_support_iff.mp indexMem
  · rintro rfl
    simp [coefficientCarrierNormSq]

theorem coefficientCarrierNormSq_pos_iff
    (carrier : IntegerShellCoefficientCarrier) :
    0 < coefficientCarrierNormSq carrier ↔ carrier ≠ 0 := by
  exact
    (coefficientCarrierNormSq_nonneg carrier).lt_iff_ne.trans
      (not_congr
        (eq_comm.trans
          (coefficientCarrierNormSq_eq_zero_iff carrier)))

theorem coefficientCarrierInner_eq_zero_of_disjoint_support
    {left right : IntegerShellCoefficientCarrier}
    (disjoint : Disjoint left.support right.support) :
    coefficientCarrierInner left right = 0 := by
  classical
  rw [coefficientCarrierInner, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro index indexMem
  have indexNotRight : index ∉ right.support :=
    Finset.disjoint_left.mp disjoint indexMem
  have rightZero : right index = 0 :=
    Finsupp.notMem_support_iff.mp indexNotRight
  simp [rightZero]

theorem coefficientCarrierNormSq_add_of_disjoint_support
    {left right : IntegerShellCoefficientCarrier}
    (disjoint : Disjoint left.support right.support) :
    coefficientCarrierNormSq (left + right) =
      coefficientCarrierNormSq left +
        coefficientCarrierNormSq right := by
  classical
  rw [coefficientCarrierNormSq,
    Finsupp.support_add_eq disjoint,
    Finset.sum_union disjoint,
    coefficientCarrierNormSq,
    coefficientCarrierNormSq]
  congr 1
  · apply Finset.sum_congr rfl
    intro index indexMem
    have indexNotRight : index ∉ right.support :=
      Finset.disjoint_left.mp disjoint indexMem
    have rightZero : right index = 0 :=
      Finsupp.notMem_support_iff.mp indexNotRight
    simp [Finsupp.add_apply, rightZero]
  · apply Finset.sum_congr rfl
    intro index indexMem
    have indexNotLeft : index ∉ left.support :=
      Finset.disjoint_right.mp disjoint indexMem
    have leftZero : left index = 0 :=
      Finsupp.notMem_support_iff.mp indexNotLeft
    simp [Finsupp.add_apply, leftZero]

theorem integerShellWeightedNormSq_add_of_disjoint_support
    {left right : IntegerShellCoefficientCarrier}
    (disjoint : Disjoint left.support right.support) :
    integerShellWeightedNormSq (left + right) =
      integerShellWeightedNormSq left +
        integerShellWeightedNormSq right := by
  classical
  rw [integerShellWeightedNormSq,
    Finsupp.support_add_eq disjoint,
    Finset.sum_union disjoint,
    integerShellWeightedNormSq,
    integerShellWeightedNormSq]
  congr 1
  · apply Finset.sum_congr rfl
    intro index indexMem
    have indexNotRight : index ∉ right.support :=
      Finset.disjoint_left.mp disjoint indexMem
    have rightZero : right index = 0 :=
      Finsupp.notMem_support_iff.mp indexNotRight
    simp [Finsupp.add_apply, rightZero]
  · apply Finset.sum_congr rfl
    intro index indexMem
    have indexNotLeft : index ∉ left.support :=
      Finset.disjoint_right.mp disjoint indexMem
    have leftZero : left index = 0 :=
      Finsupp.notMem_support_iff.mp indexNotLeft
    simp [Finsupp.add_apply, leftZero]

/-- Different source-selected shells have disjoint flattened coefficient
supports. -/
theorem coefficientTrace_support_disjoint_of_selectedShellSq_ne
    {left right : GeneratedIntegerShellReceipt}
    (shellNe :
      left.selectedShellSq ≠ right.selectedShellSq) :
    Disjoint
      (generatedIntegerShellReceiptTrace left).support
      (generatedIntegerShellReceiptTrace right).support := by
  classical
  rw [Finset.disjoint_left]
  intro index leftMem rightMem
  apply shellNe
  calc
    left.selectedShellSq =
        integerWaveShellSq index.1 :=
      (shellSq_of_mem_coefficientTrace_support
        left leftMem).symm
    _ = right.selectedShellSq :=
      shellSq_of_mem_coefficientTrace_support
        right rightMem

/-- Different source-selected receipts contain disjoint whole frequency
shells, independently of the coordinate flattening. -/
theorem coefficientTrace_waveSupport_disjoint_of_selectedShellSq_ne
    {left right : GeneratedIntegerShellReceipt}
    (shellNe :
      left.selectedShellSq ≠ right.selectedShellSq) :
    Disjoint
      (coefficientWaveSupport
        (generatedIntegerShellReceiptTrace left))
      (coefficientWaveSupport
        (generatedIntegerShellReceiptTrace right)) := by
  classical
  rw [coefficientTrace_waveSupport left,
    coefficientTrace_waveSupport right,
    Finset.disjoint_left]
  intro wave leftMem rightMem
  have leftShell :
      integerWaveShellSq wave = left.selectedShellSq :=
    ((mem_generatedOuterNonlinearShellModes_iff
      left.current left.selectedShellSq wave).mp leftMem).2
  have rightShell :
      integerWaveShellSq wave = right.selectedShellSq :=
    ((mem_generatedOuterNonlinearShellModes_iff
      right.current right.selectedShellSq wave).mp rightMem).2
  exact shellNe (leftShell.symm.trans rightShell)

/-- Distinct selected-shell receipt traces are Hermitian orthogonal. -/
theorem coefficientTrace_inner_eq_zero_of_selectedShellSq_ne
    {left right : GeneratedIntegerShellReceipt}
    (shellNe :
      left.selectedShellSq ≠ right.selectedShellSq) :
    coefficientCarrierInner
        (generatedIntegerShellReceiptTrace left)
        (generatedIntegerShellReceiptTrace right) = 0 :=
  coefficientCarrierInner_eq_zero_of_disjoint_support
    (coefficientTrace_support_disjoint_of_selectedShellSq_ne shellNe)

/-- The integer-shell moment of one receipt is exactly its shell label times
its squared coefficient norm. -/
theorem generatedIntegerShellReceiptTrace_integerShellWeightedNormSq
    (receipt : GeneratedIntegerShellReceipt) :
    integerShellWeightedNormSq
        (generatedIntegerShellReceiptTrace receipt) =
      (receipt.selectedShellSq : ℝ) *
        coefficientCarrierNormSq
          (generatedIntegerShellReceiptTrace receipt) := by
  classical
  rw [integerShellWeightedNormSq,
    coefficientCarrierNormSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index indexMem
  rw [shellSq_of_mem_coefficientTrace_support receipt indexMem]

/-- Every actual successful receipt has strictly positive squared coefficient
norm. -/
theorem generatedIntegerShellReceiptTrace_normSq_pos
    (receipt : GeneratedIntegerShellReceipt) :
    0 <
      coefficientCarrierNormSq
        (generatedIntegerShellReceiptTrace receipt) :=
  (coefficientCarrierNormSq_pos_iff
    (generatedIntegerShellReceiptTrace receipt)).mpr
      (coefficientTrace_ne_zero receipt)

/-! ## Arbitrary finite generated paths -/

/-- Chronological coefficient traces generated by an exact finite path. -/
def generatedIntegerShellReachableTraces
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    List IntegerShellCoefficientCarrier :=
  (generatedIntegerShellReachableReceipts arrival).map
    generatedIntegerShellReceiptTrace

/-- Cumulative coefficient trace generated by an exact finite path. -/
def generatedIntegerShellCumulativeTrace
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    IntegerShellCoefficientCarrier :=
  (generatedIntegerShellReachableTraces arrival).sum

/-- Chronological whole-frequency supports generated by an exact path. -/
def generatedIntegerShellReachableWaveSupports
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    List (Finset IntegerWavevector) :=
  (generatedIntegerShellReachableReceipts arrival).map
    fun receipt =>
      coefficientWaveSupport
        (generatedIntegerShellReceiptTrace receipt)

@[simp] theorem generatedIntegerShellReachableTraces_length
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableTraces arrival).length =
      arrival.occurrence := by
  simp [generatedIntegerShellReachableTraces]

private theorem receiptList_pairwise_shell_lt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableReceipts arrival).Pairwise
      (fun left right =>
        left.selectedShellSq < right.selectedShellSq) := by
  have shellsPairwise :=
    generatedIntegerShellReachableShells_pairwise_lt arrival
  rw [←
    generatedIntegerShellReachableReceipts_map_selectedShellSq
      arrival] at shellsPairwise
  simpa only [List.pairwise_map] using shellsPairwise

private theorem receiptTraces_pairwise_disjoint
    (receipts : List GeneratedIntegerShellReceipt)
    (shellsPairwise :
      receipts.Pairwise
        (fun left right =>
          left.selectedShellSq < right.selectedShellSq)) :
    (receipts.map generatedIntegerShellReceiptTrace).Pairwise
      (Disjoint on Finsupp.support) := by
  induction receipts with
  | nil =>
      exact List.Pairwise.nil
  | cons receipt receipts inductionHypothesis =>
      rw [List.pairwise_cons] at shellsPairwise
      rw [List.map_cons, List.pairwise_cons]
      constructor
      · intro trace traceMem
        rcases List.mem_map.mp traceMem with
          ⟨later, laterMem, traceEq⟩
        subst trace
        exact
          coefficientTrace_support_disjoint_of_selectedShellSq_ne
            (ne_of_lt (shellsPairwise.1 later laterMem))
      · exact inductionHypothesis shellsPairwise.2

private theorem receiptWaveSupports_pairwise_disjoint
    (receipts : List GeneratedIntegerShellReceipt)
    (shellsPairwise :
      receipts.Pairwise
        (fun left right =>
          left.selectedShellSq < right.selectedShellSq)) :
    (receipts.map fun receipt =>
      coefficientWaveSupport
        (generatedIntegerShellReceiptTrace receipt)).Pairwise
      Disjoint := by
  induction receipts with
  | nil =>
      exact List.Pairwise.nil
  | cons receipt receipts inductionHypothesis =>
      rw [List.pairwise_cons] at shellsPairwise
      rw [List.map_cons, List.pairwise_cons]
      constructor
      · intro laterSupport laterSupportMem
        rcases List.mem_map.mp laterSupportMem with
          ⟨later, laterMem, supportEq⟩
        subst laterSupport
        exact
          coefficientTrace_waveSupport_disjoint_of_selectedShellSq_ne
            (ne_of_lt
              (shellsPairwise.1 later laterMem))
      · exact inductionHypothesis shellsPairwise.2

/-- All actual per-response traces on a generated finite path have pairwise
disjoint supports.  Thus every flattened frequency-coordinate slot is written
at most once. -/
theorem generatedIntegerShellReachableTraces_pairwise_disjoint
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableTraces arrival).Pairwise
      (Disjoint on Finsupp.support) := by
  exact
    receiptTraces_pairwise_disjoint
      (generatedIntegerShellReachableReceipts arrival)
      (receiptList_pairwise_shell_lt arrival)

/--
Every whole frequency is written at most once: the chronological wave
supports of distinct successful responses are pairwise disjoint.
-/
theorem generatedIntegerShellReachableWaveSupports_pairwise_disjoint
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableWaveSupports arrival).Pairwise
      Disjoint := by
  exact
    receiptWaveSupports_pairwise_disjoint
      (generatedIntegerShellReachableReceipts arrival)
      (receiptList_pairwise_shell_lt arrival)

/-- All distinct chronological traces are Hermitian orthogonal. -/
theorem generatedIntegerShellReachableTraces_pairwise_orthogonal
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableTraces arrival).Pairwise
      (fun left right =>
        coefficientCarrierInner left right = 0) :=
  (generatedIntegerShellReachableTraces_pairwise_disjoint arrival).imp
    fun disjoint =>
      coefficientCarrierInner_eq_zero_of_disjoint_support disjoint

/-- Every chronological trace was generated by a successful receipt and is
nonzero. -/
theorem generatedIntegerShellReachableTraces_ne_zero
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    {trace : IntegerShellCoefficientCarrier}
    (traceMem :
      trace ∈ generatedIntegerShellReachableTraces arrival) :
    trace ≠ 0 := by
  rcases List.mem_map.mp traceMem with
    ⟨receipt, _, rfl⟩
  exact coefficientTrace_ne_zero receipt

private theorem disjoint_support_list_sum
    (head : IntegerShellCoefficientCarrier)
    (tail : List IntegerShellCoefficientCarrier)
    (headDisjoint :
      ∀ later ∈ tail,
        Disjoint head.support later.support) :
    Disjoint head.support tail.sum.support := by
  classical
  rw [Finset.disjoint_left]
  intro index indexHead indexTail
  have indexUnion :
      index ∈
        tail.foldr (Finsupp.support · ⊔ ·) ∅ :=
    List.support_sum_subset tail indexTail
  rcases List.mem_foldr_sup_support_iff.mp indexUnion with
    ⟨later, laterMem, indexLater⟩
  exact
    Finset.disjoint_left.mp
      (headDisjoint later laterMem)
      indexHead indexLater

private theorem coefficientCarrierNormSq_list_sum
    (traces : List IntegerShellCoefficientCarrier)
    (pairwise :
      traces.Pairwise (Disjoint on Finsupp.support)) :
    coefficientCarrierNormSq traces.sum =
      (traces.map coefficientCarrierNormSq).sum := by
  induction traces with
  | nil =>
      simp [coefficientCarrierNormSq]
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at pairwise
      rw [List.sum_cons, List.map_cons, List.sum_cons,
        coefficientCarrierNormSq_add_of_disjoint_support
          (disjoint_support_list_sum head tail pairwise.1),
        inductionHypothesis pairwise.2]

private theorem integerShellWeightedNormSq_list_sum
    (traces : List IntegerShellCoefficientCarrier)
    (pairwise :
      traces.Pairwise (Disjoint on Finsupp.support)) :
    integerShellWeightedNormSq traces.sum =
      (traces.map integerShellWeightedNormSq).sum := by
  induction traces with
  | nil =>
      simp [integerShellWeightedNormSq]
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at pairwise
      rw [List.sum_cons, List.map_cons, List.sum_cons,
        integerShellWeightedNormSq_add_of_disjoint_support
          (disjoint_support_list_sum head tail pairwise.1),
        inductionHypothesis pairwise.2]

/-- Exact cumulative source write-back on the complete finite coefficient
carrier. -/
theorem generatedCoefficientCarrier_eq_seed_add_cumulativeTrace
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    generatedCoefficientCarrier current =
      generatedCoefficientCarrier seed +
        generatedIntegerShellCumulativeTrace arrival := by
  induction arrival with
  | initial =>
      simp [generatedIntegerShellCumulativeTrace,
        generatedIntegerShellReachableTraces,
        generatedIntegerShellReachableReceipts]
  | @step prior arrival response generated inductionHypothesis =>
      let receipt : GeneratedIntegerShellReceipt :=
        ⟨prior, response, generated⟩
      calc
        generatedCoefficientCarrier response.1 =
            generatedCoefficientCarrier prior +
              generatedIntegerShellReceiptTrace receipt :=
          coefficientCarrier_next receipt
        _ =
            generatedCoefficientCarrier seed +
              (generatedIntegerShellCumulativeTrace arrival +
                generatedIntegerShellReceiptTrace receipt) := by
          rw [inductionHypothesis]
          abel
        _ =
            generatedCoefficientCarrier seed +
              generatedIntegerShellCumulativeTrace
                (NativeReachable.step arrival generated) := by
          simp [generatedIntegerShellCumulativeTrace,
            generatedIntegerShellReachableTraces,
            receipt,
            generatedIntegerShellReachableReceipts_step,
            List.concat_eq_append]

/-- Exact Pythagorean identity for every finite source-generated successful
path. -/
theorem generatedIntegerShellCumulativeTrace_normSq
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    coefficientCarrierNormSq
        (generatedIntegerShellCumulativeTrace arrival) =
      ((generatedIntegerShellReachableReceipts arrival).map
        (fun receipt =>
          coefficientCarrierNormSq
            (generatedIntegerShellReceiptTrace receipt))).sum := by
  calc
    coefficientCarrierNormSq
          (generatedIntegerShellCumulativeTrace arrival) =
        ((generatedIntegerShellReachableTraces arrival).map
          coefficientCarrierNormSq).sum :=
      coefficientCarrierNormSq_list_sum
        (generatedIntegerShellReachableTraces arrival)
        (generatedIntegerShellReachableTraces_pairwise_disjoint arrival)
    _ = _ := by
      rw [generatedIntegerShellReachableTraces, List.map_map]
      rfl

/-- Exact integer-shell-weighted sum over every source-generated receipt. -/
theorem generatedIntegerShellCumulativeTrace_integerShellWeightedNormSq
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    integerShellWeightedNormSq
        (generatedIntegerShellCumulativeTrace arrival) =
      ((generatedIntegerShellReachableReceipts arrival).map
        (fun receipt =>
          (receipt.selectedShellSq : ℝ) *
            coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt))).sum := by
  unfold generatedIntegerShellCumulativeTrace
  rw [integerShellWeightedNormSq_list_sum
    (generatedIntegerShellReachableTraces arrival)
    (generatedIntegerShellReachableTraces_pairwise_disjoint arrival)]
  rw [generatedIntegerShellReachableTraces, List.map_map]
  have functionEquality :
      integerShellWeightedNormSq ∘
          generatedIntegerShellReceiptTrace =
        fun receipt =>
          (receipt.selectedShellSq : ℝ) *
            coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) := by
    funext receipt
    exact
      generatedIntegerShellReceiptTrace_integerShellWeightedNormSq
        receipt
  rw [functionEquality]

/-- Exact viscosity-weighted shell sum.  No sign or positivity assumption on
the viscosity is needed for this algebraic identity. -/
theorem generatedIntegerShellCumulativeTrace_viscosityWeightedNormSq
    {seed current : RawVorticityFourierSource}
    (ν : ℝ)
    (arrival : GeneratedIntegerShellReachable seed current) :
    viscosityWeightedNormSq ν
        (generatedIntegerShellCumulativeTrace arrival) =
      ν *
        ((generatedIntegerShellReachableReceipts arrival).map
          (fun receipt =>
            (receipt.selectedShellSq : ℝ) *
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt))).sum := by
  rw [viscosityWeightedNormSq,
    generatedIntegerShellCumulativeTrace_integerShellWeightedNormSq]

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
end NavierStokes
end SaturationMonoid
