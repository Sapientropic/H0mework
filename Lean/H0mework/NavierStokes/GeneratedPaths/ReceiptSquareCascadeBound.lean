import H0mework.NavierStokes.GeneratedPaths.WholeReceiptPersistenceWindow
import H0mework.NavierStokes.GeneratedPaths.ViscousEnstrophyCost

/-!
# Receipt-square bound for arbitrary generated shell cascades

For every finite source-generated shell path below the strict critical
margin, this module combines:

* one common actual Galerkin trajectory;
* the internally generated lifetime of every exact receipt;
* quarter persistence on the whole receipt support;
* pairwise-disjoint shell write-back; and
* the viscous enstrophy absorption ledger.

The selected-shell frequency in each persistence time cancels the same
frequency in its viscous cost.  What remains is the cutoff- and path-length
independent source invariant

```text
Σ receipt, coefficientCarrierNormSq(receipt trace)².
```

No trajectory, time interval, cutoff, path length, amplitude quantum,
compactness witness, or target blow-up scenario occurs in the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareCascadeBound

open scoped BigOperators Interval ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPathTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistence
open ThreeDimensionalVorticityCoefficientGeneratedPathViscousEnstrophyCost
open ThreeDimensionalVorticityCoefficientGeneratedPathCommonTimeCompactnessBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistenceWindow

noncomputable section

/-- Frequency-free square mass of every exact trace written by a generated
finite shell path. -/
def generatedPathReceiptTraceSquareMass
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) : ℝ :=
  ((generatedIntegerShellReachableReceipts arrival).map
    fun receipt =>
      coefficientCarrierNormSq
          (generatedIntegerShellReceiptTrace receipt) ^ 2).sum

theorem generatedPathReceiptTraceSquareMass_nonneg
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    0 ≤ generatedPathReceiptTraceSquareMass arrival := by
  unfold generatedPathReceiptTraceSquareMass
  exact List.sum_nonneg fun mass massMem => by
    rcases List.mem_map.mp massMem with
      ⟨receipt, receiptMem, rfl⟩
    exact sq_nonneg _

private theorem intervalIntegrable_listSum
    {α : Type*}
    (indices : List α)
    (summand : α → ℝ → ℝ)
    (a b : ℝ)
    (integrable :
      ∀ index ∈ indices,
        IntervalIntegrable (summand index) volume a b) :
    IntervalIntegrable
      (fun t => (indices.map fun index => summand index t).sum)
      volume a b := by
  induction indices with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact
        (integrable head (by simp)).add
          (inductionHypothesis fun index indexMem =>
            integrable index (by simp [indexMem]))

private theorem intervalIntegral_listSum
    {α : Type*}
    (indices : List α)
    (summand : α → ℝ → ℝ)
    (a b : ℝ)
    (integrable :
      ∀ index ∈ indices,
        IntervalIntegrable (summand index) volume a b) :
    (∫ t in a..b,
      (indices.map fun index => summand index t).sum) =
        (indices.map fun index =>
          ∫ t in a..b, summand index t).sum := by
  induction indices with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [
        intervalIntegral.integral_add
          (integrable head (by simp))
          (intervalIntegrable_listSum
            tail summand a b
            (fun index indexMem =>
              integrable index (by simp [indexMem]))),
        inductionHypothesis
          (fun index indexMem =>
            integrable index (by simp [indexMem]))]

private theorem receiptPersistenceIntegral_lower
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity)
    (θ : ℝ)
    (budget :
      GeneratedPathCommonTimeCompactnessBudget
        arrival ν θ
          (generatedPathPersistenceHorizon arrival ν θ))
    {receipt : GeneratedIntegerShellReceipt}
    (receiptMem :
      receipt ∈ generatedIntegerShellReachableReceipts arrival)
    (persists :
      ∀ t ∈
          Icc (0 : ℝ)
            (generatedReceiptPersistenceTime
              current receipt ν θ),
        coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) /
            4 ≤
          receiptSupportEnergy receipt
            (budget.trajectory t)) :
    coefficientCarrierNormSq
            (generatedIntegerShellReceiptTrace receipt) ^ 2 /
          (48 * (2 * Real.pi) ^ 2 *
            max 1
              (generatedPathNegativeOneTimeCeiling current ν θ)) ≤
      ∫ t in (0 : ℝ)..
          generatedReceiptPersistenceTime
            current receipt ν θ,
        receiptSupportEnstrophyMass receipt
          (budget.trajectory t) := by
  let persistenceTime :=
    generatedReceiptPersistenceTime current receipt ν θ
  have persistenceTimePos :
      0 < persistenceTime :=
    generatedReceiptPersistenceTime_pos
      current receipt ν θ
  have persistenceTimeLe :
      persistenceTime ≤
        generatedPathPersistenceHorizon arrival ν θ :=
    generatedReceiptPersistenceTime_le_pathHorizon
      arrival receiptMem ν θ
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) persistenceTime,
        HasDerivAt budget.trajectory
          (finiteStateVorticityGenerator
            (generatedSupport current) ν.coeff
            (budget.trajectory t)) t := by
    intro t tMem
    exact
      (budget.physicalProperties t
        ⟨tMem.1, tMem.2.trans persistenceTimeLe⟩).1
  have supportContinuous :
      ContinuousOn
        (fun t =>
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t))
        (Icc (0 : ℝ) persistenceTime) := by
    intro t tMem
    exact
      ((receiptSupportEnergy_continuousAt_of_hasDerivAt
        receipt budget.trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν.coeff
          (budget.trajectory t))
        (evolves t tMem)).const_mul
          (receipt.selectedShellSq : ℝ)).continuousWithinAt
  have supportIntegrable :
      IntervalIntegrable
        (fun t =>
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t))
        volume 0 persistenceTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      persistenceTimePos.le supportContinuous
  have constantIntegrable :
      IntervalIntegrable
        (fun _ : ℝ =>
          (receipt.selectedShellSq : ℝ) *
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
            4)
        volume 0 persistenceTime :=
    continuous_const.intervalIntegrable 0 persistenceTime
  have pointwiseLower :
      ∀ t ∈ Icc (0 : ℝ) persistenceTime,
        (receipt.selectedShellSq : ℝ) *
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
            4 ≤
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t) := by
    intro t tMem
    have retained := persists t tMem
    have shellNonneg :
        0 ≤ (receipt.selectedShellSq : ℝ) :=
      (generatedIntegerShellReceipt_selectedShellSq_cast_pos receipt).le
    unfold receiptSupportEnstrophyMass
    nlinarith [mul_le_mul_of_nonneg_left retained shellNonneg]
  have integratedLower :=
    intervalIntegral.integral_mono_on
      persistenceTimePos.le
      constantIntegrable supportIntegrable pointwiseLower
  have normalizedLower :
      persistenceTime *
            ((receipt.selectedShellSq : ℝ) *
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
              4) ≤
        ∫ t in (0 : ℝ)..persistenceTime,
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t) := by
    have integratedLower' :
        (receipt.selectedShellSq : ℝ) *
              (persistenceTime *
                coefficientCarrierNormSq
                  (generatedIntegerShellReceiptTrace receipt)) /
            4 ≤
          ∫ t in (0 : ℝ)..persistenceTime,
            receiptSupportEnstrophyMass receipt
              (budget.trajectory t) := by
      simpa [
        intervalIntegral.integral_const,
        sub_zero,
        smul_eq_mul] using integratedLower
    calc
      persistenceTime *
            ((receipt.selectedShellSq : ℝ) *
              coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) /
              4) =
          (receipt.selectedShellSq : ℝ) *
              (persistenceTime *
                coefficientCarrierNormSq
                  (generatedIntegerShellReceiptTrace receipt)) /
            4 := by ring
      _ ≤ _ := integratedLower'
  rw [
    generatedReceiptPersistenceTime_weighted_trace_eq
      current receipt ν θ] at normalizedLower
  exact normalizedLower

private theorem receiptPersistenceIntegral_le_fullHorizon
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity)
    (θ : ℝ)
    (budget :
      GeneratedPathCommonTimeCompactnessBudget
        arrival ν θ
          (generatedPathPersistenceHorizon arrival ν θ))
    {receipt : GeneratedIntegerShellReceipt}
    (receiptMem :
      receipt ∈ generatedIntegerShellReachableReceipts arrival) :
    (∫ t in (0 : ℝ)..
        generatedReceiptPersistenceTime
          current receipt ν θ,
      receiptSupportEnstrophyMass receipt
        (budget.trajectory t)) ≤
      ∫ t in (0 : ℝ)..
          generatedPathPersistenceHorizon arrival ν θ,
        receiptSupportEnstrophyMass receipt
          (budget.trajectory t) := by
  have horizonPos :=
    generatedPathPersistenceHorizon_pos arrival ν θ
  have evolves :
      ∀ t ∈
          Icc (0 : ℝ)
            (generatedPathPersistenceHorizon arrival ν θ),
        HasDerivAt budget.trajectory
          (finiteStateVorticityGenerator
            (generatedSupport current) ν.coeff
            (budget.trajectory t)) t := by
    intro t tMem
    exact (budget.physicalProperties t tMem).1
  have supportContinuous :
      ContinuousOn
        (fun t =>
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t))
        (Icc (0 : ℝ)
          (generatedPathPersistenceHorizon arrival ν θ)) := by
    intro t tMem
    exact
      ((receiptSupportEnergy_continuousAt_of_hasDerivAt
        receipt budget.trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν.coeff
          (budget.trajectory t))
        (evolves t tMem)).const_mul
          (receipt.selectedShellSq : ℝ)).continuousWithinAt
  have supportIntegrable :
      IntervalIntegrable
        (fun t =>
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t))
        volume 0
          (generatedPathPersistenceHorizon arrival ν θ) :=
    ContinuousOn.intervalIntegrable_of_Icc
      horizonPos.le supportContinuous
  exact
    intervalIntegral.integral_mono_interval
      (μ := volume)
      (c := (0 : ℝ))
      (d := generatedPathPersistenceHorizon arrival ν θ)
      le_rfl
      (generatedReceiptPersistenceTime_pos
        current receipt ν θ).le
      (generatedReceiptPersistenceTime_le_pathHorizon
        arrival receiptMem ν θ)
      (Filter.Eventually.of_forall fun t =>
        receiptSupportEnstrophyMass_nonneg
          receipt (budget.trajectory t))
      supportIntegrable

/-! ## The frequency-free cascade bound -/

/-- Every arbitrary finite source-generated shell cascade in the strict
critical regime pays a cutoff- and path-length independent square-mass
budget.  This is the first whole-path estimate in which generated frequency
growth cancels rather than entering the final constant. -/
theorem generatedIntegerShellReachable_critical_receiptTraceSquareMass_le
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (initialMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport current)
            (generatedComplexVorticityState current
              (generatedSupport current)) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    generatedPathReceiptTraceSquareMass arrival ≤
      48 * (2 * Real.pi) ^ 2 *
          max 1
            (generatedPathNegativeOneTimeCeiling current ν θ) *
          finiteStateVorticityHalfEnstrophy
            (generatedSupport current)
            (generatedComplexVorticityState current
              (generatedSupport current)) /
        criticalEnstrophyAbsorptionCoefficient θ ν := by
  let receipts :=
    generatedIntegerShellReachableReceipts arrival
  let horizon :=
    generatedPathPersistenceHorizon arrival ν θ
  obtain ⟨budget, persists⟩ :=
    generatedIntegerShellReachable_receipts_persist_on_common_horizon
      arrival ν θ θLtOne initialMargin
  let normalizedReceiptMass : GeneratedIntegerShellReceipt → ℝ :=
    fun receipt =>
      coefficientCarrierNormSq
              (generatedIntegerShellReceiptTrace receipt) ^ 2 /
        (48 * (2 * Real.pi) ^ 2 *
          max 1
            (generatedPathNegativeOneTimeCeiling current ν θ))
  let persistenceIntegral : GeneratedIntegerShellReceipt → ℝ :=
    fun receipt =>
      ∫ t in (0 : ℝ)..
          generatedReceiptPersistenceTime
            current receipt ν θ,
        receiptSupportEnstrophyMass receipt
          (budget.trajectory t)
  let horizonIntegral : GeneratedIntegerShellReceipt → ℝ :=
    fun receipt =>
      ∫ t in (0 : ℝ)..horizon,
        receiptSupportEnstrophyMass receipt
          (budget.trajectory t)
  have normalizedLePersistence :
      (receipts.map normalizedReceiptMass).sum ≤
        (receipts.map persistenceIntegral).sum := by
    apply List.sum_le_sum
    intro receipt receiptMem
    exact
      receiptPersistenceIntegral_lower
        arrival ν θ budget receiptMem
        (persists receipt receiptMem)
  have persistenceLeHorizon :
      (receipts.map persistenceIntegral).sum ≤
        (receipts.map horizonIntegral).sum := by
    apply List.sum_le_sum
    intro receipt receiptMem
    exact
      receiptPersistenceIntegral_le_fullHorizon
        arrival ν θ budget receiptMem
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) horizon,
        HasDerivAt budget.trajectory
          (finiteStateVorticityGenerator
            (generatedSupport current) ν.coeff
            (budget.trajectory t)) t := by
    intro t tMem
    exact (budget.physicalProperties t tMem).1
  have eachHorizonIntegrable :
      ∀ receipt ∈ receipts,
        IntervalIntegrable
          (fun t =>
            receiptSupportEnstrophyMass receipt
              (budget.trajectory t))
          volume 0 horizon := by
    intro receipt receiptMem
    apply ContinuousOn.intervalIntegrable_of_Icc
      (generatedPathPersistenceHorizon_pos arrival ν θ).le
    intro t tMem
    exact
      ((receiptSupportEnergy_continuousAt_of_hasDerivAt
        receipt budget.trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν.coeff
          (budget.trajectory t))
        (evolves t tMem)).const_mul
          (receipt.selectedShellSq : ℝ)).continuousWithinAt
  have horizonSumEq :
      (receipts.map horizonIntegral).sum =
        ∫ t in (0 : ℝ)..horizon,
          pathReceiptSupportEnstrophyMass arrival
            (budget.trajectory t) := by
    unfold horizonIntegral pathReceiptSupportEnstrophyMass
    change
      (receipts.map fun receipt =>
        ∫ t in (0 : ℝ)..horizon,
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t)).sum =
        ∫ t in (0 : ℝ)..horizon,
          (receipts.map fun receipt =>
            receiptSupportEnstrophyMass receipt
              (budget.trajectory t)).sum
    exact
      (intervalIntegral_listSum
        receipts
        (fun receipt t =>
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t))
        0 horizon eachHorizonIntegrable).symm
  have pathSupportIntegrable :
      IntervalIntegrable
        (fun t =>
          pathReceiptSupportEnstrophyMass arrival
            (budget.trajectory t))
        volume 0 horizon := by
    unfold pathReceiptSupportEnstrophyMass
    exact
      intervalIntegrable_listSum
        receipts
        (fun receipt t =>
          receiptSupportEnstrophyMass receipt
            (budget.trajectory t))
        0 horizon eachHorizonIntegrable
  have enstrophyContinuous :
      ContinuousOn
        (fun t =>
          finiteStateVorticityEnstrophyMass
            (generatedSupport current)
            (budget.trajectory t))
        (Icc (0 : ℝ) horizon) := by
    intro t tMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        (generatedSupport current)
        budget.trajectory t
        (finiteStateVorticityGenerator
          (generatedSupport current) ν.coeff
          (budget.trajectory t))
        (evolves t tMem)).continuousWithinAt
  have enstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass
            (generatedSupport current)
            (budget.trajectory t))
        volume 0 horizon :=
    ContinuousOn.intervalIntegrable_of_Icc
      (generatedPathPersistenceHorizon_pos arrival ν θ).le
      enstrophyContinuous
  have pathIntegralLeEnstrophy :
      (∫ t in (0 : ℝ)..horizon,
        pathReceiptSupportEnstrophyMass arrival
          (budget.trajectory t)) ≤
        ∫ t in (0 : ℝ)..horizon,
          finiteStateVorticityEnstrophyMass
            (generatedSupport current)
            (budget.trajectory t) :=
    intervalIntegral.integral_mono_on
      (generatedPathPersistenceHorizon_pos arrival ν θ).le
      pathSupportIntegrable enstrophyIntegrable
      (fun t tMem =>
        pathReceiptSupportEnstrophyMass_le_endpointFiniteState
          arrival (budget.trajectory t))
  have normalizedSumLeEnstrophy :
      (receipts.map normalizedReceiptMass).sum ≤
        ∫ t in (0 : ℝ)..horizon,
          finiteStateVorticityEnstrophyMass
            (generatedSupport current)
            (budget.trajectory t) := by
    exact
      normalizedLePersistence.trans
        (persistenceLeHorizon.trans
          (horizonSumEq.le.trans pathIntegralLeEnstrophy))
  have denominatorPos :
      0 <
        48 * (2 * Real.pi) ^ 2 *
          max 1
            (generatedPathNegativeOneTimeCeiling current ν θ) := by
    exact
      mul_pos
        (mul_pos (by norm_num)
          (sq_pos_of_pos
            (mul_pos (by norm_num) Real.pi_pos)))
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have normalizedSumEq :
      (receipts.map normalizedReceiptMass).sum =
        generatedPathReceiptTraceSquareMass arrival /
          (48 * (2 * Real.pi) ^ 2 *
            max 1
              (generatedPathNegativeOneTimeCeiling current ν θ)) := by
    unfold normalizedReceiptMass
      generatedPathReceiptTraceSquareMass
    change
      (receipts.map fun receipt =>
        coefficientCarrierNormSq
                (generatedIntegerShellReceiptTrace receipt) ^ 2 /
          (48 * (2 * Real.pi) ^ 2 *
            max 1
              (generatedPathNegativeOneTimeCeiling current ν θ))).sum =
        (receipts.map fun receipt =>
          coefficientCarrierNormSq
            (generatedIntegerShellReceiptTrace receipt) ^ 2).sum /
          (48 * (2 * Real.pi) ^ 2 *
            max 1
              (generatedPathNegativeOneTimeCeiling current ν θ))
    induction receipts with
    | nil => simp
    | cons head tail inductionHypothesis =>
        simp only [List.map_cons, List.sum_cons]
        rw [inductionHypothesis]
        ring
  have squareMassLeIntegrated :
      generatedPathReceiptTraceSquareMass arrival ≤
        (48 * (2 * Real.pi) ^ 2 *
          max 1
            (generatedPathNegativeOneTimeCeiling current ν θ)) *
          (∫ t in (0 : ℝ)..horizon,
            finiteStateVorticityEnstrophyMass
              (generatedSupport current)
              (budget.trajectory t)) := by
    have quotientLe :
        generatedPathReceiptTraceSquareMass arrival /
              (48 * (2 * Real.pi) ^ 2 *
                max 1
                  (generatedPathNegativeOneTimeCeiling
                    current ν θ)) ≤
            ∫ t in (0 : ℝ)..horizon,
              finiteStateVorticityEnstrophyMass
                (generatedSupport current)
                (budget.trajectory t) := by
      rw [← normalizedSumEq]
      exact normalizedSumLeEnstrophy
    have multiplied :=
      (div_le_iff₀ denominatorPos).1 quotientLe
    simpa [mul_comm] using multiplied
  have terminalHalfEnstrophyNonneg :
      0 ≤
        finiteStateVorticityHalfEnstrophy
          (generatedSupport current)
          (budget.trajectory horizon) :=
    finiteStateVorticityHalfEnstrophy_nonneg _ _
  have absorbedLeInitial :
      criticalEnstrophyAbsorptionCoefficient θ ν *
          (∫ t in (0 : ℝ)..horizon,
            finiteStateVorticityEnstrophyMass
              (generatedSupport current)
              (budget.trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
          (generatedSupport current)
          (budget.trajectory 0) :=
    budget.enstrophyAbsorption.trans
      (sub_le_self _ terminalHalfEnstrophyNonneg)
  have enstrophyIntegralLe :
      (∫ t in (0 : ℝ)..horizon,
        finiteStateVorticityEnstrophyMass
          (generatedSupport current)
          (budget.trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
              (generatedSupport current)
              (generatedComplexVorticityState current
                (generatedSupport current)) /
          criticalEnstrophyAbsorptionCoefficient θ ν := by
    rw [budget.initial] at absorbedLeInitial
    exact
      (le_div_iff₀
        (criticalEnstrophyAbsorptionCoefficient_pos
          θ θLtOne ν)).2
        (by simpa [mul_comm] using absorbedLeInitial)
  exact
    squareMassLeIntegrated.trans
      (by
        have denominatorNonneg := denominatorPos.le
        have multiplied :=
          mul_le_mul_of_nonneg_left
            enstrophyIntegralLe denominatorNonneg
        calc
          (48 * (2 * Real.pi) ^ 2 *
                max 1
                  (generatedPathNegativeOneTimeCeiling
                    current ν θ)) *
              (∫ t in (0 : ℝ)..horizon,
                finiteStateVorticityEnstrophyMass
                  (generatedSupport current)
                  (budget.trajectory t)) ≤
            (48 * (2 * Real.pi) ^ 2 *
                max 1
                  (generatedPathNegativeOneTimeCeiling
                    current ν θ)) *
              (finiteStateVorticityHalfEnstrophy
                    (generatedSupport current)
                    (generatedComplexVorticityState current
                      (generatedSupport current)) /
                criticalEnstrophyAbsorptionCoefficient θ ν) :=
            multiplied
          _ =
            48 * (2 * Real.pi) ^ 2 *
                  max 1
                    (generatedPathNegativeOneTimeCeiling
                      current ν θ) *
                  finiteStateVorticityHalfEnstrophy
                    (generatedSupport current)
                    (generatedComplexVorticityState current
                      (generatedSupport current)) /
              criticalEnstrophyAbsorptionCoefficient θ ν := by
            ring)

end

end ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareCascadeBound
end NavierStokes
end SaturationMonoid
