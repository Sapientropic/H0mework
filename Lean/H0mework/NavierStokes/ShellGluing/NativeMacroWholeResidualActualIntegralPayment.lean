import H0mework.NavierStokes.ShellGluing.NativeMacroWholeResidualLineage
import H0mework.NavierStokes.ShellGluing.NativeMacroAdaptiveDuhamelResidualTelescope

/-!
# Actual integral payment of one whole-PDE residual redirect

At one current of the native macro lineage, the genuine obstruction is the
whole-lattice Navier--Stokes residual on the missing Fourier rows.  The same
source event installs exactly those rows into its next conservative carrier.
On the actual positive-time unforced receipt, every installed row starts at
zero and its derivative is the negative of the old residual.

This module takes the finite intersection of all nonzero residual
coordinates before coefficient quotient.  It produces a source-owned common
time window and the quantitative payment

```text
T³ / 12 * Σ missing k, |k|² ‖old whole-PDE residual(k)‖²
  < ∫₀ᵀ Σ active residual coordinates,
      |k|² |physical trajectory(t,k,j)|² dt.
```

The weighted quantum is exactly the Euclidean Fourier residual mass; the
coordinate support merely deletes zero summands.  No interval, path,
response, branch, support, residual, nonzero witness, smallness parameter,
coverage certificate, or target solution is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualActualIntegralPayment

open scoped BigOperators Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroAdaptiveDuhamelResidualTelescope
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualFeedback
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualLineage

noncomputable section

/-! ## The pre-quotient whole-residual quantum -/

/--
All nonzero scalar coordinates of the source-owned missing whole-PDE
residual at one actual macro occurrence.
-/
def lineageActiveWholeResidualCoordinates
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    Finset (IntegerWavevector × Coordinate) :=
  ((lineageMissingResidualSupport lineage index).product Finset.univ).filter
    fun residualIndex =>
      lineageOwnedWholeResidual lineage index
          residualIndex.1 residualIndex.2 ≠
        0

/--
Integer-frequency weighted Euclidean mass of the actual old whole-PDE
residual.  This is a physical Fourier quantity, not an occurrence norm.
-/
def lineageWholeResidualEnstrophyQuantum
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) : ℝ :=
  ∑ residualIndex ∈
      lineageActiveWholeResidualCoordinates lineage index,
    (integerWaveShellSq residualIndex.1 : ℝ) *
      Complex.normSq
        (lineageOwnedWholeResidual lineage index
          residualIndex.1 residualIndex.2)

/--
The physical enstrophy mass on exactly the scalar coordinates activated by
the current old whole-PDE residual.
-/
def lineageActiveWholeResidualEnstrophyMass
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ residualIndex ∈
      lineageActiveWholeResidualCoordinates lineage index,
    (integerWaveShellSq residualIndex.1 : ℝ) *
      Complex.normSq
        (state residualIndex.1 residualIndex.2)

private theorem exists_nonzero_coordinate
    (vector : ComplexCoordinateVector)
    (vectorNonzero : vector ≠ 0) :
    ∃ coordinate : Coordinate, vector coordinate ≠ 0 := by
  by_contra noCoordinate
  push Not at noCoordinate
  exact vectorNonzero (funext noCoordinate)

theorem lineageActiveWholeResidualCoordinates_nonempty_of_residual_ne_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (residualNonzero :
      lineageOwnedWholeResidual lineage index ≠ 0) :
    (lineageActiveWholeResidualCoordinates lineage index).Nonempty := by
  have missingNonempty :
      (lineageMissingResidualSupport lineage index).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro missingEmpty
    apply residualNonzero
    exact
      (ownedCarrierWholeResidual_eq_zero_iff_missingModes_eq_empty
        ν (lineage.current index)).mpr missingEmpty
  rcases missingNonempty with ⟨output, outputMem⟩
  rcases exists_nonzero_coordinate
      (lineageOwnedWholeResidual lineage index output)
      (lineageMissingResidualRow_ne_zero
        lineage index outputMem) with
    ⟨coordinate, coordinateNonzero⟩
  refine ⟨(output, coordinate), ?_⟩
  simp [lineageActiveWholeResidualCoordinates, outputMem,
    coordinateNonzero]

theorem lineageWholeResidualEnstrophyQuantum_nonneg
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    0 ≤ lineageWholeResidualEnstrophyQuantum lineage index := by
  unfold lineageWholeResidualEnstrophyQuantum
  exact Finset.sum_nonneg fun residualIndex residualIndexMem =>
    mul_nonneg
      (by
        exact_mod_cast
          integerWaveShellSq_nonneg residualIndex.1)
      (Complex.normSq_nonneg _)

/--
Deleting zero scalar coordinates does not change the weighted Euclidean row
mass.  This identifies the pre-quotient coordinate inventory with the usual
Fourier enstrophy weight of the complete old residual.
-/
theorem lineageWholeResidualEnstrophyQuantum_eq_weighted_row_sum
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    lineageWholeResidualEnstrophyQuantum lineage index =
      ∑ output ∈ lineageMissingResidualSupport lineage index,
        (integerWaveShellSq output : ℝ) *
          complexCoordinateVectorNormSq
            (lineageOwnedWholeResidual lineage index output) := by
  classical
  unfold lineageWholeResidualEnstrophyQuantum
  unfold lineageActiveWholeResidualCoordinates
  rw [Finset.sum_filter]
  calc
    (∑ residualIndex ∈
        (lineageMissingResidualSupport lineage index).product Finset.univ,
      if lineageOwnedWholeResidual lineage index
            residualIndex.1 residualIndex.2 ≠
          0 then
        (integerWaveShellSq residualIndex.1 : ℝ) *
          Complex.normSq
            (lineageOwnedWholeResidual lineage index
              residualIndex.1 residualIndex.2)
      else
        0) =
        ∑ output ∈ lineageMissingResidualSupport lineage index,
          ∑ coordinate : Coordinate,
            if lineageOwnedWholeResidual lineage index output coordinate ≠
                0 then
              (integerWaveShellSq output : ℝ) *
                Complex.normSq
                  (lineageOwnedWholeResidual lineage index
                    output coordinate)
            else
              0 := by
      exact Finset.sum_product _ _ _
    _ = _ := by
      unfold complexCoordinateVectorNormSq
      apply Finset.sum_congr rfl
      intro output outputMem
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro coordinate coordinateMem
      by_cases coordinateNonzero :
          lineageOwnedWholeResidual lineage index output coordinate ≠ 0
      · simp [coordinateNonzero]
      · have coordinateZero :
            lineageOwnedWholeResidual lineage index output coordinate = 0 :=
          not_ne_iff.mp coordinateNonzero
        simp [coordinateZero]

/--
The generated weighted quantum is strictly positive exactly when the old
whole-PDE residual is nonzero.  Positivity comes from the actual missing
Fourier row and its nonzero scalar coordinate.
-/
theorem lineageWholeResidualEnstrophyQuantum_pos_iff_residual_ne_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    0 < lineageWholeResidualEnstrophyQuantum lineage index ↔
      lineageOwnedWholeResidual lineage index ≠ 0 := by
  constructor
  · intro quantumPositive residualZero
    have coordinateSupportEmpty :
        lineageActiveWholeResidualCoordinates lineage index = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro residualIndex residualIndexMem
      have coordinateNonzero :=
        (Finset.mem_filter.mp residualIndexMem).2
      exact coordinateNonzero (congrFun (congrFun residualZero _) _)
    simp [lineageWholeResidualEnstrophyQuantum,
      coordinateSupportEmpty] at quantumPositive
  · intro residualNonzero
    unfold lineageWholeResidualEnstrophyQuantum
    apply Finset.sum_pos
    · intro residualIndex residualIndexMem
      have supportData := Finset.mem_filter.mp residualIndexMem
      have outputMem :
          residualIndex.1 ∈
            lineageMissingResidualSupport lineage index :=
        (Finset.mem_product.mp supportData.1).1
      have activeMem :
          residualIndex.1 ∈
            generatedActiveNonliveNonlinearModes
              (lineage.current index).physicalSource :=
        ((mem_generatedMissingNonlinearModes_iff
          (lineage.current index).physicalSource residualIndex.1).mp
            outputMem).1
      have outputNonzero : residualIndex.1 ≠ 0 :=
        ((mem_generatedActiveNonliveNonlinearModes_iff
          (lineage.current index).physicalSource residualIndex.1).mp
            activeMem).2.1
      have shellPositive :
          0 < (integerWaveShellSq residualIndex.1 : ℝ) := by
        exact_mod_cast integerWaveShellSq_pos outputNonzero
      exact
        mul_pos shellPositive
          (Complex.normSq_pos.mpr supportData.2)
    · exact
        lineageActiveWholeResidualCoordinates_nonempty_of_residual_ne_zero
          lineage index residualNonzero

theorem lineageWholeResidualEnstrophyQuantum_eq_zero_iff_residual_eq_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    lineageWholeResidualEnstrophyQuantum lineage index = 0 ↔
      lineageOwnedWholeResidual lineage index = 0 := by
  constructor
  · intro quantumZero
    by_contra residualNonzero
    have quantumPositive :=
      (lineageWholeResidualEnstrophyQuantum_pos_iff_residual_ne_zero
        lineage index).mpr residualNonzero
    linarith
  · intro residualZero
    have quantumNotPositive :
        ¬ 0 < lineageWholeResidualEnstrophyQuantum lineage index := by
      intro quantumPositive
      exact
        ((lineageWholeResidualEnstrophyQuantum_pos_iff_residual_ne_zero
          lineage index).mp quantumPositive) residualZero
    exact
      le_antisymm
        (le_of_not_gt quantumNotPositive)
        (lineageWholeResidualEnstrophyQuantum_nonneg
          lineage index)

/-! ## Same-event unforced integral payment -/

/--
At every actual current, the complete old whole-PDE residual is either
faithfully zero or it generates a common positive activation window on the
same native unforced receipt.  In the active branch the entire weighted
Euclidean residual quantum is paid, before quotient, by the physical
enstrophy integral on those exact coordinates.

This is a transporter/consumer of the already generated residual redirect.
Its theorem mouth contains only the source-owned lineage and occurrence.
-/
theorem generatedWholeResidualRedirect_actualCubicPayment
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    lineageOwnedWholeResidual lineage index = 0 ∨
      (lineageOwnedWholeResidual lineage index ≠ 0 ∧
        ∃ localTime : ℝ,
          0 < localTime ∧
            localTime < (lineage.physicalReceipt index).duration ∧
            localTime ^ 3 *
                  lineageWholeResidualEnstrophyQuantum lineage index /
                12 <
              ∫ time in (0 : ℝ)..localTime,
                lineageActiveWholeResidualEnstrophyMass
                  lineage index
                  ((lineage.physicalReceipt index).trajectory time)) := by
  by_cases residualZero :
      lineageOwnedWholeResidual lineage index = 0
  · exact Or.inl residualZero
  · have coordinateSupportNonempty :
        (lineageActiveWholeResidualCoordinates lineage index).Nonempty :=
      lineageActiveWholeResidualCoordinates_nonempty_of_residual_ne_zero
        lineage index residualZero
    have eventuallyCoordinateLower :
        ∀ᶠ time in 𝓝[>] (0 : ℝ),
          ∀ residualIndex ∈
              lineageActiveWholeResidualCoordinates lineage index,
            time *
                  (‖lineageOwnedWholeResidual lineage index
                      residualIndex.1 residualIndex.2‖ /
                    2) <
              ‖(lineage.physicalReceipt index).trajectory
                  time residualIndex.1 residualIndex.2‖ := by
      rw [eventually_all_finset]
      intro residualIndex residualIndexMem
      have supportData := Finset.mem_filter.mp residualIndexMem
      have outputMem :
          residualIndex.1 ∈
            lineageMissingResidualSupport lineage index :=
        (Finset.mem_product.mp supportData.1).1
      have activeMem :
          residualIndex.1 ∈
            generatedActiveNonliveNonlinearModes
              (lineage.current index).physicalSource :=
        ((mem_generatedMissingNonlinearModes_iff
          (lineage.current index).physicalSource residualIndex.1).mp
            outputMem).1
      have coordinateInitial :
          (lineage.physicalReceipt index).trajectory
              0 residualIndex.1 residualIndex.2 =
            0 := by
        simpa [physicalReceipt, redirectedMacroPhysicalReceipt] using
          congrFun
            (completeOmittedPhysicalTimeReceipt_activeNonlive_initial_zero
              (lineage.current index).physicalSource ν activeMem)
            residualIndex.2
      have rowDerivative :
          HasDerivAt
            (fun time =>
              (lineage.physicalReceipt index).trajectory
                time residualIndex.1)
            (generatedVorticityNonlinearCoefficientAt
              (lineage.current index).physicalSource residualIndex.1)
            0 := by
        simpa [physicalReceipt, redirectedMacroPhysicalReceipt] using
          completeOmittedPhysicalTimeReceipt_activeNonlive_derivative
            (lineage.current index).physicalSource ν activeMem
      have coordinateDerivative :
          HasDerivAt
            (fun time =>
              (lineage.physicalReceipt index).trajectory
                time residualIndex.1 residualIndex.2)
            (generatedVorticityNonlinearCoefficientAt
              (lineage.current index).physicalSource
              residualIndex.1 residualIndex.2)
            0 := by
        simpa using
          ((hasDerivAt_const (0 : ℝ)
            (ContinuousLinearMap.proj residualIndex.2)).clm_apply
              rowDerivative)
      have residualRowEqNegGenerated :
          lineageOwnedWholeResidual lineage index residualIndex.1 =
            -generatedVorticityNonlinearCoefficientAt
              (lineage.current index).physicalSource residualIndex.1 := by
        simpa [lineageOwnedWholeResidual, ownedCarrierWholeResidual,
          ownedCarrierTangent, currentPhysicalState] using
          currentFullPDEResidual_missing_eq_neg_generated
            (lineage.current index).physicalSource
            ν.coeff outputMem
      have derivativeEqNegResidual :
          generatedVorticityNonlinearCoefficientAt
              (lineage.current index).physicalSource
              residualIndex.1 residualIndex.2 =
            -lineageOwnedWholeResidual lineage index
              residualIndex.1 residualIndex.2 := by
        have generatedRowEqNegResidual :
            generatedVorticityNonlinearCoefficientAt
                (lineage.current index).physicalSource residualIndex.1 =
              -lineageOwnedWholeResidual lineage index residualIndex.1 := by
          rw [residualRowEqNegGenerated]
          simp
        exact congrFun generatedRowEqNegResidual residualIndex.2
      have derivativeNonzero :
          generatedVorticityNonlinearCoefficientAt
              (lineage.current index).physicalSource
              residualIndex.1 residualIndex.2 ≠
            0 := by
        rw [derivativeEqNegResidual]
        exact neg_ne_zero.mpr supportData.2
      have coordinateLower :=
        eventually_norm_gt_time_mul_half_of_hasDerivAt_zero_ne
          (fun time =>
            (lineage.physicalReceipt index).trajectory
              time residualIndex.1 residualIndex.2)
          (generatedVorticityNonlinearCoefficientAt
            (lineage.current index).physicalSource
            residualIndex.1 residualIndex.2)
          coordinateInitial derivativeNonzero coordinateDerivative
      simpa only [derivativeEqNegResidual, norm_neg] using
        coordinateLower
    have eventuallyNeighborhood :
        ∀ᶠ time in 𝓝 (0 : ℝ),
          time ∈ Ioi (0 : ℝ) →
            ∀ residualIndex ∈
                lineageActiveWholeResidualCoordinates lineage index,
              time *
                    (‖lineageOwnedWholeResidual lineage index
                        residualIndex.1 residualIndex.2‖ /
                      2) <
                ‖(lineage.physicalReceipt index).trajectory
                    time residualIndex.1 residualIndex.2‖ :=
      eventually_nhdsWithin_iff.mp eventuallyCoordinateLower
    obtain ⟨liveRadius, liveRadiusPos, liveWithin⟩ :=
      Metric.eventually_nhds_iff.mp eventuallyNeighborhood
    let localTime :=
      min (lineage.physicalReceipt index).duration liveRadius / 2
    have commonRadiusPos :
        0 <
          min (lineage.physicalReceipt index).duration liveRadius :=
      lt_min
        (lineage.physicalReceipt index).duration_pos
        liveRadiusPos
    have localTimePos : 0 < localTime := by
      dsimp [localTime]
      linarith
    have localTimeLtCommon :
        localTime <
          min (lineage.physicalReceipt index).duration liveRadius := by
      dsimp [localTime]
      linarith
    have localTimeLtReceipt :
        localTime < (lineage.physicalReceipt index).duration :=
      lt_of_lt_of_le localTimeLtCommon (min_le_left _ _)
    have localTimeLtLiveRadius : localTime < liveRadius :=
      lt_of_lt_of_le localTimeLtCommon (min_le_right _ _)
    have coordinateLower :
        ∀ time ∈ Ioc (0 : ℝ) localTime,
          ∀ residualIndex ∈
              lineageActiveWholeResidualCoordinates lineage index,
            time *
                  (‖lineageOwnedWholeResidual lineage index
                      residualIndex.1 residualIndex.2‖ /
                    2) <
              ‖(lineage.physicalReceipt index).trajectory
                  time residualIndex.1 residualIndex.2‖ := by
      intro time timeMem
      exact
        liveWithin
          (by
            rw [Real.dist_eq, sub_zero, abs_of_pos timeMem.1]
            exact
              lt_of_le_of_lt timeMem.2
                localTimeLtLiveRadius)
          timeMem.1
    have pointwiseWholeResidualLower :
        ∀ time ∈ Ioc (0 : ℝ) localTime,
          time ^ 2 *
                lineageWholeResidualEnstrophyQuantum lineage index /
              4 <
            lineageActiveWholeResidualEnstrophyMass
              lineage index
              ((lineage.physicalReceipt index).trajectory time) := by
      intro time timeMem
      have eachCoordinateSq :
          ∀ residualIndex ∈
              lineageActiveWholeResidualCoordinates lineage index,
            time ^ 2 *
                  ((integerWaveShellSq residualIndex.1 : ℝ) *
                    Complex.normSq
                      (lineageOwnedWholeResidual lineage index
                        residualIndex.1 residualIndex.2)) /
                4 <
              (integerWaveShellSq residualIndex.1 : ℝ) *
                Complex.normSq
                  ((lineage.physicalReceipt index).trajectory
                    time residualIndex.1 residualIndex.2) := by
        intro residualIndex residualIndexMem
        have supportData := Finset.mem_filter.mp residualIndexMem
        have outputMem :
            residualIndex.1 ∈
              lineageMissingResidualSupport lineage index :=
          (Finset.mem_product.mp supportData.1).1
        have activeMem :
            residualIndex.1 ∈
              generatedActiveNonliveNonlinearModes
                (lineage.current index).physicalSource :=
          ((mem_generatedMissingNonlinearModes_iff
            (lineage.current index).physicalSource residualIndex.1).mp
              outputMem).1
        have outputNonzero : residualIndex.1 ≠ 0 :=
          ((mem_generatedActiveNonliveNonlinearModes_iff
            (lineage.current index).physicalSource residualIndex.1).mp
              activeMem).2.1
        have shellPositive :
            0 < (integerWaveShellSq residualIndex.1 : ℝ) := by
          exact_mod_cast integerWaveShellSq_pos outputNonzero
        have lower :=
          coordinateLower time timeMem residualIndex residualIndexMem
        have leftNonnegative :
            0 ≤
              time *
                (‖lineageOwnedWholeResidual lineage index
                    residualIndex.1 residualIndex.2‖ /
                  2) :=
          mul_nonneg timeMem.1.le
            (div_nonneg (norm_nonneg _) (by norm_num))
        have squared :
            (time *
                  (‖lineageOwnedWholeResidual lineage index
                      residualIndex.1 residualIndex.2‖ /
                    2)) ^ 2 <
              ‖(lineage.physicalReceipt index).trajectory
                  time residualIndex.1 residualIndex.2‖ ^ 2 :=
          (sq_lt_sq₀ leftNonnegative (norm_nonneg _)).mpr lower
        have unweighted :
            time ^ 2 *
                  Complex.normSq
                    (lineageOwnedWholeResidual lineage index
                      residualIndex.1 residualIndex.2) /
                4 <
              Complex.normSq
                ((lineage.physicalReceipt index).trajectory
                  time residualIndex.1 residualIndex.2) := by
          rw [Complex.normSq_eq_norm_sq,
            Complex.normSq_eq_norm_sq]
          nlinarith
        calc
          time ^ 2 *
                  ((integerWaveShellSq residualIndex.1 : ℝ) *
                    Complex.normSq
                      (lineageOwnedWholeResidual lineage index
                        residualIndex.1 residualIndex.2)) /
                4 =
              (integerWaveShellSq residualIndex.1 : ℝ) *
                (time ^ 2 *
                    Complex.normSq
                      (lineageOwnedWholeResidual lineage index
                        residualIndex.1 residualIndex.2) /
                  4) := by
              ring
          _ < _ := mul_lt_mul_of_pos_left unweighted shellPositive
      have sumStrict :
          (∑ residualIndex ∈
              lineageActiveWholeResidualCoordinates lineage index,
            time ^ 2 *
                  ((integerWaveShellSq residualIndex.1 : ℝ) *
                    Complex.normSq
                      (lineageOwnedWholeResidual lineage index
                        residualIndex.1 residualIndex.2)) /
                4) <
            lineageActiveWholeResidualEnstrophyMass
              lineage index
              ((lineage.physicalReceipt index).trajectory time) := by
        unfold lineageActiveWholeResidualEnstrophyMass
        exact
          Finset.sum_lt_sum_of_nonempty
            coordinateSupportNonempty eachCoordinateSq
      calc
        time ^ 2 *
                lineageWholeResidualEnstrophyQuantum lineage index /
              4 =
            ∑ residualIndex ∈
                lineageActiveWholeResidualCoordinates lineage index,
              time ^ 2 *
                    ((integerWaveShellSq residualIndex.1 : ℝ) *
                      Complex.normSq
                        (lineageOwnedWholeResidual lineage index
                          residualIndex.1 residualIndex.2)) /
                  4 := by
            unfold lineageWholeResidualEnstrophyQuantum
            calc
              time ^ 2 *
                      (∑ residualIndex ∈
                        lineageActiveWholeResidualCoordinates
                          lineage index,
                        (integerWaveShellSq residualIndex.1 : ℝ) *
                          Complex.normSq
                            (lineageOwnedWholeResidual lineage index
                              residualIndex.1 residualIndex.2)) /
                    4 =
                  (time ^ 2 / 4) *
                    (∑ residualIndex ∈
                      lineageActiveWholeResidualCoordinates
                        lineage index,
                      (integerWaveShellSq residualIndex.1 : ℝ) *
                        Complex.normSq
                          (lineageOwnedWholeResidual lineage index
                            residualIndex.1 residualIndex.2)) := by
                    ring
              _ = _ := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro residualIndex residualIndexMem
                    ring
        _ < _ := sumStrict
    have localIntervalSubset :
        Icc (0 : ℝ) localTime ⊆
          Icc (0 : ℝ) (lineage.physicalReceipt index).duration := by
      intro time timeMem
      exact
        ⟨timeMem.1,
          timeMem.2.trans localTimeLtReceipt.le⟩
    have massContinuous :
        ContinuousOn
          (fun time =>
            lineageActiveWholeResidualEnstrophyMass
              lineage index
              ((lineage.physicalReceipt index).trajectory time))
          (Icc (0 : ℝ) localTime) := by
      unfold lineageActiveWholeResidualEnstrophyMass
      apply continuousOn_finsetSum
      intro residualIndex residualIndexMem
      have trajectoryContinuous :
          ContinuousOn
            (lineage.physicalReceipt index).trajectory
            (Icc (0 : ℝ) localTime) :=
        (adaptiveTrajectory_continuousOn lineage index).mono
          localIntervalSubset
      have rowContinuous :
          ContinuousOn
            (fun time =>
              (lineage.physicalReceipt index).trajectory
                time residualIndex.1)
            (Icc (0 : ℝ) localTime) :=
        (lp.evalCLM
          ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector)
          2 residualIndex.1).continuous.comp_continuousOn
            trajectoryContinuous
      have coordinateContinuous :
          ContinuousOn
            (fun time =>
              (lineage.physicalReceipt index).trajectory
                time residualIndex.1 residualIndex.2)
            (Icc (0 : ℝ) localTime) :=
        (ContinuousLinearMap.proj
          (R := ℂ) residualIndex.2).continuous.comp_continuousOn
          rowContinuous
      exact
        (Complex.continuous_normSq.comp_continuousOn
          coordinateContinuous).const_mul
            (integerWaveShellSq residualIndex.1 : ℝ)
    let lowerIntegrand : ℝ → ℝ :=
      fun time =>
        time ^ 2 *
            lineageWholeResidualEnstrophyQuantum lineage index /
          4
    have lowerContinuous :
        ContinuousOn lowerIntegrand (Icc (0 : ℝ) localTime) := by
      apply Continuous.continuousOn
      dsimp [lowerIntegrand]
      fun_prop
    have integralStrict :
        (∫ time in (0 : ℝ)..localTime,
            lowerIntegrand time) <
          ∫ time in (0 : ℝ)..localTime,
            lineageActiveWholeResidualEnstrophyMass
              lineage index
              ((lineage.physicalReceipt index).trajectory time) := by
      apply
        intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          localTimePos lowerContinuous massContinuous
      · intro time timeMem
        exact (pointwiseWholeResidualLower time timeMem).le
      · refine ⟨localTime / 2, ?_, ?_⟩
        · constructor <;> linarith
        · exact
            pointwiseWholeResidualLower
              (localTime / 2)
              ⟨by linarith, by linarith⟩
    have lowerIntegral :
        (∫ time in (0 : ℝ)..localTime,
            lowerIntegrand time) =
          localTime ^ 3 *
                lineageWholeResidualEnstrophyQuantum lineage index /
              12 := by
      have integrandEq :
          lowerIntegrand =
            fun time : ℝ =>
              (lineageWholeResidualEnstrophyQuantum lineage index / 4) *
                time ^ 2 := by
        funext time
        dsimp [lowerIntegrand]
        ring
      rw [integrandEq,
        intervalIntegral.integral_const_mul,
        integral_pow]
      norm_num
      ring
    rw [lowerIntegral] at integralStrict
    exact
      Or.inr
        ⟨residualZero, localTime, localTimePos,
          localTimeLtReceipt, integralStrict⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualActualIntegralPayment
end NavierStokes
end SaturationMonoid
