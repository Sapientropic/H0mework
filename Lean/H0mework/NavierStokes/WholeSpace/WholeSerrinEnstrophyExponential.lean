import H0mework.NavierStokes.WholeSpace.WholeSerrinEnstrophyGronwall

/-!
# Exponential whole-receipt enstrophy control

The cutoff-free whole-carrier estimate is stable under every actual positive
restriction of the same unforced receipt.  Transporting those restricted
updates to the real interval gives the inhomogeneous integral inequality

```text
E(t) ≤ E(0) + ∫₀ᵗ (72 / ν) U(s)² E(s) ds.
```

The repository's factorial `L¹` Grönwall consumer therefore removes the
unknown enstrophy from the right-hand side and leaves only the receipt's own
critical Serrin action.  No uniform coefficient ceiling, time cutoff,
continuation witness, or target endpoint occurs in the theorem mouth.
-/

open Set Filter MeasureTheory Topology

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyExponential

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall

noncomputable section

theorem restrict_serrinDensity_ae_eq
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {Tsmall Tbig : ℝ}
    (smallTimePos : 0 < Tsmall)
    (timeLe : Tsmall ≤ Tbig)
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState Tbig) :
    ∀ᵐ time ∂(commonTimeMeasure Tsmall),
      (restrictWholeContinuousMildSerrinReceipt
          smallTimePos timeLe receipt).serrinDensity time =
        receipt.serrinDensity (commonTimeInclusion timeLe time) := by
  let bigPathLp :=
    BoundedContinuousFunction.toLp 2
      (commonTimeMeasure Tbig) ℂ receipt.wholePath
  have pathLpEq :
      BoundedContinuousFunction.toLp 2
          (commonTimeMeasure Tsmall) ℂ
          ((restrictWholeContinuousMildSerrinReceipt
              smallTimePos timeLe receipt).wholePath) =
        restrictCommonTimeLp timeLe bigPathLp := by
    simpa only [bigPathLp,
      restrictWholeContinuousMildSerrinReceipt] using
        boundedContinuousFunction_toLp_compContinuous
          timeLe receipt.wholePath
  have restrictedAE :=
    restrictCommonTimeLp_apply_ae timeLe bigPathLp
  filter_upwards [restrictedAE] with time restrictedEq
  unfold WholeContinuousMildSerrinReceipt.serrinDensity
  rw [pathLpEq, restrictedEq]

theorem restrict_serrinEnergy_eq_intervalIntegral_zeroExtension
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {Tsmall Tbig : ℝ}
    (smallTimePos : 0 < Tsmall)
    (timeLe : Tsmall ≤ Tbig)
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState Tbig) :
    (∫ time,
        (restrictWholeContinuousMildSerrinReceipt
            smallTimePos timeLe receipt).serrinDensity time *
          wholeVorticityEuclideanMass
            ((restrictWholeContinuousMildSerrinReceipt
                smallTimePos timeLe receipt).wholePath time)
        ∂(commonTimeMeasure Tsmall)) =
      ∫ time in (0 : ℝ)..Tsmall,
        commonTimeZeroExtension Tbig
          (fun actualTime =>
            receipt.serrinDensity actualTime *
              wholeVorticityEuclideanMass
                (receipt.wholePath actualTime)) time := by
  rw [← commonTime_integral_eq_intervalIntegral
    Tsmall smallTimePos.le]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [
    restrict_serrinDensity_ae_eq
      smallTimePos timeLe receipt] with time densityEq
  rw [densityEq]
  rw [commonTimeZeroExtension_of_mem Tbig _ time.1
    ⟨time.2.1, time.2.2.trans timeLe⟩]
  rfl

def receiptVorticityMassReal
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ℝ → ℝ :=
  commonTimeZeroExtension requestedTime fun time =>
    wholeVorticityEuclideanMass (receipt.wholePath time)

def receiptSerrinCoefficientReal
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ℝ → ℝ :=
  commonTimeZeroExtension requestedTime fun time =>
    (72 * ν.coeff⁻¹) * receipt.serrinDensity time

@[simp] theorem receiptVorticityMassReal_of_mem
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    receiptVorticityMassReal receipt time =
      wholeVorticityEuclideanMass
        (receipt.wholePath ⟨time, timeMem⟩) := by
  exact commonTimeZeroExtension_of_mem requestedTime _ time timeMem

@[simp] theorem receiptSerrinCoefficientReal_of_mem
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    receiptSerrinCoefficientReal receipt time =
      (72 * ν.coeff⁻¹) * receipt.serrinDensity ⟨time, timeMem⟩ := by
  exact commonTimeZeroExtension_of_mem requestedTime _ time timeMem

theorem receiptSerrinCoefficientReal_intervalIntegrable
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    IntervalIntegrable
      (receiptSerrinCoefficientReal receipt)
      volume 0 requestedTime := by
  unfold receiptSerrinCoefficientReal
  apply commonTimeZeroExtension_intervalIntegrable_of_integrable
    requestedTime receipt.requestedTimePos.le
  exact receipt.serrinDensity_integrable.const_mul (72 * ν.coeff⁻¹)

theorem receiptSerrinCoefficientReal_nonneg
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    0 ≤ receiptSerrinCoefficientReal receipt time := by
  rw [receiptSerrinCoefficientReal_of_mem receipt time timeMem]
  exact mul_nonneg
    (mul_nonneg (by norm_num) (inv_nonneg.2 ν.coeff_pos.le))
    (sq_nonneg _)

theorem receiptVorticityMassReal_continuousOn
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ContinuousOn (receiptVorticityMassReal receipt)
      (Icc (0 : ℝ) requestedTime) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous fun time : Icc (0 : ℝ) requestedTime =>
    receiptVorticityMassReal receipt time.1
  convert wholeReceiptVorticityMass_continuous receipt using 1
  funext time
  rw [receiptVorticityMassReal_of_mem receipt time.1 time.2]

theorem receiptVorticityMassReal_le_ceiling
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    receiptVorticityMassReal receipt time ≤
      wholeReceiptVorticityMassCeiling receipt := by
  rw [receiptVorticityMassReal_of_mem receipt time timeMem]
  exact wholeReceiptVorticityMass_le_ceiling receipt ⟨time, timeMem⟩

theorem receiptSerrinCoefficient_mul_mass_intervalIntegral
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    (∫ earlier in (0 : ℝ)..time,
        receiptSerrinCoefficientReal receipt earlier *
          receiptVorticityMassReal receipt earlier) =
      (72 * ν.coeff⁻¹) *
        ∫ earlier in (0 : ℝ)..time,
          commonTimeZeroExtension requestedTime
            (fun actualTime =>
              receipt.serrinDensity actualTime *
                wholeVorticityEuclideanMass
                  (receipt.wholePath actualTime)) earlier := by
  calc
    (∫ earlier in (0 : ℝ)..time,
        receiptSerrinCoefficientReal receipt earlier *
          receiptVorticityMassReal receipt earlier) =
        ∫ earlier in (0 : ℝ)..time,
          (72 * ν.coeff⁻¹) *
            commonTimeZeroExtension requestedTime
              (fun actualTime =>
                receipt.serrinDensity actualTime *
                  wholeVorticityEuclideanMass
                    (receipt.wholePath actualTime)) earlier := by
      apply intervalIntegral.integral_congr
      intro earlier earlierMem
      rw [uIcc_of_le timeMem.1] at earlierMem
      have earlierMemBig :
          earlier ∈ Icc (0 : ℝ) requestedTime :=
        ⟨earlierMem.1, earlierMem.2.trans timeMem.2⟩
      change
        receiptSerrinCoefficientReal receipt earlier *
            receiptVorticityMassReal receipt earlier =
          (72 * ν.coeff⁻¹) *
            commonTimeZeroExtension requestedTime
              (fun actualTime =>
                receipt.serrinDensity actualTime *
                  wholeVorticityEuclideanMass
                    (receipt.wholePath actualTime)) earlier
      rw [receiptSerrinCoefficientReal_of_mem
          receipt earlier earlierMemBig,
        receiptVorticityMassReal_of_mem
          receipt earlier earlierMemBig,
        commonTimeZeroExtension_of_mem
          requestedTime _ earlier earlierMemBig]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]

theorem receiptVorticityMassReal_le_initial_add_integral
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      receiptVorticityMassReal receipt time ≤
        wholeVorticityEuclideanMass initialState +
          ∫ earlier in (0 : ℝ)..time,
            receiptSerrinCoefficientReal receipt earlier *
              receiptVorticityMassReal receipt earlier := by
  intro time timeMem
  rcases eq_or_lt_of_le timeMem.1 with rfl | timePos
  · have zeroMem : (0 : ℝ) ∈ Icc (0 : ℝ) requestedTime :=
      ⟨le_rfl, receipt.requestedTimePos.le⟩
    rw [receiptVorticityMassReal_of_mem receipt 0 zeroMem]
    have zeroTimeEq :
        (⟨0, zeroMem⟩ : Icc (0 : ℝ) requestedTime) =
          ⟨0, ⟨le_rfl, receipt.requestedTimePos.le⟩⟩ := by
      rfl
    rw [zeroTimeEq, receipt.wholePath_initial]
    simp
  · let restricted :=
      restrictWholeContinuousMildSerrinReceipt
        timePos timeMem.2 receipt
    have terminalBound :=
      WholeContinuousMildSerrinReceipt.terminal_vorticityMass_le_initial_add_serrinEnergy
        restricted
    rw [restrict_serrinEnergy_eq_intervalIntegral_zeroExtension
      timePos timeMem.2 receipt] at terminalBound
    have integralEq :=
      receiptSerrinCoefficient_mul_mass_intervalIntegral
        receipt time timeMem
    rw [integralEq]
    have leftEq :
        receiptVorticityMassReal receipt time =
          wholeVorticityEuclideanMass
            (restricted.wholePath
              ⟨time, ⟨timePos.le, le_rfl⟩⟩) := by
      rw [receiptVorticityMassReal_of_mem receipt time timeMem]
      unfold restricted restrictWholeContinuousMildSerrinReceipt
      dsimp only [BoundedContinuousFunction.compContinuous_apply,
        Function.comp_apply]
      congr 2
    rw [← leftEq] at terminalBound
    exact terminalBound

theorem receiptVorticityMassReal_le_initial_mul_exp
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      receiptVorticityMassReal receipt time ≤
        wholeVorticityEuclideanMass initialState *
          Real.exp
            (∫ earlier in (0 : ℝ)..time,
              receiptSerrinCoefficientReal receipt earlier) := by
  exact le_initial_mul_exp_of_nonneg_le_initial_add_integral_mul
    receipt.requestedTimePos.le
    (receiptSerrinCoefficientReal_intervalIntegrable receipt)
    (receiptSerrinCoefficientReal_nonneg receipt)
    (receiptVorticityMassReal_continuousOn receipt)
    (receiptVorticityMassReal_le_ceiling receipt)
    (receiptVorticityMassReal_le_initial_add_integral receipt)

theorem receiptSerrinCoefficientReal_intervalIntegral_eq
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    (∫ time in (0 : ℝ)..requestedTime,
        receiptSerrinCoefficientReal receipt time) =
      (72 * ν.coeff⁻¹) *
        ∫ time,
          receipt.serrinDensity time
          ∂(commonTimeMeasure requestedTime) := by
  calc
    (∫ time in (0 : ℝ)..requestedTime,
        receiptSerrinCoefficientReal receipt time) =
        ∫ time in (0 : ℝ)..requestedTime,
          (72 * ν.coeff⁻¹) *
            commonTimeZeroExtension requestedTime
              receipt.serrinDensity time := by
      apply intervalIntegral.integral_congr
      intro time timeMem
      rw [uIcc_of_le receipt.requestedTimePos.le] at timeMem
      change
        receiptSerrinCoefficientReal receipt time =
          (72 * ν.coeff⁻¹) *
            commonTimeZeroExtension requestedTime
              receipt.serrinDensity time
      rw [receiptSerrinCoefficientReal_of_mem receipt time timeMem,
        commonTimeZeroExtension_of_mem
          requestedTime receipt.serrinDensity time timeMem]
    _ = (72 * ν.coeff⁻¹) *
          ∫ time in (0 : ℝ)..requestedTime,
            commonTimeZeroExtension requestedTime
              receipt.serrinDensity time := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      congr 1
      rw [← commonTime_integral_eq_intervalIntegral
        requestedTime receipt.requestedTimePos.le]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with time
      rw [commonTimeZeroExtension_of_mem
        requestedTime receipt.serrinDensity time.1 time.2]

theorem WholeContinuousMildSerrinReceipt.terminal_vorticityMass_le_initial_mul_exp_serrinAction
    {ν : Viscosity}
    {initialState :
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    wholeVorticityEuclideanMass
        (receipt.wholePath
          ⟨requestedTime,
            ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) ≤
      wholeVorticityEuclideanMass initialState *
        Real.exp
          ((72 * ν.coeff⁻¹) *
            ∫ time,
              receipt.serrinDensity time
              ∂(commonTimeMeasure requestedTime)) := by
  have terminalMem :
      requestedTime ∈ Icc (0 : ℝ) requestedTime :=
    ⟨receipt.requestedTimePos.le, le_rfl⟩
  have bound :=
    receiptVorticityMassReal_le_initial_mul_exp
      receipt requestedTime terminalMem
  rw [receiptVorticityMassReal_of_mem
      receipt requestedTime terminalMem,
    receiptSerrinCoefficientReal_intervalIntegral_eq receipt] at bound
  exact bound

end

end ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyExponential
end NavierStokes
end SaturationMonoid
