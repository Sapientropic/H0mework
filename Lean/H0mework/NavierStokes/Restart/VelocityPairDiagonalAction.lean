import H0mework.NavierStokes.Fourier.WholeVelocityPairDiagonalBudget
import H0mework.NavierStokes.PairRestart.PairDuhamelKineticTriadRedirect
import H0mework.NavierStokes.KineticRestart.ActualKineticViscousExhaustion
import H0mework.NavierStokes.Crossing.MassPersistence
import H0mework.NavierStokes.WholeSpace.WholeSerrinEnstrophyGronwall

/-!
# Source-generated whole-velocity pair diagonal action

The actual whole unforced receipt already determines its complete velocity
pair table before the fixed-output convolution quotient.  Installing its
Biot--Savart velocity on the common whole carrier commutes literally with
pair formation.  The complete negative-one diagonal action is therefore
paid by the same receipt's physical kinetic mass.

This module settles the occurrence-diagonal part of the endpoint
interference gate.  It does not bound the square of an aggregated output
row: any excess remains a concrete cross-pair gluing responsibility.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityPairDiagonalAction

open scoped BigOperators ENNReal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticViscousExhaustion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open
  ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation

noncomputable section

/-! ## Same-event pair formation -/

/-- One actual velocity-convection occurrence is literally pair formation
after the receipt's own Biot--Savart velocity has been installed on the
whole carrier. -/
theorem actualWholeContinuousVelocityPairVector_eq_wholeBiotSavartPair
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    actualWholeContinuousVelocityPairVector
        receipt first second time =
      wholeStateVelocityBilinearPairContribution
        (wholeBiotSavartVelocityState (receipt.wholePath time))
        (wholeBiotSavartVelocityState (receipt.wholePath time))
        (first, second) := by
  rfl

/-- Complete ordered-pair diagonal at one time of an actual whole receipt.
This is a readout of the existing pair carrier, not a new provenance norm. -/
def actualWholeVelocityPairNegativeOneDiagonalMass
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : Icc (0 : ℝ) requestedTime) : ℝ :=
  wholeVelocityPairNegativeOneDiagonalMass
    (wholeBiotSavartVelocityState (receipt.wholePath time))

theorem actualWholeVelocityPairNegativeOneDiagonalMass_nonneg
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    0 ≤ actualWholeVelocityPairNegativeOneDiagonalMass receipt time := by
  unfold actualWholeVelocityPairNegativeOneDiagonalMass
    wholeVelocityPairNegativeOneDiagonalMass
  exact tsum_nonneg fun pair =>
    wholeVelocityPairNegativeOneDiagonalDensity_nonneg _ pair

/-- Pointwise payment on the same actual receipt: the entire pre-quotient
ordered-pair diagonal is bounded by the square of its physical kinetic
mass. -/
theorem actualWholeVelocityPairNegativeOneDiagonalMass_le_kinetic
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    actualWholeVelocityPairNegativeOneDiagonalMass receipt time ≤
      puncturedWholeVorticityKineticMass
          (receipt.wholePath time) ^ 2 := by
  exact
    wholeVelocityPairNegativeOneDiagonalMass_wholeBiotSavartVelocityState_le
      (receipt.wholePath time)
      (wholePath_transverse receipt time)

/-! ## Whole source-owned receipt action -/

/-- The complete occurrence-diagonal action over the next whole unforced
receipt generated by one actual restart current. -/
def wholeRestartNextReceiptVelocityPairDiagonalAction
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) : ℝ≥0∞ :=
  ∫⁻ time,
    ENNReal.ofReal
      (actualWholeVelocityPairNegativeOneDiagonalMass
        current.nextReceipt time)
    ∂(commonTimeMeasure (wholeRestartDuration current.contact))

/-- The whole action is paid by the current physical kinetic mass and the
actual duration generated by the same source event.  No cutoff, pair count,
time horizon, or external energy certificate occurs in the mouth. -/
theorem wholeRestartNextReceiptVelocityPairDiagonalAction_le
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    wholeRestartNextReceiptVelocityPairDiagonalAction current ≤
      ENNReal.ofReal
          (puncturedWholeVorticityKineticMass
            current.contact.physicalState ^ 2) *
        (commonTimeMeasure
          (wholeRestartDuration current.contact)) Set.univ := by
  let mass :=
    puncturedWholeVorticityKineticMass current.contact.physicalState
  have massNonneg : 0 ≤ mass :=
    puncturedWholeVorticityKineticMass_nonneg _
  have kineticAE :
      ∀ᵐ time ∂(commonTimeMeasure
          (wholeRestartDuration current.contact)),
        puncturedWholeVorticityKineticMass
            (current.nextReceipt.wholePath time) ≤
          mass := by
    simpa only [mass, GeneratedWholeRestartCurrent.nextReceipt,
      wholeRestartPhysicalState_generatedPositiveWholeRestartContact] using
      (generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticMass_ae_le
        (generatedWholeRestartCanonicalReplay current.contact))
  unfold wholeRestartNextReceiptVelocityPairDiagonalAction
  calc
    (∫⁻ time,
        ENNReal.ofReal
          (actualWholeVelocityPairNegativeOneDiagonalMass
            current.nextReceipt time)
        ∂(commonTimeMeasure
          (wholeRestartDuration current.contact))) ≤
        ∫⁻ _time,
          ENNReal.ofReal (mass ^ 2)
          ∂(commonTimeMeasure
            (wholeRestartDuration current.contact)) := by
      apply lintegral_mono_ae
      filter_upwards [kineticAE] with time kineticLe
      apply ENNReal.ofReal_le_ofReal
      calc
        actualWholeVelocityPairNegativeOneDiagonalMass
              current.nextReceipt time ≤
            puncturedWholeVorticityKineticMass
                (current.nextReceipt.wholePath time) ^ 2 :=
          actualWholeVelocityPairNegativeOneDiagonalMass_le_kinetic
            current.nextReceipt time
        _ ≤ mass ^ 2 := by
          exact
            (sq_le_sq₀
              (puncturedWholeVorticityKineticMass_nonneg _)
              massNonneg).2 kineticLe
    _ =
        ENNReal.ofReal (mass ^ 2) *
          (commonTimeMeasure
            (wholeRestartDuration current.contact)) Set.univ := by
      rw [lintegral_const]
    _ =
        ENNReal.ofReal
            (puncturedWholeVorticityKineticMass
              current.contact.physicalState ^ 2) *
          (commonTimeMeasure
            (wholeRestartDuration current.contact)) Set.univ := by
      rfl

/-- In particular the source-generated diagonal action is finite.  This
closes the individual-occurrence side of the action ledger; locating any
remaining endpoint quadratic variation in the existing cross-gluing carrier
is the separate whole-output consumer. -/
theorem wholeRestartNextReceiptVelocityPairDiagonalAction_ne_top
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    wholeRestartNextReceiptVelocityPairDiagonalAction current ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_
    (wholeRestartNextReceiptVelocityPairDiagonalAction_le current)
  exact
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top
        (commonTimeMeasure
          (wholeRestartDuration current.contact)) Set.univ)

/-! ## Literal input-pair polarization -/

/-- Euclidean diagonal of an absolutely summable family before aggregation. -/
def pairVectorEuclideanDiagonal
    {index : Type*}
    (pairVector : index → ComplexCoordinateVector) : Real :=
  ∑' item, complexCoordinateAmplitudeSq (pairVector item)

/-- Literal ordered off-diagonal real interference of a pair family. -/
def pairVectorLiteralCrossInterference
    {index : Type*}
    [DecidableEq index]
    (pairVector : index → ComplexCoordinateVector) : Real :=
  ∑' first, ∑' second,
    if second = first then 0
    else complexCoordinateRealInner
      (pairVector first) (pairVector second)

private theorem norm_add_sq_le_two_mul
    {E : Type*}
    [NormedAddCommGroup E]
    (left right : E) :
    ‖left + right‖ ^ 2 ≤
      2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
  have normLe := norm_add_le left right
  have squareLe :
      ‖left + right‖ ^ 2 ≤ (‖left‖ + ‖right‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 normLe
  calc
    ‖left + right‖ ^ 2 ≤ (‖left‖ + ‖right‖) ^ 2 := squareLe
    _ ≤ 2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
      nlinarith [sq_nonneg (‖left‖ - ‖right‖)]

private theorem complexCoordinateAmplitudeSq_add_le_two_mul
    (left right : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (left + right) ≤
      2 * complexCoordinateAmplitudeSq left +
        2 * complexCoordinateAmplitudeSq right := by
  unfold complexCoordinateAmplitudeSq
  calc
    (∑ coordinate : Coordinate,
        Complex.normSq ((left + right) coordinate)) ≤
        ∑ coordinate : Coordinate,
          (2 * Complex.normSq (left coordinate) +
            2 * Complex.normSq (right coordinate)) := by
      apply Finset.sum_le_sum
      intro coordinate _coordinateMem
      simpa only [Pi.add_apply, Complex.normSq_eq_norm_sq] using
        norm_add_sq_le_two_mul
          (left coordinate) (right coordinate)
    _ =
        2 * (∑ coordinate : Coordinate,
          Complex.normSq (left coordinate)) +
        2 * (∑ coordinate : Coordinate,
          Complex.normSq (right coordinate)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem complexCoordinateAmplitudeSq_real_smul
    (scalar : ℝ)
    (vector : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (scalar • vector) =
      scalar ^ 2 * complexCoordinateAmplitudeSq vector := by
  simp_rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  change
    complexCoordinateVectorNormSq ((scalar : ℂ) • vector) = _
  rw [complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal]
  ring

private theorem complexCoordinateAmplitudeSq_half_add_le
    (left right : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq
        ((1 / 2 : ℝ) • (left + right)) ≤
      (1 / 2 : ℝ) *
        (complexCoordinateAmplitudeSq left +
          complexCoordinateAmplitudeSq right) := by
  rw [complexCoordinateAmplitudeSq_real_smul]
  have addLe := complexCoordinateAmplitudeSq_add_le_two_mul left right
  nlinarith

private theorem fourierCurlCoefficient_amplitudeSq_le_multiplier
    (wave : IntegerWavevector)
    (velocity : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq
        (fourierCurlCoefficient wave velocity) ≤
      integerWaveViscousMultiplier wave *
        complexCoordinateAmplitudeSq velocity := by
  have crossBound := complexWavevector_cross_normSq_le wave velocity
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rw [fourierCurlCoefficient,
    complexCoordinateVectorNormSq_smul,
    Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul]
  unfold integerWaveViscousMultiplier
  simpa only [pow_two, mul_assoc] using
    mul_le_mul_of_nonneg_left crossBound (sq_nonneg (2 * Real.pi))

private theorem complexCoordinateRealInner_comm
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left right =
      complexCoordinateRealInner right left := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _coordinateMem
  ring

/-- Exact countable polarization on the Euclidean three-coordinate carrier.
The off-diagonal summand retains both ordered input-pair indices. -/
theorem
    complexCoordinateAmplitudeSq_tsum_eq_pairDiagonal_add_literalCross
    {index : Type*}
    [DecidableEq index]
    (pairVector : index → ComplexCoordinateVector)
    (normSummable : Summable fun item => ‖pairVector item‖) :
    complexCoordinateAmplitudeSq (∑' item, pairVector item) =
      pairVectorEuclideanDiagonal pairVector +
        pairVectorLiteralCrossInterference pairVector := by
  let total : ComplexCoordinateVector := ∑' item, pairVector item
  have pairSummable : Summable pairVector := normSummable.of_norm
  have normProductSummable :
      Summable fun pair : index × index =>
        ‖pairVector pair.1‖ * ‖pairVector pair.2‖ := by
    have product :=
      summable_mul_of_summable_norm normSummable.norm normSummable.norm
    simpa only [Real.norm_eq_abs, abs_norm] using product
  have normSquareSummable :
      Summable fun item : index => ‖pairVector item‖ ^ 2 := by
    have diagonal :
        Summable fun item : index =>
          ‖pairVector item‖ * ‖pairVector item‖ :=
      normProductSummable.comp_injective
      (i := fun item : index => (item, item))
      (fun left right equality => congrArg Prod.fst equality)
    exact diagonal.congr fun item => (pow_two _).symm
  have diagonalSummable :
      Summable fun item : index =>
        complexCoordinateAmplitudeSq (pairVector item) := by
    exact ((normSquareSummable.mul_left 3).of_nonneg_of_le
      (fun item => complexCoordinateAmplitudeSq_nonneg _)
      (fun item =>
        complexCoordinateAmplitudeSq_le_three_mul_norm_sq
          (pairVector item)))
  have innerRowSummable (left : ComplexCoordinateVector) :
      Summable fun item : index =>
        complexCoordinateRealInner left (pairVector item) := by
    let functional := complexCoordinateRealInnerRightCLM left
    have mapped := pairSummable.map functional functional.continuous
    exact mapped.congr fun item => by
      simp only [Function.comp_apply, functional,
        complexCoordinateRealInnerRightCLM_apply]
  have totalInnerSummable :
      Summable fun item : index =>
        complexCoordinateRealInner (pairVector item) total := by
    have mapped := innerRowSummable total
    exact mapped.congr fun item =>
      complexCoordinateRealInner_comm total (pairVector item)
  have selfInnerSummable :
      Summable fun item : index =>
        complexCoordinateRealInner
          (pairVector item) (pairVector item) := by
    exact diagonalSummable.congr fun item => by
      rw [complexCoordinateRealInner_self,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  let crossRow : index → Real := fun first =>
    ∑' second,
      if second = first then 0
      else complexCoordinateRealInner
        (pairVector first) (pairVector second)
  have crossRowEq (first : index) :
      crossRow first =
        complexCoordinateRealInner (pairVector first) total -
          complexCoordinateRealInner
            (pairVector first) (pairVector first) := by
    have split :=
      (innerRowSummable (pairVector first)).tsum_eq_add_tsum_ite first
    rw [← complexCoordinateRealInner_tsum_right
      (pairVector first) pairVector pairSummable] at split
    change _ = _ - _
    linarith
  have crossRowSummable : Summable crossRow := by
    exact (totalInnerSummable.sub selfInnerSummable).congr
      (fun first => (crossRowEq first).symm)
  calc
    complexCoordinateAmplitudeSq (∑' item, pairVector item) =
        complexCoordinateRealInner total total := by
      rw [complexCoordinateRealInner_self,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    _ = ∑' item : index,
          complexCoordinateRealInner (pairVector item) total := by
      rw [show total = ∑' item, pairVector item by rfl]
      calc
        complexCoordinateRealInner (∑' item, pairVector item) total =
            complexCoordinateRealInner total
              (∑' item, pairVector item) :=
          complexCoordinateRealInner_comm _ _
        _ = _ :=
          complexCoordinateRealInner_tsum_right
            total pairVector pairSummable
        _ = ∑' item : index,
              complexCoordinateRealInner (pairVector item) total := by
          apply tsum_congr
          intro item
          exact complexCoordinateRealInner_comm _ _
    _ = ∑' item : index,
          (complexCoordinateRealInner
              (pairVector item) (pairVector item) + crossRow item) := by
      apply tsum_congr
      intro item
      rw [crossRowEq]
      ring
    _ =
        (∑' item : index,
          complexCoordinateRealInner
            (pairVector item) (pairVector item)) +
          ∑' item : index, crossRow item := by
      exact selfInnerSummable.tsum_add crossRowSummable
    _ = pairVectorEuclideanDiagonal pairVector +
          pairVectorLiteralCrossInterference pairVector := by
      unfold pairVectorEuclideanDiagonal
        pairVectorLiteralCrossInterference crossRow
      congr 1

/-! ## The actual same-receipt pair family -/

/-- Symmetric input-pair occurrence at one fixed output.  The factor `1/2`
keeps the complete ordered family equal to the original nonlinear row. -/
def actualWholeSymmetricVorticityPairVector
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    ComplexCoordinateVector :=
  (1 / 2 : Real) •
    (actualWholeContinuousPairVector receipt output first time +
      actualWholeContinuousPairVector
        receipt output (output - first) time)

/-- The same symmetric input orbit before the physical curl. -/
def actualWholeSymmetricVelocityPairVector
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    ComplexCoordinateVector :=
  (1 / 2 : Real) •
    (actualWholeContinuousVelocityPairVector
        receipt first (output - first) time +
      actualWholeContinuousVelocityPairVector
        receipt (output - first) first time)

/-- The actual symmetric velocity occurrence compiles exactly to the
symmetric vorticity occurrence on the identical receipt and incidence. -/
theorem actualWholeSymmetricVelocityPairVector_curl_eq
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    fourierCurlCoefficient output
        (actualWholeSymmetricVelocityPairVector
          receipt output first time) =
      actualWholeSymmetricVorticityPairVector
        receipt output first time := by
  let second := output - first
  have incidence : first + second = output := by
    unfold second
    ext coordinate
    simp
  have compiler :=
    actualWholeContinuousVelocityPair_add_swap_curl_eq_pairVector
      receipt first second time
  rw [incidence] at compiler
  unfold actualWholeSymmetricVelocityPairVector
    actualWholeSymmetricVorticityPairVector
  change
    fourierCurlCoefficient output
        (((1 / 2 : Real) : Complex) •
          (actualWholeContinuousVelocityPairVector
              receipt first second time +
            actualWholeContinuousVelocityPairVector
              receipt second first time)) =
      (((1 / 2 : Real) : Complex) •
        (actualWholeContinuousPairVector receipt output first time +
          actualWholeContinuousPairVector receipt output second time))
  rw [← fourierCurlCoefficientContinuousLinearMap_apply,
    map_smul, fourierCurlCoefficientContinuousLinearMap_apply,
    compiler]

/-- Inverse-Laplacian square of one symmetric fixed-output pair orbit. -/
def actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) : Real :=
  (integerWaveViscousMultiplier output)⁻¹ *
    complexCoordinateAmplitudeSq
      (actualWholeSymmetricVorticityPairVector
        receipt output first time)

theorem
    actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_nonneg
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    0 ≤ actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
      receipt output first time := by
  unfold actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
  apply mul_nonneg
  · apply inv_nonneg.mpr
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _)
  · exact complexCoordinateAmplitudeSq_nonneg _

/-- The strong-vorticity diagonal of one actual incidence is paid by the
two ordered velocity occurrences that generate that same curl orbit. -/
theorem
    actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_le
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
        receipt output first time ≤
      (1 / 2 : Real) *
        (wholeBiotSavartVelocityPairEuclideanDensity
            (receipt.wholePath time) (first, output - first) +
          wholeBiotSavartVelocityPairEuclideanDensity
            (receipt.wholePath time) (output - first, first)) := by
  by_cases outputZero : output = 0
  · rw [outputZero]
    simp [actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity,
      integerWaveViscousMultiplier]
    exact add_nonneg
      (wholeBiotSavartVelocityPairEuclideanDensity_nonneg _ _)
      (wholeBiotSavartVelocityPairEuclideanDensity_nonneg _ _)
  · have multiplierPos :
        0 < integerWaveViscousMultiplier output := by
      unfold integerWaveViscousMultiplier
      exact mul_pos
        (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
        (integerWaveNormSq_pos outputZero)
    have curlLe :=
      fourierCurlCoefficient_amplitudeSq_le_multiplier output
        (actualWholeSymmetricVelocityPairVector
          receipt output first time)
    have symmetricVelocityLe :=
      complexCoordinateAmplitudeSq_half_add_le
        (actualWholeContinuousVelocityPairVector
          receipt first (output - first) time)
        (actualWholeContinuousVelocityPairVector
          receipt (output - first) first time)
    rw [actualWholeSymmetricVelocityPairVector_curl_eq
      receipt output first time] at curlLe
    unfold actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
    calc
      (integerWaveViscousMultiplier output)⁻¹ *
          complexCoordinateAmplitudeSq
            (actualWholeSymmetricVorticityPairVector
              receipt output first time) ≤
          (integerWaveViscousMultiplier output)⁻¹ *
            (integerWaveViscousMultiplier output *
              complexCoordinateAmplitudeSq
                (actualWholeSymmetricVelocityPairVector
                  receipt output first time)) := by
        exact mul_le_mul_of_nonneg_left curlLe (inv_nonneg.mpr multiplierPos.le)
      _ = complexCoordinateAmplitudeSq
            (actualWholeSymmetricVelocityPairVector
              receipt output first time) := by
        field_simp [multiplierPos.ne']
      _ ≤
          (1 / 2 : Real) *
            (complexCoordinateAmplitudeSq
                (actualWholeContinuousVelocityPairVector
                  receipt first (output - first) time) +
              complexCoordinateAmplitudeSq
                (actualWholeContinuousVelocityPairVector
                  receipt (output - first) first time)) := symmetricVelocityLe
      _ =
          (1 / 2 : Real) *
            (wholeBiotSavartVelocityPairEuclideanDensity
                (receipt.wholePath time) (first, output - first) +
              wholeBiotSavartVelocityPairEuclideanDensity
                (receipt.wholePath time) (output - first, first)) := by
        rfl

private def outputFirstInputPairEquiv :
    (IntegerWavevector × IntegerWavevector) ≃
      (IntegerWavevector × IntegerWavevector) where
  toFun indexed := (indexed.2, indexed.1 - indexed.2)
  invFun pair := (pair.1 + pair.2, pair.1)
  left_inv indexed := by
    ext coordinate <;> simp
  right_inv pair := by
    ext coordinate <;> simp

@[simp] private theorem outputFirstInputPairEquiv_apply
    (indexed : IntegerWavevector × IntegerWavevector) :
    outputFirstInputPairEquiv indexed =
      (indexed.2, indexed.1 - indexed.2) :=
  rfl

private def outputFirstSwappedInputPairEquiv :
    (IntegerWavevector × IntegerWavevector) ≃
      (IntegerWavevector × IntegerWavevector) :=
  outputFirstInputPairEquiv.trans
    (Equiv.prodComm IntegerWavevector IntegerWavevector)

@[simp] private theorem outputFirstSwappedInputPairEquiv_apply
    (indexed : IntegerWavevector × IntegerWavevector) :
    outputFirstSwappedInputPairEquiv indexed =
      (indexed.1 - indexed.2, indexed.2) :=
  rfl

/-- Complete strong-vorticity occurrence diagonal before fixed-output
aggregation, on one actual receipt and time. -/
def actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime) : Real :=
  ∑' indexed : IntegerWavevector × IntegerWavevector,
    actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
      receipt indexed.1 indexed.2 time

theorem
    actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output first : IntegerWavevector) :
    Continuous fun time : Icc (0 : Real) requestedTime =>
      actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
        receipt output first time := by
  unfold actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
  apply Continuous.const_mul
  apply
    ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin.complexCoordinateAmplitudeSq_continuous.comp
  unfold actualWholeSymmetricVorticityPairVector
  exact ((actualWholeContinuousPairVector_continuous
    receipt output first).add
      (actualWholeContinuousPairVector_continuous
        receipt output (output - first))).const_smul (1 / 2 : Real)

theorem actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_measurable
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    Measurable fun time : Icc (0 : Real) requestedTime =>
      actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
        receipt time := by
  unfold actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
  apply Measurable.tsum
  intro indexed
  exact
    (actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_continuous
      receipt indexed.1 indexed.2).measurable

theorem actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_nonneg
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime) :
    0 ≤ actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
      receipt time := by
  exact tsum_nonneg fun indexed =>
    actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_nonneg
      receipt indexed.1 indexed.2 time

theorem
    summable_actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime) :
    Summable fun indexed : IntegerWavevector × IntegerWavevector =>
      actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
        receipt indexed.1 indexed.2 time := by
  let base := wholeBiotSavartVelocityPairEuclideanDensity
    (receipt.wholePath time)
  have baseSummable : Summable base :=
    summable_wholeBiotSavartVelocityPairEuclideanDensity
      (receipt.wholePath time) (wholePath_transverse receipt time)
  have directSummable :
      Summable fun indexed : IntegerWavevector × IntegerWavevector =>
        base (indexed.2, indexed.1 - indexed.2) := by
    exact (outputFirstInputPairEquiv.summable_iff.mpr baseSummable).congr
      fun indexed => rfl
  have swappedSummable :
      Summable fun indexed : IntegerWavevector × IntegerWavevector =>
        base (indexed.1 - indexed.2, indexed.2) := by
    exact
      (outputFirstSwappedInputPairEquiv.summable_iff.mpr baseSummable).congr
        fun indexed => rfl
  have majorantSummable :
      Summable fun indexed : IntegerWavevector × IntegerWavevector =>
        (1 / 2 : Real) *
          (base (indexed.2, indexed.1 - indexed.2) +
            base (indexed.1 - indexed.2, indexed.2)) :=
    (directSummable.add swappedSummable).mul_left (1 / 2 : Real)
  exact majorantSummable.of_nonneg_of_le
    (fun indexed =>
      actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_nonneg
        receipt indexed.1 indexed.2 time)
    (fun indexed => by
      simpa only [base] using
        actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_le
          receipt indexed.1 indexed.2 time)

/-- The complete strong-vorticity pair diagonal is paid by the identical
state's native kinetic--vorticity product. -/
theorem actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_le
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime) :
    actualWholeSymmetricVorticityPairNegativeOneDiagonalMass receipt time ≤
      puncturedWholeVorticityKineticMass (receipt.wholePath time) *
        wholeVorticityEuclideanMass (receipt.wholePath time) := by
  let base := wholeBiotSavartVelocityPairEuclideanDensity
    (receipt.wholePath time)
  have baseSummable : Summable base :=
    summable_wholeBiotSavartVelocityPairEuclideanDensity
      (receipt.wholePath time) (wholePath_transverse receipt time)
  have directSummable :
      Summable fun indexed : IntegerWavevector × IntegerWavevector =>
        base (indexed.2, indexed.1 - indexed.2) := by
    exact (outputFirstInputPairEquiv.summable_iff.mpr baseSummable).congr
      fun indexed => rfl
  have swappedSummable :
      Summable fun indexed : IntegerWavevector × IntegerWavevector =>
        base (indexed.1 - indexed.2, indexed.2) := by
    exact
      (outputFirstSwappedInputPairEquiv.summable_iff.mpr baseSummable).congr
        fun indexed => rfl
  have directTsum :
      (∑' indexed : IntegerWavevector × IntegerWavevector,
        base (indexed.2, indexed.1 - indexed.2)) = ∑' pair, base pair := by
    simpa only [Function.comp_apply, outputFirstInputPairEquiv_apply] using
      (outputFirstInputPairEquiv.tsum_eq base)
  have swappedTsum :
      (∑' indexed : IntegerWavevector × IntegerWavevector,
        base (indexed.1 - indexed.2, indexed.2)) = ∑' pair, base pair := by
    simpa only [Function.comp_apply,
      outputFirstSwappedInputPairEquiv_apply]
      using (outputFirstSwappedInputPairEquiv.tsum_eq base)
  have targetSummable :=
    summable_actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
      receipt time
  have majorantSummable :
      Summable fun indexed : IntegerWavevector × IntegerWavevector =>
        (1 / 2 : Real) *
          (base (indexed.2, indexed.1 - indexed.2) +
            base (indexed.1 - indexed.2, indexed.2)) :=
    (directSummable.add swappedSummable).mul_left (1 / 2 : Real)
  calc
    actualWholeSymmetricVorticityPairNegativeOneDiagonalMass receipt time ≤
        ∑' indexed : IntegerWavevector × IntegerWavevector,
          (1 / 2 : Real) *
            (base (indexed.2, indexed.1 - indexed.2) +
              base (indexed.1 - indexed.2, indexed.2)) := by
      unfold actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
      exact Summable.tsum_le_tsum
        (fun indexed => by
          simpa only [base] using
            actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_le
              receipt indexed.1 indexed.2 time)
        targetSummable majorantSummable
    _ = ∑' pair, base pair := by
      rw [tsum_mul_left,
        directSummable.tsum_add swappedSummable,
        directTsum, swappedTsum]
      ring
    _ = wholeBiotSavartVelocityPairEuclideanMass
          (receipt.wholePath time) := rfl
    _ ≤
        puncturedWholeVorticityKineticMass (receipt.wholePath time) *
          wholeVorticityEuclideanMass (receipt.wholePath time) :=
      wholeBiotSavartVelocityPairEuclideanMass_le
        (receipt.wholePath time) (wholePath_transverse receipt time)

/-- Product-indexed incidence mass is exactly the outputwise weighted
diagonal appearing in the fixed-output polarization. -/
theorem
    actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_eq_outputTsum
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime) :
    actualWholeSymmetricVorticityPairNegativeOneDiagonalMass receipt time =
      ∑' output : IntegerWavevector,
        (integerWaveViscousMultiplier output)⁻¹ *
          pairVectorEuclideanDiagonal
            (fun first : IntegerWavevector =>
              actualWholeSymmetricVorticityPairVector
                receipt output first time) := by
  have pairSummable :=
    summable_actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
      receipt time
  unfold actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
  rw [pairSummable.tsum_prod]
  apply tsum_congr
  intro output
  unfold actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
    pairVectorEuclideanDiagonal
  change
    (∑' first : IntegerWavevector,
      (integerWaveViscousMultiplier output)⁻¹ *
        complexCoordinateAmplitudeSq
          (actualWholeSymmetricVorticityPairVector
            receipt output first time)) = _
  rw [tsum_mul_left]

/-! ## Native kinetic--viscous payment of the strong diagonal -/

private theorem pairDiagonal_ae_comp_commonTimeInclusion
    {Tsmall Tbig : ℝ}
    (timeLe : Tsmall ≤ Tbig)
    {predicate : Icc (0 : ℝ) Tbig → Prop}
    (eventuallyBig :
      ∀ᵐ time ∂(commonTimeMeasure Tbig), predicate time) :
    ∀ᵐ time ∂(commonTimeMeasure Tsmall),
      predicate (commonTimeInclusion timeLe time) := by
  have onImage :
      ∀ᵐ time ∂
          (commonTimeMeasure Tbig).restrict
            (Set.range (commonTimeInclusion timeLe)),
        predicate time :=
    MeasureTheory.ae_restrict_le eventuallyBig
  exact
    (commonTimeInclusion_measurePreserving timeLe
      |>.quasiMeasurePreserving.tendsto_ae) onImage

private theorem wholeVorticityEuclideanMass_nonneg_local
    (state : ComplexVorticityHilbertState) :
    0 ≤ wholeVorticityEuclideanMass state := by
  unfold wholeVorticityEuclideanMass
  exact tsum_nonneg fun wave => sq_nonneg _

/-- The source-selected prefix inherits the kinetic ceiling of its actual
restart current. -/
theorem nextContactPrefix_kineticMass_ae_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time ∂(commonTimeMeasure current.nextContact.time.1),
      puncturedWholeVorticityKineticMass
          (current.nextContact.prefixReceipt.wholePath time) ≤
        puncturedWholeVorticityKineticMass
          current.contact.physicalState := by
  have fullMassLe :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticMass_ae_le
      (generatedWholeRestartCanonicalReplay current.contact)
  have pulled :=
    pairDiagonal_ae_comp_commonTimeInclusion
      current.nextContact.time.2.2 fullMassLe
  filter_upwards [pulled] with time massLe
  simpa only [prefixReceipt,
    restrictWholeContinuousMildSerrinReceipt,
    BoundedContinuousFunction.compContinuous_apply,
    GeneratedWholeRestartCurrent.nextReceipt,
    wholeRestartPhysicalState_generatedPositiveWholeRestartContact] using
      massLe

/-- The complete physical vorticity integral of one receipt is its abstract
whole-prefix ledger payment at the terminal time. -/
theorem lintegral_receiptWholeVorticityMass_eq_prefix
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    (∫⁻ time,
        ENNReal.ofReal
          (wholeVorticityEuclideanMass (receipt.wholePath time))
        ∂(commonTimeMeasure requestedTime)) =
      ENNReal.ofReal
        (wholePrefixVorticityMass
          ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
          receipt.stateLimit) := by
  let mass : Icc (0 : Real) requestedTime → Real := fun time =>
    wholeVorticityEuclideanMass (receipt.wholePath time)
  have massContinuous : Continuous mass :=
    wholeReceiptVorticityMass_continuous receipt
  have massIntegrable :
      Integrable mass (commonTimeMeasure requestedTime) :=
    massContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have massNonneg :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime), 0 ≤ mass time :=
    Filter.Eventually.of_forall fun time =>
      wholeVorticityEuclideanMass_nonneg_local (receipt.wholePath time)
  have realIntegralEq :
      (∫ time, mass time ∂(commonTimeMeasure requestedTime)) =
        wholePrefixVorticityMass
          ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
          receipt.stateLimit := by
    calc
      (∫ time, mass time ∂(commonTimeMeasure requestedTime)) =
          ∫ time,
            wholeVorticityEuclideanMass
              (wholeRestartReceiptPhysicalTrajectory receipt time.1)
            ∂(commonTimeMeasure requestedTime) := by
        apply integral_congr_ae
        filter_upwards with time
        unfold mass wholeRestartReceiptPhysicalTrajectory
        rw [projIcc_of_mem receipt.requestedTimePos.le time.2]
      _ =
          ∫ actual in (0 : Real)..requestedTime,
            wholeVorticityEuclideanMass
              (wholeRestartReceiptPhysicalTrajectory receipt actual) := by
        simpa only [] using
          (commonTime_integral_eq_intervalIntegral
            requestedTime receipt.requestedTimePos.le
            (fun actual =>
              wholeVorticityEuclideanMass
                (wholeRestartReceiptPhysicalTrajectory receipt actual)))
      _ =
          wholePrefixVorticityMass
            ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
            receipt.stateLimit := by
        symm
        exact wholePrefixVorticityMass_receipt_eq_intervalIntegral
          receipt
          ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
  rw [← ofReal_integral_eq_lintegral_ofReal
    massIntegrable massNonneg, realIntegralEq]

/-- Lintegral of the strong-vorticity pair diagonal on the exact selected
prefix of one native restart edge. -/
def wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : ℝ≥0∞ :=
  ∫⁻ time,
    ENNReal.ofReal
      (actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
        current.nextContact.prefixReceipt time)
    ∂(commonTimeMeasure current.nextContact.time.1)

/-- The edge action is paid by the same current's kinetic mass and its
source-generated prefix vorticity ledger. -/
theorem wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction current ≤
      ENNReal.ofReal
        (puncturedWholeVorticityKineticMass
            current.contact.physicalState *
          wholePrefixVorticityMass
            ⟨current.nextContact.time.1,
              ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
            current.nextContact.prefixReceipt.stateLimit) := by
  let receipt := current.nextContact.prefixReceipt
  let kinetic := puncturedWholeVorticityKineticMass
    current.contact.physicalState
  have kineticNonneg : 0 ≤ kinetic :=
    puncturedWholeVorticityKineticMass_nonneg _
  have kineticAE := nextContactPrefix_kineticMass_ae_le current
  have massAE :
      ∀ᵐ time ∂(commonTimeMeasure current.nextContact.time.1),
        actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
            receipt time ≤
          kinetic * wholeVorticityEuclideanMass
            (receipt.wholePath time) := by
    filter_upwards [kineticAE] with time kineticLe
    calc
      actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
            receipt time ≤
          puncturedWholeVorticityKineticMass
              (receipt.wholePath time) *
            wholeVorticityEuclideanMass (receipt.wholePath time) :=
        actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_le
          receipt time
      _ ≤
          kinetic * wholeVorticityEuclideanMass
            (receipt.wholePath time) :=
        mul_le_mul_of_nonneg_right kineticLe
          (wholeVorticityEuclideanMass_nonneg_local _)
  have vorticityMeasurable :
      Measurable fun time : Icc (0 : Real) current.nextContact.time.1 =>
        ENNReal.ofReal
          (wholeVorticityEuclideanMass (receipt.wholePath time)) :=
    (wholeReceiptVorticityMass_continuous receipt).measurable.ennreal_ofReal
  unfold wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction
  calc
    (∫⁻ time,
        ENNReal.ofReal
          (actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
            receipt time)
        ∂(commonTimeMeasure current.nextContact.time.1)) ≤
        ∫⁻ time,
          ENNReal.ofReal
            (kinetic * wholeVorticityEuclideanMass
              (receipt.wholePath time))
          ∂(commonTimeMeasure current.nextContact.time.1) := by
      apply lintegral_mono_ae
      filter_upwards [massAE] with time massLe
      exact ENNReal.ofReal_le_ofReal massLe
    _ =
        ENNReal.ofReal kinetic *
          ∫⁻ time,
            ENNReal.ofReal
              (wholeVorticityEuclideanMass (receipt.wholePath time))
            ∂(commonTimeMeasure current.nextContact.time.1) := by
      simp_rw [ENNReal.ofReal_mul kineticNonneg]
      exact lintegral_const_mul
        (ENNReal.ofReal kinetic) vorticityMeasurable
    _ =
        ENNReal.ofReal kinetic *
          ENNReal.ofReal
            (wholePrefixVorticityMass
              ⟨current.nextContact.time.1,
                ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
              receipt.stateLimit) := by
      rw [lintegral_receiptWholeVorticityMass_eq_prefix receipt]
    _ =
        ENNReal.ofReal
          (puncturedWholeVorticityKineticMass
              current.contact.physicalState *
            wholePrefixVorticityMass
              ⟨current.nextContact.time.1,
                ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
              current.nextContact.prefixReceipt.stateLimit) := by
      rw [ENNReal.ofReal_mul kineticNonneg]

/-- Real readout of the finite source-owned edge action. -/
def wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  (wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction current).toReal

/-- The exact pair diagonal on one source-selected prefix is integrable in
physical time; its finiteness is paid by that prefix's kinetic--viscous
ledger. -/
theorem
    integrable_nextContactPrefixSymmetricVorticityPairNegativeOneDiagonalMass
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    Integrable
      (actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
        current.nextContact.prefixReceipt)
      (commonTimeMeasure current.nextContact.time.1) := by
  let mass := actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
    current.nextContact.prefixReceipt
  have massMeasurable : Measurable mass :=
    actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_measurable
      current.nextContact.prefixReceipt
  have massNonneg :
      0 ≤ᵐ[commonTimeMeasure current.nextContact.time.1] mass :=
    Filter.Eventually.of_forall fun time =>
      actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_nonneg
        current.nextContact.prefixReceipt time
  have actionFinite :
      wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction current < ⊤ :=
    lt_of_le_of_lt
      (wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction_le current)
      ENNReal.ofReal_lt_top
  have finiteIntegral : HasFiniteIntegral mass
      (commonTimeMeasure current.nextContact.time.1) :=
    (hasFiniteIntegral_iff_ofReal massNonneg).2 actionFinite
  exact ⟨massMeasurable.aestronglyMeasurable, finiteIntegral⟩

/-- The real edge readout is the ordinary integral of the same literal
pair-diagonal incidence mass. -/
theorem
    wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal_eq_integral
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal current =
      ∫ time,
        actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
          current.nextContact.prefixReceipt time
        ∂(commonTimeMeasure current.nextContact.time.1) := by
  let mass := actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
    current.nextContact.prefixReceipt
  have massIntegrable : Integrable mass
      (commonTimeMeasure current.nextContact.time.1) :=
    integrable_nextContactPrefixSymmetricVorticityPairNegativeOneDiagonalMass
      current
  have massNonneg :
      0 ≤ᵐ[commonTimeMeasure current.nextContact.time.1] mass :=
    Filter.Eventually.of_forall fun time =>
      actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_nonneg
        current.nextContact.prefixReceipt time
  have ofRealIntegral :=
    ofReal_integral_eq_lintegral_ofReal massIntegrable massNonneg
  unfold wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
    wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction
  change
    (∫⁻ time, ENNReal.ofReal (mass time)
      ∂(commonTimeMeasure current.nextContact.time.1)).toReal =
      ∫ time, mass time ∂(commonTimeMeasure current.nextContact.time.1)
  rw [← ofRealIntegral, ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae massNonneg

theorem wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal current ≤
      puncturedWholeVorticityKineticMass
          current.contact.physicalState *
        wholePrefixVorticityMass
          ⟨current.nextContact.time.1,
            ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
          current.nextContact.prefixReceipt.stateLimit := by
  unfold wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
  have actionLe :=
    wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction_le current
  calc
    (wholeRestartNextPrefixSymmetricVorticityPairDiagonalAction current).toReal ≤
        (ENNReal.ofReal
          (puncturedWholeVorticityKineticMass
              current.contact.physicalState *
            wholePrefixVorticityMass
              ⟨current.nextContact.time.1,
                ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
              current.nextContact.prefixReceipt.stateLimit)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top actionLe
    _ = _ := by
      rw [ENNReal.toReal_ofReal]
      exact mul_nonneg
        (puncturedWholeVorticityKineticMass_nonneg _)
        (wholePrefixVorticityMass_nonneg _ _)

/-- Same-edge kinetic--vorticity product selected by the native restart
source. -/
def wholeRestartPrefixKineticVorticityPayment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) : Real :=
  puncturedWholeVorticityKineticMass
      (run initial index).contact.physicalState *
    wholePrefixVorticityMass
      ⟨(run initial index).nextContact.time.1,
        ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩
      (run initial index).nextContact.prefixReceipt.stateLimit

theorem wholeRestartPrefixKineticVorticityPayment_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) :
    0 ≤ wholeRestartPrefixKineticVorticityPayment initial index := by
  unfold wholeRestartPrefixKineticVorticityPayment
  exact mul_nonneg
    (puncturedWholeVorticityKineticMass_nonneg _)
    (wholePrefixVorticityMass_nonneg _ _)

/-- The existing native kinetic telescope pays the complete pair-diagonal
product of the identical edge. -/
theorem wholeRestartPrefixKineticVorticityPayment_le_nextDissipation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) :
    wholeRestartPrefixKineticVorticityPayment initial index ≤
      (puncturedWholeVorticityKineticMass
          initial.contact.physicalState /
        (2 * nu.coeff)) *
      wholeRestartNextKineticDissipationPayment initial index := by
  unfold wholeRestartPrefixKineticVorticityPayment
  rw [prefixReceipt_terminal_wholePrefixVorticityMass_eq]
  unfold wholeRestartNextKineticDissipationPayment
  have kineticLe :=
    run_contact_kineticMass_antitone initial (Nat.zero_le index)
  have prefixNonneg :=
    wholePrefixVorticityMass_nonneg
      (run initial index).nextContact.time
      (run initial index).nextReceipt.stateLimit
  calc
    puncturedWholeVorticityKineticMass
          (run initial index).contact.physicalState *
        wholePrefixVorticityMass
          (run initial index).nextContact.time
          (run initial index).nextReceipt.stateLimit ≤
      puncturedWholeVorticityKineticMass
          initial.contact.physicalState *
        wholePrefixVorticityMass
          (run initial index).nextContact.time
          (run initial index).nextReceipt.stateLimit :=
      mul_le_mul_of_nonneg_right kineticLe prefixNonneg
    _ =
      (puncturedWholeVorticityKineticMass
          initial.contact.physicalState /
        (2 * nu.coeff)) *
        (2 * nu.coeff *
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit) := by
      field_simp [nu.coeff_pos.ne']

/-- Across the complete actual restart run, the strong-vorticity occurrence
diagonal is summable by the source-owned kinetic dissipation ledger. -/
theorem
    summable_run_nextPrefixSymmetricVorticityPairDiagonalActionReal
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Summable fun index : Nat =>
      wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
        (run initial index) := by
  have paymentSummable :
      Summable fun index : Nat =>
        wholeRestartPrefixKineticVorticityPayment initial index := by
    have scaledSummable :=
      (summable_wholeRestartNextKineticDissipationPayment initial).mul_left
        (puncturedWholeVorticityKineticMass
            initial.contact.physicalState /
          (2 * nu.coeff))
    exact scaledSummable.of_nonneg_of_le
      (wholeRestartPrefixKineticVorticityPayment_nonneg initial)
      (wholeRestartPrefixKineticVorticityPayment_le_nextDissipation initial)
  exact paymentSummable.of_nonneg_of_le
    (fun index => ENNReal.toReal_nonneg)
    (fun index =>
      wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal_le
        (run initial index))

theorem summable_norm_actualWholeSymmetricVorticityPairVector
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    Summable fun first : IntegerWavevector =>
      ‖actualWholeSymmetricVorticityPairVector
        receipt output first time‖ := by
  let pairVector : IntegerWavevector → ComplexCoordinateVector :=
    fun first =>
      actualWholeContinuousPairVector receipt output first time
  have directSummable : Summable fun first => ‖pairVector first‖ :=
    summable_norm_actualWholeContinuousPairVector
      receipt output time
  have swappedSummable :
      Summable fun first => ‖pairVector (output - first)‖ := by
    have reindexed :=
      (outputSubEquiv output).summable_iff.mpr directSummable
    exact reindexed.congr fun first => by
      rw [Function.comp_apply, outputSubEquiv_apply]
  have majorantSummable :
      Summable fun first =>
        (1 / 2 : Real) *
          (‖pairVector first‖ + ‖pairVector (output - first)‖) :=
    (directSummable.add swappedSummable).mul_left (1 / 2 : Real)
  exact majorantSummable.of_nonneg_of_le
    (fun first => norm_nonneg _)
    (fun first => by
      unfold actualWholeSymmetricVorticityPairVector pairVector
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
      exact mul_le_mul_of_nonneg_left
        (norm_add_le _ _) (by norm_num))

/-- Aggregating the actual symmetric pair family reproduces the original
fixed-output nonlinear row on the identical receipt and time. -/
theorem tsum_actualWholeSymmetricVorticityPairVector_eq_pairTsum
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    (∑' first : IntegerWavevector,
        actualWholeSymmetricVorticityPairVector
          receipt output first time) =
      ∑' first : IntegerWavevector,
        actualWholeContinuousPairVector receipt output first time := by
  let pairVector : IntegerWavevector → ComplexCoordinateVector :=
    fun first =>
      actualWholeContinuousPairVector receipt output first time
  have pairSummable : Summable pairVector :=
    (summable_norm_actualWholeContinuousPairVector
      receipt output time).of_norm
  have swappedSummable :
      Summable fun first => pairVector (output - first) := by
    have reindexed :=
      (outputSubEquiv output).summable_iff.mpr pairSummable
    exact reindexed.congr fun first => by
      rw [Function.comp_apply, outputSubEquiv_apply]
  have swappedTsum :
      (∑' first : IntegerWavevector,
        pairVector (output - first)) =
      ∑' first : IntegerWavevector, pairVector first := by
    simpa only [outputSubEquiv_apply] using
      (outputSubEquiv output).tsum_eq pairVector
  have pairAddSummable :
      Summable fun first =>
        pairVector first + pairVector (output - first) :=
    pairSummable.add swappedSummable
  calc
    (∑' first : IntegerWavevector,
        actualWholeSymmetricVorticityPairVector
          receipt output first time) =
        (1 / 2 : Real) •
          ∑' first : IntegerWavevector,
            (pairVector first + pairVector (output - first)) := by
      exact (pairAddSummable.hasSum.const_smul (1 / 2 : Real)).tsum_eq
    _ = (1 / 2 : Real) •
          ((∑' first : IntegerWavevector, pairVector first) +
            ∑' first : IntegerWavevector,
              pairVector (output - first)) := by
      rw [pairSummable.tsum_add swappedSummable]
    _ = ∑' first : IntegerWavevector, pairVector first := by
      rw [swappedTsum]
      module

/-- The fixed-output nonlinear square of one actual receipt is exactly its
symmetric input-pair diagonal plus literal ordered cross-pair interference. -/
theorem
    actualWholeContinuousPairAggregateAmplitudeSq_eq_diagonal_add_literalCross
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    complexCoordinateAmplitudeSq
        (∑' first : IntegerWavevector,
          actualWholeContinuousPairVector receipt output first time) =
      pairVectorEuclideanDiagonal
          (fun first : IntegerWavevector =>
            actualWholeSymmetricVorticityPairVector
              receipt output first time) +
        pairVectorLiteralCrossInterference
          (fun first : IntegerWavevector =>
            actualWholeSymmetricVorticityPairVector
              receipt output first time) := by
  rw [← tsum_actualWholeSymmetricVorticityPairVector_eq_pairTsum
    receipt output time]
  exact
    complexCoordinateAmplitudeSq_tsum_eq_pairDiagonal_add_literalCross
      (fun first : IntegerWavevector =>
        actualWholeSymmetricVorticityPairVector
          receipt output first time)
      (summable_norm_actualWholeSymmetricVorticityPairVector
        receipt output time)

/-- Complete inverse-Laplacian weighted literal interference between
distinct ordered input pairs of one actual receipt and time. -/
def actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime) : Real :=
  ∑' output : IntegerWavevector,
    (integerWaveViscousMultiplier output)⁻¹ *
      pairVectorLiteralCrossInterference
        (fun first : IntegerWavevector =>
          actualWholeSymmetricVorticityPairVector
            receipt output first time)

/-- Inverse-Laplacian Euclidean density of the complete actual input-pair
aggregate at one output. -/
def actualWholeContinuousPairAggregateNegativeOneDensity
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (output : IntegerWavevector) : Real :=
  (integerWaveViscousMultiplier output)⁻¹ *
    complexCoordinateAmplitudeSq
      (∑' first : IntegerWavevector,
        actualWholeContinuousPairVector receipt output first time)

theorem actualWholeContinuousPairAggregateNegativeOneDensity_nonneg
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (output : IntegerWavevector) :
    0 ≤ actualWholeContinuousPairAggregateNegativeOneDensity
      receipt time output := by
  exact mul_nonneg
    (inv_nonneg.mpr (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output)))
    (complexCoordinateAmplitudeSq_nonneg _)

theorem actualWholeContinuousPairAggregateNegativeOneDensity_le
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (output : IntegerWavevector) :
    actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output ≤
      3 * wholeStateVorticityNonlinearNegativeOneDensity
        (receipt.wholePath time) output := by
  by_cases outputZero : output = 0
  · subst output
    simp [actualWholeContinuousPairAggregateNegativeOneDensity,
      integerWaveViscousMultiplier,
      wholeStateVorticityNonlinearNegativeOneDensity]
  · unfold actualWholeContinuousPairAggregateNegativeOneDensity
    rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput]
    have amplitudeLe :=
      complexCoordinateAmplitudeSq_le_three_mul_norm_sq
        (wholeStateVorticityNonlinearCoefficientAt
          (receipt.wholePath time) output)
    have inverseNonneg :
        0 ≤ (integerWaveViscousMultiplier output)⁻¹ := by
      apply inv_nonneg.mpr
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg output)
    unfold wholeStateVorticityNonlinearNegativeOneDensity
    rw [if_neg outputZero, div_eq_mul_inv]
    calc
      (integerWaveViscousMultiplier output)⁻¹ *
          complexCoordinateAmplitudeSq
            (wholeStateVorticityNonlinearCoefficientAt
              (receipt.wholePath time) output) ≤
        (integerWaveViscousMultiplier output)⁻¹ *
          (3 * ‖wholeStateVorticityNonlinearCoefficientAt
            (receipt.wholePath time) output‖ ^ 2) :=
        mul_le_mul_of_nonneg_left amplitudeLe inverseNonneg
      _ = 3 * (‖wholeStateVorticityNonlinearCoefficientAt
            (receipt.wholePath time) output‖ ^ 2 *
          (integerWaveViscousMultiplier output)⁻¹) := by ring

theorem summable_actualWholeContinuousPairAggregateNegativeOneDensity
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave)) :
    Summable fun output : IntegerWavevector =>
      actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output := by
  have nonlinearSummable :=
    summable_wholeStateVorticityNonlinearNegativeOneDensity
      (receipt.wholePath time) (wholePath_transverse receipt time)
      gradientSummable
  exact (nonlinearSummable.mul_left 3).of_nonneg_of_le
    (actualWholeContinuousPairAggregateNegativeOneDensity_nonneg
      receipt time)
    (actualWholeContinuousPairAggregateNegativeOneDensity_le receipt time)

/-- On every gradient-summable time slice, the complete nonlinear Euclidean
mass is exactly the paid pair diagonal plus literal ordered cross-pair
interference of that same receipt. -/
theorem
    actualWholeContinuousPairAggregateNegativeOneMass_eq_diagonal_add_literalCross
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave)) :
    (∑' output : IntegerWavevector,
      (integerWaveViscousMultiplier output)⁻¹ *
        complexCoordinateAmplitudeSq
          (∑' first : IntegerWavevector,
            actualWholeContinuousPairVector receipt output first time)) =
      actualWholeSymmetricVorticityPairNegativeOneDiagonalMass receipt time +
        actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
          receipt time := by
  let diagonalOutput : IntegerWavevector → Real := fun output =>
    (integerWaveViscousMultiplier output)⁻¹ *
      pairVectorEuclideanDiagonal
        (fun first : IntegerWavevector =>
          actualWholeSymmetricVorticityPairVector
            receipt output first time)
  let crossOutput : IntegerWavevector → Real := fun output =>
    (integerWaveViscousMultiplier output)⁻¹ *
      pairVectorLiteralCrossInterference
        (fun first : IntegerWavevector =>
          actualWholeSymmetricVorticityPairVector
            receipt output first time)
  let aggregateOutput : IntegerWavevector → Real := fun output =>
    actualWholeContinuousPairAggregateNegativeOneDensity
      receipt time output
  have aggregateSummable : Summable aggregateOutput :=
    summable_actualWholeContinuousPairAggregateNegativeOneDensity
      receipt time gradientSummable
  have pairDensitySummable :=
    summable_actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
      receipt time
  have diagonalSummable : Summable diagonalOutput := by
    have outerSummable :=
      (summable_prod_of_nonneg
        (fun indexed : IntegerWavevector × IntegerWavevector =>
          actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity_nonneg
            receipt indexed.1 indexed.2 time)).mp pairDensitySummable |>.2
    exact outerSummable.congr fun output => by
      unfold diagonalOutput
      unfold actualWholeSymmetricVorticityPairNegativeOneDiagonalDensity
        pairVectorEuclideanDiagonal
      change
        (∑' first : IntegerWavevector,
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (actualWholeSymmetricVorticityPairVector
                receipt output first time)) =
          (integerWaveViscousMultiplier output)⁻¹ *
            ∑' first : IntegerWavevector,
              complexCoordinateAmplitudeSq
                (actualWholeSymmetricVorticityPairVector
                  receipt output first time)
      rw [tsum_mul_left]
  have rowEq (output : IntegerWavevector) :
      aggregateOutput output =
        diagonalOutput output + crossOutput output := by
    unfold aggregateOutput diagonalOutput crossOutput
    unfold actualWholeContinuousPairAggregateNegativeOneDensity
    rw [
      actualWholeContinuousPairAggregateAmplitudeSq_eq_diagonal_add_literalCross]
    ring
  have crossSummable : Summable crossOutput := by
    exact (aggregateSummable.sub diagonalSummable).congr fun output => by
      rw [rowEq output]
      ring
  rw [
    actualWholeSymmetricVorticityPairNegativeOneDiagonalMass_eq_outputTsum]
  unfold actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
  change
    (∑' output : IntegerWavevector, aggregateOutput output) =
      (∑' output : IntegerWavevector, diagonalOutput output) +
        ∑' output : IntegerWavevector, crossOutput output
  rw [← diagonalSummable.tsum_add crossSummable]
  exact tsum_congr rowEq

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityPairDiagonalAction
end NavierStokes
end SaturationMonoid
