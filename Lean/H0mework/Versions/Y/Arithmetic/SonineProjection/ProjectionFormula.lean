import H0mework.Versions.Y.Arithmetic.SonineProjection.EvenCorrection

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

theorem burnolAmbientEvenMeanZeroCorrection_position
    (value : BurnolL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction
          (burnolAmbientEvenMeanZeroCorrection value)) =
      (burnolAmbientMeanZeroPosition value :
        BurnolQuarterIntervalL2) := by
  unfold burnolAmbientEvenMeanZeroCorrection
  rw [burnolAmbientEvenPart_restriction_meanZero,
    burnolAmbientRawMeanZeroCorrection_position]
  have blockRead := congrArg
    (fun state : BurnolQuarterMeanZeroCarrier ↦
      (state : BurnolQuarterIntervalL2))
    (burnolMeanZeroBlock_first_equation
      (burnolAmbientMeanZeroBlockRhs value))
  change
    (burnolAmbientMeanZeroFirstCorrection value :
        BurnolQuarterIntervalL2) +
      (burnolMeanZeroTruncatedFourier
        (burnolAmbientMeanZeroSecondCorrection value) :
          BurnolQuarterIntervalL2) =
    (burnolAmbientMeanZeroPosition value : BurnolQuarterIntervalL2)
      at blockRead
  rw [blockRead, burnolAmbientMeanZeroPosition_reflection_fixed]
  module

theorem burnolAmbientEvenMeanZeroCorrection_fourier
    (value : BurnolL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction
          (fourierL2 (burnolAmbientEvenMeanZeroCorrection value))) =
      (burnolAmbientMeanZeroFourier value :
        BurnolQuarterIntervalL2) := by
  unfold burnolAmbientEvenMeanZeroCorrection
  rw [burnolAmbientEvenPart_fourierRestriction_meanZero,
    burnolAmbientRawMeanZeroCorrection_fourier, map_add,
    reflectRestricted_quarter_involutive]
  have blockRead := congrArg
    (fun state : BurnolQuarterMeanZeroCarrier ↦
      (state : BurnolQuarterIntervalL2))
    (burnolMeanZeroBlock_second_equation
      (burnolAmbientMeanZeroBlockRhs value))
  change
    (burnolMeanZeroTruncatedFourier
        (burnolAmbientMeanZeroFirstCorrection value) :
          BurnolQuarterIntervalL2) +
      (burnolAmbientMeanZeroSecondCorrection value :
        BurnolQuarterIntervalL2) =
      (burnolAmbientMeanZeroFourier value : BurnolQuarterIntervalL2)
    at blockRead
  have reflectedBlockRead := congrArg (reflectRestricted (1 / 4 : ℝ))
    blockRead
  rw [map_add, burnolAmbientMeanZeroFourier_reflection_fixed]
    at reflectedBlockRead
  calc
    _ = (1 / 2 : ℂ) •
        (((burnolMeanZeroTruncatedFourier
            (burnolAmbientMeanZeroFirstCorrection value) :
              BurnolQuarterIntervalL2) +
          (burnolAmbientMeanZeroSecondCorrection value :
            BurnolQuarterIntervalL2)) +
        (reflectRestricted (1 / 4 : ℝ)
            (burnolMeanZeroTruncatedFourier
              (burnolAmbientMeanZeroFirstCorrection value) :
                BurnolQuarterIntervalL2) +
          reflectRestricted (1 / 4 : ℝ)
            (burnolAmbientMeanZeroSecondCorrection value :
              BurnolQuarterIntervalL2))) := by
      congr 1
      abel
    _ = (1 / 2 : ℂ) •
        ((burnolAmbientMeanZeroFourier value : BurnolQuarterIntervalL2) +
          (burnolAmbientMeanZeroFourier value : BurnolQuarterIntervalL2)) := by
      rw [blockRead, reflectedBlockRead]
    _ = (burnolAmbientMeanZeroFourier value : BurnolQuarterIntervalL2) := by
      module

theorem burnolAmbientEvenMeanZeroCorrection_even
    (value : BurnolL2) :
    reflectL2 (burnolAmbientEvenMeanZeroCorrection value) =
      burnolAmbientEvenMeanZeroCorrection value :=
  burnolAmbientEvenPart_even _

theorem burnolAmbientExtendedSonineProjectionFormula_even
    (value : BurnolL2) :
    reflectL2 (burnolAmbientExtendedSonineProjectionFormula value) =
      burnolAmbientExtendedSonineProjectionFormula value := by
  unfold burnolAmbientExtendedSonineProjectionFormula
  rw [map_sub, burnolAmbientEvenPart_even,
    burnolAmbientEvenMeanZeroCorrection_even]

theorem burnolAmbientExtendedSonineProjectionFormula_position_zero
    (value : BurnolL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction
          (burnolAmbientExtendedSonineProjectionFormula value)) = 0 := by
  unfold burnolAmbientExtendedSonineProjectionFormula
  rw [map_sub, map_sub, burnolAmbientEvenMeanZeroCorrection_position]
  change (burnolAmbientMeanZeroPosition value : BurnolQuarterIntervalL2) -
      (burnolAmbientMeanZeroPosition value : BurnolQuarterIntervalL2) = 0
  exact sub_self _

theorem burnolAmbientExtendedSonineProjectionFormula_fourier_zero
    (value : BurnolL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterRestriction
          (fourierL2 (burnolAmbientExtendedSonineProjectionFormula value))) = 0 := by
  unfold burnolAmbientExtendedSonineProjectionFormula
  rw [map_sub, map_sub, map_sub,
    burnolAmbientEvenMeanZeroCorrection_fourier]
  change (burnolAmbientMeanZeroFourier value : BurnolQuarterIntervalL2) -
      (burnolAmbientMeanZeroFourier value : BurnolQuarterIntervalL2) = 0
  exact sub_self _

theorem burnolAmbientExtendedSonineProjectionFormula_mem
    (value : BurnolL2) :
    burnolAmbientExtendedSonineProjectionFormula value ∈
      evenBurnolClosedFace (1 / 4 : ℝ) := by
  refine ⟨?_, mem_evenL2ClosedFace_iff.mpr
    (burnolAmbientExtendedSonineProjectionFormula_even value)⟩
  change burnolAmbientExtendedSonineProjectionFormula value ∈
    burnolFace (1 / 4 : ℝ)
  rw [mem_burnolQuarterFace_iff_meanZero_residuals]
  exact ⟨burnolAmbientExtendedSonineProjectionFormula_position_zero value,
    burnolAmbientExtendedSonineProjectionFormula_fourier_zero value⟩

theorem burnolAmbientRawMeanZeroCorrection_inner_physical_eq_zero
    (value : BurnolL2)
    (test : EvenBurnolPhysicalCarrier (1 / 4 : ℝ)) :
    inner ℂ (burnolAmbientRawMeanZeroCorrection value) (test : BurnolL2) = 0 := by
  have positionConstant :
      burnolQuarterRestriction (test : BurnolL2) ∈
        intervalConstantLine (1 / 4 : ℝ) := test.property.1.1
  have fourierConstant :
      burnolQuarterRestriction (fourierL2 (test : BurnolL2)) ∈
        intervalConstantLine (1 / 4 : ℝ) := test.property.1.2
  have firstZero :
      inner ℂ
          (burnolQuarterZeroExtension
            (burnolAmbientMeanZeroFirstCorrection value :
              BurnolQuarterIntervalL2))
          (test : BurnolL2) = 0 := by
    unfold burnolQuarterZeroExtension burnolRadiusZeroExtension
    rw [ContinuousLinearMap.adjoint_inner_left, inner_eq_zero_symm]
    exact (burnolAmbientMeanZeroFirstCorrection value).property _
      positionConstant
  have testEven : reflectL2 (test : BurnolL2) = test :=
    mem_evenL2ClosedFace_iff.mp test.property.2
  have testFourierTwice :
      fourierL2 (fourierL2 (test : BurnolL2)) = test := by
    rw [fourierL2_fourierL2, testEven]
  have secondZero :
      inner ℂ
          (fourierL2 (burnolQuarterZeroExtension
            (burnolAmbientMeanZeroSecondCorrection value :
              BurnolQuarterIntervalL2)))
          (test : BurnolL2) = 0 := by
    calc
      _ = inner ℂ
          (fourierL2 (burnolQuarterZeroExtension
            (burnolAmbientMeanZeroSecondCorrection value :
              BurnolQuarterIntervalL2)))
          (fourierL2 (fourierL2 (test : BurnolL2))) := by
            rw [testFourierTwice]
      _ = inner ℂ
          (burnolQuarterZeroExtension
            (burnolAmbientMeanZeroSecondCorrection value :
              BurnolQuarterIntervalL2))
          (fourierL2 (test : BurnolL2)) := by
            exact Lp.inner_fourier_eq
              (burnolQuarterZeroExtension
                (burnolAmbientMeanZeroSecondCorrection value :
                  BurnolQuarterIntervalL2))
              (fourierL2 (test : BurnolL2))
      _ = inner ℂ
          (burnolAmbientMeanZeroSecondCorrection value :
            BurnolQuarterIntervalL2)
          (burnolQuarterRestriction (fourierL2 (test : BurnolL2))) := by
            exact ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = 0 := by
        rw [inner_eq_zero_symm]
        exact (burnolAmbientMeanZeroSecondCorrection value).property _
          fourierConstant
  unfold burnolAmbientRawMeanZeroCorrection
  rw [inner_add_left, firstZero, secondZero, add_zero]

theorem burnolAmbientEvenMeanZeroCorrection_inner_physical_eq_zero
    (value : BurnolL2)
    (test : EvenBurnolPhysicalCarrier (1 / 4 : ℝ)) :
    inner ℂ (burnolAmbientEvenMeanZeroCorrection value) (test : BurnolL2) = 0 := by
  have rawZero :=
    burnolAmbientRawMeanZeroCorrection_inner_physical_eq_zero value test
  have testEven : reflectL2 (test : BurnolL2) = test :=
    mem_evenL2ClosedFace_iff.mp test.property.2
  have reflectedZero :
      inner ℂ (reflectL2 (burnolAmbientRawMeanZeroCorrection value))
          (test : BurnolL2) = 0 := by
    calc
      _ = inner ℂ (reflectL2 (burnolAmbientRawMeanZeroCorrection value))
          (reflectL2 (test : BurnolL2)) := by rw [testEven]
      _ = inner ℂ (burnolAmbientRawMeanZeroCorrection value)
          (test : BurnolL2) :=
        (reflectL2.inner_map_map _ _)
      _ = 0 := rawZero
  unfold burnolAmbientEvenMeanZeroCorrection burnolAmbientEvenPart
  rw [inner_smul_left, inner_add_left, rawZero, reflectedZero]
  simp

theorem burnolAmbientOddResidual_inner_physical_eq_zero
    (value : BurnolL2)
    (test : EvenBurnolPhysicalCarrier (1 / 4 : ℝ)) :
    inner ℂ (value - burnolAmbientEvenPart value) (test : BurnolL2) = 0 := by
  have testEven : reflectL2 (test : BurnolL2) = test :=
    mem_evenL2ClosedFace_iff.mp test.property.2
  have reflectedInner :
      inner ℂ (reflectL2 value) (test : BurnolL2) =
        inner ℂ value (test : BurnolL2) := by
    calc
      _ = inner ℂ (reflectL2 value) (reflectL2 (test : BurnolL2)) := by
        rw [testEven]
      _ = _ := reflectL2.inner_map_map _ _
  unfold burnolAmbientEvenPart
  rw [inner_sub_left, inner_smul_left, inner_add_left, reflectedInner]
  have starHalf : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    have starTwo : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
      simpa using (map_ofNat (starRingEnd ℂ) 2)
    rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num,
      map_inv₀, starTwo]
  rw [starHalf]
  ring

theorem burnolAmbientProjectionFormulaResidual_inner_physical_eq_zero
    (value : BurnolL2)
    (test : EvenBurnolPhysicalCarrier (1 / 4 : ℝ)) :
    inner ℂ
        (value - burnolAmbientExtendedSonineProjectionFormula value)
        (test : BurnolL2) = 0 := by
  have oddZero := burnolAmbientOddResidual_inner_physical_eq_zero value test
  have correctionZero :=
    burnolAmbientEvenMeanZeroCorrection_inner_physical_eq_zero value test
  have residualSplit :
      value - burnolAmbientExtendedSonineProjectionFormula value =
        (value - burnolAmbientEvenPart value) +
          burnolAmbientEvenMeanZeroCorrection value := by
    unfold burnolAmbientExtendedSonineProjectionFormula
    abel
  rw [residualSplit, inner_add_left, oddZero, correctionZero, add_zero]

theorem burnolAmbientProjectionFormulaResidual_mem_orthogonal
    (value : BurnolL2) :
    value - burnolAmbientExtendedSonineProjectionFormula value ∈
      Submodule.orthogonal
        (evenBurnolClosedFace (1 / 4 : ℝ)).toSubmodule := by
  intro test testMem
  rw [inner_eq_zero_symm]
  exact burnolAmbientProjectionFormulaResidual_inner_physical_eq_zero value
    ⟨test, testMem⟩

theorem burnolEvenOrthogonalProjection_eq_resolventFormula
    (value : BurnolL2) :
    (evenBurnolClosedFace (1 / 4 : ℝ)).toSubmodule.starProjection value =
      burnolAmbientExtendedSonineProjectionFormula value := by
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (burnolAmbientExtendedSonineProjectionFormula_mem value)
    (burnolAmbientProjectionFormulaResidual_mem_orthogonal value)

theorem burnolEvenOrthogonalProjectionOnto_eq_resolventFormula
    (value : BurnolL2) :
    ((evenBurnolClosedFace (1 / 4 : ℝ)).toSubmodule.orthogonalProjectionOnto value :
      BurnolL2) = burnolAmbientExtendedSonineProjectionFormula value :=
  burnolEvenOrthogonalProjection_eq_resolventFormula value

theorem burnolCompletedMellinRieszVector_eq_resolventFormula
    (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      burnolAmbientExtendedSonineProjectionFormula
        (burnolAmbientCompletedMellinKernelFormula coordinate) := by
  rw [burnolCompletedMellinRieszVector_eq_ambientProjection,
    burnolAmbientCompletedMellinRieszVector_eq_kernelFormula]
  exact burnolEvenOrthogonalProjectionOnto_eq_resolventFormula _

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
