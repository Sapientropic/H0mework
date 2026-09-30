import H0mework.Physics.DiracEvolution.CountableWeakPairingCompactness
import H0mework.Physics.DiracEvolution.SafeWeakEnergyEstimate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness

open Filter MeasureTheory Set
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineHolonomicField
open StageNineCountableWeakPairingCompactness
open scoped BoundedContinuousFunction Interval

noncomputable section

set_option autoImplicit false

/-- One generated finite weak evolution carrying exactly the hypotheses used
by the mode-uniform energy and weak-pairing estimates. -/
structure FixedP506L0CauchySafeWeakGalerkinApproximation
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (energyCap : ℝ) where
  modeCount : ℕ
  basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ
  basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode)
  basisCompact : ∀ mode, HasCompactSupport (basis mode)
  basisZeroOutside :
    DiracMatterSpatialBasisSupportedInBoxInterior basis a b
  coefficient : ℝ → DiracMatterGalerkinCoefficient modeCount
  velocity : ℝ → DiracMatterGalerkinCoefficient modeCount
  evolution : ∀ time ∈ Icc timeStart timeEnd,
    HasDerivWithinAt coefficient (velocity time) (Icc timeStart timeEnd) time
  weakEquation : ∀ time ∈ Icc timeStart timeEnd,
    ∀ test : DiracMatterGalerkinCoefficient modeCount,
      fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact time
          (velocity time) test +
        fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact time (coefficient time) test = 0
  initialEnergyBound :
    ‖galerkinWeakEnergy
        (fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact)
        coefficient timeStart‖ ≤ energyCap

theorem FixedP506L0CauchySafeWeakGalerkinApproximation.weakPairingRate_continuousOn
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    (approximation : FixedP506L0CauchySafeWeakGalerkinApproximation
      timeStart timeEnd a b energyCap)
    (test : DiracMatterGalerkinCoefficient approximation.modeCount) :
    ContinuousOn
      (galerkinWeakTestPairingRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative
          approximation.basis approximation.basisRegular
          approximation.basisCompact)
        (fixedP506L0CauchySafeMatterWeakStiffnessForm
          approximation.basis approximation.basisRegular
          approximation.basisCompact)
        approximation.coefficient test)
      (Icc timeStart timeEnd) := by
  have coefficientContinuousOn : ContinuousOn approximation.coefficient
      (Icc timeStart timeEnd) := by
    intro time timeMem
    exact (approximation.evolution time timeMem).continuousWithinAt
  have massDerivativeContinuous : Continuous
      (fixedP506L0CauchySafeMatterWeakMassFormDerivative
        approximation.basis approximation.basisRegular
        approximation.basisCompact) :=
    (fixedP506L0CauchySafeMatterWeakMassForm_contDiff_one
      approximation.basis approximation.basisRegular
      approximation.basisCompact).continuous_deriv le_rfl
  have stiffnessContinuous : Continuous
      (fixedP506L0CauchySafeMatterWeakStiffnessForm
        approximation.basis approximation.basisRegular
        approximation.basisCompact) :=
    fixedP506L0CauchySafeMatterWeakStiffnessForm_continuous
      approximation.basis approximation.basisRegular approximation.basisCompact
  exact ((massDerivativeContinuous.continuousOn.clm_apply
    coefficientContinuousOn).clm_apply continuousOn_const).sub
    ((stiffnessContinuous.continuousOn.clm_apply coefficientContinuousOn
      ).clm_apply continuousOn_const)

/-- Every generated finite weak approximation satisfies the integrated
action equation for each coefficient-space test. -/
theorem FixedP506L0CauchySafeWeakGalerkinApproximation.weakPairing_integral_rate
    {timeStart timeEnd : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {energyCap : ℝ}
    (approximation : FixedP506L0CauchySafeWeakGalerkinApproximation
      timeStart timeEnd a b energyCap)
    (test : DiracMatterGalerkinCoefficient approximation.modeCount)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    (∫ candidateTime in timeStart..time,
        galerkinWeakTestPairingRate
          (fixedP506L0CauchySafeMatterWeakMassFormDerivative
            approximation.basis approximation.basisRegular
            approximation.basisCompact)
          (fixedP506L0CauchySafeMatterWeakStiffnessForm
            approximation.basis approximation.basisRegular
            approximation.basisCompact)
          approximation.coefficient test candidateTime) =
      galerkinWeakTestPairing
          (fixedP506L0CauchySafeMatterWeakMassForm approximation.basis
            (fun mode ↦ (approximation.basisRegular mode).continuous)
            approximation.basisCompact)
          approximation.coefficient test time -
        galerkinWeakTestPairing
          (fixedP506L0CauchySafeMatterWeakMassForm approximation.basis
            (fun mode ↦ (approximation.basisRegular mode).continuous)
            approximation.basisCompact)
          approximation.coefficient test timeStart := by
  let massForm := fixedP506L0CauchySafeMatterWeakMassForm
    approximation.basis
    (fun mode ↦ (approximation.basisRegular mode).continuous)
    approximation.basisCompact
  let massDerivative := fixedP506L0CauchySafeMatterWeakMassFormDerivative
    approximation.basis approximation.basisRegular approximation.basisCompact
  let stiffness := fixedP506L0CauchySafeMatterWeakStiffnessForm
    approximation.basis approximation.basisRegular approximation.basisCompact
  let pairing := galerkinWeakTestPairing massForm approximation.coefficient test
  let rate := galerkinWeakTestPairingRate massDerivative stiffness
    approximation.coefficient test
  have coefficientContinuousOn : ContinuousOn approximation.coefficient
      (Icc timeStart timeEnd) := by
    intro candidateTime candidateTimeMem
    exact (approximation.evolution candidateTime
      candidateTimeMem).continuousWithinAt
  have massFormContinuous : Continuous massForm := by
    exact fixedP506L0CauchySafeMatterWeakMassForm_continuous
      approximation.basis
      (fun mode ↦ (approximation.basisRegular mode).continuous)
      approximation.basisCompact
  have massDerivativeContinuous : Continuous massDerivative := by
    exact (fixedP506L0CauchySafeMatterWeakMassForm_contDiff_one
      approximation.basis approximation.basisRegular
      approximation.basisCompact).continuous_deriv le_rfl
  have stiffnessContinuous : Continuous stiffness := by
    exact fixedP506L0CauchySafeMatterWeakStiffnessForm_continuous
      approximation.basis approximation.basisRegular
      approximation.basisCompact
  have pairingContinuousOn : ContinuousOn pairing
      (Icc timeStart timeEnd) := by
    exact (massFormContinuous.continuousOn.clm_apply coefficientContinuousOn
      ).clm_apply continuousOn_const
  have rateContinuousOn : ContinuousOn rate (Icc timeStart timeEnd) := by
    exact ((massDerivativeContinuous.continuousOn.clm_apply
      coefficientContinuousOn).clm_apply continuousOn_const).sub
      ((stiffnessContinuous.continuousOn.clm_apply coefficientContinuousOn
        ).clm_apply continuousOn_const)
  have pairingDerivative : ∀ candidateTime ∈ Ioo timeStart time,
      HasDerivAt pairing (rate candidateTime) candidateTime := by
    intro candidateTime candidateTimeMem
    have candidateTimeFull : candidateTime ∈ Icc timeStart timeEnd :=
      ⟨candidateTimeMem.1.le, candidateTimeMem.2.le.trans timeMem.2⟩
    exact (galerkinWeakTestPairing_hasDerivWithinAt massForm massDerivative
      stiffness approximation.coefficient
      (approximation.velocity candidateTime) test (Icc timeStart timeEnd)
      candidateTime
      (fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt
        approximation.basis approximation.basisRegular
        approximation.basisCompact candidateTime).hasDerivWithinAt
      (approximation.evolution candidateTime candidateTimeFull)
      (approximation.weakEquation candidateTime candidateTimeFull test)
      ).hasDerivAt (Icc_mem_nhds candidateTimeMem.1
        (candidateTimeMem.2.trans_le timeMem.2))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le timeMem.1
    (pairingContinuousOn.mono (Icc_subset_Icc le_rfl timeMem.2))
    pairingDerivative
    ((rateContinuousOn.mono (Icc_subset_Icc le_rfl timeMem.2)
      ).intervalIntegrable_of_Icc timeMem.1)

/-- Every generated finite weak approximation satisfies the time-weighted
action equation for each coefficient-space test. -/
theorem FixedP506L0CauchySafeWeakGalerkinApproximation.weakPairing_weighted_integral_rate
    {timeStart timeEnd : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {energyCap : ℝ}
    (approximation : FixedP506L0CauchySafeWeakGalerkinApproximation
      timeStart timeEnd a b energyCap)
    (test : DiracMatterGalerkinCoefficient approximation.modeCount)
    (timeOrder : timeStart ≤ timeEnd)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (∫ candidateTime in timeStart..timeEnd,
        weight candidateTime *
          galerkinWeakTestPairingRate
            (fixedP506L0CauchySafeMatterWeakMassFormDerivative
              approximation.basis approximation.basisRegular
              approximation.basisCompact)
            (fixedP506L0CauchySafeMatterWeakStiffnessForm
              approximation.basis approximation.basisRegular
              approximation.basisCompact)
            approximation.coefficient test candidateTime) =
      weight timeEnd *
          galerkinWeakTestPairing
            (fixedP506L0CauchySafeMatterWeakMassForm approximation.basis
              (fun mode ↦ (approximation.basisRegular mode).continuous)
              approximation.basisCompact)
            approximation.coefficient test timeEnd -
        weight timeStart *
          galerkinWeakTestPairing
            (fixedP506L0CauchySafeMatterWeakMassForm approximation.basis
              (fun mode ↦ (approximation.basisRegular mode).continuous)
              approximation.basisCompact)
            approximation.coefficient test timeStart -
        ∫ candidateTime in timeStart..timeEnd,
          deriv weight candidateTime *
            galerkinWeakTestPairing
              (fixedP506L0CauchySafeMatterWeakMassForm approximation.basis
                (fun mode ↦ (approximation.basisRegular mode).continuous)
                approximation.basisCompact)
              approximation.coefficient test candidateTime := by
  let massForm := fixedP506L0CauchySafeMatterWeakMassForm
    approximation.basis
    (fun mode ↦ (approximation.basisRegular mode).continuous)
    approximation.basisCompact
  let massDerivative := fixedP506L0CauchySafeMatterWeakMassFormDerivative
    approximation.basis approximation.basisRegular approximation.basisCompact
  let stiffness := fixedP506L0CauchySafeMatterWeakStiffnessForm
    approximation.basis approximation.basisRegular approximation.basisCompact
  let pairing := galerkinWeakTestPairing massForm approximation.coefficient test
  let rate := galerkinWeakTestPairingRate massDerivative stiffness
    approximation.coefficient test
  have massDerivativeContinuous : Continuous massDerivative :=
    (fixedP506L0CauchySafeMatterWeakMassForm_contDiff_one
      approximation.basis approximation.basisRegular
      approximation.basisCompact).continuous_deriv le_rfl
  have stiffnessContinuous : Continuous stiffness :=
    fixedP506L0CauchySafeMatterWeakStiffnessForm_continuous
      approximation.basis approximation.basisRegular approximation.basisCompact
  have coefficientContinuousOn : ContinuousOn approximation.coefficient
      (Icc timeStart timeEnd) := by
    intro candidateTime candidateTimeMem
    exact (approximation.evolution candidateTime
      candidateTimeMem).continuousWithinAt
  have rateContinuousOn : ContinuousOn rate (Icc timeStart timeEnd) :=
    ((massDerivativeContinuous.continuousOn.clm_apply
      coefficientContinuousOn).clm_apply continuousOn_const).sub
      ((stiffnessContinuous.continuousOn.clm_apply coefficientContinuousOn
        ).clm_apply continuousOn_const)
  have pairingDerivative : ∀ candidateTime ∈ [[timeStart, timeEnd]],
      HasDerivWithinAt pairing (rate candidateTime)
        [[timeStart, timeEnd]] candidateTime := by
    intro candidateTime candidateTimeMem
    rw [uIcc_of_le timeOrder] at candidateTimeMem ⊢
    exact galerkinWeakTestPairing_hasDerivWithinAt massForm massDerivative
      stiffness approximation.coefficient
      (approximation.velocity candidateTime) test (Icc timeStart timeEnd)
      candidateTime
      (fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt
        approximation.basis approximation.basisRegular
        approximation.basisCompact candidateTime).hasDerivWithinAt
      (approximation.evolution candidateTime candidateTimeMem)
      (approximation.weakEquation candidateTime candidateTimeMem test)
  have weightDerivative : ∀ candidateTime ∈ [[timeStart, timeEnd]],
      HasDerivWithinAt weight (deriv weight candidateTime)
        [[timeStart, timeEnd]] candidateTime := by
    intro candidateTime _
    exact (weightRegular.differentiable (by norm_num)
      candidateTime).hasDerivAt.hasDerivWithinAt
  have derivWeightIntegrable : IntervalIntegrable (deriv weight) volume
      timeStart timeEnd :=
    weightRegular.continuous_deriv le_rfl |>.continuousOn
      |>.intervalIntegrable_of_Icc timeOrder
  have rateIntegrable : IntervalIntegrable rate volume timeStart timeEnd :=
    rateContinuousOn.intervalIntegrable_of_Icc timeOrder
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    weightDerivative pairingDerivative derivWeightIntegrable rateIntegrable

/-- A source-owned countable test family has one strict Galerkin subsequence
whose weak pairings converge uniformly in canonical time for every test.  The
same subsequence transports every finite action equation to the limit of its
integrated weak rate.  The `test`th field need only enter the finite carriers
from `testEntry test` on. -/
theorem exists_fixedP506L0CauchySafeCommonWeakPairingSubsequence
    (testCoordinates : ℕ → BasePoint → MatterCoordinateCarrier)
    (testRegular : ∀ test, ContDiff ℝ 1 (testCoordinates test))
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      testCoordinates test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point)) :
    ∃ limit : ℕ → (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ,
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          ∀ test,
            TendstoUniformly
                (fun sequenceIndex (time : Icc timeStart timeEnd) ↦
                  galerkinWeakTestPairing
                    (fixedP506L0CauchySafeMatterWeakMassForm
                      (approximation (subsequence sequenceIndex)).basis
                      (fun mode ↦
                        ((approximation (subsequence sequenceIndex)
                          ).basisRegular mode).continuous)
                      (approximation
                        (subsequence sequenceIndex)).basisCompact)
                    (approximation (subsequence sequenceIndex)).coefficient
                    (testCoefficient (subsequence sequenceIndex) test)
                    time.1)
                (limit test) atTop ∧
              (∀ time (timeMem : time ∈ Icc timeStart timeEnd),
                Tendsto
                  (fun sequenceIndex ↦
                    ∫ candidateTime in timeStart..time,
                      galerkinWeakTestPairingRate
                        (fixedP506L0CauchySafeMatterWeakMassFormDerivative
                          (approximation
                            (subsequence sequenceIndex)).basis
                          (approximation
                            (subsequence sequenceIndex)).basisRegular
                          (approximation
                            (subsequence sequenceIndex)).basisCompact)
                        (fixedP506L0CauchySafeMatterWeakStiffnessForm
                          (approximation
                            (subsequence sequenceIndex)).basis
                          (approximation
                            (subsequence sequenceIndex)).basisRegular
                          (approximation
                            (subsequence sequenceIndex)).basisCompact)
                        (approximation
                          (subsequence sequenceIndex)).coefficient
                        (testCoefficient (subsequence sequenceIndex) test)
                        candidateTime)
                  atTop
                  (nhds ((limit test) ⟨time, timeMem⟩ -
                    (limit test)
                      ⟨timeStart, left_mem_Icc.mpr timeOrder⟩))) ∧
              ∀ weight : ℝ → ℝ, ContDiff ℝ 1 weight →
                Tendsto
                  (fun sequenceIndex ↦
                    ∫ candidateTime in timeStart..timeEnd,
                      weight candidateTime *
                        galerkinWeakTestPairingRate
                          (fixedP506L0CauchySafeMatterWeakMassFormDerivative
                            (approximation
                              (subsequence sequenceIndex)).basis
                            (approximation
                              (subsequence sequenceIndex)).basisRegular
                            (approximation
                              (subsequence sequenceIndex)).basisCompact)
                          (fixedP506L0CauchySafeMatterWeakStiffnessForm
                            (approximation
                              (subsequence sequenceIndex)).basis
                            (approximation
                              (subsequence sequenceIndex)).basisRegular
                            (approximation
                              (subsequence sequenceIndex)).basisCompact)
                          (approximation
                            (subsequence sequenceIndex)).coefficient
                          (testCoefficient (subsequence sequenceIndex) test)
                          candidateTime)
                  atTop
                  (nhds (weight timeEnd *
                      (limit test)
                        ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
                    weight timeStart *
                      (limit test)
                        ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
                    ∫ candidateTime in timeStart..timeEnd,
                      deriv weight candidateTime *
                        (limit test)
                          (projIcc timeStart timeEnd timeOrder
                            candidateTime))) := by
  have uniformBounds := fun test ↦
    exists_fixedModeUniformGalerkinWeakTestPairingUniformBoundOnBox
      (testCoordinates test) (testRegular test) timeStart timeEnd a b
      timeOrder boxOrder energyCap energyCapNonnegative
  choose B BNonnegative pairingBound using uniformBounds
  have uniformLipschitz := fun test ↦
    exists_fixedModeUniformGalerkinWeakTestPairingLipschitzOnBox
      (testCoordinates test) (testRegular test) timeStart timeEnd a b
      timeOrder boxOrder energyCap energyCapNonnegative
  choose L LNonnegative pairingLipschitzBound using uniformLipschitz
  let Time := Icc timeStart timeEnd
  letI : CompactSpace Time := isCompact_iff_compactSpace.mp isCompact_Icc
  have pairingLipschitz (approximationIndex test : ℕ)
      (testEntered : testEntry test ≤ approximationIndex) :
      LipschitzWith (Real.toNNReal (L test))
        (fun time : Time ↦
          galerkinWeakTestPairing
            (fixedP506L0CauchySafeMatterWeakMassForm
              (approximation approximationIndex).basis
              (fun mode ↦
                ((approximation approximationIndex).basisRegular mode
                  ).continuous)
              (approximation approximationIndex).basisCompact)
            (approximation approximationIndex).coefficient
            (testCoefficient approximationIndex test) time.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro firstTime secondTime
    simpa [Real.dist_eq, dist_eq_norm, Subtype.dist_eq,
      Real.coe_toNNReal (L test) (LNonnegative test)] using
      pairingLipschitzBound test
        (approximation approximationIndex).modeCount
        (approximation approximationIndex).basis
        (approximation approximationIndex).basisRegular
        (approximation approximationIndex).basisCompact
        (approximation approximationIndex).basisZeroOutside
        (approximation approximationIndex).coefficient
        (approximation approximationIndex).velocity
        (testCoefficient approximationIndex test)
        (approximation approximationIndex).evolution
        (approximation approximationIndex).weakEquation
        (testRepresentation approximationIndex test testEntered)
        (approximation approximationIndex).initialEnergyBound
        secondTime.1 secondTime.2 firstTime.1 firstTime.2
  have pairingContinuous (approximationIndex test : ℕ) : Continuous
      (fun time : Icc timeStart timeEnd ↦
        galerkinWeakTestPairing
          (fixedP506L0CauchySafeMatterWeakMassForm
            (approximation approximationIndex).basis
            (fun mode ↦
              ((approximation approximationIndex).basisRegular mode
                ).continuous)
            (approximation approximationIndex).basisCompact)
          (approximation approximationIndex).coefficient
          (testCoefficient approximationIndex test) time.1) := by
    change Continuous (Set.restrict (Icc timeStart timeEnd)
      (galerkinWeakTestPairing
        (fixedP506L0CauchySafeMatterWeakMassForm
          (approximation approximationIndex).basis
          (fun mode ↦
            ((approximation approximationIndex).basisRegular mode
              ).continuous)
          (approximation approximationIndex).basisCompact)
        (approximation approximationIndex).coefficient
        (testCoefficient approximationIndex test)))
    apply continuousOn_iff_continuous_restrict.mp
    intro time timeMem
    exact (galerkinWeakTestPairing_hasDerivWithinAt
      (fixedP506L0CauchySafeMatterWeakMassForm
        (approximation approximationIndex).basis
        (fun mode ↦
          ((approximation approximationIndex).basisRegular mode).continuous)
        (approximation approximationIndex).basisCompact)
      (fixedP506L0CauchySafeMatterWeakMassFormDerivative
        (approximation approximationIndex).basis
        (approximation approximationIndex).basisRegular
        (approximation approximationIndex).basisCompact)
      (fixedP506L0CauchySafeMatterWeakStiffnessForm
        (approximation approximationIndex).basis
        (approximation approximationIndex).basisRegular
        (approximation approximationIndex).basisCompact)
      (approximation approximationIndex).coefficient
      ((approximation approximationIndex).velocity time)
      (testCoefficient approximationIndex test)
      (Icc timeStart timeEnd) time
      (fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt
        (approximation approximationIndex).basis
        (approximation approximationIndex).basisRegular
        (approximation approximationIndex).basisCompact time).hasDerivWithinAt
      ((approximation approximationIndex).evolution time timeMem)
      ((approximation approximationIndex).weakEquation time timeMem
        (testCoefficient approximationIndex test))).continuousWithinAt
  let pairing : ℕ → ℕ → Time →ᵇ ℝ := fun approximationIndex test ↦
    BoundedContinuousFunction.mkOfCompact
      ⟨fun time ↦
        galerkinWeakTestPairing
          (fixedP506L0CauchySafeMatterWeakMassForm
            (approximation approximationIndex).basis
            (fun mode ↦
              ((approximation approximationIndex).basisRegular mode
                ).continuous)
            (approximation approximationIndex).basisCompact)
          (approximation approximationIndex).coefficient
          (testCoefficient approximationIndex test) time.1,
        pairingContinuous approximationIndex test⟩
  have pairingBounded : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex → ∀ time,
      ‖pairing approximationIndex test time‖ ≤ B test := by
    intro approximationIndex test testEntered time
    exact pairingBound test
      (approximation approximationIndex).modeCount
      (approximation approximationIndex).basis
      (approximation approximationIndex).basisRegular
      (approximation approximationIndex).basisCompact
      (approximation approximationIndex).basisZeroOutside
      (approximation approximationIndex).coefficient
      (approximation approximationIndex).velocity
      (testCoefficient approximationIndex test)
      (approximation approximationIndex).evolution
      (approximation approximationIndex).weakEquation
      (testRepresentation approximationIndex test testEntered)
      (approximation approximationIndex).initialEnergyBound time.1 time.2
  obtain ⟨limit, subsequence, subsequenceStrict, convergence⟩ :=
    exists_commonUniformSubsequence_of_eventually_lipschitz pairing testEntry
      (fun test ↦ Real.toNNReal (L test)) B pairingLipschitz pairingBounded
  refine ⟨limit, subsequence, subsequenceStrict, ?_⟩
  intro test
  have uniformConvergence :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (convergence test)
  refine ⟨uniformConvergence, ?_, ?_⟩
  · intro time timeMem
    have endpointConvergence :=
      (uniformConvergence.tendsto_at ⟨time, timeMem⟩).sub
        (uniformConvergence.tendsto_at
          ⟨timeStart, left_mem_Icc.mpr timeOrder⟩)
    apply endpointConvergence.congr'
    filter_upwards with sequenceIndex
    exact ((approximation (subsequence sequenceIndex)
      ).weakPairing_integral_rate
        (testCoefficient (subsequence sequenceIndex) test) time timeMem).symm
  · intro weight weightRegular
    apply weightedRateIntegral_tendsto_of_boundedContinuousPairing
      timeOrder
      (fun sequenceIndex ↦ pairing (subsequence sequenceIndex) test)
      (fun sequenceIndex candidateTime ↦
        galerkinWeakTestPairingRate
          (fixedP506L0CauchySafeMatterWeakMassFormDerivative
            (approximation (subsequence sequenceIndex)).basis
            (approximation (subsequence sequenceIndex)).basisRegular
            (approximation (subsequence sequenceIndex)).basisCompact)
          (fixedP506L0CauchySafeMatterWeakStiffnessForm
            (approximation (subsequence sequenceIndex)).basis
            (approximation (subsequence sequenceIndex)).basisRegular
            (approximation (subsequence sequenceIndex)).basisCompact)
          (approximation (subsequence sequenceIndex)).coefficient
          (testCoefficient (subsequence sequenceIndex) test)
          candidateTime)
      (limit test) (convergence test) weight weightRegular
    intro sequenceIndex
    calc
      ∫ candidateTime in timeStart..timeEnd,
          weight candidateTime *
            galerkinWeakTestPairingRate
              (fixedP506L0CauchySafeMatterWeakMassFormDerivative
                (approximation (subsequence sequenceIndex)).basis
                (approximation (subsequence sequenceIndex)).basisRegular
                (approximation (subsequence sequenceIndex)).basisCompact)
              (fixedP506L0CauchySafeMatterWeakStiffnessForm
                (approximation (subsequence sequenceIndex)).basis
                (approximation (subsequence sequenceIndex)).basisRegular
                (approximation (subsequence sequenceIndex)).basisCompact)
              (approximation (subsequence sequenceIndex)).coefficient
              (testCoefficient (subsequence sequenceIndex) test)
              candidateTime =
          weight timeEnd *
              galerkinWeakTestPairing
                (fixedP506L0CauchySafeMatterWeakMassForm
                  (approximation (subsequence sequenceIndex)).basis
                  (fun mode ↦ ((approximation
                    (subsequence sequenceIndex)).basisRegular mode).continuous)
                  (approximation (subsequence sequenceIndex)).basisCompact)
                (approximation (subsequence sequenceIndex)).coefficient
                (testCoefficient (subsequence sequenceIndex) test) timeEnd -
            weight timeStart *
              galerkinWeakTestPairing
                (fixedP506L0CauchySafeMatterWeakMassForm
                  (approximation (subsequence sequenceIndex)).basis
                  (fun mode ↦ ((approximation
                    (subsequence sequenceIndex)).basisRegular mode).continuous)
                  (approximation (subsequence sequenceIndex)).basisCompact)
                (approximation (subsequence sequenceIndex)).coefficient
                (testCoefficient (subsequence sequenceIndex) test) timeStart -
            ∫ candidateTime in timeStart..timeEnd,
              deriv weight candidateTime *
                galerkinWeakTestPairing
                  (fixedP506L0CauchySafeMatterWeakMassForm
                    (approximation (subsequence sequenceIndex)).basis
                    (fun mode ↦ ((approximation
                      (subsequence sequenceIndex)).basisRegular mode).continuous)
                    (approximation (subsequence sequenceIndex)).basisCompact)
                  (approximation (subsequence sequenceIndex)).coefficient
                  (testCoefficient (subsequence sequenceIndex) test)
                  candidateTime :=
        (approximation (subsequence sequenceIndex)
          ).weakPairing_weighted_integral_rate
            (testCoefficient (subsequence sequenceIndex) test)
            timeOrder weight weightRegular
      _ = weight timeEnd *
              pairing (subsequence sequenceIndex) test
                ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
            weight timeStart *
              pairing (subsequence sequenceIndex) test
                ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
            ∫ candidateTime in timeStart..timeEnd,
              deriv weight candidateTime *
                pairing (subsequence sequenceIndex) test
                  (projIcc timeStart timeEnd timeOrder candidateTime) := by
        have projectedPairingIntegralEq :
            (∫ candidateTime in timeStart..timeEnd,
              deriv weight candidateTime *
                galerkinWeakTestPairing
                  (fixedP506L0CauchySafeMatterWeakMassForm
                    (approximation (subsequence sequenceIndex)).basis
                    (fun mode ↦ ((approximation
                      (subsequence sequenceIndex)).basisRegular mode).continuous)
                    (approximation (subsequence sequenceIndex)).basisCompact)
                  (approximation (subsequence sequenceIndex)).coefficient
                  (testCoefficient (subsequence sequenceIndex) test)
                  candidateTime) =
              ∫ candidateTime in timeStart..timeEnd,
                deriv weight candidateTime *
                  pairing (subsequence sequenceIndex) test
                    (projIcc timeStart timeEnd timeOrder candidateTime) := by
          apply intervalIntegral.integral_congr
          intro candidateTime candidateTimeMem
          rw [uIcc_of_le timeOrder] at candidateTimeMem
          simp [pairing, projIcc_of_mem timeOrder candidateTimeMem]
        rw [← projectedPairingIntegralEq]
        rfl

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
