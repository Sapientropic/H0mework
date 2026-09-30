import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import H0mework.Physics.DiracEvolution.SafeCanonicalAffineTailEnergyActionLaw

/-!
# Canonical affine Volterra recognition

The source-owned whole-time `L²` output already satisfies the mother-action
law.  This file recognizes its canonical scalar mass reads as the exact
Volterra representative selected by the source initial trace.  It introduces
no supplied weak solution, subsequence, graph carrier, or evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRecognition

open Filter MeasureTheory Set
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalGreenEquation
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter
open StageNineDiracMatterSpatialEnergyBalance

noncomputable section

set_option autoImplicit false

/-- Weighted distributional form of one scalar Volterra action equation. -/
def WeakVolterraActionZero
    (timeEnd initial : ℝ)
    (mass rate : ℝ → ℝ) : Prop :=
  ∀ (weight : ℝ → ℝ),
    ContDiff ℝ 1 weight →
    weight timeEnd = 0 →
    (∫ time in 0..timeEnd,
      weight time * rate time + deriv weight time * mass time) =
        -weight 0 * initial

/-- Almost-everywhere integral form of the same scalar Volterra equation. -/
def WeakVolterraFixedPoint
    (timeEnd initial : ℝ)
    (mass rate : ℝ → ℝ) : Prop :=
  ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd),
    mass time = initial + ∫ candidateTime in 0..time, rate candidateTime

theorem weakVolterra_ae_eq_initial_add_integral
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (mass rate : ℝ → ℝ)
    (initial : ℝ)
    (massIntegrable : IntervalIntegrable mass volume 0 timeEnd)
    (rateIntegrable : IntervalIntegrable rate volume 0 timeEnd)
    (actionLaw : ∀ (weight : ℝ → ℝ),
      ContDiff ℝ 1 weight →
      weight timeEnd = 0 →
      (∫ time in 0..timeEnd,
        weight time * rate time + deriv weight time * mass time) =
          -weight 0 * initial) :
    ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd),
      mass time = initial + ∫ candidateTime in 0..time, rate candidateTime := by
  let primitive : ℝ → ℝ := fun time ↦
    ∫ candidateTime in 0..time, rate candidateTime
  let difference : ℝ → ℝ := fun time ↦ mass time - (initial + primitive time)
  have primitiveAC : AbsolutelyContinuousOnInterval primitive 0 timeEnd := by
    exact rateIntegrable.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have primitiveIntegrable : IntervalIntegrable primitive volume 0 timeEnd :=
    primitiveAC.continuousOn.intervalIntegrable
  have expectedIntegrable : IntervalIntegrable
      (fun time ↦ initial + primitive time) volume 0 timeEnd :=
    (continuous_const.intervalIntegrable 0 timeEnd).add primitiveIntegrable
  have differenceIntegrable : IntervalIntegrable difference volume 0 timeEnd :=
    massIntegrable.sub expectedIntegrable
  have derivativeDifferenceLaw : ∀ (weight : ℝ → ℝ),
      ContDiff ℝ 1 weight →
      weight timeEnd = 0 →
      (∫ time in 0..timeEnd, deriv weight time * difference time) = 0 := by
    intro weight weightRegular weightEndZero
    have weightAC : AbsolutelyContinuousOnInterval weight 0 timeEnd :=
      weightRegular.contDiffOn.absolutelyContinuousOnInterval
    have primitiveDerivative : ∀ᵐ time ∂volume,
        time ∈ Icc 0 timeEnd → deriv primitive time = rate time := by
      filter_upwards [rateIntegrable.ae_hasDerivAt_integral] with time derivative
      intro timeMem
      exact (derivative (by
        rw [uIcc_of_le timePositive.le]
        exact timeMem) 0 (by simp)).deriv
    have weightedPrimitiveEq :
        (∫ time in 0..timeEnd, weight time * rate time) =
          -∫ time in 0..timeEnd, deriv weight time * primitive time := by
      have integrationByParts :=
        weightAC.integral_mul_deriv_eq_deriv_mul primitiveAC
      have derivativeIntegralEq :
          (∫ time in 0..timeEnd, weight time * deriv primitive time) =
            ∫ time in 0..timeEnd, weight time * rate time := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [primitiveDerivative] with time derivative timeMem
        rw [derivative (by
          rw [← uIcc_of_le timePositive.le]
          exact uIoc_subset_uIcc timeMem)]
      rw [derivativeIntegralEq] at integrationByParts
      rw [weightEndZero] at integrationByParts
      have primitiveZero : primitive 0 = 0 := by simp [primitive]
      rw [primitiveZero] at integrationByParts
      simp only [zero_mul, mul_zero, sub_zero, zero_sub] at integrationByParts
      simpa using integrationByParts
    have law := actionLaw weight weightRegular weightEndZero
    have rateTermIntegrable : IntervalIntegrable
        (fun time ↦ weight time * rate time) volume 0 timeEnd := by
      simpa [mul_comm] using rateIntegrable.mul_continuousOn
        weightRegular.continuous.continuousOn
    have massTermIntegrable : IntervalIntegrable
        (fun time ↦ deriv weight time * mass time) volume 0 timeEnd := by
      simpa [mul_comm] using massIntegrable.mul_continuousOn
        (weightRegular.continuous_deriv le_rfl).continuousOn
    rw [intervalIntegral.integral_add rateTermIntegrable massTermIntegrable,
      weightedPrimitiveEq] at law
    have primitiveTermIntegrable : IntervalIntegrable
        (fun time ↦ deriv weight time * primitive time) volume 0 timeEnd := by
      simpa [mul_comm] using primitiveIntegrable.mul_continuousOn
        (weightRegular.continuous_deriv le_rfl).continuousOn
    have initialTermIntegrable : IntervalIntegrable
        (fun time ↦ deriv weight time * initial) volume 0 timeEnd :=
      (weightRegular.continuous_deriv le_rfl).continuousOn
        |>.intervalIntegrable |>.mul_const _
    have initialIntegral :
        (∫ time in 0..timeEnd, deriv weight time * initial) =
          -weight 0 * initial := by
      rw [intervalIntegral.integral_mul_const, weightAC.integral_deriv_eq_sub,
        weightEndZero]
      ring
    rw [show (fun time ↦ deriv weight time * difference time) =
        (fun time ↦ deriv weight time * mass time -
          (deriv weight time * initial + deriv weight time * primitive time)) by
      funext time
      simp [difference]
      ring,
      intervalIntegral.integral_sub massTermIntegrable
        (initialTermIntegrable.add primitiveTermIntegrable),
      intervalIntegral.integral_add initialTermIntegrable primitiveTermIntegrable,
      initialIntegral]
    linarith
  have differenceLocallyIntegrable : LocallyIntegrable difference
      (volume.restrict (Icc 0 timeEnd)) := by
    apply Integrable.locallyIntegrable
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le timePositive.le).mp
      differenceIntegrable
  have differenceAEZero := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    differenceLocallyIntegrable (fun test testRegular _testCompact ↦ ?_)
  · filter_upwards [differenceAEZero] with time differenceZero
    dsimp only [difference, primitive] at differenceZero ⊢
    linarith
  let weight : ℝ → ℝ := fun time ↦ ∫ candidateTime in timeEnd..time, test candidateTime
  have weightDerivative : ∀ time, HasDerivAt weight (test time) time := by
    intro time
    exact intervalIntegral.integral_hasDerivAt_right
      (testRegular.continuous.intervalIntegrable timeEnd time)
      (testRegular.continuous.stronglyMeasurableAtFilter volume (nhds time))
      testRegular.continuous.continuousAt
  have weightRegular : ContDiff ℝ 1 weight := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun time ↦ (weightDerivative time).differentiableAt, ?_⟩
    have derivativeEq : deriv weight = test := by
      funext time
      exact (weightDerivative time).deriv
    rw [derivativeEq]
    exact testRegular.continuous
  have weightEndZero : weight timeEnd = 0 := by
    simp [weight]
  have law := derivativeDifferenceLaw weight weightRegular weightEndZero
  have derivativeEq : deriv weight = test := by
    funext time
    exact (weightDerivative time).deriv
  rw [derivativeEq] at law
  change (∫ time in Icc 0 timeEnd, test time • difference time) = 0
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le timePositive.le]
  simpa [smul_eq_mul] using law

/-- The weighted action equation and the almost-everywhere Volterra integral
equation are equivalent on a positive source-time interval. -/
theorem weakVolterraActionZero_iff_fixedPoint
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (mass rate : ℝ → ℝ)
    (initial : ℝ)
    (massIntegrable : IntervalIntegrable mass volume 0 timeEnd)
    (rateIntegrable : IntervalIntegrable rate volume 0 timeEnd) :
    WeakVolterraActionZero timeEnd initial mass rate ↔
      WeakVolterraFixedPoint timeEnd initial mass rate := by
  constructor
  · intro actionZero
    exact weakVolterra_ae_eq_initial_add_integral
      timeEnd timePositive mass rate initial massIntegrable rateIntegrable
      actionZero
  · intro fixedPoint weight weightRegular weightEndZero
    let primitive : ℝ → ℝ := fun time ↦
      ∫ candidateTime in 0..time, rate candidateTime
    have primitiveAC : AbsolutelyContinuousOnInterval primitive 0 timeEnd := by
      exact rateIntegrable.absolutelyContinuousOnInterval_intervalIntegral
        (by simp)
    have primitiveIntegrable : IntervalIntegrable primitive volume 0 timeEnd :=
      primitiveAC.continuousOn.intervalIntegrable
    have rateTermIntegrable : IntervalIntegrable
        (fun time ↦ weight time * rate time) volume 0 timeEnd := by
      simpa [mul_comm] using rateIntegrable.mul_continuousOn
        weightRegular.continuous.continuousOn
    have massTermIntegrable : IntervalIntegrable
        (fun time ↦ deriv weight time * mass time) volume 0 timeEnd := by
      simpa [mul_comm] using massIntegrable.mul_continuousOn
        (weightRegular.continuous_deriv le_rfl).continuousOn
    have primitiveDerivative : ∀ᵐ time ∂volume,
        time ∈ Icc 0 timeEnd → deriv primitive time = rate time := by
      filter_upwards [rateIntegrable.ae_hasDerivAt_integral] with time derivative
      intro timeMem
      exact (derivative (by
        rw [uIcc_of_le timePositive.le]
        exact timeMem) 0 (by simp)).deriv
    have weightedPrimitiveEq :
        (∫ time in 0..timeEnd, weight time * rate time) =
          -∫ time in 0..timeEnd, deriv weight time * primitive time := by
      have weightAC : AbsolutelyContinuousOnInterval weight 0 timeEnd :=
        weightRegular.contDiffOn.absolutelyContinuousOnInterval
      have integrationByParts :=
        weightAC.integral_mul_deriv_eq_deriv_mul primitiveAC
      have derivativeIntegralEq :
          (∫ time in 0..timeEnd, weight time * deriv primitive time) =
            ∫ time in 0..timeEnd, weight time * rate time := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [primitiveDerivative] with time derivative timeMem
        rw [derivative (by
          rw [← uIcc_of_le timePositive.le]
          exact uIoc_subset_uIcc timeMem)]
      rw [derivativeIntegralEq, weightEndZero] at integrationByParts
      have primitiveZero : primitive 0 = 0 := by simp [primitive]
      rw [primitiveZero] at integrationByParts
      simp only [zero_mul, mul_zero, sub_zero, zero_sub] at integrationByParts
      simpa using integrationByParts
    have fixedPointOnVolume : ∀ᵐ time ∂volume,
        time ∈ Icc 0 timeEnd →
          mass time = initial + primitive time := by
      unfold WeakVolterraFixedPoint at fixedPoint
      rw [ae_restrict_iff' measurableSet_Icc] at fixedPoint
      simpa only [primitive] using fixedPoint
    have massTermEq :
        (∫ time in 0..timeEnd, deriv weight time * mass time) =
          ∫ time in 0..timeEnd,
            deriv weight time * (initial + primitive time) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [fixedPointOnVolume] with time equality timeMem
      have timeMemIcc : time ∈ Icc 0 timeEnd := by
        rw [← uIcc_of_le timePositive.le]
        exact uIoc_subset_uIcc timeMem
      rw [equality timeMemIcc]
    have primitiveTermIntegrable : IntervalIntegrable
        (fun time ↦ deriv weight time * primitive time) volume 0 timeEnd := by
      simpa [mul_comm] using primitiveIntegrable.mul_continuousOn
        (weightRegular.continuous_deriv le_rfl).continuousOn
    have initialTermIntegrable : IntervalIntegrable
        (fun time ↦ deriv weight time * initial) volume 0 timeEnd :=
      (weightRegular.continuous_deriv le_rfl).continuousOn
        |>.intervalIntegrable |>.mul_const _
    have initialIntegral :
        (∫ time in 0..timeEnd, deriv weight time * initial) =
          -weight 0 * initial := by
      rw [intervalIntegral.integral_mul_const,
        weightRegular.contDiffOn.absolutelyContinuousOnInterval.integral_deriv_eq_sub,
        weightEndZero]
      ring
    rw [intervalIntegral.integral_add rateTermIntegrable massTermIntegrable,
      massTermEq,
      show (fun time ↦ deriv weight time * (initial + primitive time)) =
          (fun time ↦ deriv weight time * initial +
            deriv weight time * primitive time) by
        funext time
        ring,
      intervalIntegral.integral_add initialTermIntegrable
        primitiveTermIntegrable,
      initialIntegral, weightedPrimitiveEq]
    ring

/-- The source-generated scalar representative selected by the initial trace
and the canonical Green-rate read. -/
def canonicalAffinePhysicalMassVolterraRepresentative
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (time : ℝ) : ℝ :=
  canonicalSourceLiftMassRead a b test 0 +
    ∫ candidateTime in 0..time,
      canonicalAffinePhysicalTimeL2GreenRate
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le candidateTime)

/-- Every generated Volterra mass read has a continuous representative on
the complete source-time interval. -/
theorem canonicalAffinePhysicalMassVolterraRepresentative_continuousOn
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    ContinuousOn
      (canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder test)
      (Icc 0 timeEnd) := by
  have rateIntegrable :=
    canonicalAffinePhysicalTimeL2GreenRate_intervalIntegrable
      timeEnd timePositive a b boxOrder test
  have primitiveAC : AbsolutelyContinuousOnInterval
      (fun time ↦ ∫ candidateTime in 0..time,
        canonicalAffinePhysicalTimeL2GreenRate
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le candidateTime))
      0 timeEnd :=
    rateIntegrable.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have primitiveContinuousOn : ContinuousOn
      (fun time ↦ ∫ candidateTime in 0..time,
        canonicalAffinePhysicalTimeL2GreenRate
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le candidateTime))
      (Icc 0 timeEnd) := by
    simpa [uIcc_of_le timePositive.le] using primitiveAC.continuousOn
  exact continuousOn_const.add primitiveContinuousOn

/-- Almost every source time reads the exact generated Green rate as the
derivative of one canonical Volterra mass coordinate. -/
theorem canonicalAffinePhysicalMassVolterraRepresentative_ae_hasDerivAt
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd),
      HasDerivAt
        (canonicalAffinePhysicalMassVolterraRepresentative
          timeEnd timePositive a b boxOrder test)
        (canonicalAffinePhysicalTimeL2GreenRate
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le time))
        time := by
  have rateIntegrable :=
    canonicalAffinePhysicalTimeL2GreenRate_intervalIntegrable
      timeEnd timePositive a b boxOrder test
  have derivativeAE := rateIntegrable.ae_hasDerivAt_integral
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [derivativeAE] with time derivative timeMem
  have timeMem' : time ∈ uIcc 0 timeEnd := by
    simpa [uIcc_of_le timePositive.le] using timeMem
  have zeroMem : 0 ∈ uIcc 0 timeEnd := by
    simp [timePositive.le]
  have primitiveDerivative := derivative timeMem' 0 zeroMem
  unfold canonicalAffinePhysicalMassVolterraRepresentative
  exact primitiveDerivative.const_add _

/-- Countability puts every canonical Volterra velocity read on one common
full-measure source-time occurrence. -/
theorem canonicalAffinePhysicalMassVolterraRepresentative_ae_all_hasDerivAt
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd), ∀ test : ℕ,
      HasDerivAt
        (canonicalAffinePhysicalMassVolterraRepresentative
          timeEnd timePositive a b boxOrder test)
        (canonicalAffinePhysicalTimeL2GreenRate
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le time))
        time := by
  apply ae_all_iff.2
  intro test
  exact canonicalAffinePhysicalMassVolterraRepresentative_ae_hasDerivAt
    timeEnd timePositive a b boxOrder test

/-- Each canonical dense mass read of the unique source-owned time-`L²`
output is almost everywhere its exact Volterra representative. -/
theorem canonicalAffinePhysicalTimeL2MassRead_ae_eq_volterraRepresentative
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd),
      canonicalAffinePhysicalTimeL2MassRead
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le time) =
        canonicalAffinePhysicalMassVolterraRepresentative
          timeEnd timePositive a b boxOrder test time := by
  apply weakVolterra_ae_eq_initial_add_integral
    timeEnd timePositive
    (fun time ↦ canonicalAffinePhysicalTimeL2MassRead
      timeEnd timePositive.le a b boxOrder test
        (projIcc 0 timeEnd timePositive.le time))
    (fun time ↦ canonicalAffinePhysicalTimeL2GreenRate
      timeEnd timePositive.le a b boxOrder test
        (projIcc 0 timeEnd timePositive.le time))
    (canonicalSourceLiftMassRead a b test 0)
    (canonicalAffinePhysicalTimeL2MassRead_intervalIntegrable
      timeEnd timePositive a b boxOrder test)
    (canonicalAffinePhysicalTimeL2GreenRate_intervalIntegrable
      timeEnd timePositive a b boxOrder test)
  intro weight weightRegular weightEndZero
  have subtypeLaw :=
    canonicalAffinePhysicalTimeL2Output_weightedIntegralActionLaw_of_endZero
      timeEnd timePositive.le a b boxOrder test weight weightRegular
        weightEndZero
  let field : ℝ → ℝ := fun time ↦
    weight time *
        canonicalAffinePhysicalTimeL2GreenRate
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le time) +
      deriv weight time *
        canonicalAffinePhysicalTimeL2MassRead
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le time)
  have subtypeEqInterval :
      (∫ time : Icc 0 timeEnd,
          weight time.1 *
              canonicalAffinePhysicalTimeL2GreenRate
                timeEnd timePositive.le a b boxOrder test time +
            deriv weight time.1 *
              canonicalAffinePhysicalTimeL2MassRead
                timeEnd timePositive.le a b boxOrder test time
          ∂canonicalAffineTimeMeasure timeEnd) =
        ∫ time in 0..timeEnd, field time := by
    calc
      _ = ∫ time : Icc 0 timeEnd, field time.1
          ∂canonicalAffineTimeMeasure timeEnd := by
        apply integral_congr_ae
        filter_upwards with time
        simp only [field, projIcc_val]
      _ = ∫ time in 0..timeEnd, field time := by
        unfold canonicalAffineTimeMeasure
        rw [integral_subtype_comap measurableSet_Icc]
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le timePositive.le]
  change (∫ time in 0..timeEnd, field time) = _
  rw [← subtypeEqInterval]
  exact subtypeLaw

/-- The fixed source's weighted action zero and its generated Volterra
integral equation are the same weak matter law. -/
theorem canonicalAffinePhysicalTimeL2Output_weakActionZero_iff_fixedPoint
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    let mass : ℝ → ℝ := fun time ↦
      canonicalAffinePhysicalTimeL2MassRead
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le time)
    let rate : ℝ → ℝ := fun time ↦
      canonicalAffinePhysicalTimeL2GreenRate
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le time)
    let initial := canonicalSourceLiftMassRead a b test 0
    WeakVolterraActionZero timeEnd initial mass rate ↔
      WeakVolterraFixedPoint timeEnd initial mass rate := by
  dsimp only
  exact weakVolterraActionZero_iff_fixedPoint
    timeEnd timePositive _ _ _
    (canonicalAffinePhysicalTimeL2MassRead_intervalIntegrable
      timeEnd timePositive a b boxOrder test)
    (canonicalAffinePhysicalTimeL2GreenRate_intervalIntegrable
      timeEnd timePositive a b boxOrder test)

/-- The canonical source output simultaneously carries the weighted action
zero and the equivalent Volterra integral read. -/
theorem canonicalAffinePhysicalTimeL2Output_weakMatterClosure
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    let mass : ℝ → ℝ := fun time ↦
      canonicalAffinePhysicalTimeL2MassRead
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le time)
    let rate : ℝ → ℝ := fun time ↦
      canonicalAffinePhysicalTimeL2GreenRate
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le time)
    let initial := canonicalSourceLiftMassRead a b test 0
    WeakVolterraActionZero timeEnd initial mass rate ∧
      WeakVolterraFixedPoint timeEnd initial mass rate := by
  dsimp only
  have fixedPoint : WeakVolterraFixedPoint timeEnd
      (canonicalSourceLiftMassRead a b test 0)
      (fun time ↦ canonicalAffinePhysicalTimeL2MassRead
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le time))
      (fun time ↦ canonicalAffinePhysicalTimeL2GreenRate
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le time)) := by
    unfold WeakVolterraFixedPoint
    simpa only [canonicalAffinePhysicalMassVolterraRepresentative] using
      canonicalAffinePhysicalTimeL2MassRead_ae_eq_volterraRepresentative
        timeEnd timePositive a b boxOrder test
  exact ⟨
    (canonicalAffinePhysicalTimeL2Output_weakActionZero_iff_fixedPoint
      timeEnd timePositive a b boxOrder test).2 fixedPoint,
    fixedPoint⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRecognition
