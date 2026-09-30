import H0mework.Physics.DiracEvolution.SafeCanonicalAffineEssentialBound
import H0mework.Physics.DiracEvolution.SafeCanonicalAffineVolterraActualization
import H0mework.Physics.DiracEvolution.GeneratedWeakLimitActualization

/-!
# Canonical affine Volterra--Riesz actualization

The unique source-generated whole-time affine output has continuous Volterra
mass coordinates on the canonical dense tests.  This module extends those
coordinates linearly on the exact dense span, actualizes the bounded
functional by Fréchet--Riesz at every source time, and inverts the
mother-action mass form.  The resulting pointwise field is uniquely fixed by
the Volterra reads and is almost everywhere the existing Bochner output.

No approximation family, subsequence, solution field, residual, or target is
supplied to the constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRieszActualization

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineEssentialBound
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalGreenEquation
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSameSourceGalerkinFamily
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineGeneratedWeakLimitActualization

noncomputable section

set_option autoImplicit false

def canonicalAffinePhysicalMassRawRead
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (test : CauchySafeMatterSmoothCompactTest)
    (time : Icc 0 timeEnd) : ℝ :=
  fixedP506L0CauchySafeMatterL2MassForm
    time.1 a b C (matrixBound time.1 time.2)
    (canonicalAffinePhysicalTimeL2Output
      timeEnd timePositive.le a b boxOrder time)
    (cauchySafeMatterSmoothCompactTestToL2 a b test)

private theorem canonicalAffinePhysicalMassRawRead_generator
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (test : ℕ)
    (time : Icc 0 timeEnd) :
    canonicalAffinePhysicalMassRawRead
        timeEnd timePositive a b boxOrder C matrixBound
        (cauchySafeMatterCanonicalInteriorDenseTest a b test) time =
      canonicalAffinePhysicalTimeL2MassRead
        timeEnd timePositive.le a b boxOrder test time := by
  calc
    _ = ∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          ((canonicalAffinePhysicalTimeL2Output
            timeEnd timePositive.le a b boxOrder time) space)
          ((cauchySafeMatterSmoothCompactTestToL2 a b
            (cauchySafeMatterCanonicalInteriorDenseTest a b test)) space)
        ∂volume.restrict (Icc a b) :=
      fixedP506L0CauchySafeMatterL2MassForm_eq_integral
        time.1 a b C (matrixBound time.1 time.2)
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timePositive.le a b boxOrder time)
        (cauchySafeMatterSmoothCompactTestToL2 a b
          (cauchySafeMatterCanonicalInteriorDenseTest a b test))
    _ = fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b
          (canonicalAffinePhysicalTimeL2Output
            timeEnd timePositive.le a b boxOrder time) test := by
      simp only [fixedP506L0CauchySafeMatterSpatialMassRead]
    _ = _ := (canonicalAffinePhysicalTimeL2MassRead_eq_spatialMassRead
      timeEnd timePositive.le a b boxOrder test time).symm

private theorem exists_canonicalAffinePhysicalMassRawRead_continuousRepresentative
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (test : CauchySafeMatterSmoothCompactTest)
    (testMem : test ∈ CauchySafeMatterCanonicalInteriorTestSpan a b) :
    ∃ representative : ℝ → ℝ,
      ContinuousOn representative (Icc 0 timeEnd) ∧
        ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd),
          canonicalAffinePhysicalMassRawRead
              timeEnd timePositive a b boxOrder C matrixBound test
              (projIcc 0 timeEnd timePositive.le time) =
            representative time := by
  induction testMem using Submodule.span_induction with
  | mem test testMem =>
      obtain ⟨index, rfl⟩ := testMem
      refine ⟨canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder index, ?_, ?_⟩
      · exact canonicalAffinePhysicalMassVolterraRepresentative_continuousOn
          timeEnd timePositive a b boxOrder index
      · filter_upwards [
          canonicalAffinePhysicalTimeL2MassRead_ae_eq_volterraRepresentative
            timeEnd timePositive a b boxOrder index] with time readEq
        rw [canonicalAffinePhysicalMassRawRead_generator]
        exact readEq
  | zero =>
      refine ⟨fun _ ↦ 0, continuousOn_const, ?_⟩
      filter_upwards with time
      simp [canonicalAffinePhysicalMassRawRead]
  | add first second _ _ firstRep secondRep =>
      obtain ⟨firstRepresentative, firstContinuous, firstAE⟩ := firstRep
      obtain ⟨secondRepresentative, secondContinuous, secondAE⟩ := secondRep
      refine ⟨fun time ↦ firstRepresentative time + secondRepresentative time,
        firstContinuous.add secondContinuous, ?_⟩
      filter_upwards [firstAE, secondAE] with time firstEq secondEq
      rw [show canonicalAffinePhysicalMassRawRead
          timeEnd timePositive a b boxOrder C matrixBound
          (first + second) (projIcc 0 timeEnd timePositive.le time) =
        canonicalAffinePhysicalMassRawRead
            timeEnd timePositive a b boxOrder C matrixBound first
              (projIcc 0 timeEnd timePositive.le time) +
          canonicalAffinePhysicalMassRawRead
            timeEnd timePositive a b boxOrder C matrixBound second
              (projIcc 0 timeEnd timePositive.le time) by
        simp [canonicalAffinePhysicalMassRawRead]]
      rw [firstEq, secondEq]
  | smul parameter test _ testRep =>
      obtain ⟨representative, representativeContinuous, representativeAE⟩ := testRep
      refine ⟨fun time ↦ parameter • representative time,
        representativeContinuous.const_smul parameter, ?_⟩
      filter_upwards [representativeAE] with time readEq
      rw [show canonicalAffinePhysicalMassRawRead
          timeEnd timePositive a b boxOrder C matrixBound
          (parameter • test) (projIcc 0 timeEnd timePositive.le time) =
        parameter • canonicalAffinePhysicalMassRawRead
          timeEnd timePositive a b boxOrder C matrixBound test
            (projIcc 0 timeEnd timePositive.le time) by
        simp [canonicalAffinePhysicalMassRawRead]]
      rw [readEq]

def canonicalAffinePhysicalMassSpanVolterraRepresentative
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (test : CauchySafeMatterCanonicalInteriorTestSpan a b) : ℝ → ℝ :=
  Classical.choose
    (exists_canonicalAffinePhysicalMassRawRead_continuousRepresentative
      timeEnd timePositive a b boxOrder C matrixBound test.1 test.2)

theorem canonicalAffinePhysicalMassSpanVolterraRepresentative_continuousOn
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (test : CauchySafeMatterCanonicalInteriorTestSpan a b) :
    ContinuousOn
      (canonicalAffinePhysicalMassSpanVolterraRepresentative
        timeEnd timePositive a b boxOrder C matrixBound test)
      (Icc 0 timeEnd) :=
  (Classical.choose_spec
    (exists_canonicalAffinePhysicalMassRawRead_continuousRepresentative
      timeEnd timePositive a b boxOrder C matrixBound test.1 test.2)).1

theorem canonicalAffinePhysicalMassRawRead_ae_eq_spanVolterraRepresentative
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (test : CauchySafeMatterCanonicalInteriorTestSpan a b) :
    ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd),
      canonicalAffinePhysicalMassRawRead
          timeEnd timePositive a b boxOrder C matrixBound test.1
            (projIcc 0 timeEnd timePositive.le time) =
        canonicalAffinePhysicalMassSpanVolterraRepresentative
          timeEnd timePositive a b boxOrder C matrixBound test time :=
  (Classical.choose_spec
    (exists_canonicalAffinePhysicalMassRawRead_continuousRepresentative
      timeEnd timePositive a b boxOrder C matrixBound test.1 test.2)).2

private theorem canonicalAffinePhysicalMassSpanVolterraRepresentative_eq_of_ae
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (test : CauchySafeMatterCanonicalInteriorTestSpan a b)
    (candidate : ℝ → ℝ)
    (candidateContinuous : ContinuousOn candidate (Icc 0 timeEnd))
    (candidateAE : ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd),
      canonicalAffinePhysicalMassRawRead
          timeEnd timePositive a b boxOrder C matrixBound test.1
            (projIcc 0 timeEnd timePositive.le time) = candidate time)
    (time : Icc 0 timeEnd) :
    canonicalAffinePhysicalMassSpanVolterraRepresentative
        timeEnd timePositive a b boxOrder C matrixBound test time =
      candidate time := by
  have representativeAE :=
    canonicalAffinePhysicalMassRawRead_ae_eq_spanVolterraRepresentative
      timeEnd timePositive a b boxOrder C matrixBound test
  have functionsAE :
      canonicalAffinePhysicalMassSpanVolterraRepresentative
          timeEnd timePositive a b boxOrder C matrixBound test =ᵐ[
        volume.restrict (Icc 0 timeEnd)] candidate :=
    by
      filter_upwards [representativeAE, candidateAE] with candidateTime
        representativeEq candidateEq
      exact representativeEq.symm.trans candidateEq
  exact Measure.eqOn_Icc_of_ae_eq volume timePositive.ne functionsAE
    (canonicalAffinePhysicalMassSpanVolterraRepresentative_continuousOn
      timeEnd timePositive a b boxOrder C matrixBound test)
    candidateContinuous time.2

def canonicalAffinePhysicalMassVolterraSpanFunctionalAt
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (time : Icc 0 timeEnd) :
    CauchySafeMatterCanonicalInteriorTestSpan a b →ₗ[ℝ] ℝ where
  toFun test := canonicalAffinePhysicalMassSpanVolterraRepresentative
    timeEnd timePositive a b boxOrder C matrixBound test time
  map_add' first second := by
    apply canonicalAffinePhysicalMassSpanVolterraRepresentative_eq_of_ae
      timeEnd timePositive a b boxOrder C matrixBound (first + second)
      (fun candidateTime ↦
        canonicalAffinePhysicalMassSpanVolterraRepresentative
            timeEnd timePositive a b boxOrder C matrixBound first candidateTime +
          canonicalAffinePhysicalMassSpanVolterraRepresentative
            timeEnd timePositive a b boxOrder C matrixBound second candidateTime)
    · exact
        (canonicalAffinePhysicalMassSpanVolterraRepresentative_continuousOn
          timeEnd timePositive a b boxOrder C matrixBound first).add
        (canonicalAffinePhysicalMassSpanVolterraRepresentative_continuousOn
          timeEnd timePositive a b boxOrder C matrixBound second)
    · filter_upwards [
          canonicalAffinePhysicalMassRawRead_ae_eq_spanVolterraRepresentative
            timeEnd timePositive a b boxOrder C matrixBound first,
          canonicalAffinePhysicalMassRawRead_ae_eq_spanVolterraRepresentative
            timeEnd timePositive a b boxOrder C matrixBound second]
        with candidateTime firstEq secondEq
      simpa [canonicalAffinePhysicalMassRawRead] using congrArg₂ (fun x y ↦ x + y)
        firstEq secondEq
  map_smul' parameter test := by
    apply canonicalAffinePhysicalMassSpanVolterraRepresentative_eq_of_ae
      timeEnd timePositive a b boxOrder C matrixBound (parameter • test)
      (fun candidateTime ↦ parameter •
        canonicalAffinePhysicalMassSpanVolterraRepresentative
          timeEnd timePositive a b boxOrder C matrixBound test candidateTime)
    · exact (canonicalAffinePhysicalMassSpanVolterraRepresentative_continuousOn
        timeEnd timePositive a b boxOrder C matrixBound test).const_smul parameter
    · filter_upwards [
          canonicalAffinePhysicalMassRawRead_ae_eq_spanVolterraRepresentative
            timeEnd timePositive a b boxOrder C matrixBound test]
        with candidateTime readEq
      simpa [canonicalAffinePhysicalMassRawRead] using
        congrArg (fun x ↦ parameter • x) readEq

theorem canonicalAffinePhysicalMassSpanVolterraRepresentative_generator
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (test : ℕ)
    (time : Icc 0 timeEnd) :
    canonicalAffinePhysicalMassSpanVolterraRepresentative
        timeEnd timePositive a b boxOrder C matrixBound
        ⟨cauchySafeMatterCanonicalInteriorDenseTest a b test,
          Submodule.subset_span (Set.mem_range_self test)⟩ time.1 =
      canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder test time.1 := by
  apply canonicalAffinePhysicalMassSpanVolterraRepresentative_eq_of_ae
    timeEnd timePositive a b boxOrder C matrixBound
    ⟨cauchySafeMatterCanonicalInteriorDenseTest a b test,
      Submodule.subset_span (Set.mem_range_self test)⟩
    (canonicalAffinePhysicalMassVolterraRepresentative
      timeEnd timePositive a b boxOrder test)
    (canonicalAffinePhysicalMassVolterraRepresentative_continuousOn
      timeEnd timePositive a b boxOrder test)
  filter_upwards [
      canonicalAffinePhysicalTimeL2MassRead_ae_eq_volterraRepresentative
        timeEnd timePositive a b boxOrder test] with candidateTime readEq
  rw [canonicalAffinePhysicalMassRawRead_generator]
  exact readEq

private theorem weakMassMatrixCoordinateLp_norm_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C) :
    ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
      time a b C operatorBound‖ ≤ C := by
  rw [fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp,
    Lp.norm_toLp, eLpNorm_exponent_top]
  calc
    ENNReal.toReal
        (eLpNormEssSup
          (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time)
          (volume.restrict (Icc a b))) ≤
        ENNReal.toReal (ENNReal.ofReal C) := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      apply eLpNormEssSup_le_of_ae_bound
      filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
      exact operatorBound space spaceMem
    _ = C := ENNReal.toReal_ofReal CNonnegative

private theorem l2MassAction_norm_apply_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖fixedP506L0CauchySafeMatterL2MassAction
      time a b C operatorBound field‖ ≤
        ‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖field‖ := by
  change
    ‖matterFiberMassRieszCoordinateBilinear.holder 2
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
        time a b C operatorBound) field‖ ≤ _
  calc
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ *
          ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
            time a b C operatorBound‖ * ‖field‖ :=
      matterFiberMassRieszCoordinateBilinear.norm_holder_apply_apply_le _ _
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖field‖ := by
      gcongr
      exact weakMassMatrixCoordinateLp_norm_le
        time a b C CNonnegative operatorBound

theorem exists_canonicalAffinePhysicalMassVolterraSpanFunctionalAt_bound
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (time : Icc 0 timeEnd)
        (test : CauchySafeMatterCanonicalInteriorTestSpan a b),
        ‖canonicalAffinePhysicalMassVolterraSpanFunctionalAt
          timeEnd timePositive a b boxOrder C matrixBound time test‖ ≤
          B * ‖cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test‖ := by
  obtain ⟨R, RNonnegative, outputBound⟩ :=
    exists_canonicalAffinePhysicalTimeL2Output_ae_norm_bound
      timeEnd timePositive.le a b boxOrder
  let B := ‖matterFiberMassRieszCoordinateBilinear‖ * C * R
  refine ⟨B, by positivity, ?_⟩
  intro time test
  have rawBoundAE :
      ∀ᵐ candidateTime ∂canonicalAffineTimeMeasure timeEnd,
        ‖canonicalAffinePhysicalMassRawRead
          timeEnd timePositive a b boxOrder C matrixBound test.1
            candidateTime‖ ≤
          B * ‖cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test‖ := by
    filter_upwards [outputBound] with physicalTime outputNormBound
    let output := canonicalAffinePhysicalTimeL2Output
      timeEnd timePositive.le a b boxOrder physicalTime
    let embeddedTest :=
      cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test
    change ‖inner ℝ
      (fixedP506L0CauchySafeMatterL2MassAction
        physicalTime.1 a b C (matrixBound physicalTime.1 physicalTime.2) output)
      embeddedTest‖ ≤ B * ‖embeddedTest‖
    calc
      _ ≤ ‖fixedP506L0CauchySafeMatterL2MassAction
            physicalTime.1 a b C
              (matrixBound physicalTime.1 physicalTime.2) output‖ *
            ‖embeddedTest‖ := by
        simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm
          (fixedP506L0CauchySafeMatterL2MassAction
            physicalTime.1 a b C
              (matrixBound physicalTime.1 physicalTime.2) output)
          embeddedTest
      _ ≤ (‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖output‖) *
            ‖embeddedTest‖ := by
        gcongr
        exact l2MassAction_norm_apply_le physicalTime.1 a b C CNonnegative
          (matrixBound physicalTime.1 physicalTime.2) output
      _ ≤ B * ‖embeddedTest‖ := by
        dsimp only [B]
        gcongr
  have representativeReadAE :
      ∀ᵐ candidateTime ∂canonicalAffineTimeMeasure timeEnd,
        canonicalAffinePhysicalMassRawRead
            timeEnd timePositive a b boxOrder C matrixBound test.1
              candidateTime =
          canonicalAffinePhysicalMassSpanVolterraRepresentative
            timeEnd timePositive a b boxOrder C matrixBound test
              candidateTime.1 := by
    unfold canonicalAffineTimeMeasure
    have transported := (ae_restrict_iff_subtype measurableSet_Icc).1
      (canonicalAffinePhysicalMassRawRead_ae_eq_spanVolterraRepresentative
        timeEnd timePositive a b boxOrder C matrixBound test)
    filter_upwards [transported] with candidateTime readEq
    have projEq : projIcc 0 timeEnd timePositive.le candidateTime.1 =
        candidateTime := by
      exact projIcc_val timePositive.le candidateTime
    rw [projEq] at readEq
    exact readEq
  have representativeBoundAESubtype :
      ∀ᵐ candidateTime ∂canonicalAffineTimeMeasure timeEnd,
        ‖canonicalAffinePhysicalMassSpanVolterraRepresentative
          timeEnd timePositive a b boxOrder C matrixBound test candidateTime.1‖ ≤
          B * ‖cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test‖ := by
    filter_upwards [
        representativeReadAE, rawBoundAE] with candidateTime readEq readBound
    rw [← readEq]
    exact readBound
  have representativeBoundAE :
      ∀ᵐ candidateTime ∂volume.restrict (Icc 0 timeEnd),
        ‖canonicalAffinePhysicalMassSpanVolterraRepresentative
          timeEnd timePositive a b boxOrder C matrixBound test candidateTime‖ ≤
          B * ‖cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test‖ := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    unfold canonicalAffineTimeMeasure at representativeBoundAESubtype
    exact representativeBoundAESubtype
  let representativeNorm : ℝ → ℝ := fun candidateTime ↦
    ‖canonicalAffinePhysicalMassSpanVolterraRepresentative
      timeEnd timePositive a b boxOrder C matrixBound test candidateTime‖
  let boundValue : ℝ :=
    B * ‖cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test‖
  have minAE : representativeNorm =ᵐ[volume.restrict (Icc 0 timeEnd)]
      fun candidateTime ↦ min (representativeNorm candidateTime) boundValue := by
    filter_upwards [representativeBoundAE] with candidateTime bound
    exact (min_eq_left bound).symm
  have normContinuous : ContinuousOn representativeNorm (Icc 0 timeEnd) :=
    (canonicalAffinePhysicalMassSpanVolterraRepresentative_continuousOn
      timeEnd timePositive a b boxOrder C matrixBound test).norm
  have minContinuous : ContinuousOn
      (fun candidateTime ↦ min (representativeNorm candidateTime) boundValue)
      (Icc 0 timeEnd) :=
    normContinuous.inf continuousOn_const
  have pointEq := Measure.eqOn_Icc_of_ae_eq volume timePositive.ne minAE
    normContinuous minContinuous time.2
  change representativeNorm time ≤ boundValue
  calc
    representativeNorm time = min (representativeNorm time) boundValue := pointEq
    _ ≤ boundValue := min_le_right _ _

private theorem canonicalDenseTestRieszActualization_pairing
    (a b : DiracMatterSpatialCoordinates)
    (functional : CauchySafeMatterCanonicalInteriorTestSpan a b →ₗ[ℝ] ℝ)
    (B : ℝ)
    (functionalBound : ∀ test,
      ‖functional test‖ ≤
        B * ‖cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test‖)
    (test : CauchySafeMatterCanonicalInteriorTestSpan a b) :
    inner ℝ
        (denseTestRieszActualization
          (Test := CauchySafeMatterCanonicalInteriorTestSpan a b)
          (Hilbert := CauchySafeMatterSpatialL2 a b)
          (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b) functional)
        (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test) =
      functional test := by
  have testDense : DenseRange
      (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b) := by
    apply (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b).mono
    rintro _ ⟨index, rfl⟩
    exact ⟨⟨cauchySafeMatterCanonicalInteriorDenseTest a b index,
      Submodule.subset_span (Set.mem_range_self index)⟩, rfl⟩
  exact @denseTestRieszActualization_pairing
    (CauchySafeMatterCanonicalInteriorTestSpan a b)
    (CauchySafeMatterSpatialL2 a b)
    (inferInstance : AddCommGroup
      (CauchySafeMatterCanonicalInteriorTestSpan a b))
    (inferInstance : Module ℝ
      (CauchySafeMatterCanonicalInteriorTestSpan a b))
    (inferInstance : NormedAddCommGroup
      (CauchySafeMatterSpatialL2 a b))
    (inferInstance : InnerProductSpace ℝ
      (CauchySafeMatterSpatialL2 a b))
    (inferInstance : CompleteSpace (CauchySafeMatterSpatialL2 a b))
    (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b) functional
    testDense B functionalBound test

@[irreducible] def canonicalAffinePhysicalMassVolterraRieszAt
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (time : Icc 0 timeEnd) : CauchySafeMatterSpatialL2 a b :=
  denseTestRieszActualization
    (Test := CauchySafeMatterCanonicalInteriorTestSpan a b)
    (Hilbert := CauchySafeMatterSpatialL2 a b)
    (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b)
    (canonicalAffinePhysicalMassVolterraSpanFunctionalAt
      timeEnd timePositive a b boxOrder C matrixBound time)

theorem canonicalAffinePhysicalMassVolterraRieszAt_pairing_of_bound
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (time : Icc 0 timeEnd)
    (B : ℝ)
    (functionalBound : ∀ test :
      CauchySafeMatterCanonicalInteriorTestSpan a b,
      ‖canonicalAffinePhysicalMassVolterraSpanFunctionalAt
        timeEnd timePositive a b boxOrder C matrixBound time test‖ ≤
        B * ‖cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test‖)
    (test : CauchySafeMatterCanonicalInteriorTestSpan a b) :
    inner ℝ
        (canonicalAffinePhysicalMassVolterraRieszAt
          timeEnd timePositive a b boxOrder C matrixBound time)
        (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test) =
      canonicalAffinePhysicalMassSpanVolterraRepresentative
        timeEnd timePositive a b boxOrder C matrixBound test time.1 := by
  rw [canonicalAffinePhysicalMassVolterraRieszAt]
  calc
    _ = canonicalAffinePhysicalMassVolterraSpanFunctionalAt
          timeEnd timePositive a b boxOrder C matrixBound time test :=
      canonicalDenseTestRieszActualization_pairing a b
        (canonicalAffinePhysicalMassVolterraSpanFunctionalAt
          timeEnd timePositive a b boxOrder C matrixBound time)
        B functionalBound test
    _ = _ := rfl

@[irreducible] def canonicalAffineVolterraPhysicalFieldAt
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (time : Icc 0 timeEnd) : CauchySafeMatterSpatialL2 a b :=
  fixedP506L0CauchySafeMatterPhysicalL2OfMassRepresentative
    time.1 a b boxOrder C (matrixBound time.1 time.2)
    (canonicalAffinePhysicalMassVolterraRieszAt
      timeEnd timePositive a b boxOrder C matrixBound time)

theorem canonicalAffineVolterraPhysicalFieldAt_massRead
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (time : Icc 0 timeEnd)
    (test : ℕ) :
    fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b
        (canonicalAffineVolterraPhysicalFieldAt
          timeEnd timePositive a b boxOrder C matrixBound time) test =
      canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder test time.1 := by
  obtain ⟨B, _BNonnegative, functionalBound⟩ :=
    exists_canonicalAffinePhysicalMassVolterraSpanFunctionalAt_bound
      timeEnd timePositive a b boxOrder C CNonnegative matrixBound
  let spanTest : CauchySafeMatterCanonicalInteriorTestSpan a b :=
    ⟨cauchySafeMatterCanonicalInteriorDenseTest a b test,
      Submodule.subset_span (Set.mem_range_self test)⟩
  let embeddedTest :=
    cauchySafeMatterCanonicalInteriorTestSpanToL2 a b spanTest
  calc
    _ = fixedP506L0CauchySafeMatterL2MassForm
          time.1 a b C (matrixBound time.1 time.2)
          (canonicalAffineVolterraPhysicalFieldAt
            timeEnd timePositive a b boxOrder C matrixBound time)
          embeddedTest := by
      rw [fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
      simp only [fixedP506L0CauchySafeMatterSpatialMassRead]
      rfl
    _ = inner ℝ
          (canonicalAffinePhysicalMassVolterraRieszAt
            timeEnd timePositive a b boxOrder C matrixBound time)
          embeddedTest :=
      by
        simpa only [canonicalAffineVolterraPhysicalFieldAt] using
          fixedP506L0CauchySafeMatterPhysicalL2OfMassRepresentative_pairing
            time.1 a b boxOrder C (matrixBound time.1 time.2)
            (canonicalAffinePhysicalMassVolterraRieszAt
              timeEnd timePositive a b boxOrder C matrixBound time)
            embeddedTest
    _ = canonicalAffinePhysicalMassSpanVolterraRepresentative
          timeEnd timePositive a b boxOrder C matrixBound spanTest time.1 :=
      canonicalAffinePhysicalMassVolterraRieszAt_pairing_of_bound
        timeEnd timePositive a b boxOrder C matrixBound
        time B (functionalBound time) spanTest
    _ = _ := canonicalAffinePhysicalMassSpanVolterraRepresentative_generator
      timeEnd timePositive a b boxOrder C matrixBound test time

theorem canonicalAffineVolterraPhysicalFieldAt_ae_eq_output
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (matrixBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C) :
    canonicalAffineVolterraPhysicalFieldAt
        timeEnd timePositive a b boxOrder C matrixBound =ᵐ[
      canonicalAffineTimeMeasure timeEnd]
      canonicalAffinePhysicalTimeL2Output
        timeEnd timePositive.le a b boxOrder := by
  have allReadsReal :=
    StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraActualization.canonicalAffinePhysicalTimeL2MassRead_ae_all_volterraRepresentative
      timeEnd timePositive a b boxOrder
  unfold canonicalAffineTimeMeasure
  have allReadsSubtype :=
    (ae_restrict_iff_subtype measurableSet_Icc).1 allReadsReal
  filter_upwards [allReadsSubtype] with time reads
  apply fixedP506L0CauchySafeMatterSpatialMassRead_injective
    time.1 a b boxOrder
  intro test
  have projEq : projIcc 0 timeEnd timePositive.le time.1 = time :=
    projIcc_val timePositive.le time
  have outputRead := reads test
  rw [projEq] at outputRead
  calc
    fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b
        (canonicalAffineVolterraPhysicalFieldAt
          timeEnd timePositive a b boxOrder C matrixBound time) test =
      canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder test time.1 :=
      canonicalAffineVolterraPhysicalFieldAt_massRead
        timeEnd timePositive a b boxOrder C CNonnegative matrixBound time test
    _ = canonicalAffinePhysicalTimeL2MassRead
        timeEnd timePositive.le a b boxOrder test time := outputRead.symm
    _ = fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timePositive.le a b boxOrder time) test :=
      canonicalAffinePhysicalTimeL2MassRead_eq_spatialMassRead
        timeEnd timePositive.le a b boxOrder test time

private def canonicalAffineVolterraMassMatrixBound
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) : ℝ :=
  Classical.choose
    (exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      0 timeEnd a b)

private theorem canonicalAffineVolterraMassMatrixBound_nonnegative
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    0 ≤ canonicalAffineVolterraMassMatrixBound timeEnd a b :=
  (Classical.choose_spec
    (exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      0 timeEnd a b)).1

private theorem canonicalAffineVolterraMassMatrixBound_spec
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ canonicalAffineVolterraMassMatrixBound timeEnd a b :=
  (Classical.choose_spec
    (exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      0 timeEnd a b)).2

/-- Canonical pointwise physical field actualized from the continuous
Volterra mass reads of the source-generated affine output. -/
def canonicalAffineVolterraPhysicalRepresentative
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd) : CauchySafeMatterSpatialL2 a b :=
  canonicalAffineVolterraPhysicalFieldAt
    timeEnd timePositive a b boxOrder
    (canonicalAffineVolterraMassMatrixBound timeEnd a b)
    (canonicalAffineVolterraMassMatrixBound_spec timeEnd a b) time

/-- Every canonical dense mass read of the pointwise actualization is the
exact source-generated Volterra representative, including null-set times. -/
theorem canonicalAffineVolterraPhysicalRepresentative_massRead
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (test : ℕ) :
    fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b
        (canonicalAffineVolterraPhysicalRepresentative
          timeEnd timePositive a b boxOrder time) test =
      canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder test time.1 := by
  simpa only [canonicalAffineVolterraPhysicalRepresentative] using
    canonicalAffineVolterraPhysicalFieldAt_massRead
      timeEnd timePositive a b boxOrder
      (canonicalAffineVolterraMassMatrixBound timeEnd a b)
      (canonicalAffineVolterraMassMatrixBound_nonnegative timeEnd a b)
      (canonicalAffineVolterraMassMatrixBound_spec timeEnd a b) time test

private theorem canonicalAffineSourceInitialL2_massRead
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    fixedP506L0CauchySafeMatterSpatialMassRead 0 a b
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) test =
      canonicalSourceLiftMassRead a b test 0 := by
  rw [fixedP506L0CauchySafeMatterSpatialMassRead]
  unfold canonicalSourceLiftMassRead
  apply integral_congr_ae
  have sourceRead : ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b space =
        fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates
          0 space := by
    unfold fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
    exact MemLp.coeFn_toLp _
  have testRead : ∀ᵐ space ∂volume.restrict (Icc a b),
      (cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorDenseTest a b test)) space =
        (cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space := by
    unfold cauchySafeMatterSmoothCompactTestToL2
    exact (cauchySafeMatterSmoothCompactTest_memLp a b
      (cauchySafeMatterCanonicalInteriorDenseTest a b test)).coeFn_toLp
  filter_upwards [sourceRead, testRead] with space sourceRead testRead
  rw [sourceRead,
    fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_zero,
    testRead]
  rfl

/-- The pointwise Volterra actualization has the exact source-generated
initial spatial field. -/
theorem canonicalAffineVolterraPhysicalRepresentative_zeroTime
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    canonicalAffineVolterraPhysicalRepresentative
        timeEnd timePositive a b boxOrder
        ⟨0, left_mem_Icc.mpr timePositive.le⟩ =
      fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b := by
  apply fixedP506L0CauchySafeMatterSpatialMassRead_injective
    0 a b boxOrder
  intro test
  have representativeRead :=
    canonicalAffineVolterraPhysicalRepresentative_massRead
      timeEnd timePositive a b boxOrder
      ⟨0, left_mem_Icc.mpr timePositive.le⟩ test
  change
    fixedP506L0CauchySafeMatterSpatialMassRead 0 a b
        (canonicalAffineVolterraPhysicalRepresentative
          timeEnd timePositive a b boxOrder
          ⟨0, left_mem_Icc.mpr timePositive.le⟩) test =
      fixedP506L0CauchySafeMatterSpatialMassRead 0 a b
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) test
  rw [representativeRead, canonicalAffineSourceInitialL2_massRead]
  simp [canonicalAffinePhysicalMassVolterraRepresentative]

/-- The pointwise Volterra actualization is a representative of the already
generated whole-time Bochner output; it introduces no new evolution. -/
theorem canonicalAffineVolterraPhysicalRepresentative_ae_eq_output
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    canonicalAffineVolterraPhysicalRepresentative
        timeEnd timePositive a b boxOrder =ᵐ[
      canonicalAffineTimeMeasure timeEnd]
      canonicalAffinePhysicalTimeL2Output
        timeEnd timePositive.le a b boxOrder := by
  change canonicalAffineVolterraPhysicalFieldAt
      timeEnd timePositive a b boxOrder
      (canonicalAffineVolterraMassMatrixBound timeEnd a b)
      (canonicalAffineVolterraMassMatrixBound_spec timeEnd a b) =ᵐ[
    canonicalAffineTimeMeasure timeEnd]
      canonicalAffinePhysicalTimeL2Output
        timeEnd timePositive.le a b boxOrder
  exact canonicalAffineVolterraPhysicalFieldAt_ae_eq_output
    timeEnd timePositive a b boxOrder
    (canonicalAffineVolterraMassMatrixBound timeEnd a b)
    (canonicalAffineVolterraMassMatrixBound_nonnegative timeEnd a b)
    (canonicalAffineVolterraMassMatrixBound_spec timeEnd a b)

/-- Exact Volterra dense reads determine the pointwise physical field
uniquely at every source time. -/
theorem canonicalAffineVolterraPhysicalRepresentative_unique
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (candidate : CauchySafeMatterSpatialL2 a b)
    (candidateReads : ∀ test,
      fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b candidate test =
        canonicalAffinePhysicalMassVolterraRepresentative
          timeEnd timePositive a b boxOrder test time.1) :
    candidate = canonicalAffineVolterraPhysicalRepresentative
      timeEnd timePositive a b boxOrder time := by
  apply fixedP506L0CauchySafeMatterSpatialMassRead_injective
    time.1 a b boxOrder
  intro test
  exact (candidateReads test).trans
    (canonicalAffineVolterraPhysicalRepresentative_massRead
      timeEnd timePositive a b boxOrder time test).symm

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRieszActualization

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraActualization.CanonicalAffineVolterraLimitOccurrence

open MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRieszActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSameSourceGalerkinFamily
open StageNineDiracMatterSpatialEnergyBalance

noncomputable section

set_option autoImplicit false

/-! ## Exact lower-occurrence pointwise readout -/

/-- The pointwise physical output read from the same exact source-history
occurrence.  The occurrence carries no output or representative payload. -/
def pointwisePhysicalOutput
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (_occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) :=
  canonicalAffineVolterraPhysicalRepresentative
    timeEnd timePositive a b boxOrder

theorem pointwisePhysicalOutput_eq
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) :
    occurrence.pointwisePhysicalOutput =
      canonicalAffineVolterraPhysicalRepresentative
        timeEnd timePositive a b boxOrder :=
  rfl

/-- Alternate presentations of the same exact occurrence cannot change the
pointwise authoritative output. -/
theorem pointwisePhysicalOutput_eq_of_occurrences
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (first second : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) :
    first.pointwisePhysicalOutput = second.pointwisePhysicalOutput :=
  rfl

theorem pointwisePhysicalOutput_massRead
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder)
    (time : Icc 0 timeEnd)
    (test : ℕ) :
    fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b
        (occurrence.pointwisePhysicalOutput time) test =
      canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder test time.1 := by
  exact canonicalAffineVolterraPhysicalRepresentative_massRead
    timeEnd timePositive a b boxOrder time test

/-- The pointwise readout is the canonical representative of the occurrence's
already generated whole-time Bochner output. -/
theorem pointwisePhysicalOutput_ae_eq_physicalOutput
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) :
    occurrence.pointwisePhysicalOutput =ᵐ[
      canonicalAffineTimeMeasure timeEnd] occurrence.physicalOutput := by
  exact canonicalAffineVolterraPhysicalRepresentative_ae_eq_output
    timeEnd timePositive a b boxOrder

theorem pointwisePhysicalOutput_unique
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder)
    (time : Icc 0 timeEnd)
    (candidate : CauchySafeMatterSpatialL2 a b)
    (candidateReads : ∀ test,
      fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b candidate test =
        canonicalAffinePhysicalMassVolterraRepresentative
          timeEnd timePositive a b boxOrder test time.1) :
    candidate = occurrence.pointwisePhysicalOutput time := by
  exact canonicalAffineVolterraPhysicalRepresentative_unique
    timeEnd timePositive a b boxOrder time candidate candidateReads

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraActualization.CanonicalAffineVolterraLimitOccurrence
