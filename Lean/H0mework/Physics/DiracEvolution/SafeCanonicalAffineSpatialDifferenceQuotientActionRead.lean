import H0mework.Physics.DiracEvolution.SafeCanonicalAffineSpatialDifferenceQuotientCommutator

/-!
# Fixed canonical affine spatial difference-quotient action read

The existing weighted mother-action law is resolved into its Green and mass
reads before it is specialized to the source-generated canonical Volterra
output's spatial difference-quotient test.  The small read carriers prevent
the two large L² action terms from being unfolded in the same definitional
equality.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientActionRead

open MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineInteriorFirstJetActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientTest
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRieszActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance

open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

@[irreducible] def canonicalInteriorSmoothTestActionValue
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (weight : ℝ → ℝ) : ℝ :=
  canonicalInteriorFirstJetWeightedActionValue
    timeEnd timeNonnegative a b boxOrder weight
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test)

def canonicalInteriorSmoothTestGreenReadAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : Icc 0 timeEnd) : ℝ :=
  inner ℝ
    (greenRateCanonicalInteriorFirstJetL2Action time.1 a b
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test))
    (canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder time)

def canonicalInteriorSmoothTestMassReadAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : Icc 0 timeEnd) : ℝ :=
  inner ℝ
    (massCanonicalInteriorFirstJetL2Action time.1 a b
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test))
    (canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder time)

def canonicalInteriorSmoothTestActionReadAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (weight : ℝ → ℝ)
    (time : Icc 0 timeEnd) : ℝ :=
  weight time.1 * canonicalInteriorSmoothTestGreenReadAt
      timeEnd timeNonnegative a b boxOrder test time +
    deriv weight time.1 * canonicalInteriorSmoothTestMassReadAt
      timeEnd timeNonnegative a b boxOrder test time

theorem canonicalInteriorSmoothTestGreenReadAt_eq
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : Icc 0 timeEnd) :
    canonicalInteriorSmoothTestGreenReadAt
        timeEnd timeNonnegative a b boxOrder test time =
      fixedP506L0CauchySafeMatterGreenRateL2Read
        (interiorSpacetimeTest test)
        (interiorSpacetimeTest_contDiff_one test) time.1 a b
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time) := by
  exact greenRateCanonicalInteriorFirstJetL2Read_eq test time.1 _

/-- Every generated smooth-test Green section is time-integrable against the
physical `L²` output.  The proof stays on the native Green time-`L²` carrier,
so no constant-weight reduction or pointwise regularization is introduced. -/
theorem canonicalInteriorSmoothTestGreenReadAt_integrable
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b) :
    Integrable (canonicalInteriorSmoothTestGreenReadAt
      timeEnd timeNonnegative a b boxOrder test)
      (canonicalAffineTimeMeasure timeEnd) := by
  let jet := cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test
  have timeL2Integrable := L2.integrable_inner (𝕜 := ℝ)
    (greenRateCanonicalInteriorFirstJetL2ActionTimeL2 timeEnd a b jet)
    (canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder)
  refine timeL2Integrable.congr ?_
  refine (greenRateCanonicalInteriorFirstJetL2ActionTimeL2_coe_ae
    timeEnd a b jet).mono ?_
  intro time actionRead
  calc
    inner ℝ
        ((greenRateCanonicalInteriorFirstJetL2ActionTimeL2
          timeEnd a b jet) time)
        ((canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder) time) =
      inner ℝ
        (greenRateCanonicalInteriorFirstJetL2Action time.1 a b jet)
        ((canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder) time) :=
      congrArg
        (fun field ↦ inner ℝ field
          ((canonicalAffinePhysicalTimeL2Output
            timeEnd timeNonnegative a b boxOrder) time))
        actionRead
    _ = canonicalInteriorSmoothTestGreenReadAt
        timeEnd timeNonnegative a b boxOrder test time := rfl

theorem canonicalInteriorSmoothTestMassReadAt_eq
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : Icc 0 timeEnd) :
    canonicalInteriorSmoothTestMassReadAt
        timeEnd timeNonnegative a b boxOrder test time =
      ∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (test.1.1 space)
          ((canonicalAffinePhysicalTimeL2Output
            timeEnd timeNonnegative a b boxOrder time) space)
        ∂volume.restrict (Icc a b) := by
  exact massCanonicalInteriorFirstJetL2Read_eq_integral test time.1 _

theorem weightedCanonicalInteriorSmoothTestAction_inner_eq_readAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (weight : ℝ → ℝ)
    (time : Icc 0 timeEnd) :
    inner ℝ
        (weightedCanonicalInteriorFirstJetL2Action time.1 a b weight
          (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test))
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time) =
      canonicalInteriorSmoothTestActionReadAt
        timeEnd timeNonnegative a b boxOrder test weight time := by
  exact weightedCanonicalInteriorFirstJetL2Action_inner_eq
    time.1 a b weight
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test)
      (canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder time)

theorem canonicalInteriorFirstJetWeightedActionValue_eq_actionReads
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (weight : ℝ → ℝ) :
    canonicalInteriorSmoothTestActionValue
        timeEnd timeNonnegative a b boxOrder test weight =
      ∫ time : Icc 0 timeEnd,
        canonicalInteriorSmoothTestActionReadAt
          timeEnd timeNonnegative a b boxOrder test weight time
        ∂canonicalAffineTimeMeasure timeEnd := by
  rw [canonicalInteriorSmoothTestActionValue]
  rw [canonicalInteriorFirstJetWeightedActionValue]
  apply integral_congr_ae
  filter_upwards with time
  exact weightedCanonicalInteriorSmoothTestAction_inner_eq_readAt
    timeEnd timeNonnegative a b boxOrder test weight time

theorem canonicalInteriorSmoothTestActionRead_integral_zero
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightZero : weight 0 = 0)
    (weightEndZero : weight timeEnd = 0) :
    (∫ time : Icc 0 timeEnd,
        canonicalInteriorSmoothTestActionReadAt
          timeEnd timeNonnegative a b boxOrder test weight time
        ∂canonicalAffineTimeMeasure timeEnd) = 0 := by
  calc
    _ = canonicalInteriorSmoothTestActionValue
          timeEnd timeNonnegative a b boxOrder test weight :=
      (canonicalInteriorFirstJetWeightedActionValue_eq_actionReads
        timeEnd timeNonnegative a b boxOrder test weight).symm
    _ = canonicalInteriorFirstJetWeightedActionValue
          timeEnd timeNonnegative a b boxOrder weight
          (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) := by
      rw [canonicalInteriorSmoothTestActionValue]
    _ = 0 :=
      canonicalAffinePhysicalTimeL2Output_weightedActionLaw_of_interiorSmoothTest
        timeEnd timeNonnegative a b boxOrder test weight weightRegular
          weightZero weightEndZero

/-- The action-generated canonical Volterra output annihilates the exact
cutoff-mollified spatial difference-quotient test. -/
theorem
    canonicalAffineVolterraPhysicalRepresentative_differenceQuotientActionRead_integral_zero
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (sourceTime : Icc 0 timeEnd)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (cutoff : DiracMatterSpatialCoordinates → ℝ)
    (cutoffCompact : HasCompactSupport cutoff)
    (cutoffSmooth : ContDiff ℝ (⊤ : ℕ∞) cutoff)
    (cutoffInterior : ∀ space,
      ¬ DiracMatterSpatialBoxInterior a b space → cutoff space = 0)
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightZero : weight 0 = 0)
    (weightEndZero : weight timeEnd = 0) :
    (∫ time : Icc 0 timeEnd,
        canonicalInteriorSmoothTestActionReadAt
          timeEnd timePositive.le a b boxOrder
          (canonicalAffineCutoffMollifiedDifferenceQuotientTest
            cutoff cutoffCompact cutoffSmooth cutoffInterior bump shift scale
              (canonicalAffineVolterraPhysicalRepresentative
                timeEnd timePositive a b boxOrder sourceTime))
          weight time
        ∂canonicalAffineTimeMeasure timeEnd) = 0 := by
  exact canonicalInteriorSmoothTestActionRead_integral_zero
    timeEnd timePositive.le a b boxOrder
      (canonicalAffineCutoffMollifiedDifferenceQuotientTest
        cutoff cutoffCompact cutoffSmooth cutoffInterior bump shift scale
          (canonicalAffineVolterraPhysicalRepresentative
            timeEnd timePositive a b boxOrder sourceTime))
      weight weightRegular weightZero weightEndZero

/-- The canonical pointwise Volterra output at `sourceTime`, converted into
the exact cutoff-mollified spatial difference-quotient test. -/
def canonicalAffineVolterraDifferenceQuotientTest
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (sourceTime : Icc 0 timeEnd)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (cutoff : DiracMatterSpatialCoordinates → ℝ)
    (cutoffCompact : HasCompactSupport cutoff)
    (cutoffSmooth : ContDiff ℝ (⊤ : ℕ∞) cutoff)
    (cutoffInterior : ∀ space,
      ¬ DiracMatterSpatialBoxInterior a b space → cutoff space = 0)
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates)) :
    CauchySafeMatterCanonicalInteriorSmoothTest a b :=
  canonicalAffineCutoffMollifiedDifferenceQuotientTest
    cutoff cutoffCompact cutoffSmooth cutoffInterior bump shift scale
      (canonicalAffineVolterraPhysicalRepresentative
        timeEnd timePositive a b boxOrder sourceTime)

/-- Green part of the two-time weak difference-quotient action kernel. -/
def canonicalAffineDifferenceQuotientGreenKernel
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (sourceTime targetTime : Icc 0 timeEnd)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (cutoff : DiracMatterSpatialCoordinates → ℝ)
    (cutoffCompact : HasCompactSupport cutoff)
    (cutoffSmooth : ContDiff ℝ (⊤ : ℕ∞) cutoff)
    (cutoffInterior : ∀ space,
      ¬ DiracMatterSpatialBoxInterior a b space → cutoff space = 0)
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates)) : ℝ :=
  canonicalInteriorSmoothTestGreenReadAt
    timeEnd timePositive.le a b boxOrder
      (canonicalAffineVolterraDifferenceQuotientTest
        timeEnd timePositive a b boxOrder sourceTime shift scale cutoff
          cutoffCompact cutoffSmooth cutoffInterior bump)
      targetTime

/-- Mass part of the same two-time weak difference-quotient action kernel. -/
def canonicalAffineDifferenceQuotientMassKernel
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (sourceTime targetTime : Icc 0 timeEnd)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (cutoff : DiracMatterSpatialCoordinates → ℝ)
    (cutoffCompact : HasCompactSupport cutoff)
    (cutoffSmooth : ContDiff ℝ (⊤ : ℕ∞) cutoff)
    (cutoffInterior : ∀ space,
      ¬ DiracMatterSpatialBoxInterior a b space → cutoff space = 0)
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates)) : ℝ :=
  canonicalInteriorSmoothTestMassReadAt
    timeEnd timePositive.le a b boxOrder
      (canonicalAffineVolterraDifferenceQuotientTest
        timeEnd timePositive a b boxOrder sourceTime shift scale cutoff
          cutoffCompact cutoffSmooth cutoffInterior bump)
      targetTime

/-- For every source time, the two-time difference-quotient kernel obeys
the original generated weighted action law in its target-time variable. -/
theorem canonicalAffineDifferenceQuotient_twoTimeWeightedActionLaw
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (sourceTime : Icc 0 timeEnd)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (cutoff : DiracMatterSpatialCoordinates → ℝ)
    (cutoffCompact : HasCompactSupport cutoff)
    (cutoffSmooth : ContDiff ℝ (⊤ : ℕ∞) cutoff)
    (cutoffInterior : ∀ space,
      ¬ DiracMatterSpatialBoxInterior a b space → cutoff space = 0)
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightZero : weight 0 = 0)
    (weightEndZero : weight timeEnd = 0) :
    (∫ targetTime : Icc 0 timeEnd,
        weight targetTime.1 *
            canonicalAffineDifferenceQuotientGreenKernel
              timeEnd timePositive a b boxOrder sourceTime targetTime shift
                scale cutoff cutoffCompact cutoffSmooth cutoffInterior bump +
          deriv weight targetTime.1 *
            canonicalAffineDifferenceQuotientMassKernel
              timeEnd timePositive a b boxOrder sourceTime targetTime shift
                scale cutoff cutoffCompact cutoffSmooth cutoffInterior bump
        ∂canonicalAffineTimeMeasure timeEnd) = 0 := by
  calc
    _ = ∫ targetTime : Icc 0 timeEnd,
        canonicalInteriorSmoothTestActionReadAt
          timeEnd timePositive.le a b boxOrder
          (canonicalAffineVolterraDifferenceQuotientTest
            timeEnd timePositive a b boxOrder sourceTime shift scale cutoff
              cutoffCompact cutoffSmooth cutoffInterior bump)
          weight targetTime
        ∂canonicalAffineTimeMeasure timeEnd := by
      apply integral_congr_ae
      filter_upwards with targetTime
      rfl
    _ = 0 := canonicalInteriorSmoothTestActionRead_integral_zero
      timeEnd timePositive.le a b boxOrder
        (canonicalAffineVolterraDifferenceQuotientTest
          timeEnd timePositive a b boxOrder sourceTime shift scale cutoff
            cutoffCompact cutoffSmooth cutoffInterior bump)
        weight weightRegular weightZero weightEndZero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientActionRead
