import H0mework.Physics.DiracEvolution.SafeCanonicalAffineGreenGeneratedLimitRecognition

/-!
# Fixed P506/L0 canonical affine physical Green equation

The dynamic mass read of the fixed source lift is differentiated directly
from the source-owned mass coefficient.  Adding that closed path to the
generated correction occurrence identifies the canonical affine physical
Green read with both its endpoint and weighted mother-action laws.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalGreenEquation

open Filter MeasureTheory Metric Set
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenAssembly
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenGeneratedLimitRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalActionTransport
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineRieszActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineWeakLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterHermitianEnergyIdentity
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open scoped ContDiff Interval Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

private def sourceLiftMassDensity
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  matterFiberMassPairing
    (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
    (matterCoordinateEquiv diracSpinTwoMatterProbe)
    ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space)

private def sourceLiftMassPairing
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) : ℝ :=
  ∫ space in Icc a b, sourceLiftMassDensity a b test time space

/-- Dynamic action-mass read of the fixed source-owned affine lift. -/
def canonicalSourceLiftMassRead
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) : ℝ :=
  sourceLiftMassPairing a b test time

private def sourceLiftMassRateDensity
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  diracExteriorMatterEnergyPairing
    (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
      canonicalLorentzianTimeDirection time space)
    diracSpinTwoMatterProbe
    (matterCoordinateEquiv.symm
      ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space))

private def sourceLiftMassPairingCoordinates :
    CauchySafeMatterDiracMatrixCoordinates →L[ℝ]
      (MatterCoordinateCarrier →L[ℝ]
        (MatterCoordinateCarrier →L[ℝ] ℝ)) :=
  matterFiberMassPairing.comp diracMatrixOfCoordinates

private def sourceLiftMassRateMatrixCoordinates
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    CauchySafeMatterDiracMatrixCoordinates :=
  WithLp.toLp 2 fun coordinatePair ↦
    fixedEvolutionPrincipalDirectionalDerivativeOnSlice
      canonicalLorentzianTimeDirection time space
      coordinatePair.1 coordinatePair.2

@[simp] private theorem
    diracMatrixOfCoordinates_sourceLiftMassRateMatrixCoordinates
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatrixOfCoordinates
        (sourceLiftMassRateMatrixCoordinates time space) =
      fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection time space :=
  rfl

private theorem sourceLiftMassDensity_joint_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      sourceLiftMassDensity a b test input.1 input.2) := by
  have matrixContinuous : Continuous (fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        input.1 input.2) := by
    apply (PiLp.continuous_toLp 2
      (fun _ : DiracSpinorIndex × DiracSpinorIndex ↦ ℂ)).comp
    apply continuous_pi
    intro coordinatePair
    exact fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
      coordinatePair.1 coordinatePair.2
  have testContinuous : Continuous (fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
      (cauchySafeMatterCanonicalInteriorDenseTest a b test).1 input.2) :=
    (cauchySafeMatterCanonicalInteriorDenseTest a b test).property.2.continuous
      |>.comp continuous_snd
  have functionEq :
      (fun input : ℝ × DiracMatterSpatialCoordinates ↦
        sourceLiftMassDensity a b test input.1 input.2) =
      (fun input ↦ sourceLiftMassPairingCoordinates
        (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          input.1 input.2)
        (matterCoordinateEquiv diracSpinTwoMatterProbe)
        ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1
          input.2)) := by
    rfl
  rw [functionEq]
  exact (((sourceLiftMassPairingCoordinates.continuous.comp matrixContinuous
    ).clm_apply continuous_const).clm_apply testContinuous)

private theorem sourceLiftMassRateDensity_joint_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      sourceLiftMassRateDensity a b test input.1 input.2) := by
  have matrixContinuous : Continuous (fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
      sourceLiftMassRateMatrixCoordinates input.1 input.2) := by
    apply (PiLp.continuous_toLp 2
      (fun _ : DiracSpinorIndex × DiracSpinorIndex ↦ ℂ)).comp
    apply continuous_pi
    intro coordinatePair
    exact fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
      canonicalLorentzianTimeDirection coordinatePair.1 coordinatePair.2
  have testContinuous : Continuous (fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
      (cauchySafeMatterCanonicalInteriorDenseTest a b test).1 input.2) :=
    (cauchySafeMatterCanonicalInteriorDenseTest a b test).property.2.continuous
      |>.comp continuous_snd
  have functionEq :
      (fun input : ℝ × DiracMatterSpatialCoordinates ↦
        sourceLiftMassRateDensity a b test input.1 input.2) =
      (fun input ↦ sourceLiftMassPairingCoordinates
        (sourceLiftMassRateMatrixCoordinates input.1 input.2)
        (matterCoordinateEquiv diracSpinTwoMatterProbe)
        ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1
          input.2)) := by
    funext input
    simp only [sourceLiftMassRateDensity, sourceLiftMassPairingCoordinates,
      ContinuousLinearMap.comp_apply, matterFiberMassPairing_apply,
      matterCoordinateEquiv.symm_apply_apply,
      diracMatrixOfCoordinates_sourceLiftMassRateMatrixCoordinates]
  rw [functionEq]
  exact (((sourceLiftMassPairingCoordinates.continuous.comp matrixContinuous
    ).clm_apply continuous_const).clm_apply testContinuous)

private theorem fixedMassMatrix_eq_fixedEvolutionPrincipalOnSlice
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    fixedP506L0CauchySafeMatterWeakMassMatrix time space =
      fixedEvolutionPrincipalOnSlice canonicalLorentzianTimeDirection
        time space := by
  rfl

private theorem fixedEvolutionPrincipalOnSlice_entry_time_hasDerivAt
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (row column : DiracSpinorIndex) :
    HasDerivAt
      (fun candidateTime ↦
        fixedEvolutionPrincipalOnSlice canonicalLorentzianTimeDirection
          candidateTime space row column)
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection time space row column)
      time := by
  let entry : ℝ × DiracMatterSpatialCoordinates → ℂ :=
    fun input ↦ fixedEvolutionPrincipalOnSlice
      canonicalLorentzianTimeDirection input.1 input.2 row column
  have entryDerivative :=
    (((fixedEvolutionPrincipalOnSlice_entry_contDiff
      canonicalLorentzianTimeDirection row column).of_le (by norm_num)
      ).differentiable one_ne_zero (time, space)).hasFDerivAt
  have sliceDerivative : HasDerivAt
      (fun candidateTime : ℝ ↦ (candidateTime, space))
      (diracMatterSliceDirection canonicalLorentzianTimeDirection) time := by
    simpa [diracMatterSliceDirection, canonicalLorentzianTimeDirection] using
      (hasDerivAt_id time).prodMk (hasDerivAt_const time space)
  change HasDerivAt
    (entry ∘ fun candidateTime : ℝ ↦ (candidateTime, space))
    ((fderiv ℝ entry (time, space))
      (diracMatterSliceDirection canonicalLorentzianTimeDirection)) time
  exact entryDerivative.comp_hasDerivAt time sliceDerivative

private theorem fixedMassMatrix_entry_time_hasDerivAt
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (row column : DiracSpinorIndex) :
    HasDerivAt
      (fun candidateTime ↦
        fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime space row column)
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection time space row column)
      time := by
  simpa only [fixedMassMatrix_eq_fixedEvolutionPrincipalOnSlice] using
    fixedEvolutionPrincipalOnSlice_entry_time_hasDerivAt
      time space row column

private theorem sourceLiftActedTestCoordinate_hasDerivAt
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (internal : InternalMatterCoordinateIndex)
    (row : DiracSpinorIndex) :
    HasDerivAt
      (fun candidateTime ↦
        internalMatterCoordinate internal
          (diracMatrixMatterAction
            (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime space)
            (matterCoordinateEquiv.symm
              ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space))
            row))
      (internalMatterCoordinate internal
        (diracMatrixMatterAction
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection time space)
          (matterCoordinateEquiv.symm
            ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space))
          row))
      time := by
  simp only [internalMatterCoordinate_diracMatrixMatterAction]
  exact HasDerivAt.fun_sum (u := Finset.univ)
    (fun column _ ↦
      (fixedMassMatrix_entry_time_hasDerivAt time space row column).mul_const
        (internalMatterCoordinate internal
          ((matterCoordinateEquiv.symm
            ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space))
            column)))

private theorem sourceLiftMassDensity_time_hasDerivAt
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    HasDerivAt
      (fun candidateTime ↦
        sourceLiftMassDensity a b test candidateTime space)
      (diracExteriorMatterEnergyPairing
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection time space)
        diracSpinTwoMatterProbe
        (matterCoordinateEquiv.symm
          ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space)))
      time := by
  let testField : DiracExteriorMatterCarrier :=
    matterCoordinateEquiv.symm
      ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space)
  let actedTest : ℝ → DiracExteriorMatterCarrier :=
    fun candidateTime ↦
      diracMatrixMatterAction
        (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime space)
        testField
  have sourceDerivative : ∀ internal spin, HasDerivAt
      (fun _candidateTime : ℝ ↦
        internalMatterCoordinate internal (diracSpinTwoMatterProbe spin))
      (internalMatterCoordinate internal ((0 : DiracExteriorMatterCarrier) spin))
      time := by
    intro internal spin
    simpa using hasDerivAt_const time
      (internalMatterCoordinate internal (diracSpinTwoMatterProbe spin))
  have actedDerivative : ∀ internal spin, HasDerivAt
      (fun candidateTime ↦
        internalMatterCoordinate internal (actedTest candidateTime spin))
      (internalMatterCoordinate internal
        ((diracMatrixMatterAction
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection time space)
          testField) spin))
      time := by
    intro internal spin
    exact sourceLiftActedTestCoordinate_hasDerivAt
      a b test time space internal spin
  have pairingDerivative :=
    diracExteriorMatterCoordinatePairing_re_hasDerivAt
      (fun _candidateTime : ℝ ↦ diracSpinTwoMatterProbe)
      actedTest 0
      (diracMatrixMatterAction
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection time space)
        testField)
      time sourceDerivative actedDerivative
  have zeroPairing : Complex.re
      (diracExteriorMatterCoordinatePairing
        (0 : DiracExteriorMatterCarrier) (actedTest time)) = 0 := by
    simp [diracExteriorMatterCoordinatePairing, dotProduct]
  rw [zeroPairing, zero_add] at pairingDerivative
  simpa [sourceLiftMassDensity, matterFiberMassPairing_apply,
    diracExteriorMatterEnergyPairing, actedTest, testField] using
    pairingDerivative

private theorem sourceLiftMassIntegral_hasDerivAt
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) :
    HasDerivAt
      (fun candidateTime ↦ ∫ space in Icc a b,
        sourceLiftMassDensity a b test candidateTime space)
      (∫ space in Icc a b,
        sourceLiftMassRateDensity a b test time space)
      time := by
  let compactSet : Set (ℝ × DiracMatterSpatialCoordinates) :=
    closedBall time 1 ×ˢ Icc a b
  have compactSetCompact : IsCompact compactSet :=
    (isCompact_closedBall time (1 : ℝ)).prod isCompact_Icc
  have rateContinuous := sourceLiftMassRateDensity_joint_continuous a b test
  obtain ⟨C, rateBound⟩ := compactSetCompact.exists_bound_of_continuousOn
    rateContinuous.continuousOn
  let bound : DiracMatterSpatialCoordinates → ℝ := fun _space ↦ C
  have timeNeighborhood : closedBall time 1 ∈ nhds time :=
    mem_of_superset (ball_mem_nhds time zero_lt_one) ball_subset_closedBall
  have result := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc a b))
    (F := sourceLiftMassDensity a b test)
    (F' := sourceLiftMassRateDensity a b test)
    (bound := bound)
    timeNeighborhood
    (by
      filter_upwards with candidateTime
      exact (sourceLiftMassDensity_joint_continuous a b test).comp
        (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable)
    ((sourceLiftMassDensity_joint_continuous a b test).comp
      (continuous_const.prodMk continuous_id) |>.continuousOn
      |>.integrableOn_compact isCompact_Icc)
    ((sourceLiftMassRateDensity_joint_continuous a b test).comp
      (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
      intro candidateTime candidateTimeMem
      exact rateBound (candidateTime, space) ⟨candidateTimeMem, spaceMem⟩)
    (integrableOn_const isCompact_Icc.measure_ne_top)
    (by
      filter_upwards with space candidateTime _
      simpa [sourceLiftMassRateDensity] using
        sourceLiftMassDensity_time_hasDerivAt
          a b test candidateTime space)).2
  exact result

private theorem sourceLiftMassRateIntegral_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    Continuous (fun time : ℝ ↦ ∫ space in Icc a b,
      sourceLiftMassRateDensity a b test time space) := by
  exact continuous_parametric_integral_of_continuous
    (sourceLiftMassRateDensity_joint_continuous a b test) isCompact_Icc

private theorem canonicalSourceLiftMassRate_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    Continuous (canonicalSourceLiftMassRate a b test) := by
  have rateEq : (fun time ↦ canonicalSourceLiftMassRate a b test time) =
      (fun time ↦ ∫ space in Icc a b,
        sourceLiftMassRateDensity a b test time space) := by
    funext time
    simp only [canonicalSourceLiftMassRate, sourceLiftMassRateDensity,
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_slice]
  change Continuous (fun time ↦ canonicalSourceLiftMassRate a b test time)
  rw [rateEq]
  exact sourceLiftMassRateIntegral_continuous a b test

def canonicalSourceLiftMassPairingPath
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    CanonicalAffineWeakPairingPath timeEnd where
  pairing := sourceLiftMassPairing a b test
  rate := canonicalSourceLiftMassRate a b test
  derivative := by
    intro time _timeMem
    have rateEq : canonicalSourceLiftMassRate a b test time =
        ∫ space in Icc a b,
          sourceLiftMassRateDensity a b test time space := by
      simp only [canonicalSourceLiftMassRate, sourceLiftMassRateDensity,
        cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_slice]
    rw [rateEq]
    change HasDerivWithinAt
      (fun candidateTime ↦ ∫ space in Icc a b,
        sourceLiftMassDensity a b test candidateTime space)
      (∫ space in Icc a b,
        sourceLiftMassRateDensity a b test time space)
      (Icc 0 timeEnd) time
    exact (sourceLiftMassIntegral_hasDerivAt a b test time).hasDerivWithinAt
  rateContinuousOn := by
    exact (canonicalSourceLiftMassRate_continuous a b test).continuousOn

private theorem canonicalSourceLiftMassPairing_endpointActionLaw
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc 0 timeEnd) :
    (∫ candidateTime in 0..time,
        canonicalSourceLiftMassRate a b test candidateTime) =
      sourceLiftMassPairing a b test time -
        sourceLiftMassPairing a b test 0 := by
  exact (canonicalSourceLiftMassPairingPath timeEnd a b test).integral_rate
    time timeMem

/-- Weighted integration by parts for the dynamic mother-action mass read of
the fixed source-owned affine lift. -/
theorem canonicalSourceLiftMassRead_weighted_integral_rate
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (∫ candidateTime in 0..timeEnd,
        weight candidateTime *
          canonicalSourceLiftMassRate a b test candidateTime) =
      weight timeEnd * canonicalSourceLiftMassRead a b test timeEnd -
        weight 0 * canonicalSourceLiftMassRead a b test 0 -
        ∫ candidateTime in 0..timeEnd,
          deriv weight candidateTime *
            canonicalSourceLiftMassRead a b test candidateTime := by
  simpa [canonicalSourceLiftMassPairingPath,
    canonicalSourceLiftMassRead] using
    (canonicalSourceLiftMassPairingPath timeEnd a b test
      ).weighted_integral_rate timeNonnegative weight weightRegular

/-- Endpoint-vanishing weights annihilate the complete dynamic mass action
of the fixed source lift. -/
theorem canonicalSourceLiftMassRead_weighted_cancellation
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightZero : weight 0 = 0)
    (weightEndZero : weight timeEnd = 0) :
    (∫ candidateTime in 0..timeEnd,
        weight candidateTime *
            canonicalSourceLiftMassRate a b test candidateTime +
          deriv weight candidateTime *
            canonicalSourceLiftMassRead a b test candidateTime) = 0 := by
  let path := canonicalSourceLiftMassPairingPath timeEnd a b test
  have rateIntegrable : IntervalIntegrable
      (fun candidateTime ↦ weight candidateTime *
        canonicalSourceLiftMassRate a b test candidateTime)
      volume 0 timeEnd :=
    (weightRegular.continuous.continuousOn.mul path.rateContinuousOn
      ).intervalIntegrable_of_Icc timeNonnegative
  have massIntegrable : IntervalIntegrable
      (fun candidateTime ↦ deriv weight candidateTime *
        canonicalSourceLiftMassRead a b test candidateTime)
      volume 0 timeEnd :=
    ((weightRegular.continuous_deriv le_rfl).continuousOn.mul
      path.pairingContinuousOn).intervalIntegrable_of_Icc timeNonnegative
  rw [intervalIntegral.integral_add rateIntegrable massIntegrable,
    canonicalSourceLiftMassRead_weighted_integral_rate
      timeEnd timeNonnegative a b test weight weightRegular,
    weightEndZero, weightZero]
  ring

/-- Green-rate read of the generated affine physical output. -/
def canonicalAffinePhysicalGreenRate
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (time : ℝ) : ℝ :=
  fixedP506L0CauchySafeMatterGreenRateL2Read
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
      a b test)
    time a b
    (occurrence.affinePhysicalField
      (projIcc 0 timeEnd timeNonnegative time))

/-- Total action-mass read: generated correction plus fixed source lift. -/
def canonicalAffinePhysicalMassRead
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (time : Icc 0 timeEnd) : ℝ :=
  canonicalAffineCorrectionPhysicalMassRead occurrence test time +
    canonicalSourceLiftMassRead a b test time.1

private theorem sourceLiftMassPairing_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    Continuous (sourceLiftMassPairing a b test) := by
  rw [continuous_iff_continuousAt]
  intro time
  exact (sourceLiftMassIntegral_hasDerivAt a b test time).continuousAt

private theorem canonicalAffineWeightedTotalRate_tendsto_physicalGreenIntegral
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc 0 timeEnd)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Tendsto
      (fun sequenceIndex ↦ ∫ candidateTime in 0..time,
        weight candidateTime *
          ((canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) test).rate
              candidateTime +
            canonicalSourceLiftMassRate a b test candidateTime))
      atTop
      (nhds (∫ candidateTime in 0..time,
        weight candidateTime *
          canonicalAffinePhysicalGreenRate occurrence test candidateTime)) := by
  obtain ⟨L, _LNonnegative, correctionBound⟩ :=
    exists_canonicalAffineCorrectionPairing_rate_uniform_bound
      timeEnd timeNonnegative a b boxOrder test
  have sourceRateContinuous :=
    canonicalSourceLiftMassRate_continuous a b test
  obtain ⟨C, sourceBound⟩ :=
    (isCompact_Icc : IsCompact (Icc 0 timeEnd)).exists_bound_of_continuousOn
      sourceRateContinuous.continuousOn
  have intervalSubset : Ι 0 time ⊆ Icc 0 timeEnd := by
    intro candidateTime candidateTimeMem
    have candidateTimeShort : candidateTime ∈ Icc 0 time := by
      rw [← uIcc_of_le timeMem.1]
      exact uIoc_subset_uIcc candidateTimeMem
    exact ⟨candidateTimeShort.1, candidateTimeShort.2.trans timeMem.2⟩
  have eventuallyEntered : ∀ᶠ sequenceIndex : ℕ in atTop,
      cauchySafeMatterCanonicalInteriorTestEntry test ≤
        occurrence.weakLimit.subsequence sequenceIndex :=
    occurrence.weakLimit.subsequenceStrict.tendsto_atTop
      (eventually_ge_atTop
        (cauchySafeMatterCanonicalInteriorTestEntry test))
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun candidateTime ↦ ‖weight candidateTime‖ * (L + C))
  · exact Filter.Eventually.of_forall fun sequenceIndex ↦
      (((weightRegular.continuous.continuousOn).mul
        (((canonicalAffineCorrectionPairingPath
          timeEnd timeNonnegative a b
          (occurrence.weakLimit.subsequence sequenceIndex) test
          ).rateContinuousOn).add sourceRateContinuous.continuousOn)).mono
            intervalSubset).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [eventuallyEntered] with sequenceIndex entered
    exact Filter.Eventually.of_forall fun candidateTime candidateTimeMem ↦ by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg (weight candidateTime))
      exact (norm_add_le _ _).trans (add_le_add
        (correctionBound _ entered candidateTime
          (intervalSubset candidateTimeMem))
        (sourceBound candidateTime (intervalSubset candidateTimeMem)))
  · exact (weightRegular.continuous.norm.mul continuous_const).continuousOn
      |>.intervalIntegrable_of_Icc timeMem.1
  · exact Filter.Eventually.of_forall fun candidateTime candidateTimeMem ↦ by
      let physicalTime : Icc 0 timeEnd :=
        ⟨candidateTime, intervalSubset candidateTimeMem⟩
      have correctionConvergence :=
        canonicalAffineCorrectionRate_weakConvergence_to_physicalGreen
          timeEnd timeNonnegative a b boxOrder occurrence test physicalTime
      have totalConvergence := correctionConvergence.add_const
        (canonicalSourceLiftMassRate a b test candidateTime)
      have weightConvergence : Tendsto
          (fun _sequenceIndex : ℕ ↦ weight candidateTime) atTop
          (nhds (weight candidateTime)) := tendsto_const_nhds
      have weightedConvergence := weightConvergence.mul totalConvergence
      rw [canonicalAffinePhysicalGreenRate,
        projIcc_of_mem timeNonnegative (intervalSubset candidateTimeMem)]
      change Tendsto
        (fun sequenceIndex ↦ weight candidateTime *
          ((canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) test).rate
              candidateTime +
            canonicalSourceLiftMassRate a b test candidateTime))
        atTop
        (nhds (weight candidateTime *
          fixedP506L0CauchySafeMatterGreenRateL2Read
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test)
            candidateTime a b (occurrence.affinePhysicalField physicalTime)))
      simpa [physicalTime] using weightedConvergence

private theorem canonicalAffineWeightedTotalRate_tendsto_actionMass
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Tendsto
      (fun sequenceIndex ↦ ∫ candidateTime in 0..timeEnd,
        weight candidateTime *
          ((canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) test).rate
              candidateTime +
            canonicalSourceLiftMassRate a b test candidateTime))
      atTop
      (nhds (weight timeEnd *
          canonicalAffinePhysicalMassRead occurrence test
            ⟨timeEnd, right_mem_Icc.mpr timeNonnegative⟩ -
        weight 0 * canonicalAffinePhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩ -
        ∫ candidateTime in 0..timeEnd,
          deriv weight candidateTime *
            canonicalAffinePhysicalMassRead occurrence test
              (projIcc 0 timeEnd timeNonnegative candidateTime))) := by
  have correctionConvergence :=
    canonicalAffineCorrectionWeightedPhysicalActionLaw occurrence test weight
      weightRegular
  have sourceWeighted :=
    (canonicalSourceLiftMassPairingPath timeEnd a b test
      ).weighted_integral_rate timeNonnegative weight weightRegular
  have sourceWeightedEq :
      (∫ candidateTime in 0..timeEnd,
        weight candidateTime *
          canonicalSourceLiftMassRate a b test candidateTime) =
      weight timeEnd * sourceLiftMassPairing a b test timeEnd -
        weight 0 * sourceLiftMassPairing a b test 0 -
        ∫ candidateTime in 0..timeEnd,
          deriv weight candidateTime *
            sourceLiftMassPairing a b test candidateTime := by
    simpa [canonicalSourceLiftMassPairingPath] using sourceWeighted
  have sourceDerivativeProjectedEq :
      (∫ candidateTime in 0..timeEnd,
        deriv weight candidateTime *
          sourceLiftMassPairing a b test candidateTime) =
      ∫ candidateTime in 0..timeEnd,
        deriv weight candidateTime *
          sourceLiftMassPairing a b test
            (projIcc 0 timeEnd timeNonnegative candidateTime).1 := by
    apply intervalIntegral.integral_congr
    intro candidateTime candidateTimeMem
    rw [uIcc_of_le timeNonnegative] at candidateTimeMem
    change deriv weight candidateTime *
        sourceLiftMassPairing a b test candidateTime =
      deriv weight candidateTime *
        sourceLiftMassPairing a b test
          (projIcc 0 timeEnd timeNonnegative candidateTime).1
    rw [projIcc_of_mem timeNonnegative candidateTimeMem]
  have shifted := correctionConvergence.add_const
    (∫ candidateTime in 0..timeEnd,
      weight candidateTime *
        canonicalSourceLiftMassRate a b test candidateTime)
  have correctionMassContinuous : Continuous (fun candidateTime ↦
      canonicalAffineCorrectionPhysicalMassRead occurrence test
        (projIcc 0 timeEnd timeNonnegative candidateTime)) := by
    have limitContinuous :=
      (occurrence.weakLimit.limit test).continuous.comp
        (continuous_projIcc (h := timeNonnegative))
    have readEq : (fun candidateTime ↦
        canonicalAffineCorrectionPhysicalMassRead occurrence test
          (projIcc 0 timeEnd timeNonnegative candidateTime)) =
        (fun candidateTime ↦ occurrence.weakLimit.limit test
          (projIcc 0 timeEnd timeNonnegative candidateTime)) := by
      funext candidateTime
      exact canonicalAffineCorrectionPhysicalMassRead_eq_limit occurrence test _
    rw [readEq]
    exact limitContinuous
  have sourceMassContinuous : Continuous (fun candidateTime ↦
      sourceLiftMassPairing a b test
        (projIcc 0 timeEnd timeNonnegative candidateTime).1) :=
    (sourceLiftMassPairing_continuous a b test).comp
      (continuous_subtype_val.comp
        (continuous_projIcc (h := timeNonnegative)))
  have derivativeContinuous : Continuous (deriv weight) :=
    weightRegular.continuous_deriv le_rfl
  have correctionDerivativeIntegrable : IntervalIntegrable
      (fun candidateTime ↦ deriv weight candidateTime *
        canonicalAffineCorrectionPhysicalMassRead occurrence test
          (projIcc 0 timeEnd timeNonnegative candidateTime))
      volume 0 timeEnd :=
    (derivativeContinuous.mul correctionMassContinuous).continuousOn
      |>.intervalIntegrable_of_Icc timeNonnegative
  have sourceDerivativeIntegrable : IntervalIntegrable
      (fun candidateTime ↦ deriv weight candidateTime *
        sourceLiftMassPairing a b test
          (projIcc 0 timeEnd timeNonnegative candidateTime).1)
      volume 0 timeEnd :=
    (derivativeContinuous.mul sourceMassContinuous).continuousOn
      |>.intervalIntegrable_of_Icc timeNonnegative
  have derivativeIntegralEq :
      (∫ candidateTime in 0..timeEnd,
        deriv weight candidateTime *
          canonicalAffinePhysicalMassRead occurrence test
            (projIcc 0 timeEnd timeNonnegative candidateTime)) =
      (∫ candidateTime in 0..timeEnd,
        deriv weight candidateTime *
          canonicalAffineCorrectionPhysicalMassRead occurrence test
            (projIcc 0 timeEnd timeNonnegative candidateTime)) +
      ∫ candidateTime in 0..timeEnd,
        deriv weight candidateTime *
          sourceLiftMassPairing a b test
            (projIcc 0 timeEnd timeNonnegative candidateTime).1 := by
    rw [← intervalIntegral.integral_add correctionDerivativeIntegrable
      sourceDerivativeIntegrable]
    apply intervalIntegral.integral_congr
    intro candidateTime _candidateTimeMem
    simp only [canonicalAffinePhysicalMassRead, canonicalSourceLiftMassRead]
    ring
  have endpointEq :
      (weight timeEnd *
          canonicalAffineCorrectionPhysicalMassRead occurrence test
            ⟨timeEnd, right_mem_Icc.mpr timeNonnegative⟩ -
        weight 0 * canonicalAffineCorrectionPhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩ -
        ∫ candidateTime in 0..timeEnd,
          deriv weight candidateTime *
            canonicalAffineCorrectionPhysicalMassRead occurrence test
              (projIcc 0 timeEnd timeNonnegative candidateTime)) +
        (∫ candidateTime in 0..timeEnd,
          weight candidateTime *
            canonicalSourceLiftMassRate a b test candidateTime) =
      weight timeEnd *
          canonicalAffinePhysicalMassRead occurrence test
            ⟨timeEnd, right_mem_Icc.mpr timeNonnegative⟩ -
        weight 0 * canonicalAffinePhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩ -
        ∫ candidateTime in 0..timeEnd,
          deriv weight candidateTime *
            canonicalAffinePhysicalMassRead occurrence test
              (projIcc 0 timeEnd timeNonnegative candidateTime) := by
    rw [sourceWeightedEq, sourceDerivativeProjectedEq,
      derivativeIntegralEq]
    simp only [canonicalAffinePhysicalMassRead, canonicalSourceLiftMassRead]
    ring
  rw [← endpointEq]
  apply shifted.congr'
  filter_upwards with sequenceIndex
  have correctionIntegrable : IntervalIntegrable
      (fun candidateTime ↦ weight candidateTime *
        (canonicalAffineCorrectionPairingPath
          timeEnd timeNonnegative a b
          (occurrence.weakLimit.subsequence sequenceIndex) test).rate
            candidateTime)
      volume 0 timeEnd :=
    ((weightRegular.continuous.continuousOn).mul
      (canonicalAffineCorrectionPairingPath
        timeEnd timeNonnegative a b
        (occurrence.weakLimit.subsequence sequenceIndex) test).rateContinuousOn
      ).intervalIntegrable_of_Icc timeNonnegative
  have sourceRateContinuous :=
    canonicalSourceLiftMassRate_continuous a b test
  have sourceIntegrable : IntervalIntegrable
      (fun candidateTime ↦ weight candidateTime *
        canonicalSourceLiftMassRate a b test candidateTime)
      volume 0 timeEnd :=
    (weightRegular.continuous.mul sourceRateContinuous).continuousOn
      |>.intervalIntegrable_of_Icc timeNonnegative
  rw [← intervalIntegral.integral_add correctionIntegrable sourceIntegrable]
  apply intervalIntegral.integral_congr
  intro candidateTime _candidateTimeMem
  ring

/-- Weighted distributional mother-action law on the same generated affine
physical occurrence. -/
theorem canonicalAffinePhysicalWeightedGreenLaw
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (∫ candidateTime in 0..timeEnd,
        weight candidateTime *
          canonicalAffinePhysicalGreenRate occurrence test candidateTime) =
      weight timeEnd *
          canonicalAffinePhysicalMassRead occurrence test
            ⟨timeEnd, right_mem_Icc.mpr timeNonnegative⟩ -
        weight 0 * canonicalAffinePhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩ -
        ∫ candidateTime in 0..timeEnd,
          deriv weight candidateTime *
            canonicalAffinePhysicalMassRead occurrence test
              (projIcc 0 timeEnd timeNonnegative candidateTime) := by
  exact tendsto_nhds_unique
    (canonicalAffineWeightedTotalRate_tendsto_physicalGreenIntegral
      timeEnd timeNonnegative a b boxOrder occurrence test timeEnd
        (right_mem_Icc.mpr timeNonnegative) weight weightRegular)
    (canonicalAffineWeightedTotalRate_tendsto_actionMass
      timeEnd timeNonnegative a b occurrence test weight weightRegular)

private theorem canonicalAffineTotalRate_tendsto_actionMassAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc 0 timeEnd) :
    Tendsto
      (fun sequenceIndex ↦ ∫ candidateTime in 0..time,
        (canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) test).rate
              candidateTime +
          canonicalSourceLiftMassRate a b test candidateTime)
      atTop
      (nhds (canonicalAffinePhysicalMassRead occurrence test ⟨time, timeMem⟩ -
        canonicalAffinePhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩)) := by
  have correctionConvergence :=
    canonicalAffineCorrectionPhysicalEndpointActionLaw
      occurrence test time timeMem
  have combined := correctionConvergence.add_const
    (∫ candidateTime in 0..time,
      canonicalSourceLiftMassRate a b test candidateTime)
  have combinedIntegral : Tendsto
      (fun sequenceIndex ↦ ∫ candidateTime in 0..time,
        (canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) test).rate
              candidateTime +
          canonicalSourceLiftMassRate a b test candidateTime)
      atTop
      (nhds
        ((canonicalAffineCorrectionPhysicalMassRead occurrence test
              ⟨time, timeMem⟩ -
            canonicalAffineCorrectionPhysicalMassRead occurrence test
              ⟨0, left_mem_Icc.mpr timeNonnegative⟩) +
          (∫ candidateTime in 0..time,
            canonicalSourceLiftMassRate a b test candidateTime))) := by
    apply combined.congr'
    exact Filter.Eventually.of_forall fun sequenceIndex ↦ by
      change (∫ candidateTime in 0..time,
          (canonicalAffineCorrectionPairingPath
              timeEnd timeNonnegative a b
              (occurrence.weakLimit.subsequence sequenceIndex) test).rate
                candidateTime) +
          ∫ candidateTime in 0..time,
            canonicalSourceLiftMassRate a b test candidateTime =
        ∫ candidateTime in 0..time,
          (canonicalAffineCorrectionPairingPath
              timeEnd timeNonnegative a b
              (occurrence.weakLimit.subsequence sequenceIndex) test).rate
                candidateTime +
            canonicalSourceLiftMassRate a b test candidateTime
      exact (intervalIntegral.integral_add
        ((((canonicalAffineCorrectionPairingPath
          timeEnd timeNonnegative a b
          (occurrence.weakLimit.subsequence sequenceIndex) test
          ).rateContinuousOn).mono
            (Icc_subset_Icc_right timeMem.2)).intervalIntegrable_of_Icc
              timeMem.1)
        ((canonicalSourceLiftMassRate_continuous a b test
          ).continuousOn.intervalIntegrable_of_Icc timeMem.1)).symm
  rw [canonicalSourceLiftMassPairing_endpointActionLaw
    timeEnd a b test time timeMem] at combinedIntegral
  convert combinedIntegral using 1
  all_goals
    simp [canonicalAffinePhysicalMassRead, canonicalSourceLiftMassRead,
      sourceLiftMassPairing]
    ring

/-- The same generated physical output satisfies the exact Volterra endpoint
law at every canonical source time. -/
theorem canonicalAffinePhysicalEndpointGreenLawAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc 0 timeEnd) :
    (∫ candidateTime in 0..time,
        canonicalAffinePhysicalGreenRate occurrence test candidateTime) =
      canonicalAffinePhysicalMassRead occurrence test ⟨time, timeMem⟩ -
        canonicalAffinePhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩ := by
  have unitRegular : ContDiff ℝ 1 (fun _ : ℝ ↦ (1 : ℝ)) := by
    fun_prop
  have physicalConvergence :=
    canonicalAffineWeightedTotalRate_tendsto_physicalGreenIntegral
      timeEnd timeNonnegative a b boxOrder occurrence test time timeMem
        (fun _ : ℝ ↦ (1 : ℝ)) unitRegular
  exact tendsto_nhds_unique
    (by simpa using physicalConvergence)
    (canonicalAffineTotalRate_tendsto_actionMassAt
      timeEnd timeNonnegative a b occurrence test time timeMem)

/-- The arbitrary-time endpoint law specializes to the full canonical source
interval. -/
theorem canonicalAffinePhysicalEndpointGreenLaw
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ) :
    (∫ candidateTime in 0..timeEnd,
        canonicalAffinePhysicalGreenRate occurrence test candidateTime) =
      canonicalAffinePhysicalMassRead occurrence test
          ⟨timeEnd, right_mem_Icc.mpr timeNonnegative⟩ -
        canonicalAffinePhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩ := by
  exact canonicalAffinePhysicalEndpointGreenLawAt
    timeEnd timeNonnegative a b boxOrder occurrence test timeEnd
      (right_mem_Icc.mpr timeNonnegative)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalGreenEquation
