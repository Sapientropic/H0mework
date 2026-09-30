import H0mework.Physics.DiracEvolution.SafeCanonicalAffineRieszActualization

/-!
# Fixed P506/L0 canonical affine physical action transport

The source-generated correction weak limit is read back through its unique
mass actualization.  Endpoint and weighted finite action laws therefore land
on the same physical `L²` output.  The zero correction initial condition is
transported through Riesz and mother-action mass inversion, while the total
affine field retains the exact source-owned lift.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalActionTransport

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineCountableWeakPairingCompactness
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryForcing
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineRieszActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineWeakLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

def canonicalAffineCorrectionPhysicalMassRead
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (time : Icc 0 timeEnd) : ℝ :=
  ∫ space,
    matterFiberMassPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
      (occurrence.correctionPhysicalActualization.physicalField time space)
      ((cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorDenseTest a b test)) space)
    ∂volume.restrict (Icc a b)

theorem canonicalAffineCorrectionPhysicalMassRead_eq_limit
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (time : Icc 0 timeEnd) :
    canonicalAffineCorrectionPhysicalMassRead occurrence test time =
      occurrence.weakLimit.limit test time := by
  unfold canonicalAffineCorrectionPhysicalMassRead
  rw [occurrence.correctionPhysicalActualization.massLaw]
  exact occurrence.correctionMassRepresentative_generatorPairing time test

theorem canonicalAffineCorrectionBoundedPairing_zeroTime
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ) :
    canonicalAffineCorrectionBoundedPairing
        timeEnd timeNonnegative a b testCount test
        ⟨0, left_mem_Icc.mpr timeNonnegative⟩ = 0 := by
  change galerkinWeakTestPairing
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
        timeEnd timeNonnegative a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
        a b testCount test) 0 = 0
  unfold galerkinWeakTestPairing
  rw [fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_initial]
  simp

theorem canonicalAffineCorrectionWeakLimit_limit_zeroTime
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ) :
    occurrence.weakLimit.limit test
        ⟨0, left_mem_Icc.mpr timeNonnegative⟩ = 0 := by
  let initialTime : Icc 0 timeEnd :=
    ⟨0, left_mem_Icc.mpr timeNonnegative⟩
  have generatedConvergence :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (occurrence.weakLimit.pairingConvergence test)).tendsto_at initialTime
  have zeroConvergence : Tendsto
      (fun sequenceIndex ↦
        canonicalAffineCorrectionBoundedPairing
          timeEnd timeNonnegative a b
          (occurrence.weakLimit.subsequence sequenceIndex) test initialTime)
      atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun sequenceIndex ↦ by
      exact (canonicalAffineCorrectionBoundedPairing_zeroTime
        timeEnd timeNonnegative a b
        (occurrence.weakLimit.subsequence sequenceIndex) test).symm
  exact tendsto_nhds_unique generatedConvergence zeroConvergence

theorem canonicalAffineCorrectionPhysicalMassRead_zeroTime
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ) :
    canonicalAffineCorrectionPhysicalMassRead occurrence test
        ⟨0, left_mem_Icc.mpr timeNonnegative⟩ = 0 := by
  rw [canonicalAffineCorrectionPhysicalMassRead_eq_limit]
  exact canonicalAffineCorrectionWeakLimit_limit_zeroTime occurrence test

theorem canonicalAffineCorrectionMassRepresentative_zeroTime
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b) :
    occurrence.correctionMassRepresentative
        ⟨0, left_mem_Icc.mpr timeNonnegative⟩ = 0 := by
  apply (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b).eq_of_inner_left ℝ
  intro test
  rw [occurrence.correctionMassRepresentative_generatorPairing,
    canonicalAffineCorrectionWeakLimit_limit_zeroTime]
  simp

theorem canonicalAffineCorrectionPhysicalField_zeroTime
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b) :
    occurrence.correctionPhysicalActualization.physicalField
        ⟨0, left_mem_Icc.mpr timeNonnegative⟩ = 0 := by
  obtain ⟨C, _CNonnegative, operatorBound⟩ :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      0 timeEnd a b
  let initialTime : Icc 0 timeEnd :=
    ⟨0, left_mem_Icc.mpr timeNonnegative⟩
  let massEquiv := fixedP506L0CauchySafeMatterL2MassEquiv
    0 a b boxOrder C (operatorBound 0 (left_mem_Icc.mpr timeNonnegative))
  have zeroEqMass :
      (0 : CauchySafeMatterSpatialL2 a b) =
        massEquiv
          (occurrence.correctionPhysicalActualization.physicalField
            initialTime) := by
    exact fixedP506L0CauchySafeMatterL2MassEquiv_unique
      0 a b boxOrder C
      (operatorBound 0 (left_mem_Icc.mpr timeNonnegative))
      (occurrence.correctionPhysicalActualization.physicalField initialTime)
      0 (by
        intro test
        rw [fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
        calc
          inner ℝ 0 test = 0 := by simp
          _ = inner ℝ
              (occurrence.correctionMassRepresentative initialTime) test := by
            rw [canonicalAffineCorrectionMassRepresentative_zeroTime]
            simp
          _ = _ := by
            simpa [initialTime] using
              (occurrence.correctionPhysicalActualization.massLaw
                initialTime test).symm)
  have recovered := congrArg massEquiv.symm zeroEqMass
  simpa [massEquiv] using recovered.symm

theorem canonicalAffinePhysicalField_zeroTime
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b) :
    occurrence.affinePhysicalField
        ⟨0, left_mem_Icc.mpr timeNonnegative⟩ =
      fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b := by
  rw [FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence.affinePhysicalField,
    canonicalAffineCorrectionPhysicalField_zeroTime boxOrder]
  simp

theorem canonicalAffineCorrectionPhysicalEndpointActionLaw
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
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
            candidateTime)
      atTop
      (nhds (canonicalAffineCorrectionPhysicalMassRead occurrence test
          ⟨time, timeMem⟩ -
        canonicalAffineCorrectionPhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩)) := by
  simpa only [canonicalAffineCorrectionPhysicalMassRead_eq_limit] using
    occurrence.weakLimit.endpointRateConvergence test time timeMem

theorem canonicalAffineCorrectionWeightedPhysicalActionLaw
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Tendsto
      (fun sequenceIndex ↦ ∫ candidateTime in 0..timeEnd,
        weight candidateTime *
          (canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) test).rate
              candidateTime)
      atTop
      (nhds (weight timeEnd *
          canonicalAffineCorrectionPhysicalMassRead occurrence test
            ⟨timeEnd, right_mem_Icc.mpr timeNonnegative⟩ -
        weight 0 * canonicalAffineCorrectionPhysicalMassRead occurrence test
          ⟨0, left_mem_Icc.mpr timeNonnegative⟩ -
        ∫ candidateTime in 0..timeEnd,
          deriv weight candidateTime *
            canonicalAffineCorrectionPhysicalMassRead occurrence test
              (projIcc 0 timeEnd timeNonnegative candidateTime))) := by
  simpa only [canonicalAffineCorrectionPhysicalMassRead_eq_limit] using
    occurrence.weakLimit.weightedRateConvergence test weight weightRegular

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalActionTransport
