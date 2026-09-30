import H0mework.Physics.DiracEvolution.SafeAllL2MassRead

/-!
# Fixed P506 Cauchy-safe Green-rate L² read

Green transport turns the finite mother-action weak rate into one continuous
linear functional on the spatial `L²` trial field.  Its canonical fiberwise
Riesz representative gives the ambient read consumed by generated weak-limit
actualization.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read

open Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterAllL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

variable {modeCount : ℕ}

def fixedP506L0CauchySafeMatterGreenRateRieszField
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm
    (fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates
      (time, space))

theorem fixedP506L0CauchySafeMatterGreenRateRieszField_continuous
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ) :
    Continuous
      (fixedP506L0CauchySafeMatterGreenRateRieszField testCoordinates time) := by
  have fiberReadContinuous : Continuous (fun space :
      DiracMatterSpatialCoordinates ↦
    fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates
      (time, space)) := by
    rw [continuous_clm_apply]
    intro trialCoordinates
    exact (fixedP506L0CauchySafeMatterGreenRateFiberRead_apply_continuous
      testCoordinates testRegular trialCoordinates).comp
        (continuous_const.prodMk continuous_id)
  exact (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm.continuous.comp
    fiberReadContinuous

private theorem fixedP506L0CauchySafeMatterGreenRateRieszField_memLp
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    MemLp
      (fixedP506L0CauchySafeMatterGreenRateRieszField testCoordinates time)
      2 (volume.restrict (Icc a b)) := by
  have fieldContinuous :=
    fixedP506L0CauchySafeMatterGreenRateRieszField_continuous
      testCoordinates testRegular time
  obtain ⟨C, bound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    fieldContinuous.continuousOn
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  apply MemLp.of_bound fieldContinuous.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact bound space spaceMem

def fixedP506L0CauchySafeMatterGreenRateRieszL2
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b :=
  (fixedP506L0CauchySafeMatterGreenRateRieszField_memLp
    testCoordinates testRegular time a b).toLp
      (fixedP506L0CauchySafeMatterGreenRateRieszField testCoordinates time)

def fixedP506L0CauchySafeMatterGreenRateL2Read
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ :=
  innerSL ℝ
    (fixedP506L0CauchySafeMatterGreenRateRieszL2
      testCoordinates testRegular time a b)

theorem fixedP506L0CauchySafeMatterGreenRateL2Read_eq_integral
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (trial : CauchySafeMatterSpatialL2 a b) :
    fixedP506L0CauchySafeMatterGreenRateL2Read testCoordinates testRegular
        time a b trial =
      ∫ space,
        fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates
          (time, space) (trial space)
        ∂volume.restrict (Icc a b) := by
  change inner ℝ
      (fixedP506L0CauchySafeMatterGreenRateRieszL2
        testCoordinates testRegular time a b) trial = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (fixedP506L0CauchySafeMatterGreenRateRieszField_memLp
      testCoordinates testRegular time a b).coeFn_toLp] with space rieszEq
  change inner ℝ
      ((fixedP506L0CauchySafeMatterGreenRateRieszL2
        testCoordinates testRegular time a b) space)
      (trial space) = _
  unfold fixedP506L0CauchySafeMatterGreenRateRieszL2
  rw [rieszEq]
  exact InnerProductSpace.toDual_symm_apply

/-- The ambient Green-rate read on the finite Galerkin trial is exactly the
generated weak-pairing rate. -/
theorem fixedP506L0CauchySafeMatterGreenRateL2Read_fixedTrial
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (trial : ℝ → DiracMatterGalerkinCoefficient modeCount)
    (test : DiracMatterGalerkinCoefficient modeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    fixedP506L0CauchySafeMatterGreenRateL2Read testCoordinates testRegular
        time a b
        (fixedMatterTrialL2 basis (fun mode ↦ (basisRegular mode).continuous)
          basisCompact (trial time) a b) =
      galerkinWeakTestPairingRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
          basisCompact)
        (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact)
        trial test time := by
  rw [fixedP506L0CauchySafeMatterGreenRateL2Read_eq_integral]
  rw [fixedP506L0CauchySafeMatterGalerkinWeakTestPairingRate_eq_greenRead
    basis basisRegular basisCompact trial test testCoordinates
    testRepresentation time a b boxOrder basisZeroOutside]
  apply integral_congr_ae
  filter_upwards [fixedMatterTrialL2_coe_ae basis
    (fun mode ↦ (basisRegular mode).continuous) basisCompact (trial time) a b]
      with space trialEq
  rw [trialEq]
  rfl

def fixedP506L0CauchySafeMatterGreenRateMassTest
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C) :
    CauchySafeMatterSpatialL2 a b :=
  (InnerProductSpace.toDual ℝ (CauchySafeMatterSpatialL2 a b)).symm
    ((fixedP506L0CauchySafeMatterGreenRateL2Read testCoordinates testRegular
      time a b).comp
        (fixedP506L0CauchySafeMatterL2MassEquiv
          time a b boxOrder C operatorBound).symm.toContinuousLinearMap)

private theorem continuousLinearEquiv_massRiesz_pairing
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (massEquiv : H ≃L[ℝ] H)
    (read : H →L[ℝ] ℝ)
    (field : H) :
    inner ℝ (massEquiv field)
        ((InnerProductSpace.toDual ℝ H).symm
          (read.comp massEquiv.symm.toContinuousLinearMap)) =
      read field := by
  calc
    inner ℝ (massEquiv field)
        ((InnerProductSpace.toDual ℝ H).symm
          (read.comp massEquiv.symm.toContinuousLinearMap)) =
      inner ℝ
        ((InnerProductSpace.toDual ℝ H).symm
          (read.comp massEquiv.symm.toContinuousLinearMap))
        (massEquiv field) := real_inner_comm _ _
    _ = (read.comp massEquiv.symm.toContinuousLinearMap)
        (massEquiv field) := InnerProductSpace.toDual_symm_apply
    _ = read field := by simp

theorem fixedP506L0CauchySafeMatterL2MassForm_greenRateMassTest
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b) :
    fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound field
        (fixedP506L0CauchySafeMatterGreenRateMassTest testCoordinates
          testRegular time a b boxOrder C operatorBound) =
      fixedP506L0CauchySafeMatterGreenRateL2Read testCoordinates testRegular
        time a b field := by
  rw [← fixedP506L0CauchySafeMatterL2MassEquiv_pairing
    time a b boxOrder C operatorBound]
  exact continuousLinearEquiv_massRiesz_pairing
    (fixedP506L0CauchySafeMatterL2MassEquiv
      time a b boxOrder C operatorBound)
    (fixedP506L0CauchySafeMatterGreenRateL2Read
      testCoordinates testRegular time a b)
    field

theorem fixedP506L0CauchySafeAllL2MassRead_eq_massForm
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (approximationIndex : ℕ)
    (time : Icc timeStart timeEnd)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ C) :
    fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
        boxOrder energyCap energyCapNonnegative approximation
        approximationIndex time =
      fixedP506L0CauchySafeMatterL2MassForm time.1 a b C operatorBound
        (fixedMatterTrialL2 (approximation approximationIndex).basis
          (fun mode ↦
            ((approximation approximationIndex).basisRegular mode).continuous)
          (approximation approximationIndex).basisCompact
          ((approximation approximationIndex).coefficient time.1) a b) := by
  symm
  apply fixedP506L0CauchySafeAllL2MassRead_eq_of_actionLaw
    timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
    approximation approximationIndex time
  intro test
  rw [fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
  apply integral_congr_ae
  filter_upwards [
    fixedMatterTrialL2_coe_ae (approximation approximationIndex).basis
      (fun mode ↦
        ((approximation approximationIndex).basisRegular mode).continuous)
      (approximation approximationIndex).basisCompact
      ((approximation approximationIndex).coefficient time.1) a b,
    (cauchySafeMatterSmoothCompactTest_memLp a b test).coeFn_toLp]
      with space trialEq testEq
  have testEq' :
      ((cauchySafeMatterSmoothCompactTestToL2 a b test) space) =
        (test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier) space := by
    change (((cauchySafeMatterSmoothCompactTest_memLp a b test).toLp
      (test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)) space) = _
    exact testEq
  rw [trialEq, testEq']

/-- The canonical spatial `L²` trial carried by one finite generated weak
approximation at a fixed time. -/
def fixedP506L0CauchySafeMatterApproximationTrialL2
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    (approximation : FixedP506L0CauchySafeWeakGalerkinApproximation
      timeStart timeEnd a b energyCap)
    (time : ℝ) :
    CauchySafeMatterSpatialL2 a b :=
  fixedMatterTrialL2 approximation.basis
    (fun mode ↦ (approximation.basisRegular mode).continuous)
    approximation.basisCompact (approximation.coefficient time) a b

/-- Evaluation of the canonical Green-rate functional on one spatial `L²`
field. -/
def fixedP506L0CauchySafeMatterGreenRateL2Value
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) : ℝ :=
  fixedP506L0CauchySafeMatterGreenRateL2Read testCoordinates testRegular
    time a b field

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
