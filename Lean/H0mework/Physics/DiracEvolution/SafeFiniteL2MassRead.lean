import H0mework.Physics.DiracEvolution.SafeSpatialL2TestCarrier
import H0mework.Physics.DiracEvolution.FiberMassRiesz
import H0mework.Physics.DiracEvolution.SafeWeakEnergyEstimate

/-!
# Fixed P506 Cauchy-safe finite L² mass reads

The action-owned fiber mass pairing acts on the physical spatial `L²`
carrier through its canonical Riesz representative.  Every finite Galerkin
mass read is thereby recognized as a linear read on the dense smooth test
carrier.  The existing mode-uniform energy estimate supplies one functional
bound shared by all finite mode counts and canonical times.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead

open MeasureTheory Metric Set
open DiracCliffordRepresentation
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open StageNineMatterActionTemporalFirstGermResponse
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

variable {modeCount : ℕ}

private theorem fixedMassMatrix_continuous :
    Continuous fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterWeakMassMatrix input.1 input.2 := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact fixedP506L0CauchySafeMatterWeakMassMatrix_continuous row column

theorem exists_fixedMassPairingOperatorBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space ∈ Icc a b,
          ‖matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C := by
  let pointCarrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  let unitCarrier : Set
      ((ℝ × DiracMatterSpatialCoordinates) × MatterCoordinateCarrier) :=
    pointCarrier ×ˢ closedBall 0 1
  let rate := fun
      (input : (ℝ × DiracMatterSpatialCoordinates) × MatterCoordinateCarrier)
      (first : MatterCoordinateCarrier) ↦
    matterFiberMassPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix input.1.1 input.1.2)
      first input.2
  have pointCarrierCompact : IsCompact pointCarrier :=
    isCompact_Icc.prod isCompact_Icc
  have unitCarrierCompact : IsCompact unitCarrier :=
    pointCarrierCompact.prod (isCompact_closedBall 0 1)
  have unitCarrierNonempty : unitCarrier.Nonempty :=
    ⟨((timeStart, a), 0),
      ⟨⟨left_mem_Icc.mpr timeOrder, left_mem_Icc.mpr boxOrder⟩, by simp⟩⟩
  have rateContinuous : Continuous fun input :
      (((ℝ × DiracMatterSpatialCoordinates) × MatterCoordinateCarrier) ×
        MatterCoordinateCarrier) ↦
      rate input.1 input.2 := by
    have pointContinuous : Continuous fun input :
        (((ℝ × DiracMatterSpatialCoordinates) × MatterCoordinateCarrier) ×
          MatterCoordinateCarrier) ↦ input.1.1 :=
      continuous_fst.comp continuous_fst
    have matrixContinuous := fixedMassMatrix_continuous.comp pointContinuous
    have firstContinuous : Continuous fun input :
        (((ℝ × DiracMatterSpatialCoordinates) × MatterCoordinateCarrier) ×
          MatterCoordinateCarrier) ↦ input.2 :=
      continuous_snd
    have secondContinuous : Continuous fun input :
        (((ℝ × DiracMatterSpatialCoordinates) × MatterCoordinateCarrier) ×
          MatterCoordinateCarrier) ↦ input.1.2 :=
      continuous_snd.comp continuous_fst
    simpa only [rate, Function.comp_apply] using
      ((matterFiberMassPairing.continuous.comp matrixContinuous).clm_apply
        firstContinuous).clm_apply secondContinuous
  have rate_smul : ∀ point (parameter : ℝ) first,
      rate point (parameter • first) = parameter * rate point first := by
    intro point parameter first
    change
      matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix point.1.1 point.1.2)
          (parameter • first) point.2 = _
    rw [map_smul]
    rfl
  obtain ⟨C, CNonnegative, unitBound⟩ :=
    exists_modeUniformLinearRateBound unitCarrier unitCarrierCompact
      unitCarrierNonempty rate rateContinuous rate_smul
  refine ⟨C, CNonnegative, ?_⟩
  intro time timeMem space spaceMem
  apply ContinuousLinearMap.opNorm_le_bound _ CNonnegative
  intro first
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg CNonnegative (norm_nonneg _))
  intro second
  by_cases secondZero : second = 0
  · simpa [secondZero] using
      map_zero (matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space) first)
  · have normPositive : 0 < ‖second‖ := norm_pos_iff.mpr secondZero
    let unitSecond : MatterCoordinateCarrier := ‖second‖⁻¹ • second
    have unitSecondNorm : ‖unitSecond‖ = 1 := by
      simp [unitSecond, norm_smul, inv_mul_cancel₀ normPositive.ne']
    have unitSecondMem : ((time, space), unitSecond) ∈ unitCarrier := by
      refine ⟨⟨timeMem, spaceMem⟩, ?_⟩
      simp [mem_closedBall, dist_eq_norm, unitSecondNorm]
    have upperBound := unitBound ((time, space), unitSecond)
      unitSecondMem first
    have reconstruct : ‖second‖ • unitSecond = second := by
      rw [show ‖second‖ • unitSecond =
          (‖second‖ * ‖second‖⁻¹) • second by
        simp [unitSecond, smul_smul]]
      simp [normPositive.ne']
    calc
      ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          first second‖ =
          ‖second‖ * ‖matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
            first unitSecond‖ := by
        nth_rewrite 1 [← reconstruct]
        rw [map_smul, norm_smul, Real.norm_of_nonneg normPositive.le]
      _ ≤ ‖second‖ * (C * ‖first‖) :=
        mul_le_mul_of_nonneg_left upperBound normPositive.le
      _ = (C * ‖first‖) * ‖second‖ := by ring

def fixedMatterTrialCoordinates
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  matterCoordinateEquiv
    (diracMatterSpatialGalerkinSynthesis basis coefficient space)

def fixedMatterMassRieszField
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  matterFiberMassRiesz
    (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
    (fixedMatterTrialCoordinates basis coefficient space)

private theorem fixedMatterTrialCoordinates_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    Continuous (fixedMatterTrialCoordinates basis coefficient) :=
  diracMatterSpatialGalerkinSynthesis_coordinates_continuous basis
    basisContinuous coefficient

private theorem fixedMatterTrialCoordinates_hasCompactSupport
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    HasCompactSupport (fixedMatterTrialCoordinates basis coefficient) :=
  diracMatterSpatialGalerkinSynthesis_coordinates_hasCompactSupport basis
    basisCompact coefficient

private theorem fixedMatterMassRieszField_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ) :
    Continuous (fixedMatterMassRieszField basis coefficient time) := by
  have matrixContinuous : Continuous fun space : DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterWeakMassMatrix time space := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    exact diracMatterWeakMassMatrix_spatial_continuous
      fixedP506L0CauchySafeMatterWeakMassMatrix
      fixedP506L0CauchySafeMatterWeakMassMatrix_continuous time row column
  have pairingContinuous : Continuous fun space ↦
      matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (fixedMatterTrialCoordinates basis coefficient space) :=
    (matterFiberMassPairing.continuous.comp matrixContinuous).clm_apply
      (fixedMatterTrialCoordinates_continuous basis basisContinuous coefficient)
  change Continuous fun space ↦
    (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm
      (matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (fixedMatterTrialCoordinates basis coefficient space))
  exact (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm.continuous.comp
    pairingContinuous

private theorem fixedMatterTrialCoordinates_memLp
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (a b : DiracMatterSpatialCoordinates) :
    MemLp (fixedMatterTrialCoordinates basis coefficient) 2
      (volume.restrict (Icc a b)) :=
  (fixedMatterTrialCoordinates_continuous basis basisContinuous coefficient
    ).memLp_of_hasCompactSupport
      (fixedMatterTrialCoordinates_hasCompactSupport basis basisCompact coefficient)

private theorem fixedMatterMassRieszField_memLp
    (C : ℝ)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C) :
    MemLp (fixedMatterMassRieszField basis coefficient time) 2
      (volume.restrict (Icc a b)) := by
  apply MemLp.of_le_mul
    (fixedMatterTrialCoordinates_memLp basis basisContinuous basisCompact
      coefficient a b)
    (fixedMatterMassRieszField_continuous basis basisContinuous coefficient time
      ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact (norm_matterFiberMassRiesz_le
      (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
      (fixedMatterTrialCoordinates basis coefficient space)).trans
    (mul_le_mul_of_nonneg_right (operatorBound space spaceMem)
      (norm_nonneg _))

def fixedMatterTrialL2
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b :=
  (fixedMatterTrialCoordinates_memLp basis basisContinuous basisCompact
    coefficient a b).toLp (fixedMatterTrialCoordinates basis coefficient)

theorem fixedMatterTrialL2_add
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (a b : DiracMatterSpatialCoordinates) :
    fixedMatterTrialL2 basis basisContinuous basisCompact (first + second) a b =
      fixedMatterTrialL2 basis basisContinuous basisCompact first a b +
        fixedMatterTrialL2 basis basisContinuous basisCompact second a b := by
  have coordinateAdd :
      fixedMatterTrialCoordinates basis (first + second) =
        fixedMatterTrialCoordinates basis first +
          fixedMatterTrialCoordinates basis second := by
    funext space
    unfold fixedMatterTrialCoordinates
    rw [diracMatterSpatialGalerkinSynthesis_add, Pi.add_apply, map_add]
    rfl
  unfold fixedMatterTrialL2
  let firstMem := fixedMatterTrialCoordinates_memLp basis basisContinuous
    basisCompact first a b
  let secondMem := fixedMatterTrialCoordinates_memLp basis basisContinuous
    basisCompact second a b
  let sumMem := fixedMatterTrialCoordinates_memLp basis basisContinuous
    basisCompact (first + second) a b
  calc
    sumMem.toLp (fixedMatterTrialCoordinates basis (first + second)) =
        (firstMem.add secondMem).toLp
          (fixedMatterTrialCoordinates basis first +
            fixedMatterTrialCoordinates basis second) :=
      MemLp.toLp_congr sumMem (firstMem.add secondMem)
        (Filter.Eventually.of_forall fun space ↦ congrFun coordinateAdd space)
    _ = _ := MemLp.toLp_add firstMem secondMem

theorem fixedMatterTrialL2_real_smul
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (a b : DiracMatterSpatialCoordinates) :
    fixedMatterTrialL2 basis basisContinuous basisCompact
        (parameter • coefficient) a b =
      parameter •
        fixedMatterTrialL2 basis basisContinuous basisCompact coefficient a b := by
  have coordinateSmul :
      fixedMatterTrialCoordinates basis (parameter • coefficient) =
        parameter • fixedMatterTrialCoordinates basis coefficient := by
    funext space
    unfold fixedMatterTrialCoordinates
    rw [diracMatterSpatialGalerkinSynthesis_real_smul, Pi.smul_apply,
      matterCoordinateEquiv_real_smul]
    rfl
  unfold fixedMatterTrialL2
  let coefficientMem := fixedMatterTrialCoordinates_memLp basis basisContinuous
    basisCompact coefficient a b
  let scaledMem := fixedMatterTrialCoordinates_memLp basis basisContinuous
    basisCompact (parameter • coefficient) a b
  calc
    scaledMem.toLp
        (fixedMatterTrialCoordinates basis (parameter • coefficient)) =
      (coefficientMem.const_smul parameter).toLp
        (parameter • fixedMatterTrialCoordinates basis coefficient) :=
      MemLp.toLp_congr scaledMem (coefficientMem.const_smul parameter)
        (Filter.Eventually.of_forall fun space ↦ congrFun coordinateSmul space)
    _ = _ := MemLp.toLp_const_smul parameter coefficientMem

theorem fixedMatterTrialL2_coe_ae
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (a b : DiracMatterSpatialCoordinates) :
    ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedMatterTrialL2 basis basisContinuous basisCompact coefficient a b
          space =
        fixedMatterTrialCoordinates basis coefficient space := by
  exact (fixedMatterTrialCoordinates_memLp basis basisContinuous basisCompact
    coefficient a b).coeFn_toLp

def fixedMatterMassRieszL2
    (C : ℝ)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C) :
    CauchySafeMatterSpatialL2 a b :=
  (fixedMatterMassRieszField_memLp C basis basisContinuous basisCompact
    coefficient time a b operatorBound).toLp
      (fixedMatterMassRieszField basis coefficient time)

def fixedMatterFiniteMassRead
    (C : ℝ)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C) :
    CauchySafeMatterSmoothCompactTest →ₗ[ℝ] ℝ :=
  (innerSL ℝ
      (fixedMatterMassRieszL2 C basis basisContinuous basisCompact coefficient
        time a b operatorBound)).toLinearMap.comp
    (cauchySafeMatterSmoothCompactTestToL2 a b)

/-- The finite `L²` read is exactly the mother-action fiber mass pairing on
the fixed spatial box. -/
theorem fixedMatterFiniteMassRead_eq_integral
    (C : ℝ)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (test : CauchySafeMatterSmoothCompactTest) :
    fixedMatterFiniteMassRead C basis basisContinuous basisCompact coefficient
        time a b operatorBound test =
      ∫ space in Icc a b,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (fixedMatterTrialCoordinates basis coefficient space)
          ((test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)
            space) := by
  change inner ℝ
      (fixedMatterMassRieszL2 C basis basisContinuous basisCompact coefficient
        time a b operatorBound)
      (cauchySafeMatterSmoothCompactTestToL2 a b test) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (fixedMatterMassRieszField_memLp C basis basisContinuous basisCompact
      coefficient time a b operatorBound).coeFn_toLp,
    (cauchySafeMatterSmoothCompactTest_memLp a b test).coeFn_toLp]
      with space massEq testEq
  change inner ℝ
      (((fixedMatterMassRieszField_memLp C basis basisContinuous basisCompact
          coefficient time a b operatorBound).toLp
        (fixedMatterMassRieszField basis coefficient time)) space)
      (((cauchySafeMatterSmoothCompactTest_memLp a b test).toLp
        (test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier))
        space) = _
  rw [massEq, testEq]
  exact matterFiberMassRiesz_pairing _ _ _

private theorem fixedWeakMassDensity_eq_zero_of_not_mem_box
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        basis first second space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    constructor
    · intro direction
      exact (spaceInterior direction).1.le
    · intro direction
      exact (spaceInterior direction).2.le
  have firstZero :
      diracMatterSpatialGalerkinSynthesis basis first space = 0 := by
    apply matterCoordinateEquiv.injective
    simp [diracMatterSpatialGalerkinSynthesis_coordinates,
      basisZeroOutside _ space outsideInterior]
  unfold diracMatterWeakMassDensity
  rw [firstZero]
  simp [diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing, dotProduct]

theorem fixedMatterFiniteMassRead_eq_galerkinWeakTestPairing
    (C : ℝ)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (coefficient : ℝ → DiracMatterGalerkinCoefficient modeCount)
    (testCoefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (test : CauchySafeMatterSmoothCompactTest)
    (testRepresentation : ∀ space,
      fixedMatterTrialCoordinates basis testCoefficient space =
        (test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)
          space) :
    fixedMatterFiniteMassRead C basis basisContinuous basisCompact
        (coefficient time) time a b operatorBound test =
      galerkinWeakTestPairing
        (fixedP506L0CauchySafeMatterWeakMassForm basis basisContinuous
          basisCompact)
        coefficient testCoefficient time := by
  let density : DiracMatterSpatialCoordinates → ℝ := fun space ↦
    diracMatterWeakMassDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      basis (coefficient time) testCoefficient space
  have densitySetIntegral :
      (∫ space in Icc a b, density space) = ∫ space, density space :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun space spaceOutside ↦
        fixedWeakMassDensity_eq_zero_of_not_mem_box basis
          (coefficient time) testCoefficient time a b basisZeroOutside
          space spaceOutside)
  rw [fixedMatterFiniteMassRead_eq_integral]
  change _ = ∫ space, density space
  rw [← densitySetIntegral]
  apply setIntegral_congr_fun measurableSet_Icc
  intro space _
  change matterFiberMassPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
      (fixedMatterTrialCoordinates basis (coefficient time) space)
      ((test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)
        space) = density space
  rw [← testRepresentation space]
  rw [matterFiberMassPairing_apply]
  change diracExteriorMatterEnergyPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
      (matterCoordinateEquiv.symm (matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis (coefficient time) space)))
      (matterCoordinateEquiv.symm (matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis testCoefficient space))) =
    diracExteriorMatterEnergyPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
      (diracMatterSpatialGalerkinSynthesis basis (coefficient time) space)
      (diracMatterSpatialGalerkinSynthesis basis testCoefficient space)
  rw [matterCoordinateEquiv.symm_apply_apply,
    matterCoordinateEquiv.symm_apply_apply]

theorem fixedMatterFiniteMassRead_bound
    (C : ℝ)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (test : CauchySafeMatterSmoothCompactTest) :
    ‖fixedMatterFiniteMassRead C basis basisContinuous basisCompact coefficient
        time a b operatorBound test‖ ≤
      C * ‖fixedMatterTrialL2 basis basisContinuous basisCompact coefficient
        a b‖ * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖ := by
  calc
    _ ≤ ‖fixedMatterMassRieszL2 C basis basisContinuous basisCompact
          coefficient time a b operatorBound‖ *
        ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖ :=
      norm_inner_le_norm _ _
    _ ≤ (C * ‖fixedMatterTrialL2 basis basisContinuous basisCompact coefficient
          a b‖) * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖ := by
      gcongr
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [
        (fixedMatterMassRieszField_memLp C basis basisContinuous basisCompact
          coefficient time a b operatorBound).coeFn_toLp,
        (fixedMatterTrialCoordinates_memLp basis basisContinuous basisCompact
          coefficient a b).coeFn_toLp,
        ae_restrict_mem measurableSet_Icc] with space massEq trialEq spaceMem
      unfold fixedMatterMassRieszL2 fixedMatterTrialL2
      rw [massEq, trialEq]
      exact (norm_matterFiberMassRiesz_le
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (fixedMatterTrialCoordinates basis coefficient space)).trans
        (mul_le_mul_of_nonneg_right (operatorBound space spaceMem)
          (norm_nonneg _))
    _ = _ := by ring

theorem fixedMatterTrialL2_norm_sq
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (a b : DiracMatterSpatialCoordinates) :
    ‖fixedMatterTrialL2 basis basisContinuous basisCompact coefficient a b‖ ^ 2 =
      ∫ space in Icc a b,
        ‖fixedMatterTrialCoordinates basis coefficient space‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (fixedMatterTrialCoordinates_memLp basis basisContinuous basisCompact
      coefficient a b).coeFn_toLp] with space trialEq
  change inner ℝ
      (((fixedMatterTrialCoordinates_memLp basis basisContinuous basisCompact
        coefficient a b).toLp
          (fixedMatterTrialCoordinates basis coefficient)) space)
      (((fixedMatterTrialCoordinates_memLp basis basisContinuous basisCompact
        coefficient a b).toLp
          (fixedMatterTrialCoordinates basis coefficient)) space) = _
  rw [trialEq, real_inner_self_eq_norm_sq]

theorem fixedMatterFiniteMassRead_bound_of_trial_square_bound
    (C D : ℝ)
    (CNonnegative : 0 ≤ C)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (trialSquareBound :
      (∫ space in Icc a b,
        ‖fixedMatterTrialCoordinates basis coefficient space‖ ^ 2) ≤ D)
    (test : CauchySafeMatterSmoothCompactTest) :
    ‖fixedMatterFiniteMassRead C basis basisContinuous basisCompact coefficient
        time a b operatorBound test‖ ≤
      C * (D + 1) *
        ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖ := by
  have trialNormLeSquareAddOne :
      ‖fixedMatterTrialL2 basis basisContinuous basisCompact coefficient a b‖ ≤
        ‖fixedMatterTrialL2 basis basisContinuous basisCompact coefficient a b‖ ^
          2 + 1 := by
    nlinarith [sq_nonneg
      (‖fixedMatterTrialL2 basis basisContinuous basisCompact coefficient a b‖ -
        1 / 2)]
  have trialNormLe :
      ‖fixedMatterTrialL2 basis basisContinuous basisCompact coefficient a b‖ ≤
        D + 1 := by
    calc
      _ ≤ ‖fixedMatterTrialL2 basis basisContinuous basisCompact coefficient
          a b‖ ^ 2 + 1 := trialNormLeSquareAddOne
      _ = (∫ space in Icc a b,
          ‖fixedMatterTrialCoordinates basis coefficient space‖ ^ 2) + 1 := by
        rw [fixedMatterTrialL2_norm_sq]
      _ ≤ D + 1 := by
        simpa [add_comm] using add_le_add_right trialSquareBound 1
  exact (fixedMatterFiniteMassRead_bound C basis basisContinuous basisCompact
      coefficient time a b operatorBound test).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left trialNormLe CNonnegative)
      (norm_nonneg _))

theorem exists_fixedModeUniformFiniteMassReadBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ operatorBound :
        (∀ time ∈ Icc timeStart timeEnd,
          ∀ space ∈ Icc a b,
            ‖matterFiberMassPairing
              (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C),
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ (candidateModeCount : ℕ)
          (basis : Fin candidateModeCount →
            DiracMatterSpatialCoordinates → ℝ)
          (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
          (basisCompact : ∀ mode, HasCompactSupport (basis mode))
          (_basisZeroOutside :
            DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
          (coefficient velocity : ℝ →
            DiracMatterGalerkinCoefficient candidateModeCount),
        (∀ time ∈ Icc timeStart timeEnd,
          HasDerivWithinAt coefficient (velocity time)
            (Icc timeStart timeEnd) time) →
        (∀ time ∈ Icc timeStart timeEnd,
          fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact time
              (velocity time) (coefficient time) +
            fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
              basisCompact time (coefficient time) (coefficient time) = 0) →
        ‖galerkinWeakEnergy
            (fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact)
            coefficient timeStart‖ ≤ energyCap →
        ∀ time (timeMem : time ∈ Icc timeStart timeEnd)
          (test : CauchySafeMatterSmoothCompactTest),
          ‖fixedMatterFiniteMassRead C basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact
              (coefficient time) time a b
              (operatorBound time timeMem) test‖ ≤
            B * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖ := by
  obtain ⟨C, CNonnegative, operatorBound⟩ :=
    exists_fixedMassPairingOperatorBoundOnBox timeStart timeEnd a b
      timeOrder boxOrder
  obtain ⟨κ, K, κPositive, KNonnegative, spatialL2Bound⟩ :=
    exists_fixedModeUniformGalerkinSpatialL2BoundOnBox
      timeStart timeEnd a b timeOrder boxOrder
  let D := κ⁻¹ *
    (energyCap * Real.exp (K * (timeEnd - timeStart)))
  let B := C * (D + 1)
  have DNonnegative : 0 ≤ D :=
    mul_nonneg (inv_nonneg.mpr κPositive.le)
      (mul_nonneg energyCapNonnegative (Real.exp_pos _).le)
  have BNonnegative : 0 ≤ B :=
    mul_nonneg CNonnegative (add_nonneg DNonnegative zero_le_one)
  refine ⟨C, CNonnegative, operatorBound, B, BNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient velocity evolution weakEquation initialEnergyBound
    time timeMem test
  have rawSpatialBound := spatialL2Bound candidateModeCount basis basisRegular
    basisCompact basisZeroOutside coefficient velocity evolution weakEquation
    time timeMem
  have timeDifference :
      time - timeStart ≤ timeEnd - timeStart :=
    sub_le_sub_right timeMem.2 timeStart
  have exponentialBound :
      Real.exp (K * (time - timeStart)) ≤
        Real.exp (K * (timeEnd - timeStart)) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left timeDifference KNonnegative)
  have energyGrowthBound :
      ‖galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient timeStart‖ * Real.exp (K * (time - timeStart)) ≤
        energyCap * Real.exp (K * (timeEnd - timeStart)) := by
    calc
      _ ≤ energyCap * Real.exp (K * (time - timeStart)) :=
        mul_le_mul_of_nonneg_right initialEnergyBound (Real.exp_pos _).le
      _ ≤ energyCap * Real.exp (K * (timeEnd - timeStart)) :=
        mul_le_mul_of_nonneg_left exponentialBound energyCapNonnegative
  have trialSquareBound :
      (∫ space in Icc a b,
        ‖fixedMatterTrialCoordinates basis (coefficient time) space‖ ^ 2) ≤
        D := by
    exact rawSpatialBound.trans
      (mul_le_mul_of_nonneg_left energyGrowthBound
        (inv_nonneg.mpr κPositive.le))
  simpa only [B] using
    fixedMatterFiniteMassRead_bound_of_trial_square_bound C D CNonnegative
      basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
      (coefficient time) time a b (operatorBound time timeMem)
      trialSquareBound test

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
