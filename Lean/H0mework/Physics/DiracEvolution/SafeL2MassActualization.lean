import H0mework.Physics.DiracEvolution.SafeFiniteL2MassRead
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.Holder

/-!
# Fixed P506 Cauchy-safe matter `L²` mass actualization

The action-owned positive fiber mass form generates a coercive bounded form on
the spatial `L²` carrier. Lax--Milgram then actualizes a mass-pairing Riesz
representative as one uniquely determined physical `L²` field. Bounds used by
the construction are hidden behind the public mass law and uniqueness receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization

open Filter MeasureTheory Set
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageEightSourceGeneratedMatter
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineHolonomicField
open scoped ComplexOrder ENNReal Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

def matterFiberMassRieszBilinear :
    DiracMatrix →L[ℝ]
      (MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier) :=
  (ContinuousLinearMap.compL ℝ MatterCoordinateCarrier
    (MatterCoordinateCarrier →L[ℝ] ℝ) MatterCoordinateCarrier
    (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm.toContinuousLinearMap
    ).comp matterFiberMassPairing

@[simp] theorem matterFiberMassRieszBilinear_apply
    (matrix : DiracMatrix)
    (first : MatterCoordinateCarrier) :
    matterFiberMassRieszBilinear matrix first =
      matterFiberMassRiesz matrix first :=
  rfl

abbrev CauchySafeMatterDiracMatrixCoordinates :=
  EuclideanSpace ℂ (DiracSpinorIndex × DiracSpinorIndex)

def diracMatrixOfCoordinates :
    CauchySafeMatterDiracMatrixCoordinates →L[ℝ] DiracMatrix where
  toFun coordinates row column := coordinates (row, column)
  map_add' first second := by
    ext row column
    rfl
  map_smul' parameter coordinates := by
    ext row column
    rfl
  cont := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    exact PiLp.continuous_apply 2
      (fun _ : DiracSpinorIndex × DiracSpinorIndex ↦ ℂ) (row, column)

def matterFiberMassRieszCoordinateBilinear :
    CauchySafeMatterDiracMatrixCoordinates →L[ℝ]
      (MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier) :=
  matterFiberMassRieszBilinear.comp diracMatrixOfCoordinates

def fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    CauchySafeMatterDiracMatrixCoordinates :=
  WithLp.toLp 2 fun coordinatePair ↦
    fixedP506L0CauchySafeMatterWeakMassMatrix time space
      coordinatePair.1 coordinatePair.2

@[simp] theorem diracMatrixOfCoordinates_massMatrixCoordinateField
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatrixOfCoordinates
        (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space) =
      fixedP506L0CauchySafeMatterWeakMassMatrix time space :=
  rfl

@[simp] theorem matterFiberMassRieszCoordinateBilinear_massMatrixCoordinateField
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (first : MatterCoordinateCarrier) :
    matterFiberMassRieszCoordinateBilinear
        (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space)
        first =
      matterFiberMassRiesz
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space) first :=
  rfl

theorem fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_continuous
    (time : ℝ) :
    Continuous
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time) := by
  apply (PiLp.continuous_toLp 2
    (fun _ : DiracSpinorIndex × DiracSpinorIndex ↦ ℂ)).comp
  apply continuous_pi
  intro coordinatePair
  exact diracMatterWeakMassMatrix_spatial_continuous
    fixedP506L0CauchySafeMatterWeakMassMatrix
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous time
      coordinatePair.1 coordinatePair.2

theorem fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_memLp_top
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C) :
    MemLp (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time) ∞
      (volume.restrict (Icc a b)) := by
  apply memLp_top_of_bound
    (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_continuous time
      ).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact operatorBound space spaceMem

def fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C) :
    Lp CauchySafeMatterDiracMatrixCoordinates ∞
      (volume.restrict (Icc a b)) :=
  (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_memLp_top
    time a b C operatorBound).toLp
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time)

def fixedP506L0CauchySafeMatterL2MassAction
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C) :
    CauchySafeMatterSpatialL2 a b →L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  (matterFiberMassRieszCoordinateBilinear.holderL
      (volume.restrict (Icc a b)) ∞ 2 2)
    (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
      time a b C operatorBound)

def fixedP506L0CauchySafeMatterL2MassForm
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C) :
    CauchySafeMatterSpatialL2 a b →L[ℝ]
      (CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ) :=
  (innerSL ℝ).comp
    (fixedP506L0CauchySafeMatterL2MassAction
      time a b C operatorBound)

theorem fixedP506L0CauchySafeMatterL2MassForm_eq_integral
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C)
    (first second : CauchySafeMatterSpatialL2 a b) :
    fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        first second =
      ∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (first space) (second space)
        ∂volume.restrict (Icc a b) := by
  change inner ℝ
      (fixedP506L0CauchySafeMatterL2MassAction
        time a b C operatorBound first) second = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
      (matterFiberMassRieszCoordinateBilinear.coeFn_holder (r := 2)
          (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
            time a b C operatorBound) first),
      MemLp.coeFn_toLp
        (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_memLp_top
          time a b C operatorBound)] with space actionEq matrixEq
  change inner ℝ
      ((matterFiberMassRieszCoordinateBilinear.holder 2
        (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
          time a b C operatorBound) first) space)
      (second space) = _
  have matrixRead :
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
        time a b C operatorBound) space =
        fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space := by
    change
      ((fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_memLp_top
        time a b C operatorBound).toLp
          (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time))
            space = _
    exact matrixEq
  rw [actionEq, matrixRead]
  change inner ℝ
      (matterFiberMassRiesz
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (first space))
      (second space) = _
  exact matterFiberMassRiesz_pairing _ _ _

/-- The physical `L²` mass form retains the Hermitian symmetry of the
source-owned fiber coefficient. -/
theorem fixedP506L0CauchySafeMatterL2MassForm_symm
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (first second : CauchySafeMatterSpatialL2 a b) :
    fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound first second =
      fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound second first := by
  calc
    fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound first second =
        ∫ space,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
            (first space) (second space)
          ∂volume.restrict (Icc a b) :=
      fixedP506L0CauchySafeMatterL2MassForm_eq_integral
        time a b C operatorBound first second
    _ = ∫ space,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
            (second space) (first space)
          ∂volume.restrict (Icc a b) := by
      apply integral_congr_ae
      filter_upwards with space
      rw [matterFiberMassPairing_apply, matterFiberMassPairing_apply]
      exact diracExteriorMatterEnergyPairing_symm _
        (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef
          time space).isHermitian _ _
    _ = fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound second first :=
      (fixedP506L0CauchySafeMatterL2MassForm_eq_integral
        time a b C operatorBound second first).symm

private theorem fixedWeakMassDensity_eq_zero_outside_box
    {modeCount : ℕ}
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        basis first second space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    exact ⟨fun direction ↦ (spaceInterior direction).1.le,
      fun direction ↦ (spaceInterior direction).2.le⟩
  have firstZero :
      diracMatterSpatialGalerkinSynthesis basis first space = 0 := by
    apply matterCoordinateEquiv.injective
    simp [diracMatterSpatialGalerkinSynthesis_coordinates,
      basisZeroOutside _ space outsideInterior]
  unfold diracMatterWeakMassDensity
  rw [firstZero]
  simp [diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing, dotProduct]

/-- Synthesizing two finite coefficients into the physical `L²` carrier
commutes exactly with the mother-action weak mass form whenever the basis is
supported in the spatial box interior. -/
theorem fixedP506L0CauchySafeMatterWeakMassForm_eq_l2MassForm_trial
    {modeCount : ℕ}
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    fixedP506L0CauchySafeMatterWeakMassForm
        basis basisContinuous basisCompact time first second =
      fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound
        (fixedMatterTrialL2 basis basisContinuous basisCompact first a b)
        (fixedMatterTrialL2 basis basisContinuous basisCompact second a b) := by
  let density : DiracMatterSpatialCoordinates → ℝ := fun space ↦
    diracMatterWeakMassDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      basis first second space
  have densitySetIntegral :
      (∫ space in Icc a b, density space) = ∫ space, density space :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun space outside ↦
        fixedWeakMassDensity_eq_zero_outside_box
          basis a b basisZeroOutside first second time space outside)
  rw [fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
  rw [fixedP506L0CauchySafeMatterWeakMassForm,
    diracMatterWeakMassForm_apply, diracMatterWeakMassFormValue]
  change (∫ space, density space) = _
  rw [← densitySetIntegral]
  apply integral_congr_ae
  filter_upwards [
    fixedMatterTrialL2_coe_ae basis basisContinuous basisCompact first a b,
    fixedMatterTrialL2_coe_ae basis basisContinuous basisCompact second a b]
      with space firstRead secondRead
  rw [firstRead, secondRead]
  change diracMatterWeakMassDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      basis first second space =
    matterFiberMassPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
      (fixedMatterTrialCoordinates basis first space)
      (fixedMatterTrialCoordinates basis second space)
  unfold diracMatterWeakMassDensity fixedMatterTrialCoordinates
  rw [matterFiberMassPairing_apply,
    matterCoordinateEquiv.symm_apply_apply,
    matterCoordinateEquiv.symm_apply_apply]

def fixedP506L0CauchySafeMatterFiberMassEnergy
    (point : ℝ × DiracMatterSpatialCoordinates)
    (field : MatterCoordinateCarrier) : ℝ :=
  matterFiberMassPairing
    (fixedP506L0CauchySafeMatterWeakMassMatrix point.1 point.2)
    field field

theorem fixedP506L0CauchySafeMatterFiberMassEnergy_joint_continuous :
    Continuous fun input :
      (ℝ × DiracMatterSpatialCoordinates) × MatterCoordinateCarrier ↦
      fixedP506L0CauchySafeMatterFiberMassEnergy input.1 input.2 := by
  unfold fixedP506L0CauchySafeMatterFiberMassEnergy
  have matrixContinuous : Continuous fun input :
      (ℝ × DiracMatterSpatialCoordinates) × MatterCoordinateCarrier ↦
      fixedP506L0CauchySafeMatterWeakMassMatrix input.1.1 input.1.2 := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    exact
      (fixedP506L0CauchySafeMatterWeakMassMatrix_continuous row column).comp
        continuous_fst
  exact ((matterFiberMassPairing.continuous.comp matrixContinuous).clm_apply
    continuous_snd).clm_apply continuous_snd

theorem fixedP506L0CauchySafeMatterFiberMassEnergy_positive
    (point : ℝ × DiracMatterSpatialCoordinates)
    (field : MatterCoordinateCarrier)
    (fieldNonzero : field ≠ 0) :
    0 < fixedP506L0CauchySafeMatterFiberMassEnergy point field := by
  unfold fixedP506L0CauchySafeMatterFiberMassEnergy
  rw [matterFiberMassPairing_apply, diracExteriorMatterEnergyPairing_self]
  apply diracExteriorMatterCoordinateEnergy_pos
    (fixedP506L0CauchySafeMatterWeakMassMatrix point.1 point.2)
    (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef point.1 point.2)
  intro preimageZero
  apply fieldNonzero
  rw [← matterCoordinateEquiv.apply_symm_apply field, preimageZero, map_zero]

theorem fixedP506L0CauchySafeMatterFiberMassEnergy_real_smul
    (point : ℝ × DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (field : MatterCoordinateCarrier) :
    fixedP506L0CauchySafeMatterFiberMassEnergy point (parameter • field) =
      parameter ^ 2 *
        fixedP506L0CauchySafeMatterFiberMassEnergy point field := by
  unfold fixedP506L0CauchySafeMatterFiberMassEnergy
  simp [map_smul, smul_eq_mul, pow_two, mul_assoc]

local instance fixedMatterCoordinateCarrierNontrivial :
    Nontrivial MatterCoordinateCarrier := by
  refine ⟨⟨0, matterCoordinateEquiv diracSpinTwoMatterProbe, ?_⟩⟩
  intro coordinatesZero
  apply diracSpinTwoMatterProbe_nonzero
  apply matterCoordinateEquiv.injective
  simpa using coordinatesZero.symm

theorem exists_fixedP506L0CauchySafeMatterFiberMassCoercivityOnBox
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ space ∈ Icc a b, ∀ field : MatterCoordinateCarrier,
        κ * ‖field‖ ^ 2 ≤
          fixedP506L0CauchySafeMatterFiberMassEnergy (time, space) field := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    {time} ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_singleton.prod isCompact_Icc
  have carrierNonempty : carrier.Nonempty := by
    refine ⟨(time, a), ?_⟩
    exact ⟨mem_singleton time, left_mem_Icc.mpr boxOrder⟩
  obtain ⟨κ, κPositive, pointwiseCoercivity⟩ :=
    exists_modeUniformQuadraticCoercivity carrier carrierCompact
      carrierNonempty fixedP506L0CauchySafeMatterFiberMassEnergy
      fixedP506L0CauchySafeMatterFiberMassEnergy_joint_continuous
      (fun point _ field fieldNonzero ↦
        fixedP506L0CauchySafeMatterFiberMassEnergy_positive
          point field fieldNonzero)
      fixedP506L0CauchySafeMatterFiberMassEnergy_real_smul
  refine ⟨κ, κPositive, ?_⟩
  intro space spaceMem field
  exact pointwiseCoercivity (time, space)
    ⟨mem_singleton time, spaceMem⟩ field

theorem fixedP506L0CauchySafeMatterL2MassAction_coe_ae
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b) :
    fixedP506L0CauchySafeMatterL2MassAction
        time a b C operatorBound field =ᵐ[volume.restrict (Icc a b)]
      fun space ↦
        matterFiberMassRiesz
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (field space) := by
  change
    matterFiberMassRieszCoordinateBilinear.holder 2
        (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
          time a b C operatorBound) field =ᵐ[volume.restrict (Icc a b)] _
  filter_upwards [
      matterFiberMassRieszCoordinateBilinear.coeFn_holder (r := 2)
        (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
          time a b C operatorBound) field,
      MemLp.coeFn_toLp
        (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_memLp_top
          time a b C operatorBound)] with space actionEq matrixEq
  have matrixRead :
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
        time a b C operatorBound) space =
        fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space := by
    change
      ((fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_memLp_top
        time a b C operatorBound).toLp
          (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time))
            space = _
    exact matrixEq
  rw [actionEq, matrixRead]
  rfl

theorem cauchySafeMatterSpatialL2_norm_sq_eq_integral
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖field‖ ^ 2 =
      ∫ space, ‖field space‖ ^ 2 ∂volume.restrict (Icc a b) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun space ↦ real_inner_self_eq_norm_sq (field space)

theorem fixedP506L0CauchySafeMatterL2MassForm_coercive
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C) :
    IsCoercive
      (fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound) := by
  obtain ⟨κ, κPositive, pointwiseCoercivity⟩ :=
    exists_fixedP506L0CauchySafeMatterFiberMassCoercivityOnBox
      time a b boxOrder
  refine ⟨κ, κPositive, ?_⟩
  intro field
  change κ * ‖field‖ * ‖field‖ ≤ inner ℝ
    (fixedP506L0CauchySafeMatterL2MassAction
      time a b C operatorBound field) field
  rw [L2.inner_def]
  have normSquareIntegrable : Integrable
      (fun space ↦ ‖field space‖ ^ 2)
      (volume.restrict (Icc a b)) := by
    have innerIntegrable := memLp_one_iff_integrable.mp
      ((innerSL ℝ).memLp_of_bilin 1 (Lp.memLp field) (Lp.memLp field))
    refine innerIntegrable.congr ?_
    exact ae_of_all _ fun space ↦
      real_inner_self_eq_norm_sq (field space)
  have massInnerIntegrable : Integrable
      (fun space ↦ inner ℝ
        ((fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound field) space)
        (field space))
      (volume.restrict (Icc a b)) := by
    exact memLp_one_iff_integrable.mp
      ((innerSL ℝ).memLp_of_bilin 1
        (Lp.memLp (fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound field))
        (Lp.memLp field))
  calc
    κ * ‖field‖ * ‖field‖ = κ * ‖field‖ ^ 2 := by ring
    _ = κ * ∫ space, ‖field space‖ ^ 2
        ∂volume.restrict (Icc a b) := by
      rw [cauchySafeMatterSpatialL2_norm_sq_eq_integral]
    _ = ∫ space, κ * ‖field space‖ ^ 2
        ∂volume.restrict (Icc a b) := by
      rw [integral_const_mul]
    _ ≤ ∫ space, inner ℝ
        ((fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound field) space)
        (field space) ∂volume.restrict (Icc a b) := by
      apply integral_mono_ae (normSquareIntegrable.const_mul κ)
        massInnerIntegrable
      filter_upwards [
          fixedP506L0CauchySafeMatterL2MassAction_coe_ae
            time a b C operatorBound field,
          ae_restrict_mem measurableSet_Icc] with space actionEq spaceMem
      rw [actionEq, matterFiberMassRiesz_pairing]
      exact pointwiseCoercivity space spaceMem (field space)

def fixedP506L0CauchySafeMatterL2MassEquiv
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C) :
    CauchySafeMatterSpatialL2 a b ≃L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  (fixedP506L0CauchySafeMatterL2MassForm_coercive
    time a b boxOrder C operatorBound).continuousLinearEquivOfBilin

theorem fixedP506L0CauchySafeMatterL2MassEquiv_pairing
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C)
    (first second : CauchySafeMatterSpatialL2 a b) :
    inner ℝ
        (fixedP506L0CauchySafeMatterL2MassEquiv
          time a b boxOrder C operatorBound first)
        second =
      fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound first second := by
  exact IsCoercive.continuousLinearEquivOfBilin_apply
    (fixedP506L0CauchySafeMatterL2MassForm_coercive
      time a b boxOrder C operatorBound) first second

theorem fixedP506L0CauchySafeMatterL2MassEquiv_unique
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C)
    (first representative : CauchySafeMatterSpatialL2 a b)
    (pairing : ∀ test,
      inner ℝ representative test =
        fixedP506L0CauchySafeMatterL2MassForm
          time a b C operatorBound first test) :
    representative =
      fixedP506L0CauchySafeMatterL2MassEquiv
        time a b boxOrder C operatorBound first := by
  exact IsCoercive.unique_continuousLinearEquivOfBilin
    (fixedP506L0CauchySafeMatterL2MassForm_coercive
      time a b boxOrder C operatorBound) pairing

def fixedP506L0CauchySafeMatterPhysicalL2OfMassRepresentative
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C)
    (representative : CauchySafeMatterSpatialL2 a b) :
    CauchySafeMatterSpatialL2 a b :=
  (fixedP506L0CauchySafeMatterL2MassEquiv
    time a b boxOrder C operatorBound).symm representative

theorem fixedP506L0CauchySafeMatterPhysicalL2OfMassRepresentative_pairing
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time space‖ ≤ C)
    (representative test : CauchySafeMatterSpatialL2 a b) :
    fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (fixedP506L0CauchySafeMatterPhysicalL2OfMassRepresentative
          time a b boxOrder C operatorBound representative)
        test =
      inner ℝ representative test := by
  rw [← fixedP506L0CauchySafeMatterL2MassEquiv_pairing
    time a b boxOrder C operatorBound]
  simp [fixedP506L0CauchySafeMatterPhysicalL2OfMassRepresentative]

theorem fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_joint_continuous :
    Continuous fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        input.1 input.2 := by
  apply (PiLp.continuous_toLp 2
    (fun _ : DiracSpinorIndex × DiracSpinorIndex ↦ ℂ)).comp
  apply continuous_pi
  intro coordinatePair
  exact fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    coordinatePair.1 coordinatePair.2

theorem exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space ∈ Icc a b,
          ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
            time space‖ ≤ C := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, normBound⟩ :=
    carrierCompact.exists_bound_of_continuousOn
      fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_joint_continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro time timeMem space spaceMem
  exact (normBound (time, space) ⟨timeMem, spaceMem⟩).trans
    (le_max_left _ _)

/-- The generated mass representative determines one and only one physical
spatial `L²` field family through the action-owned fiber mass law. -/
structure FixedP506L0CauchySafeMatterPhysicalL2Actualization
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (representative : Icc timeStart timeEnd →
      CauchySafeMatterSpatialL2 a b) where
  physicalField : Icc timeStart timeEnd → CauchySafeMatterSpatialL2 a b
  massLaw : ∀ time test,
    (∫ space,
      matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
        (physicalField time space) (test space)
      ∂volume.restrict (Icc a b)) =
      inner ℝ (representative time) test
  physicalFieldUnique : ∀ candidate : Icc timeStart timeEnd →
      CauchySafeMatterSpatialL2 a b,
    (∀ time test,
      (∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (candidate time space) (test space)
        ∂volume.restrict (Icc a b)) =
        inner ℝ (representative time) test) →
      candidate = physicalField

theorem nonempty_fixedP506L0CauchySafeMatterPhysicalL2Actualization
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (representative : Icc timeStart timeEnd →
      CauchySafeMatterSpatialL2 a b) :
    Nonempty
      (FixedP506L0CauchySafeMatterPhysicalL2Actualization
        timeStart timeEnd a b representative) := by
  obtain ⟨C, _, operatorBound⟩ :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      timeStart timeEnd a b
  let physicalField : Icc timeStart timeEnd →
      CauchySafeMatterSpatialL2 a b := fun time ↦
    fixedP506L0CauchySafeMatterPhysicalL2OfMassRepresentative
      time.1 a b boxOrder C (operatorBound time.1 time.2)
      (representative time)
  refine ⟨{
    physicalField := physicalField
    massLaw := ?_
    physicalFieldUnique := ?_ }⟩
  · intro time test
    calc
      (∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (physicalField time space) (test space)
        ∂volume.restrict (Icc a b)) =
          fixedP506L0CauchySafeMatterL2MassForm
            time.1 a b C (operatorBound time.1 time.2)
            (physicalField time) test :=
        (fixedP506L0CauchySafeMatterL2MassForm_eq_integral
          time.1 a b C (operatorBound time.1 time.2)
          (physicalField time) test).symm
      _ = inner ℝ (representative time) test :=
        fixedP506L0CauchySafeMatterPhysicalL2OfMassRepresentative_pairing
          time.1 a b boxOrder C (operatorBound time.1 time.2)
          (representative time) test
  · intro candidate candidateLaw
    funext time
    have candidateMassLaw : ∀ test,
        fixedP506L0CauchySafeMatterL2MassForm
            time.1 a b C (operatorBound time.1 time.2)
            (candidate time) test =
          inner ℝ (representative time) test := by
      intro test
      rw [fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
      exact candidateLaw time test
    have representativeEq :=
      fixedP506L0CauchySafeMatterL2MassEquiv_unique
        time.1 a b boxOrder C (operatorBound time.1 time.2)
        (candidate time) (representative time)
        (fun test ↦ (candidateMassLaw test).symm)
    calc
      candidate time =
          (fixedP506L0CauchySafeMatterL2MassEquiv
            time.1 a b boxOrder C (operatorBound time.1 time.2)).symm
            (fixedP506L0CauchySafeMatterL2MassEquiv
              time.1 a b boxOrder C (operatorBound time.1 time.2)
              (candidate time)) := by simp
      _ = (fixedP506L0CauchySafeMatterL2MassEquiv
            time.1 a b boxOrder C (operatorBound time.1 time.2)).symm
            (representative time) :=
        congrArg
          (fixedP506L0CauchySafeMatterL2MassEquiv
            time.1 a b boxOrder C (operatorBound time.1 time.2)).symm
          representativeEq.symm
      _ = physicalField time := rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
