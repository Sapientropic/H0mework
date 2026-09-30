import H0mework.Physics.DiracEvolution.SafeWeakSpatialGalerkinStiffness
import H0mework.Physics.DiracEvolution.WeakGalerkinEnergy

/-!
# Fixed P506/L0 mode-uniform weak energy rate

The Cauchy-safe mother action supplies the four directional principal
derivatives and the constant-section temporal response.  Before a spatial
Galerkin carrier is selected, these coefficients form a continuous quadratic
energy rate on the finite matter fiber.  Compact fiber normalization then
generates one bound shared by every later finite mode space.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageEightSourceGeneratedMatter
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalRegularity
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open scoped ComplexOrder ContDiff Matrix Matrix.Norms.Elementwise NNReal

noncomputable section

set_option autoImplicit false

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

private abbrev Safe : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeGlobalActual

def fixedEvolutionPrincipal
    (direction : LorentzianIndex)
    (point : BasePoint) : DiracMatrix :=
  coframeCoordinateDiracEvolutionPrincipal (Current.coframe point) direction

private theorem safeCoframe_contDiff : ContDiff ℝ ∞ Safe.coframe :=
  holonomicCoframe_contDiff Safe
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_smooth

theorem fixedEvolutionPrincipal_entry_contDiff
    (direction row column : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point : BasePoint ↦
      fixedEvolutionPrincipal direction point row column) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  have gammaPathContDiffAt : ContDiffAt ℝ ∞
      (fun candidate : BasePoint ↦
        inverseCoframeDiracGamma
          { coframe := Safe.coframe candidate, derivative := 0 }
          direction) point := by
    have outer := inverseCoframeDiracGamma_contDiffAt (Safe.coframe point)
      (fixedP506L0CartanECConstraintCauchySafeGlobalActual_nondegenerate point)
      direction
    change ContDiffAt ℝ ∞
      ((fun coframe : LorentzianCoframe ↦
          inverseCoframeDiracGamma
            { coframe := coframe, derivative := 0 } direction) ∘
        Safe.coframe) point
    exact outer.comp point safeCoframe_contDiff.contDiffAt
  have principalEntryContDiffAt : ContDiffAt ℝ ∞
      (fun candidate : BasePoint ↦
        coframeCoordinateDiracEvolutionPrincipal
          (Safe.coframe candidate) direction row column) point := by
    unfold coframeCoordinateDiracEvolutionPrincipal
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiffAt.sum
    intro middle _
    apply contDiffAt_const.mul
    apply contDiffAt_const.mul
    exact contDiffAt_pi.mp (contDiffAt_pi.mp gammaPathContDiffAt middle) column
  rw [show (fun candidate : BasePoint ↦
      fixedEvolutionPrincipal direction candidate row column) =
      (fun candidate ↦
        coframeCoordinateDiracEvolutionPrincipal
          (Safe.coframe candidate) direction row column) by
    funext candidate
    unfold fixedEvolutionPrincipal Current Safe
    rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]]
  exact principalEntryContDiffAt

private def constantBasis (_mode : Fin 1) (_point : BasePoint) : ℝ := 1

private theorem constantBasis_contDiff_one (mode : Fin 1) :
    ContDiff ℝ 1 (constantBasis mode) :=
  contDiff_const

private def constantCandidate
    (coefficient : DiracMatterGalerkinCoefficient 1) :
    BasePoint → DiracExteriorMatterCarrier :=
  cauchySafeMatterGalerkinSynthesis constantBasis coefficient

private def constantVelocity
    (point : BasePoint)
    (coefficient : DiracMatterGalerkinCoefficient 1) : MatterCoordinateCarrier :=
  cauchySafeMatterVolterraVelocity Current
    (constantCandidate coefficient) point

theorem constantVelocity_add
    (point : BasePoint)
    (first second : DiracMatterGalerkinCoefficient 1) :
    constantVelocity point (first + second) =
      constantVelocity point first + constantVelocity point second := by
  unfold constantVelocity constantCandidate
  rw [cauchySafeMatterGalerkinSynthesis_add]
  exact cauchySafeMatterVolterraVelocity_add Current _ _ point
    (cauchySafeMatterGalerkinSynthesis_differentiableAt constantBasis
      (fun mode ↦ (constantBasis_contDiff_one mode).differentiable one_ne_zero)
      first point)
    (cauchySafeMatterGalerkinSynthesis_differentiableAt constantBasis
      (fun mode ↦ (constantBasis_contDiff_one mode).differentiable one_ne_zero)
      second point)

theorem constantVelocity_real_smul
    (point : BasePoint)
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient 1) :
    constantVelocity point (parameter • coefficient) =
      parameter • constantVelocity point coefficient := by
  unfold constantVelocity constantCandidate
  rw [cauchySafeMatterGalerkinSynthesis_real_smul]
  exact cauchySafeMatterVolterraVelocity_real_smul Current _ parameter point
    (cauchySafeMatterGalerkinSynthesis_differentiableAt constantBasis
      (fun mode ↦ (constantBasis_contDiff_one mode).differentiable one_ne_zero)
      coefficient point)

def constantVelocityLinear (point : BasePoint) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ] MatterCoordinateCarrier where
  toFun := constantVelocity point
  map_add' := constantVelocity_add point
  map_smul' := constantVelocity_real_smul point

def constantVelocityCLM (point : BasePoint) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ] MatterCoordinateCarrier :=
  ⟨constantVelocityLinear point,
    (constantVelocityLinear point).continuous_of_finiteDimensional⟩

theorem constantVelocityCLM_continuous : Continuous constantVelocityCLM := by
  rw [continuous_clm_apply]
  intro coefficient
  exact
    (fixedP506L0CauchySafeMatterGalerkinInputActual_volterraVelocity_contDiff_zero
      constantBasis constantBasis_contDiff_one coefficient).continuous

private def constantSpatialBasis
    (_mode : Fin 1) (_space : DiracMatterSpatialCoordinates) : ℝ := 1

private theorem constantSpatialBasis_continuous (mode : Fin 1) :
    Continuous (constantSpatialBasis mode) :=
  continuous_const

@[simp] theorem fixedPointwiseConstantSpatialSynthesis
    (coefficient : DiracMatterGalerkinCoefficient 1)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialGalerkinSynthesis constantSpatialBasis coefficient space =
      matterCoordinateEquiv.symm
        (diracMatterGalerkinCoefficientMode coefficient 0) := by
  apply matterCoordinateEquiv.injective
  rw [diracMatterSpatialGalerkinSynthesis_coordinates, Fin.sum_univ_one,
    matterCoordinateEquiv.apply_symm_apply]
  simp [constantSpatialBasis]

def fixedEvolutionPrincipalOnSlice
    (direction : LorentzianIndex)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : DiracMatrix :=
  fixedEvolutionPrincipal direction
    (diracMatterSpacetimeCoordinatePoint time space)

theorem fixedEvolutionPrincipalOnSlice_entry_contDiff
    (direction row column : LorentzianIndex) :
    ContDiff ℝ ∞ (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedEvolutionPrincipalOnSlice direction input.1 input.2 row column) :=
  (fixedEvolutionPrincipal_entry_contDiff direction row column).comp
    diracMatterSpacetimeCoordinatePoint_joint_contDiff

def diracMatterSliceDirection
    (direction : LorentzianIndex) : ℝ × DiracMatterSpatialCoordinates :=
  Fin.cases (1, (0 : DiracMatterSpatialCoordinates))
    (fun spatialDirection : Fin 3 ↦
      (0, Pi.single spatialDirection 1)) direction

def fixedEvolutionPrincipalDirectionalDerivativeOnSlice
    (direction : LorentzianIndex)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : DiracMatrix :=
  fun row column ↦
    fderiv ℝ (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedEvolutionPrincipalOnSlice direction input.1 input.2 row column)
      (time, space) (diracMatterSliceDirection direction)

theorem fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
    (direction row column : LorentzianIndex) :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction
        input.1 input.2 row column) := by
  unfold fixedEvolutionPrincipalDirectionalDerivativeOnSlice
  exact
    (((fixedEvolutionPrincipalOnSlice_entry_contDiff direction row column).of_le
      (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const

def fixedConstantActionResponse
    (time : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient 1)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  constantVelocity (diracMatterSpacetimeCoordinatePoint time space) coefficient

theorem fixedConstantActionResponse_joint_continuous
    (coefficient : DiracMatterGalerkinCoefficient 1) :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedConstantActionResponse input.1 coefficient input.2) := by
  exact
    ((constantVelocityCLM_continuous.comp
      diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous).clm_apply
        continuous_const)

theorem fixedConstantActionResponse_add
    (time : ℝ)
    (first second : DiracMatterGalerkinCoefficient 1) :
    fixedConstantActionResponse time (first + second) =
      fixedConstantActionResponse time first +
        fixedConstantActionResponse time second := by
  funext space
  exact constantVelocity_add
    (diracMatterSpacetimeCoordinatePoint time space) first second

theorem fixedConstantActionResponse_real_smul
    (time parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient 1) :
    fixedConstantActionResponse time (parameter • coefficient) =
      parameter • fixedConstantActionResponse time coefficient := by
  funext space
  exact constantVelocity_real_smul
    (diracMatterSpacetimeCoordinatePoint time space) parameter coefficient

def fixedPointwiseEnergyFormValue
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (first second : DiracMatterGalerkinCoefficient 1) : ℝ :=
  diracMatterWeakMassDensity
    (fixedP506L0CauchySafeMatterWeakMassMatrix time)
    constantSpatialBasis first second space

def fixedPointwiseRateFormValue
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (first second : DiracMatterGalerkinCoefficient 1) : ℝ :=
  (∑ direction : LorentzianIndex,
      diracMatterWeakMassDensity
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction time)
        constantSpatialBasis first second space) -
    2 * diracMatterWeakStiffnessDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis (fixedConstantActionResponse time)
      first second space

theorem fixedPointwiseEnergyFormValue_joint_continuous
    (first second : DiracMatterGalerkinCoefficient 1) :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedPointwiseEnergyFormValue input.1 input.2 first second) := by
  exact diracMatterWeakMassDensity_joint_continuous
    fixedP506L0CauchySafeMatterWeakMassMatrix constantSpatialBasis
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    constantSpatialBasis_continuous first second

theorem fixedPointwiseRateFormValue_joint_continuous
    (first second : DiracMatterGalerkinCoefficient 1) :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedPointwiseRateFormValue input.1 input.2 first second) := by
  unfold fixedPointwiseRateFormValue
  apply Continuous.sub
  · apply continuous_finsetSum Finset.univ
    intro direction _
    exact diracMatterWeakMassDensity_joint_continuous
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction)
      constantSpatialBasis
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
        direction)
      constantSpatialBasis_continuous first second
  · exact continuous_const.mul
      (diracMatterWeakStiffnessDensity_joint_continuous
        fixedP506L0CauchySafeMatterWeakMassMatrix constantSpatialBasis
        fixedConstantActionResponse
        fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
        constantSpatialBasis_continuous
        fixedConstantActionResponse_joint_continuous first second)

theorem fixedPointwiseEnergyFormValue_add_right
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first second third : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseEnergyFormValue time space first (second + third) =
      fixedPointwiseEnergyFormValue time space first second +
        fixedPointwiseEnergyFormValue time space first third := by
  exact congrFun
    (diracMatterWeakMassDensity_add_right
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis first second third) space

theorem fixedPointwiseEnergyFormValue_real_smul_right
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (first second : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseEnergyFormValue time space first (parameter • second) =
      parameter • fixedPointwiseEnergyFormValue time space first second := by
  exact congrFun
    (diracMatterWeakMassDensity_real_smul_right
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis parameter first second) space

theorem fixedPointwiseEnergyFormValue_add_left
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first second third : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseEnergyFormValue time space (first + second) third =
      fixedPointwiseEnergyFormValue time space first third +
        fixedPointwiseEnergyFormValue time space second third := by
  exact congrFun
    (diracMatterWeakMassDensity_add_left
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis first second third) space

theorem fixedPointwiseEnergyFormValue_real_smul_left
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (first second : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseEnergyFormValue time space (parameter • first) second =
      parameter • fixedPointwiseEnergyFormValue time space first second := by
  exact congrFun
    (diracMatterWeakMassDensity_real_smul_left
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis parameter first second) space

theorem fixedPointwiseRateFormValue_add_right
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first second third : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseRateFormValue time space first (second + third) =
      fixedPointwiseRateFormValue time space first second +
        fixedPointwiseRateFormValue time space first third := by
  unfold fixedPointwiseRateFormValue
  have massAdd (direction : LorentzianIndex) := congrFun
    (diracMatterWeakMassDensity_add_right
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction time)
      constantSpatialBasis first second third) space
  have stiffnessAdd := congrFun
    (diracMatterWeakStiffnessDensity_add_right
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis (fixedConstantActionResponse time)
      (fixedConstantActionResponse_add time) first second third) space
  simp_rw [massAdd]
  simp only [Pi.add_apply] at stiffnessAdd ⊢
  rw [Finset.sum_add_distrib, stiffnessAdd]
  ring

theorem fixedPointwiseRateFormValue_real_smul_right
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (first second : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseRateFormValue time space first (parameter • second) =
      parameter • fixedPointwiseRateFormValue time space first second := by
  unfold fixedPointwiseRateFormValue
  have massSmul (direction : LorentzianIndex) := congrFun
    (diracMatterWeakMassDensity_real_smul_right
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction time)
      constantSpatialBasis parameter first second) space
  have stiffnessSmul := congrFun
    (diracMatterWeakStiffnessDensity_real_smul_right
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis (fixedConstantActionResponse time)
      (fixedConstantActionResponse_real_smul time) parameter first second) space
  simp_rw [massSmul]
  simp only [Pi.smul_apply, smul_eq_mul] at stiffnessSmul ⊢
  rw [← Finset.mul_sum, stiffnessSmul]
  ring

theorem fixedPointwiseRateFormValue_add_left
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first second third : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseRateFormValue time space (first + second) third =
      fixedPointwiseRateFormValue time space first third +
        fixedPointwiseRateFormValue time space second third := by
  unfold fixedPointwiseRateFormValue
  have massAdd (direction : LorentzianIndex) := congrFun
    (diracMatterWeakMassDensity_add_left
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction time)
      constantSpatialBasis first second third) space
  have stiffnessAdd := congrFun
    (diracMatterWeakStiffnessDensity_add_left
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis (fixedConstantActionResponse time)
      first second third) space
  simp_rw [massAdd]
  simp only [Pi.add_apply] at stiffnessAdd ⊢
  rw [Finset.sum_add_distrib, stiffnessAdd]
  ring

theorem fixedPointwiseRateFormValue_real_smul_left
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (first second : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseRateFormValue time space (parameter • first) second =
      parameter • fixedPointwiseRateFormValue time space first second := by
  unfold fixedPointwiseRateFormValue
  have massSmul (direction : LorentzianIndex) := congrFun
    (diracMatterWeakMassDensity_real_smul_left
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction time)
      constantSpatialBasis parameter first second) space
  have stiffnessSmul := congrFun
    (diracMatterWeakStiffnessDensity_real_smul_left
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      constantSpatialBasis (fixedConstantActionResponse time)
      parameter first second) space
  simp_rw [massSmul]
  simp only [Pi.smul_apply, smul_eq_mul] at stiffnessSmul ⊢
  rw [← Finset.mul_sum, stiffnessSmul]
  ring

private def fixedPointwiseEnergyInnerLinear
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first : DiracMatterGalerkinCoefficient 1) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ] ℝ where
  toFun := fixedPointwiseEnergyFormValue time space first
  map_add' := fixedPointwiseEnergyFormValue_add_right time space first
  map_smul' := fun parameter second ↦
    fixedPointwiseEnergyFormValue_real_smul_right time space parameter
      first second

private def fixedPointwiseEnergyInnerCLM
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first : DiracMatterGalerkinCoefficient 1) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ :=
  ⟨fixedPointwiseEnergyInnerLinear time space first,
    (fixedPointwiseEnergyInnerLinear time space first
      ).continuous_of_finiteDimensional⟩

private def fixedPointwiseEnergyFormLinear
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ]
      (DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ) where
  toFun := fixedPointwiseEnergyInnerCLM time space
  map_add' := by
    intro first second
    ext third
    exact fixedPointwiseEnergyFormValue_add_left time space first second third
  map_smul' := by
    intro parameter first
    ext second
    exact fixedPointwiseEnergyFormValue_real_smul_left time space parameter
      first second

def fixedPointwiseEnergyForm
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ]
      (DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ) :=
  ⟨fixedPointwiseEnergyFormLinear time space,
    (fixedPointwiseEnergyFormLinear time space
      ).continuous_of_finiteDimensional⟩

private def fixedPointwiseRateInnerLinear
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first : DiracMatterGalerkinCoefficient 1) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ] ℝ where
  toFun := fixedPointwiseRateFormValue time space first
  map_add' := fixedPointwiseRateFormValue_add_right time space first
  map_smul' := fun parameter second ↦
    fixedPointwiseRateFormValue_real_smul_right time space parameter first
      second

private def fixedPointwiseRateInnerCLM
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first : DiracMatterGalerkinCoefficient 1) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ :=
  ⟨fixedPointwiseRateInnerLinear time space first,
    (fixedPointwiseRateInnerLinear time space first
      ).continuous_of_finiteDimensional⟩

private def fixedPointwiseRateFormLinear
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ]
      (DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ) where
  toFun := fixedPointwiseRateInnerCLM time space
  map_add' := by
    intro first second
    ext third
    exact fixedPointwiseRateFormValue_add_left time space first second third
  map_smul' := by
    intro parameter first
    ext second
    exact fixedPointwiseRateFormValue_real_smul_left time space parameter
      first second

def fixedPointwiseRateForm
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ]
      (DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ) :=
  ⟨fixedPointwiseRateFormLinear time space,
    (fixedPointwiseRateFormLinear time space
      ).continuous_of_finiteDimensional⟩

theorem fixedPointwiseEnergyForm_continuous :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedPointwiseEnergyForm input.1 input.2) := by
  rw [continuous_clm_apply]
  intro first
  rw [continuous_clm_apply]
  intro second
  exact fixedPointwiseEnergyFormValue_joint_continuous first second

theorem fixedPointwiseRateForm_continuous :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedPointwiseRateForm input.1 input.2) := by
  rw [continuous_clm_apply]
  intro first
  rw [continuous_clm_apply]
  intro second
  exact fixedPointwiseRateFormValue_joint_continuous first second

def fixedPointwiseEnergy
    (point : ℝ × DiracMatterSpatialCoordinates)
    (coefficient : DiracMatterGalerkinCoefficient 1) : ℝ :=
  fixedPointwiseEnergyForm point.1 point.2 coefficient coefficient

def fixedPointwiseRate
    (point : ℝ × DiracMatterSpatialCoordinates)
    (coefficient : DiracMatterGalerkinCoefficient 1) : ℝ :=
  fixedPointwiseRateForm point.1 point.2 coefficient coefficient

@[simp] theorem fixedPointwiseRate_eq_formValue
    (point : ℝ × DiracMatterSpatialCoordinates)
    (coefficient : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseRate point coefficient =
      fixedPointwiseRateFormValue point.1 point.2 coefficient coefficient :=
  rfl

theorem fixedPointwiseEnergy_joint_continuous :
    Continuous (fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
      fixedPointwiseEnergy input.1 input.2) := by
  unfold fixedPointwiseEnergy
  exact
    ((fixedPointwiseEnergyForm_continuous.comp continuous_fst).clm_apply
      continuous_snd).clm_apply continuous_snd

theorem fixedPointwiseRate_joint_continuous :
    Continuous (fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
      fixedPointwiseRate input.1 input.2) := by
  unfold fixedPointwiseRate
  exact
    ((fixedPointwiseRateForm_continuous.comp continuous_fst).clm_apply
      continuous_snd).clm_apply continuous_snd

theorem fixedPointwiseEnergy_real_smul
    (point : ℝ × DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseEnergy point (parameter • coefficient) =
      parameter ^ 2 * fixedPointwiseEnergy point coefficient := by
  unfold fixedPointwiseEnergy
  simp [map_smul, smul_eq_mul, pow_two, mul_assoc]

theorem fixedPointwiseRate_real_smul
    (point : ℝ × DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient 1) :
    fixedPointwiseRate point (parameter • coefficient) =
      parameter ^ 2 * fixedPointwiseRate point coefficient := by
  unfold fixedPointwiseRate
  simp [map_smul, smul_eq_mul, pow_two, mul_assoc]

theorem constantSpatialSynthesis_eq_zero_iff
    (coefficient : DiracMatterGalerkinCoefficient 1)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialGalerkinSynthesis constantSpatialBasis coefficient
        space = 0 ↔
      coefficient = 0 := by
  constructor
  · intro synthesisZero
    apply PiLp.ext
    intro index
    rcases index with ⟨mode, coordinate⟩
    fin_cases mode
    have coordinateZero := congrArg
      (fun field : DiracExteriorMatterCarrier ↦
        matterCoordinateEquiv field coordinate) synthesisZero
    simpa [diracMatterSpatialGalerkinSynthesis_coordinates,
      constantSpatialBasis, diracMatterGalerkinCoefficientMode,
      Fin.sum_univ_one] using coordinateZero
  · rintro rfl
    apply matterCoordinateEquiv.injective
    ext coordinate
    rw [diracMatterSpatialGalerkinSynthesis_coordinates, Fin.sum_univ_one]
    simp [constantSpatialBasis, diracMatterGalerkinCoefficientMode]

theorem fixedPointwiseEnergy_positive
    (point : ℝ × DiracMatterSpatialCoordinates)
    (coefficient : DiracMatterGalerkinCoefficient 1)
    (coefficientNonzero : coefficient ≠ 0) :
    0 < fixedPointwiseEnergy point coefficient := by
  change 0 < diracMatterWeakMassDensity
    (fixedP506L0CauchySafeMatterWeakMassMatrix point.1)
    constantSpatialBasis coefficient coefficient point.2
  unfold diracMatterWeakMassDensity
  rw [diracExteriorMatterEnergyPairing_self]
  exact diracExteriorMatterCoordinateEnergy_pos
    (fixedP506L0CauchySafeMatterWeakMassMatrix point.1 point.2)
    (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef point.1 point.2)
    (diracMatterSpatialGalerkinSynthesis constantSpatialBasis coefficient
      point.2)
    (mt (constantSpatialSynthesis_eq_zero_iff coefficient point.2).mp
      coefficientNonzero)

private theorem coefficientModeZero_surjective :
    Function.Surjective (fun coefficient : DiracMatterGalerkinCoefficient 1 ↦
      diracMatterGalerkinCoefficientMode coefficient 0) := by
  intro coordinates
  refine ⟨WithLp.toLp 2 (fun index ↦ coordinates index.2), ?_⟩
  ext coordinate
  rfl

local instance fixedMatterCoordinateCarrierNontrivial :
    Nontrivial MatterCoordinateCarrier := by
  refine ⟨⟨0, matterCoordinateEquiv diracSpinTwoMatterProbe, ?_⟩⟩
  intro coordinatesZero
  apply diracSpinTwoMatterProbe_nonzero
  apply matterCoordinateEquiv.injective
  simpa using coordinatesZero.symm

local instance fixedOneModeCoefficientNontrivial :
    Nontrivial (DiracMatterGalerkinCoefficient 1) :=
  Function.Surjective.nontrivial coefficientModeZero_surjective

/-- The fixed mother-action time principal generates one strict pointwise
coercivity constant on every compact spacetime carrier. -/
theorem exists_fixedModeUniformPointwiseEnergyCoercivity
    (carrier : Set (ℝ × DiracMatterSpatialCoordinates))
    (carrierCompact : IsCompact carrier)
    (carrierNonempty : carrier.Nonempty) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ point ∈ carrier, ∀ coefficient : DiracMatterGalerkinCoefficient 1,
        κ * ‖coefficient‖ ^ 2 ≤ fixedPointwiseEnergy point coefficient := by
  exact exists_modeUniformQuadraticCoercivity carrier carrierCompact
    carrierNonempty fixedPointwiseEnergy fixedPointwiseEnergy_joint_continuous
    (fun point _ coefficient coefficientNonzero ↦
      fixedPointwiseEnergy_positive point coefficient coefficientNonzero)
    fixedPointwiseEnergy_real_smul

/-- The fixed mother-action coefficients generate one pointwise energy-rate
bound on every compact spacetime carrier, before any Galerkin mode count is
chosen. -/
theorem exists_fixedModeUniformPointwiseEnergyRateBound
    (carrier : Set (ℝ × DiracMatterSpatialCoordinates))
    (carrierCompact : IsCompact carrier)
    (carrierNonempty : carrier.Nonempty) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ point ∈ carrier, ∀ coefficient : DiracMatterGalerkinCoefficient 1,
        ‖fixedPointwiseRate point coefficient‖ ≤
          K * fixedPointwiseEnergy point coefficient := by
  exact exists_modeUniformQuadraticRateBound carrier carrierCompact
    carrierNonempty fixedPointwiseEnergy fixedPointwiseRate
    fixedPointwiseEnergy_joint_continuous fixedPointwiseRate_joint_continuous
    (fun point _ coefficient coefficientNonzero ↦
      fixedPointwiseEnergy_positive point coefficient coefficientNonzero)
    fixedPointwiseEnergy_real_smul fixedPointwiseRate_real_smul

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
