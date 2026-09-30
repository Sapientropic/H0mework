import H0mework.Physics.DiracEvolution.SafeCommutedCoefficientBound

/-!
# Fixed P506/L0 temporal-jet reduction

The noncharacteristic temporal principal of the source-owned Cauchy-safe
matter action generates its inverse on finite matter coordinates.  The action
law then reconstructs the temporal derivative from the field value and its
three spatial derivatives.  On fixed spacetime boxes this closes the complete
coefficient commutator forcing against one spatial first-jet norm.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracMatterCoordinateCalculus
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalRegularity
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedCoefficientBound
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineMatterCoordinateFirstOrderCommutator

open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance temporalJetMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

private abbrev Safe : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeGlobalActual

private theorem current_coframe_contDiff_one :
    ContDiff ℝ 1 Current.coframe := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact (holonomicCoframe_contDiff Safe
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_smooth).of_le
      (by norm_num)

private theorem current_nondegenerate (point : BasePoint) :
    Matrix.det (Current.coframe point) ≠ 0 := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact fixedP506L0CartanECConstraintCauchySafeGlobalActual_nondegenerate point

private theorem current_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (Current.coframe point) ≠ 0 := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_noncharacteristic point

private def identityCoframeMatterTimePrincipalEnd :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracMatrixMatterAction (diracGamma 0)

@[simp] private theorem identityCoframeMatterTimePrincipalEnd_apply
    (matter : DiracExteriorMatterCarrier) :
    identityCoframeMatterTimePrincipalEnd matter =
      identityCoframeMatterTimePrincipal matter :=
  by simp [identityCoframeMatterTimePrincipalEnd,
    identityCoframeMatterTimePrincipal]

private def fixedEvolutionTemporalPrincipalInverseCoordinateLinear
    (point : BasePoint) :
    MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier :=
  ((matterCoordinateEquiv.toLinearMap.comp
      ((currentCoframeMatterTemporalPrincipalInverse
          (Current.coframe point)).comp
        (identityCoframeMatterTimePrincipalEnd.comp
          matterCoordinateEquiv.symm.toLinearMap))).restrictScalars ℝ)

def fixedEvolutionTemporalPrincipalInverseCoordinateCLM
    (point : BasePoint) :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  ⟨fixedEvolutionTemporalPrincipalInverseCoordinateLinear point,
    (fixedEvolutionTemporalPrincipalInverseCoordinateLinear point
      ).continuous_of_finiteDimensional⟩

@[simp] theorem fixedEvolutionTemporalPrincipalInverseCoordinateCLM_apply
    (point : BasePoint)
    (coordinates : MatterCoordinateCarrier) :
    fixedEvolutionTemporalPrincipalInverseCoordinateCLM point coordinates =
      matterCoordinateEquiv
        (currentCoframeMatterTemporalPrincipalInverse
          (Current.coframe point)
          (identityCoframeMatterTimePrincipal
            (matterCoordinateEquiv.symm coordinates))) :=
  by simp [fixedEvolutionTemporalPrincipalInverseCoordinateCLM,
    fixedEvolutionTemporalPrincipalInverseCoordinateLinear]

theorem fixedEvolutionTemporalPrincipalInverseCoordinateCLM_left
    (point : BasePoint)
    (coordinates : MatterCoordinateCarrier) :
    fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
        (fixedEvolutionPrincipalCoordinateCLM 0 point coordinates) =
      coordinates := by
  rw [fixedEvolutionTemporalPrincipalInverseCoordinateCLM_apply]
  rw [fixedEvolutionPrincipalCoordinateCLM,
    diracMatrixMatterCoordinateCLM_apply]
  rw [matterCoordinateEquiv.symm_apply_apply]
  unfold fixedEvolutionPrincipal
  rw [← identityCoframeMatterTimePrincipal_coordinatePrincipal]
  rw [identityCoframeMatterTimePrincipal_involutive]
  change matterCoordinateEquiv
      (currentCoframeMatterTemporalPrincipalInverse (Current.coframe point)
        (currentCoframeMatterTemporalPrincipal (Current.coframe point)
          (matterCoordinateEquiv.symm coordinates))) = coordinates
  rw [currentCoframeMatterTemporalPrincipalInverse_left]
  · exact matterCoordinateEquiv.apply_symm_apply coordinates
  · rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
    exact
      fixedP506L0CartanECConstraintCauchySafeGlobalActual_noncharacteristic
        point

private theorem temporalPrincipalScalar_contDiffAt_zero
    (point : BasePoint) :
    ContDiffAt ℝ 0
      (fun candidate =>
        coframeTemporalPrincipalScalar (Current.coframe candidate)) point := by
  have inverseRegular : ContDiffAt ℝ 0
      (fun candidate => (Current.coframe candidate)⁻¹) point := by
    exact
      ((StageNineCoframeVariation.coframe_inv_contDiffAt
        (Current.coframe point) (current_nondegenerate point)).of_le
          (by norm_num)).comp point
            (current_coframe_contDiff_one.contDiffAt.of_le (by norm_num))
  unfold coframeTemporalPrincipalScalar
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro internal _
  have inverseEntryRegular : ContDiffAt ℝ 0
      (fun candidate =>
        (Current.coframe candidate)⁻¹ (0 : LorentzianIndex) internal)
      point :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseRegular (0 : LorentzianIndex)) internal
  exact contDiffAt_const.mul (inverseEntryRegular.pow 2)

private theorem temporalPrincipalInverse_apply_contDiffAt_zero
    (coordinates : MatterCoordinateCarrier)
    (point : BasePoint) :
    ContDiffAt ℝ 0
      (fun candidate =>
        fixedEvolutionTemporalPrincipalInverseCoordinateCLM candidate
          coordinates) point := by
  let input : DiracExteriorMatterCarrier :=
    identityCoframeMatterTimePrincipal (matterCoordinateEquiv.symm coordinates)
  have qComplexRegular : ContDiffAt ℝ 0
      (fun candidate =>
        ((coframeTemporalPrincipalScalar
          (Current.coframe candidate) : ℝ) : ℂ)) point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point
      (temporalPrincipalScalar_contDiffAt_zero point)
  have qComplexNe :
      ((coframeTemporalPrincipalScalar
        (Current.coframe point) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast current_noncharacteristic point
  have qInverseRegular : ContDiffAt ℝ 0
      (fun candidate =>
        (((coframeTemporalPrincipalScalar
          (Current.coframe candidate) : ℝ) : ℂ)⁻¹)) point :=
    qComplexRegular.inv qComplexNe
  have gammaTimeRegular : ContDiffAt ℝ 0
      (fun candidate =>
        inverseCoframeDiracGamma
          { coframe := Current.coframe candidate, derivative := 0 }
          (0 : LorentzianIndex)) point := by
    exact
      ((inverseCoframeDiracGamma_contDiffAt
        (Current.coframe point) (current_nondegenerate point)
        (0 : LorentzianIndex)).of_le (by norm_num)).comp point
          (current_coframe_contDiff_one.contDiffAt.of_le (by norm_num))
  have inputRegular : ContDiffAt ℝ 0
      (fun _ : BasePoint => matterCoordinateEquiv input) point :=
    contDiffAt_const
  have gammaActionRegular : ContDiffAt ℝ 0
      (fun candidate => matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := Current.coframe candidate, derivative := 0 }
            (0 : LorentzianIndex)) input)) point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gammaTimeRegular).clm_apply inputRegular
    change ContDiffAt ℝ 0
      (fun candidate => matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := Current.coframe candidate, derivative := 0 }
            (0 : LorentzianIndex))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv input)))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  rw [show (fun candidate =>
      fixedEvolutionTemporalPrincipalInverseCoordinateCLM candidate
        coordinates) =
    (fun candidate =>
      (((coframeTemporalPrincipalScalar
          (Current.coframe candidate) : ℝ) : ℂ)⁻¹) •
        (Complex.I • matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := Current.coframe candidate, derivative := 0 }
              (0 : LorentzianIndex)) input))) by
    funext candidate
    simp [fixedEvolutionTemporalPrincipalInverseCoordinateCLM_apply,
      currentCoframeMatterTemporalPrincipalInverse,
      currentCoframeMatterTemporalPrincipal, input, map_smul]]
  exact qInverseRegular.smul
    ((contDiffAt_const : ContDiffAt ℝ 0
      (fun _ : BasePoint => (Complex.I : ℂ)) point).smul gammaActionRegular)

theorem fixedEvolutionTemporalPrincipalInverseCoordinateCLM_continuous :
    Continuous fixedEvolutionTemporalPrincipalInverseCoordinateCLM := by
  rw [continuous_clm_apply]
  intro coordinates
  rw [continuous_iff_continuousAt]
  intro point
  exact
    (temporalPrincipalInverse_apply_contDiffAt_zero coordinates point
      ).continuousAt

abbrev MatterCoordinateSpatialJetCarrier :=
  MatterCoordinateCarrier ×
    WithLp 2 (Fin 3 → MatterCoordinateCarrier)

def matterCoordinateSpatialJetAt
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : MatterCoordinateSpatialJetCarrier :=
  (field point, WithLp.toLp 2 fun direction =>
    fieldDirectionalDerivative field point direction.succ)

private def fixedOnShellTemporalVelocityLinear
    (point : BasePoint) :
    MatterCoordinateSpatialJetCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun jet :=
    fixedConstantCoordinateVelocityCLM point jet.1 -
      fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
        (∑ direction : Fin 3,
          fixedEvolutionPrincipalCoordinateCLM direction.succ point
            (jet.2 direction))
  map_add' first second := by
    simp only [Prod.fst_add, Prod.snd_add, WithLp.ofLp_add, Pi.add_apply,
      map_add, Finset.sum_add_distrib]
    abel
  map_smul' parameter jet := by
    simp only [Prod.smul_fst, Prod.smul_snd, WithLp.ofLp_smul,
      Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [← Finset.smul_sum]
    rw [map_smul]
    exact (smul_sub parameter _ _).symm

def fixedOnShellTemporalVelocityCLM
    (point : BasePoint) :
    MatterCoordinateSpatialJetCarrier →L[ℝ] MatterCoordinateCarrier :=
  ⟨fixedOnShellTemporalVelocityLinear point,
    (fixedOnShellTemporalVelocityLinear point
      ).continuous_of_finiteDimensional⟩

@[simp] theorem fixedOnShellTemporalVelocityCLM_apply
    (point : BasePoint)
    (jet : MatterCoordinateSpatialJetCarrier) :
    fixedOnShellTemporalVelocityCLM point jet =
      fixedConstantCoordinateVelocityCLM point jet.1 -
        fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
          (∑ direction : Fin 3,
            fixedEvolutionPrincipalCoordinateCLM direction.succ point
              (jet.2 direction)) :=
  rfl

private theorem fixedOnShellTemporalVelocityCLM_apply_continuous
    (jet : MatterCoordinateSpatialJetCarrier) :
    Continuous (fun point => fixedOnShellTemporalVelocityCLM point jet) := by
  have constantContinuous : Continuous (fun point =>
      fixedConstantCoordinateVelocityCLM point jet.1) :=
    fixedConstantCoordinateVelocityCLM_continuous.clm_apply continuous_const
  have spatialSumContinuous : Continuous (fun point =>
      ∑ direction : Fin 3,
        fixedEvolutionPrincipalCoordinateCLM direction.succ point
          (jet.2 direction)) :=
    continuous_finsetSum _ fun direction _ =>
      (fixedEvolutionPrincipalCoordinateCLM_contDiff direction.succ
        ).continuous.clm_apply continuous_const
  have inverseContinuous : Continuous (fun point =>
      fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
        (∑ direction : Fin 3,
          fixedEvolutionPrincipalCoordinateCLM direction.succ point
            (jet.2 direction))) :=
    fixedEvolutionTemporalPrincipalInverseCoordinateCLM_continuous.clm_apply
      spatialSumContinuous
  exact constantContinuous.sub inverseContinuous

theorem fixedOnShellTemporalVelocityCLM_continuous :
    Continuous fixedOnShellTemporalVelocityCLM := by
  rw [continuous_clm_apply]
  exact fixedOnShellTemporalVelocityCLM_apply_continuous

private def fixedOnShellFirstJetLinear
    (point : BasePoint) :
    MatterCoordinateSpatialJetCarrier →ₗ[ℝ]
      MatterCoordinateFirstJetCarrier where
  toFun jet :=
    (jet.1, WithLp.toLp 2 (Fin.cases
      (fixedOnShellTemporalVelocityCLM point jet)
      (fun direction => jet.2 direction)))
  map_add' first second := by
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro direction
      refine Fin.cases ?_ (fun spatial => ?_) direction
      · exact map_add (fixedOnShellTemporalVelocityCLM point) first second
      · rfl
  map_smul' parameter jet := by
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro direction
      refine Fin.cases ?_ (fun spatial => ?_) direction
      · exact map_smul (fixedOnShellTemporalVelocityCLM point)
          parameter jet
      · rfl

def fixedOnShellFirstJetCLM
    (point : BasePoint) :
    MatterCoordinateSpatialJetCarrier →L[ℝ]
      MatterCoordinateFirstJetCarrier :=
  ⟨fixedOnShellFirstJetLinear point,
    (fixedOnShellFirstJetLinear point).continuous_of_finiteDimensional⟩

@[simp] theorem fixedOnShellFirstJetCLM_fst
    (point : BasePoint)
    (jet : MatterCoordinateSpatialJetCarrier) :
    (fixedOnShellFirstJetCLM point jet).1 = jet.1 :=
  rfl

@[simp] theorem fixedOnShellFirstJetCLM_zero
    (point : BasePoint)
    (jet : MatterCoordinateSpatialJetCarrier) :
    (fixedOnShellFirstJetCLM point jet).2 (0 : LorentzianIndex) =
      fixedOnShellTemporalVelocityCLM point jet :=
  rfl

@[simp] theorem fixedOnShellFirstJetCLM_succ
    (point : BasePoint)
    (jet : MatterCoordinateSpatialJetCarrier)
    (direction : Fin 3) :
    (fixedOnShellFirstJetCLM point jet).2 direction.succ =
      jet.2 direction :=
  rfl

private theorem fixedOnShellFirstJetCLM_apply_continuous
    (jet : MatterCoordinateSpatialJetCarrier) :
    Continuous (fun point => fixedOnShellFirstJetCLM point jet) := by
  apply continuous_const.prodMk
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro direction
  refine Fin.cases ?_ (fun _ => continuous_const) direction
  exact fixedOnShellTemporalVelocityCLM_apply_continuous jet

theorem fixedOnShellFirstJetCLM_continuous :
    Continuous fixedOnShellFirstJetCLM := by
  rw [continuous_clm_apply]
  exact fixedOnShellFirstJetCLM_apply_continuous

private def coordinateMatterField
    (field : BasePoint → MatterCoordinateCarrier) :
    BasePoint → DiracExteriorMatterCarrier :=
  fun point => matterCoordinateEquiv.symm (field point)

private def centeredMatterField
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : BasePoint → DiracExteriorMatterCarrier :=
  fun candidate => matterCoordinateEquiv.symm (field candidate - field point)

theorem fixedOnShellTemporalVelocityCLM_spatialJetAt
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (fieldDifferentiable : DifferentiableAt ℝ field point) :
    fixedOnShellTemporalVelocityCLM point
        (matterCoordinateSpatialJetAt field point) =
      cauchySafeMatterVolterraVelocity Current
        (coordinateMatterField field) point := by
  have centeredLaw :=
    fixedCenteredVolterraVelocity_coordinateLaw field point
      fieldDifferentiable
  change fixedEvolutionPrincipalCoordinateCLM 0 point
        (cauchySafeMatterVolterraVelocity Current
          (centeredMatterField field point) point) +
      ∑ direction : Fin 3,
        fixedEvolutionPrincipalCoordinateCLM direction.succ point
          (fieldDirectionalDerivative field point direction.succ) = 0
    at centeredLaw
  have mapped := congrArg
    (fixedEvolutionTemporalPrincipalInverseCoordinateCLM point) centeredLaw
  simp only [map_add, map_zero,
    fixedEvolutionTemporalPrincipalInverseCoordinateCLM_left] at mapped
  have centeredEq :
      cauchySafeMatterVolterraVelocity Current
          (centeredMatterField field point) point =
        -fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
          (∑ direction : Fin 3,
            fixedEvolutionPrincipalCoordinateCLM direction.succ point
              (fieldDirectionalDerivative field point direction.succ)) :=
    eq_neg_of_add_eq_zero_left mapped
  have decomposition :=
    fixedVolterraVelocity_eq_constant_add_centered field point
      fieldDifferentiable
  change cauchySafeMatterVolterraVelocity Current
        (coordinateMatterField field) point =
      fixedConstantCoordinateVelocityCLM point (field point) +
        cauchySafeMatterVolterraVelocity Current
          (centeredMatterField field point) point at decomposition
  rw [decomposition, centeredEq]
  rfl

theorem fixedMatterFirstOrderOperator_eq_zero_implies_temporalDerivative
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (fieldDifferentiable : DifferentiableAt ℝ field point)
    (actionZero :
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point = 0) :
    fieldDirectionalDerivative field point 0 =
      fixedOnShellTemporalVelocityCLM point
        (matterCoordinateSpatialJetAt field point) := by
  have actionNormalForm :=
    fixedMatterFirstOrderOperator_eq_temporalVolterraDefect field point
      fieldDifferentiable
  change matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point =
      fixedEvolutionPrincipalCoordinateCLM 0 point
        (fieldDirectionalDerivative field point 0 -
          cauchySafeMatterVolterraVelocity Current
            (coordinateMatterField field) point) at actionNormalForm
  have principalZero :
      fixedEvolutionPrincipalCoordinateCLM 0 point
        (fieldDirectionalDerivative field point 0 -
          cauchySafeMatterVolterraVelocity Current
            (coordinateMatterField field) point) = 0 := by
    rw [← actionNormalForm]
    exact actionZero
  have mapped := congrArg
    (fixedEvolutionTemporalPrincipalInverseCoordinateCLM point) principalZero
  rw [fixedEvolutionTemporalPrincipalInverseCoordinateCLM_left,
    map_zero] at mapped
  rw [sub_eq_zero.mp mapped]
  exact (fixedOnShellTemporalVelocityCLM_spatialJetAt
    field point fieldDifferentiable).symm

theorem matterCoordinateFirstJetAt_eq_fixedOnShellFirstJetCLM
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (fieldDifferentiable : DifferentiableAt ℝ field point)
    (actionZero :
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point = 0) :
    matterCoordinateFirstJetAt field point =
      fixedOnShellFirstJetCLM point
        (matterCoordinateSpatialJetAt field point) := by
  apply Prod.ext
  · rfl
  · apply PiLp.ext
    intro direction
    refine Fin.cases ?_ (fun spatial => ?_) direction
    · exact fixedMatterFirstOrderOperator_eq_zero_implies_temporalDerivative
        field point fieldDifferentiable actionZero
    · rfl

theorem exists_fixedOnShellFirstJetBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ time ∈ Set.Icc timeStart timeEnd,
        ∀ space ∈ Set.Icc a b,
          ‖fixedOnShellFirstJetCLM
            (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Set.Icc timeStart timeEnd ×ˢ Set.Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have operatorContinuous : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates =>
      fixedOnShellFirstJetCLM
        (diracMatterSpacetimeCoordinatePoint point.1 point.2)) :=
    fixedOnShellFirstJetCLM_continuous.comp
      diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous
  obtain ⟨C, bound⟩ :=
    carrierCompact.exists_bound_of_continuousOn operatorContinuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro time timeMem space spaceMem
  exact (bound (time, space) ⟨timeMem, spaceMem⟩).trans
    (le_max_left _ _)

theorem matterCoordinateFirstJetAt_norm_le_spatialJet_onBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (bound : ∀ time ∈ Set.Icc timeStart timeEnd,
      ∀ space ∈ Set.Icc a b,
        ‖fixedOnShellFirstJetCLM
          (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C)
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldDifferentiable : Differentiable ℝ field)
    (time : ℝ)
    (timeMem : time ∈ Set.Icc timeStart timeEnd)
    (space : DiracMatterSpatialCoordinates)
    (spaceMem : space ∈ Set.Icc a b)
    (actionZero :
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field (diracMatterSpacetimeCoordinatePoint time space) = 0) :
    ‖matterCoordinateFirstJetAt field
        (diracMatterSpacetimeCoordinatePoint time space)‖ ≤
      C * ‖matterCoordinateSpatialJetAt field
        (diracMatterSpacetimeCoordinatePoint time space)‖ := by
  rw [matterCoordinateFirstJetAt_eq_fixedOnShellFirstJetCLM field
    (diracMatterSpacetimeCoordinatePoint time space)
    fieldDifferentiable.differentiableAt actionZero]
  exact (fixedOnShellFirstJetCLM
      (diracMatterSpacetimeCoordinatePoint time space)).le_opNorm
        (matterCoordinateSpatialJetAt field
          (diracMatterSpacetimeCoordinatePoint time space)) |>.trans
    (mul_le_mul_of_nonneg_right
      (bound time timeMem space spaceMem)
      (norm_nonneg _))

/-- The complete source-owned commutator forcing is controlled by the
spatial first jet on every fixed box once the same mother action is imposed. -/
theorem exists_fixedMatterCommutedActionDefectSpatialJetBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (field : BasePoint → MatterCoordinateCarrier),
        ContDiff ℝ 2 field →
        ∀ time ∈ Set.Icc timeStart timeEnd,
          ∀ space ∈ Set.Icc a b,
            matterCoordinateFirstOrderOperator
              fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
              field (diracMatterSpacetimeCoordinatePoint time space) = 0 →
            ∀ commutedDirection : LorentzianIndex,
              ‖fieldDirectionalDerivative
                    (matterCoordinateFirstOrderOperator
                      fixedEvolutionPrincipalCoordinateCLM
                      fixedMatterLowerCoefficient field)
                    (diracMatterSpacetimeCoordinatePoint time space)
                    commutedDirection -
                  matterCoordinateFirstOrderOperator
                    fixedEvolutionPrincipalCoordinateCLM
                    fixedMatterLowerCoefficient
                    (fun candidate =>
                      fieldDirectionalDerivative field candidate
                        commutedDirection)
                    (diracMatterSpacetimeCoordinatePoint time space)‖ ≤
                C * ‖matterCoordinateSpatialJetAt field
                  (diracMatterSpacetimeCoordinatePoint time space)‖ := by
  obtain ⟨coefficientBound, coefficientBoundNonnegative,
      coefficientEstimate⟩ :=
    exists_fixedMatterCoefficientChangedReadBoundOnBox
      timeStart timeEnd a b
  obtain ⟨jetBound, jetBoundNonnegative, jetEstimate⟩ :=
    exists_fixedOnShellFirstJetBoundOnBox timeStart timeEnd a b
  refine ⟨coefficientBound * jetBound,
    mul_nonneg coefficientBoundNonnegative jetBoundNonnegative, ?_⟩
  intro field fieldSmooth time timeMem space spaceMem actionZero
    commutedDirection
  calc
    ‖fieldDirectionalDerivative
          (matterCoordinateFirstOrderOperator
            fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
            field)
          (diracMatterSpacetimeCoordinatePoint time space)
          commutedDirection -
        matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          (fun candidate =>
            fieldDirectionalDerivative field candidate commutedDirection)
          (diracMatterSpacetimeCoordinatePoint time space)‖ ≤
        coefficientBound * ‖matterCoordinateFirstJetAt field
          (diracMatterSpacetimeCoordinatePoint time space)‖ :=
      fixedMatterCommutedActionDefect_norm_le_onBox
        timeStart timeEnd a b coefficientBound coefficientEstimate field
        fieldSmooth time timeMem space spaceMem commutedDirection
    _ ≤ coefficientBound *
        (jetBound * ‖matterCoordinateSpatialJetAt field
          (diracMatterSpacetimeCoordinatePoint time space)‖) :=
      mul_le_mul_of_nonneg_left
        (matterCoordinateFirstJetAt_norm_le_spatialJet_onBox
          timeStart timeEnd a b jetBound jetEstimate field
          (fieldSmooth.differentiable (by norm_num))
          time timeMem space spaceMem actionZero)
        coefficientBoundNonnegative
    _ = (coefficientBound * jetBound) *
        ‖matterCoordinateSpatialJetAt field
          (diracMatterSpacetimeCoordinatePoint time space)‖ := by ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction
