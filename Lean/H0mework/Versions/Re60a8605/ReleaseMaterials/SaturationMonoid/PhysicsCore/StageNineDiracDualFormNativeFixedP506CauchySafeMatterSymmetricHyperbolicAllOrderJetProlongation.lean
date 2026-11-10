import H0mework.Physics.DiracEvolution.SafeSymmetricHyperbolicAllOrderEnergyHierarchy

/-!
# Fixed P506/L0 all-order spatial-jet prolongation

The noncharacteristic mother action recursively reconstructs the temporal jet
of every spatially commuted field.  One finite spatial-jet carrier therefore
generates the complete coefficient forcing at arbitrary order.  The
constructor consumes only source coefficients and the spatial jet; the exact
action zero enters solely in the correctness readback.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderJetProlongation

open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCommutator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderVolterraEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedCoefficientBound
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientCommutator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCoefficients
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineMatterActionTimeVelocity
open StageNineMatterCoordinateFirstOrderCommutator
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open DiracExteriorMatterAction
open StageNineHolonomicField
open ProofFreeRicherAnholonomicSource
open Set

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance allOrderJetMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

private theorem current_nondegenerate (point : BasePoint) :
    Matrix.det (Current.coframe point) ≠ 0 := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact fixedP506L0CartanECConstraintCauchySafeGlobalActual_nondegenerate point

private theorem current_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (Current.coframe point) ≠ 0 := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact fixedP506L0CartanECConstraintCauchySafeGlobalActual_noncharacteristic point

private theorem current_coframe_contDiff_infty :
    ContDiff ℝ ∞ Current.coframe := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  exact fixedP506L0CauchySafeMatterGalerkinInputActual_smooth.1 row column

private theorem temporalPrincipalScalar_contDiffAt_infty
    (point : BasePoint) :
    ContDiffAt ℝ ∞
      (fun candidate => coframeTemporalPrincipalScalar
        (Current.coframe candidate)) point := by
  have inverseRegular : ContDiffAt ℝ ∞
      (fun candidate => (Current.coframe candidate)⁻¹) point :=
    (coframe_inv_contDiffAt (Current.coframe point)
      (current_nondegenerate point)).comp point
        current_coframe_contDiff_infty.contDiffAt
  unfold coframeTemporalPrincipalScalar
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro internal _
  have inverseEntryRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (Current.coframe candidate)⁻¹ (0 : LorentzianIndex) internal)
      point :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseRegular (0 : LorentzianIndex)) internal
  exact contDiffAt_const.mul (inverseEntryRegular.pow 2)

private theorem temporalPrincipalInverse_apply_contDiffAt_infty
    (coordinates : MatterCoordinateCarrier)
    (point : BasePoint) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        fixedEvolutionTemporalPrincipalInverseCoordinateCLM candidate
          coordinates) point := by
  let input : DiracExteriorMatterCarrier :=
    identityCoframeMatterTimePrincipal (matterCoordinateEquiv.symm coordinates)
  have qComplexRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        ((coframeTemporalPrincipalScalar
          (Current.coframe candidate) : ℝ) : ℂ)) point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point
      (temporalPrincipalScalar_contDiffAt_infty point)
  have qComplexNe :
      ((coframeTemporalPrincipalScalar
        (Current.coframe point) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast current_noncharacteristic point
  have qInverseRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (((coframeTemporalPrincipalScalar
          (Current.coframe candidate) : ℝ) : ℂ)⁻¹)) point :=
    qComplexRegular.inv qComplexNe
  have gammaTimeRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        inverseCoframeDiracGamma
          { coframe := Current.coframe candidate, derivative := 0 }
          (0 : LorentzianIndex)) point :=
    (inverseCoframeDiracGamma_contDiffAt
      (Current.coframe point) (current_nondegenerate point)
      (0 : LorentzianIndex)).comp point
        current_coframe_contDiff_infty.contDiffAt
  have inputRegular : ContDiffAt ℝ ∞
      (fun _ : BasePoint => matterCoordinateEquiv input) point :=
    contDiffAt_const
  have gammaActionRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := Current.coframe candidate, derivative := 0 }
            (0 : LorentzianIndex)) input)) point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gammaTimeRegular).clm_apply inputRegular
    change ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := Current.coframe candidate, derivative := 0 }
            (0 : LorentzianIndex))
          (matterCoordinateEquiv.symm (matterCoordinateEquiv input)))) point
      at actual
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
    ((contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : BasePoint => (Complex.I : ℂ)) point).smul gammaActionRegular)

theorem fixedEvolutionTemporalPrincipalInverseCoordinateCLM_contDiff_infty :
    ContDiff ℝ ∞ fixedEvolutionTemporalPrincipalInverseCoordinateCLM := by
  rw [contDiff_clm_apply_iff]
  intro coordinates
  rw [contDiff_iff_contDiffAt]
  exact temporalPrincipalInverse_apply_contDiffAt_infty coordinates

theorem fixedOnShellTemporalVelocityCLM_contDiff_infty :
    ContDiff ℝ ∞ fixedOnShellTemporalVelocityCLM := by
  rw [contDiff_clm_apply_iff]
  intro jet
  change ContDiff ℝ ∞ (fun point =>
    fixedConstantCoordinateVelocityCLM point jet.1 -
      fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
        (∑ direction : Fin 3,
          fixedEvolutionPrincipalCoordinateCLM direction.succ point
            (jet.2 direction)))
  have spatialRegular : ContDiff ℝ ∞ (fun point =>
      ∑ direction : Fin 3,
        fixedEvolutionPrincipalCoordinateCLM direction.succ point
          (jet.2 direction)) :=
    ContDiff.sum fun direction _ =>
      (fixedEvolutionPrincipalCoordinateCLM_contDiff_infty direction.succ
        ).clm_apply contDiff_const
  exact
    (fixedConstantCoordinateVelocityCLM_contDiff_infty.clm_apply
      contDiff_const).sub
    (fixedEvolutionTemporalPrincipalInverseCoordinateCLM_contDiff_infty.clm_apply
      spatialRegular)

theorem fixedOnShellFirstJetCLM_contDiff_infty :
    ContDiff ℝ ∞ fixedOnShellFirstJetCLM := by
  rw [contDiff_clm_apply_iff]
  intro jet
  apply contDiff_const.prodMk
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi'
  intro direction
  refine Fin.cases ?_ (fun _ => contDiff_const) direction
  exact fixedOnShellTemporalVelocityCLM_contDiff_infty.clm_apply
    contDiff_const

/-- The complete finite spatial jet through one order. -/
abbrev FixedMatterSpatialJetCarrier (order : ℕ) :=
  FixedMatterSpatialWordIndex order → MatterCoordinateCarrier

def FixedMatterSpatialWordIndex.castSucc
    {order : ℕ}
    (word : FixedMatterSpatialWordIndex order) :
    FixedMatterSpatialWordIndex (order + 1) :=
  ⟨word.1.castSucc, word.2⟩

def FixedMatterSpatialWordIndex.prepend
    {order : ℕ}
    (direction : Fin 3)
    (word : FixedMatterSpatialWordIndex order) :
    FixedMatterSpatialWordIndex (order + 1) :=
  ⟨word.1.succ, Fin.cases direction word.2⟩

@[simp] theorem FixedMatterSpatialWordIndex.toList_castSucc
    {order : ℕ}
    (word : FixedMatterSpatialWordIndex order) :
    (FixedMatterSpatialWordIndex.castSucc word).toList = word.toList := by
  unfold FixedMatterSpatialWordIndex.toList
    FixedMatterSpatialWordIndex.castSucc
  rfl

@[simp] theorem FixedMatterSpatialWordIndex.toList_prepend
    {order : ℕ}
    (direction : Fin 3)
    (word : FixedMatterSpatialWordIndex order) :
    (FixedMatterSpatialWordIndex.prepend direction word).toList =
      direction :: word.toList := by
  unfold FixedMatterSpatialWordIndex.toList
    FixedMatterSpatialWordIndex.prepend
  change List.ofFn (Fin.cons direction word.2) =
    direction :: List.ofFn word.2
  exact List.ofFn_cons direction word.2

/-- The canonical coordinate occupied by one exact spatial word. -/
def FixedMatterSpatialWordIndex.self
    (word : List (Fin 3)) : FixedMatterSpatialWordIndex word.length :=
  ⟨⟨word.length, Nat.lt_succ_self word.length⟩, word.get⟩

@[simp] theorem FixedMatterSpatialWordIndex.toList_self
    (word : List (Fin 3)) :
    (FixedMatterSpatialWordIndex.self word).toList = word := by
  unfold FixedMatterSpatialWordIndex.toList
    FixedMatterSpatialWordIndex.self
  exact List.ofFn_get word

/-- The spatial jet read directly from one smooth field. -/
def fixedMatterSpatialJetAt
    (order : ℕ)
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : FixedMatterSpatialJetCarrier order :=
  fun word => fixedSpatialWordDerivative word.toList field point

theorem fixedMatterSpatialJetAt_contDiff_infty
    (order : ℕ)
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (fixedMatterSpatialJetAt order field) := by
  rw [contDiff_pi]
  intro word
  exact fixedSpatialWordDerivative_contDiff_infty word.toList field fieldSmooth

/-- Forget the top spatial layer. -/
def fixedMatterSpatialJetLowerCLM
    (order : ℕ) :
    FixedMatterSpatialJetCarrier (order + 1) →L[ℝ]
      FixedMatterSpatialJetCarrier order :=
  ContinuousLinearMap.pi fun word =>
    ContinuousLinearMap.proj
      (FixedMatterSpatialWordIndex.castSucc word)

/-- Read the derivative in one spatial direction from the next jet layer. -/
def fixedMatterSpatialJetDerivativeCLM
    (order : ℕ)
    (direction : Fin 3) :
    FixedMatterSpatialJetCarrier (order + 1) →L[ℝ]
      FixedMatterSpatialJetCarrier order :=
  ContinuousLinearMap.pi fun word =>
    ContinuousLinearMap.proj
      (FixedMatterSpatialWordIndex.prepend direction word)

@[simp] theorem fixedMatterSpatialJetLowerCLM_apply
    (order : ℕ)
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) :
    fixedMatterSpatialJetLowerCLM order
        (fixedMatterSpatialJetAt (order + 1) field point) =
      fixedMatterSpatialJetAt order field point := by
  funext word
  simp [fixedMatterSpatialJetLowerCLM, fixedMatterSpatialJetAt]

@[simp] theorem fixedMatterSpatialJetDerivativeCLM_apply
    (order : ℕ)
    (direction : Fin 3)
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) :
    fixedMatterSpatialJetDerivativeCLM order direction
        (fixedMatterSpatialJetAt (order + 1) field point) =
      fun word => fixedSpatialWordDerivative
        (direction :: word.toList) field point := by
  funext word
  simp [fixedMatterSpatialJetDerivativeCLM, fixedMatterSpatialJetAt]

/-- The derivative of the complete jet is the next spatial layer, with no
coordinate-by-coordinate regularity premises. -/
theorem fixedMatterSpatialJetAt_directionalDerivative
    (order : ℕ)
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field)
    (point : BasePoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative (fixedMatterSpatialJetAt order field)
        point direction.succ =
      fixedMatterSpatialJetDerivativeCLM order direction
        (fixedMatterSpatialJetAt (order + 1) field point) := by
  have jetDifferentiable :
      DifferentiableAt ℝ (fixedMatterSpatialJetAt order field) point :=
    (fixedMatterSpatialJetAt_contDiff_infty order field fieldSmooth
      ).differentiable (by simp) point
  unfold fieldDirectionalDerivative
  funext word
  have coordinateFDeriv := congrArg
    (fun derivative : BasePoint →L[ℝ] MatterCoordinateCarrier =>
      derivative (coordinateDirection direction.succ))
    (fderiv_apply jetDifferentiable word)
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] at coordinateFDeriv
  rw [← coordinateFDeriv]
  change fieldDirectionalDerivative
      (fixedSpatialWordDerivative word.toList field) point direction.succ =
    fixedSpatialWordDerivative
      ((FixedMatterSpatialWordIndex.prepend direction word).toList)
      field point
  rw [FixedMatterSpatialWordIndex.toList_prepend]
  rfl

/-- The value and the three spatial derivatives of one selected word,
extracted from the next complete spatial layer. -/
private def fixedMatterSpatialFirstJetOfWordLinear
    (word : List (Fin 3)) :
    FixedMatterSpatialJetCarrier (word.length + 1) →ₗ[ℝ]
      MatterCoordinateSpatialJetCarrier where
  toFun jet :=
    (jet (FixedMatterSpatialWordIndex.castSucc
        (FixedMatterSpatialWordIndex.self word)),
      WithLp.toLp 2 fun direction =>
        jet (FixedMatterSpatialWordIndex.prepend direction
          (FixedMatterSpatialWordIndex.self word)))
  map_add' first second := by
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro direction
      rfl
  map_smul' parameter jet := by
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro direction
      rfl

def fixedMatterSpatialFirstJetOfWordCLM
    (word : List (Fin 3)) :
    FixedMatterSpatialJetCarrier (word.length + 1) →L[ℝ]
      MatterCoordinateSpatialJetCarrier :=
  ⟨fixedMatterSpatialFirstJetOfWordLinear word,
    (fixedMatterSpatialFirstJetOfWordLinear word
      ).continuous_of_finiteDimensional⟩

@[simp] theorem fixedMatterSpatialFirstJetOfWordCLM_apply
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) :
    fixedMatterSpatialFirstJetOfWordCLM word
        (fixedMatterSpatialJetAt (word.length + 1) field point) =
      matterCoordinateSpatialJetAt
        (fixedSpatialWordDerivative word field) point := by
  apply Prod.ext
  · simp [fixedMatterSpatialFirstJetOfWordCLM,
      fixedMatterSpatialFirstJetOfWordLinear,
      fixedMatterSpatialJetAt, matterCoordinateSpatialJetAt]
  · apply PiLp.ext
    intro direction
    simp [fixedMatterSpatialFirstJetOfWordCLM,
      fixedMatterSpatialFirstJetOfWordLinear,
      fixedMatterSpatialJetAt, matterCoordinateSpatialJetAt]
    rfl

/-- Insert one coordinate vector into the temporal derivative slot. -/
private def fixedMatterTemporalFirstJetInjectionLinear :
    MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateFirstJetCarrier where
  toFun velocity :=
    (0, WithLp.toLp 2 (Fin.cases velocity (fun _ => 0)))
  map_add' first second := by
    apply Prod.ext
    · simp
    · apply PiLp.ext
      intro direction
      refine Fin.cases ?_ (fun _ => ?_) direction
      · rfl
      · simp
  map_smul' parameter jet := by
    apply Prod.ext
    · simp
    · apply PiLp.ext
      intro direction
      refine Fin.cases ?_ (fun _ => ?_) direction
      · rfl
      · simp

def fixedMatterTemporalFirstJetInjectionCLM :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateFirstJetCarrier :=
  ⟨fixedMatterTemporalFirstJetInjectionLinear,
    fixedMatterTemporalFirstJetInjectionLinear.continuous_of_finiteDimensional⟩

def fixedMatterTemporalForcingFirstJetCLM
    (order : ℕ)
    (point : BasePoint)
    (forcing : FixedMatterSpatialJetCarrier order →L[ℝ]
      MatterCoordinateCarrier) :
    FixedMatterSpatialJetCarrier (order + 1) →L[ℝ]
      MatterCoordinateFirstJetCarrier :=
  fixedMatterTemporalFirstJetInjectionCLM.comp
    ((-fixedEvolutionTemporalPrincipalInverseCoordinateCLM point).comp
      (forcing.comp (fixedMatterSpatialJetLowerCLM order)))

theorem fixedMatterTemporalForcingFirstJetCLM_contDiff_infty
    (order : ℕ)
    (forcing : BasePoint →
      FixedMatterSpatialJetCarrier order →L[ℝ] MatterCoordinateCarrier)
    (forcingSmooth : ContDiff ℝ ∞ forcing) :
    ContDiff ℝ ∞ (fun point =>
      fixedMatterTemporalForcingFirstJetCLM order point (forcing point)) := by
  unfold fixedMatterTemporalForcingFirstJetCLM
  exact contDiff_const.clm_comp
    (fixedEvolutionTemporalPrincipalInverseCoordinateCLM_contDiff_infty.neg
      |>.clm_comp (forcingSmooth.clm_comp contDiff_const))

/-- The complete first jet of a selected commuted field, with its temporal
component generated by the forced mother-action equation. -/
def fixedMatterForcedFirstJetOfWordCLM
    (word : List (Fin 3))
    (point : BasePoint)
    (forcing : FixedMatterSpatialJetCarrier word.length →L[ℝ]
      MatterCoordinateCarrier) :
    FixedMatterSpatialJetCarrier (word.length + 1) →L[ℝ]
      MatterCoordinateFirstJetCarrier :=
  (fixedOnShellFirstJetCLM point).comp
      (fixedMatterSpatialFirstJetOfWordCLM word) +
    fixedMatterTemporalForcingFirstJetCLM word.length point forcing

theorem fixedMatterForcedFirstJetOfWordCLM_contDiff_infty
    (word : List (Fin 3))
    (forcing : BasePoint →
      FixedMatterSpatialJetCarrier word.length →L[ℝ]
        MatterCoordinateCarrier)
    (forcingSmooth : ContDiff ℝ ∞ forcing) :
    ContDiff ℝ ∞ (fun point =>
      fixedMatterForcedFirstJetOfWordCLM word point (forcing point)) := by
  unfold fixedMatterForcedFirstJetOfWordCLM
  exact
    (fixedOnShellFirstJetCLM_contDiff_infty.clm_comp contDiff_const).add
      (fixedMatterTemporalForcingFirstJetCLM_contDiff_infty
        word.length forcing forcingSmooth)

@[simp] theorem fixedMatterForcedFirstJetOfWordCLM_fst
    (word : List (Fin 3))
    (point : BasePoint)
    (forcing : FixedMatterSpatialJetCarrier word.length →L[ℝ]
      MatterCoordinateCarrier)
    (jet : FixedMatterSpatialJetCarrier (word.length + 1)) :
    (fixedMatterForcedFirstJetOfWordCLM word point forcing jet).1 =
      jet (FixedMatterSpatialWordIndex.castSucc
        (FixedMatterSpatialWordIndex.self word)) := by
  simp [fixedMatterForcedFirstJetOfWordCLM,
    fixedMatterTemporalForcingFirstJetCLM,
    fixedMatterTemporalFirstJetInjectionCLM,
    fixedMatterTemporalFirstJetInjectionLinear,
    fixedMatterSpatialFirstJetOfWordCLM,
    fixedMatterSpatialFirstJetOfWordLinear]

@[simp] theorem fixedMatterForcedFirstJetOfWordCLM_zero
    (word : List (Fin 3))
    (point : BasePoint)
    (forcing : FixedMatterSpatialJetCarrier word.length →L[ℝ]
      MatterCoordinateCarrier)
    (jet : FixedMatterSpatialJetCarrier (word.length + 1)) :
    (fixedMatterForcedFirstJetOfWordCLM word point forcing jet).2
        (0 : LorentzianIndex) =
      fixedOnShellTemporalVelocityCLM point
          (fixedMatterSpatialFirstJetOfWordCLM word jet) -
        fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
          (forcing (fixedMatterSpatialJetLowerCLM word.length jet)) := by
  change fixedOnShellTemporalVelocityCLM point
        (fixedMatterSpatialFirstJetOfWordCLM word jet) +
      -fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
        (forcing (fixedMatterSpatialJetLowerCLM word.length jet)) = _
  rw [sub_eq_add_neg]

@[simp] theorem fixedMatterForcedFirstJetOfWordCLM_succ
    (word : List (Fin 3))
    (point : BasePoint)
    (forcing : FixedMatterSpatialJetCarrier word.length →L[ℝ]
      MatterCoordinateCarrier)
    (jet : FixedMatterSpatialJetCarrier (word.length + 1))
    (direction : Fin 3) :
    (fixedMatterForcedFirstJetOfWordCLM word point forcing jet).2
        direction.succ =
      jet (FixedMatterSpatialWordIndex.prepend direction
        (FixedMatterSpatialWordIndex.self word)) := by
  simp [fixedMatterForcedFirstJetOfWordCLM,
    fixedMatterTemporalForcingFirstJetCLM,
    fixedMatterTemporalFirstJetInjectionCLM,
    fixedMatterTemporalFirstJetInjectionLinear,
    fixedMatterSpatialFirstJetOfWordCLM,
    fixedMatterSpatialFirstJetOfWordLinear]

/-- One source-coefficient directional changed-read, as a linear operator on
the complete first jet. -/
def fixedMatterActionCoefficientDirectionalCLM
    (point : BasePoint)
    (direction : LorentzianIndex) :
    MatterCoordinateFirstJetCarrier →L[ℝ] MatterCoordinateCarrier :=
  (fderiv ℝ fixedMatterFirstJetActionCLM point)
    (coordinateDirection direction)

theorem fixedMatterActionCoefficientDirectionalCLM_contDiff_infty
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun point => fixedMatterActionCoefficientDirectionalCLM point direction) := by
  unfold fixedMatterActionCoefficientDirectionalCLM
  exact
    (fixedMatterFirstJetActionCLM_contDiff_infty.fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const

theorem fixedMatterActionCoefficientDirectionalCLM_apply
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fixedMatterActionCoefficientDirectionalCLM point direction
        (matterCoordinateFirstJetAt field point) =
      fixedMatterFirstCommutatorForcing field direction point := by
  have coefficientDifferentiable :
      DifferentiableAt ℝ fixedMatterFirstJetActionCLM point :=
    (fixedMatterFirstJetActionCLM_contDiff_infty.differentiable (by simp)
      ).differentiableAt
  have constantDifferentiable : DifferentiableAt ℝ
      (fun _ : BasePoint => matterCoordinateFirstJetAt field point) point :=
    differentiableAt_const _
  have applyDerivative := fderiv_clm_apply coefficientDifferentiable
    constantDifferentiable
  have constantFDeriv :
      fderiv ℝ (fun _ : BasePoint => matterCoordinateFirstJetAt field point)
        point = 0 :=
    fderiv_const_apply (matterCoordinateFirstJetAt field point)
  have evaluated := congrArg
    (fun derivative : BasePoint →L[ℝ] MatterCoordinateCarrier =>
      derivative (coordinateDirection direction)) applyDerivative
  rw [constantFDeriv] at evaluated
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply] at evaluated
  calc
    fixedMatterActionCoefficientDirectionalCLM point direction
        (matterCoordinateFirstJetAt field point) =
        fieldDirectionalDerivative
          (fun candidate => fixedMatterFirstJetActionCLM candidate
            (matterCoordinateFirstJetAt field point)) point direction := by
      unfold fixedMatterActionCoefficientDirectionalCLM
        fieldDirectionalDerivative
      exact evaluated.symm
    _ = fixedMatterCoefficientChangedReadCLM point
        (matterCoordinateFirstJetAt field point) direction :=
      fixedMatterFirstJetActionCLM_directionalDerivative point
        (matterCoordinateFirstJetAt field point) direction
    _ = fixedMatterFirstCommutatorForcing field direction point := by
      rfl

/-- On an exact mother-action solution, the generated forced first-jet read is
the actual first jet of the selected commuted field. -/
theorem fixedMatterForcedFirstJetOfWordCLM_apply_of_actionZero
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field)
    (actionZero : ∀ point,
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point = 0)
    (point : BasePoint)
    (forcing : FixedMatterSpatialJetCarrier word.length →L[ℝ]
      MatterCoordinateCarrier)
    (forcingRead : forcing (fixedMatterSpatialJetAt word.length field point) =
      fixedMatterAllOrderCommutedForcing word field point) :
    fixedMatterForcedFirstJetOfWordCLM word point forcing
        (fixedMatterSpatialJetAt (word.length + 1) field point) =
      matterCoordinateFirstJetAt
        (fixedSpatialWordDerivative word field) point := by
  apply Prod.ext
  · rw [fixedMatterForcedFirstJetOfWordCLM_fst]
    simp [fixedMatterSpatialJetAt, matterCoordinateFirstJetAt]
  · apply PiLp.ext
    intro direction
    refine Fin.cases ?_ (fun spatial => ?_) direction
    · rw [fixedMatterForcedFirstJetOfWordCLM_zero,
        fixedMatterSpatialFirstJetOfWordCLM_apply,
        fixedMatterSpatialJetLowerCLM_apply, forcingRead]
      have derivativeSmooth : ContDiff ℝ ∞
          (fixedSpatialWordDerivative word field) :=
        fixedSpatialWordDerivative_contDiff_infty word field fieldSmooth
      rw [fixedOnShellTemporalVelocityCLM_spatialJetAt
        (fixedSpatialWordDerivative word field) point
        ((derivativeSmooth.differentiable (by simp)).differentiableAt)]
      have defect :=
        fixedSpatialWordDerivative_temporalVolterraDefect_of_actionZero
          word field fieldSmooth actionZero point
      change
        StageNineDiracDualFormNativeCauchySafeMatterVolterra.cauchySafeMatterVolterraVelocity
            fixedP506L0CauchySafeMatterGalerkinInputActual
            (fun candidate => matterCoordinateEquiv.symm
              (fixedSpatialWordDerivative word field candidate)) point -
          fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
            (fixedMatterAllOrderCommutedForcing word field point) =
        fieldDirectionalDerivative
          (fixedSpatialWordDerivative word field) point 0
      rw [sub_eq_add_neg]
      rw [← defect]
      abel
    · rw [fixedMatterForcedFirstJetOfWordCLM_succ]
      simp [fixedMatterSpatialJetAt, matterCoordinateFirstJetAt]
      rfl

/-- The all-order coefficient forcing is one source-owned linear read of the
complete spatial jet.  Its recursion differentiates the previous operator,
shifts the spatial jet, and applies the single first-order changed-read to the
mother-action-generated forced first jet. -/
def fixedMatterAllOrderForcingJetCLM :
    (word : List (Fin 3)) → BasePoint →
      FixedMatterSpatialJetCarrier word.length →L[ℝ]
        MatterCoordinateCarrier
  | [] => fun _ => 0
  | direction :: tail => fun point =>
      (fixedMatterAllOrderForcingJetCLM tail point).comp
          (fixedMatterSpatialJetDerivativeCLM tail.length direction) +
        ((fderiv ℝ (fixedMatterAllOrderForcingJetCLM tail) point
            (coordinateDirection direction.succ)).comp
          (fixedMatterSpatialJetLowerCLM tail.length)) +
        (fixedMatterActionCoefficientDirectionalCLM point direction.succ
          ).comp
          (fixedMatterForcedFirstJetOfWordCLM tail point
            (fixedMatterAllOrderForcingJetCLM tail point))

@[simp] theorem fixedMatterAllOrderForcingJetCLM_nil
    (point : BasePoint) :
    fixedMatterAllOrderForcingJetCLM [] point = 0 :=
  rfl

@[simp] theorem fixedMatterAllOrderForcingJetCLM_cons
    (direction : Fin 3)
    (tail : List (Fin 3))
    (point : BasePoint) :
    fixedMatterAllOrderForcingJetCLM (direction :: tail) point =
      (fixedMatterAllOrderForcingJetCLM tail point).comp
          (fixedMatterSpatialJetDerivativeCLM tail.length direction) +
        ((fderiv ℝ (fixedMatterAllOrderForcingJetCLM tail) point
            (coordinateDirection direction.succ)).comp
          (fixedMatterSpatialJetLowerCLM tail.length)) +
        (fixedMatterActionCoefficientDirectionalCLM point direction.succ
          ).comp
          (fixedMatterForcedFirstJetOfWordCLM tail point
            (fixedMatterAllOrderForcingJetCLM tail point)) :=
  rfl

theorem fixedMatterAllOrderForcingJetCLM_contDiff_infty
    (word : List (Fin 3)) :
    ContDiff ℝ ∞ (fixedMatterAllOrderForcingJetCLM word) := by
  induction word with
  | nil =>
      simp only [fixedMatterAllOrderForcingJetCLM]
      exact contDiff_const
  | cons direction tail inductionHypothesis =>
      simp only [fixedMatterAllOrderForcingJetCLM]
      have derivativeSmooth : ContDiff ℝ ∞ (fun point =>
          fderiv ℝ (fixedMatterAllOrderForcingJetCLM tail) point
            (coordinateDirection direction.succ)) :=
        (inductionHypothesis.fderiv_right (m := ∞) (by simp)).clm_apply
          contDiff_const
      exact
        (inductionHypothesis.clm_comp contDiff_const).add
          (derivativeSmooth.clm_comp contDiff_const) |>.add
        ((fixedMatterActionCoefficientDirectionalCLM_contDiff_infty
          direction.succ).clm_comp
          (fixedMatterForcedFirstJetOfWordCLM_contDiff_infty tail
            (fixedMatterAllOrderForcingJetCLM tail) inductionHypothesis))

/-- Correctness of the unified prolongation: on every smooth mother-action
solution, the finite spatial-jet operator reads exactly the recursively
generated all-order coefficient forcing. -/
theorem fixedMatterAllOrderForcingJetCLM_apply_of_actionZero
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field)
    (actionZero : ∀ point,
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point = 0)
    (point : BasePoint) :
    fixedMatterAllOrderForcingJetCLM word point
        (fixedMatterSpatialJetAt word.length field point) =
      fixedMatterAllOrderCommutedForcing word field point := by
  induction word generalizing point with
  | nil =>
      simp [fixedMatterAllOrderForcingJetCLM,
        fixedMatterAllOrderCommutedForcing]
  | cons direction tail inductionHypothesis =>
      let jetField : BasePoint → FixedMatterSpatialJetCarrier tail.length :=
        fixedMatterSpatialJetAt tail.length field
      have tailPointwise :
          (fun candidate =>
            fixedMatterAllOrderForcingJetCLM tail candidate
              (jetField candidate)) =
            fixedMatterAllOrderCommutedForcing tail field := by
        funext candidate
        exact inductionHypothesis candidate
      have operatorDifferentiable : DifferentiableAt ℝ
          (fixedMatterAllOrderForcingJetCLM tail) point :=
        (fixedMatterAllOrderForcingJetCLM_contDiff_infty tail
          |>.differentiable (by simp)).differentiableAt
      have jetDifferentiable : DifferentiableAt ℝ jetField point :=
        (fixedMatterSpatialJetAt_contDiff_infty tail.length field fieldSmooth
          |>.differentiable (by simp)).differentiableAt
      have derivativeEq :
          fieldDirectionalDerivative
              (fun candidate =>
                fixedMatterAllOrderForcingJetCLM tail candidate
                  (jetField candidate)) point direction.succ =
            fieldDirectionalDerivative
              (fixedMatterAllOrderCommutedForcing tail field)
              point direction.succ := by
        rw [tailPointwise]
      unfold fieldDirectionalDerivative at derivativeEq
      rw [fderiv_clm_apply operatorDifferentiable jetDifferentiable]
        at derivativeEq
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply] at derivativeEq
      have jetDerivativeEq := fixedMatterSpatialJetAt_directionalDerivative
        tail.length field fieldSmooth point direction
      unfold fieldDirectionalDerivative at jetDerivativeEq
      change
        (fderiv ℝ jetField point) (coordinateDirection direction.succ) = _
        at jetDerivativeEq
      rw [jetDerivativeEq] at derivativeEq
      change
        fixedMatterAllOrderForcingJetCLM tail point
            (fixedMatterSpatialJetDerivativeCLM tail.length direction
              (fixedMatterSpatialJetAt (tail.length + 1) field point)) +
          (fderiv ℝ (fixedMatterAllOrderForcingJetCLM tail) point
              (coordinateDirection direction.succ))
            (fixedMatterSpatialJetAt tail.length field point) =
        fieldDirectionalDerivative
          (fixedMatterAllOrderCommutedForcing tail field)
          point direction.succ at derivativeEq
      rw [← fixedMatterSpatialJetLowerCLM_apply tail.length field point]
        at derivativeEq
      have forcedFirstJetEq :=
        fixedMatterForcedFirstJetOfWordCLM_apply_of_actionZero
          tail field fieldSmooth actionZero point
          (fixedMatterAllOrderForcingJetCLM tail point)
          (inductionHypothesis point)
      have changedReadEq :
          fixedMatterActionCoefficientDirectionalCLM point direction.succ
              (fixedMatterForcedFirstJetOfWordCLM tail point
                (fixedMatterAllOrderForcingJetCLM tail point)
                (fixedMatterSpatialJetAt (tail.length + 1) field point)) =
            fixedMatterFirstCommutatorForcing
              (fixedSpatialWordDerivative tail field) direction.succ point := by
        rw [forcedFirstJetEq]
        exact fixedMatterActionCoefficientDirectionalCLM_apply
          (fixedSpatialWordDerivative tail field) point direction.succ
      simp only [List.length_cons, fixedMatterAllOrderForcingJetCLM_cons,
        add_apply,
        ContinuousLinearMap.comp_apply,
        fixedMatterAllOrderCommutedForcing]
      rw [derivativeEq, changedReadEq]

/-- A single source constant controls every forcing operator through one
finite hierarchy order on a compact Cauchy box. -/
theorem exists_fixedMatterAllOrderForcingJetCLMBoundOnBox
    (order : ℕ)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ word : FixedMatterSpatialWordIndex order,
        ∀ time ∈ Icc timeStart timeEnd,
          ∀ space ∈ Icc a b,
            ‖fixedMatterAllOrderForcingJetCLM word.toList
              (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have individualBound (word : FixedMatterSpatialWordIndex order) :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ time ∈ Icc timeStart timeEnd,
          ∀ space ∈ Icc a b,
            ‖fixedMatterAllOrderForcingJetCLM word.toList
              (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C := by
    have operatorContinuous : Continuous (fun point :
        ℝ × DiracMatterSpatialCoordinates =>
        fixedMatterAllOrderForcingJetCLM word.toList
          (diracMatterSpacetimeCoordinatePoint point.1 point.2)) :=
      (fixedMatterAllOrderForcingJetCLM_contDiff_infty word.toList
        ).continuous.comp
        diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous
    obtain ⟨C, bound⟩ :=
      carrierCompact.exists_bound_of_continuousOn operatorContinuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro time timeMem space spaceMem
    exact (bound (time, space) ⟨timeMem, spaceMem⟩).trans
      (le_max_left _ _)
  choose C CNonnegative CSpec using individualBound
  refine ⟨∑ word : FixedMatterSpatialWordIndex order, C word,
    Finset.sum_nonneg fun word _ => CNonnegative word, ?_⟩
  intro word time timeMem space spaceMem
  exact (CSpec word time timeMem space spaceMem).trans
    (Finset.single_le_sum (fun candidate _ => CNonnegative candidate)
      (Finset.mem_univ word))

/-- The exact all-order coefficient forcing is therefore bounded by the
complete spatial jet, uniformly for every word through the selected order. -/
theorem exists_fixedMatterAllOrderCommutedForcingSpatialJetBoundOnBox
    (order : ℕ)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ word : FixedMatterSpatialWordIndex order,
        ∀ (field : BasePoint → MatterCoordinateCarrier),
          ContDiff ℝ ∞ field →
          (∀ point,
            matterCoordinateFirstOrderOperator
              fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
              field point = 0) →
          ∀ time ∈ Icc timeStart timeEnd,
            ∀ space ∈ Icc a b,
              ‖fixedMatterAllOrderCommutedForcing word.toList field
                (diracMatterSpacetimeCoordinatePoint time space)‖ ≤
              C * ‖fixedMatterSpatialJetAt word.toList.length field
                (diracMatterSpacetimeCoordinatePoint time space)‖ := by
  obtain ⟨C, CNonnegative, bound⟩ :=
    exists_fixedMatterAllOrderForcingJetCLMBoundOnBox
      order timeStart timeEnd a b
  refine ⟨C, CNonnegative, ?_⟩
  intro word field fieldSmooth actionZero time timeMem space spaceMem
  let point := diracMatterSpacetimeCoordinatePoint time space
  rw [← fixedMatterAllOrderForcingJetCLM_apply_of_actionZero
    word.toList field fieldSmooth actionZero point]
  exact
    ((fixedMatterAllOrderForcingJetCLM word.toList point).le_opNorm
      (fixedMatterSpatialJetAt word.toList.length field point)).trans
      (mul_le_mul_of_nonneg_right
        (bound word time timeMem space spaceMem) (norm_nonneg _))

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderJetProlongation
