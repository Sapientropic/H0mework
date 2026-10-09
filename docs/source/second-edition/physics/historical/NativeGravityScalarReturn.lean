import CanonicalSourcePropagationNativeActionJets
import CanonicalPreparationOriginalJacobi

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineDiracDualYukawaLocalSpinDensity StageNineDiracDualFormNativeMotherAction
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation Stage9C.Material.SpinPair
open DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
attribute [local irreducible] SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual
open PreparationVacuumMixedFieldReturn PreparationVacuumOriginalGreenFeedback
open Filter
open scoped BigOperators Topology ContDiff

abbrev NativeJetIndex := Option (Fin 4) × Fin 289

def nativeJetBasis (index : NativeJetIndex) : NativeFirstJet :=
  match index.1 with
  | none => (Pi.single index.2 1, 0)
  | some mu => (0, Pi.single mu (Pi.single index.2 1))

def nativeJetCoefficient (jet : NativeFirstJet) (index : NativeJetIndex) : ℝ :=
  match index.1 with
  | none => jet.1 index.2
  | some mu => jet.2 mu index.2

def retainedGradient (mu : Fin 4) (field : Fin 289) : Prop :=
  field.val < 9 ∨
    (9 ≤ field.val ∧ field.val < 57 ∧ (field.val-9)/12 ≠ mu.val) ∨
    (73 ≤ field.val ∧ field.val < 97) ∨
    (121 ≤ field.val ∧ field.val < 145 ∧ (field.val-121)/6 ≠ mu.val)
instance (mu : Fin 4) (field : Fin 289) : Decidable (retainedGradient mu field) := by
  unfold retainedGradient
  infer_instance

def restrictGradient (mu : Fin 4) (f : Field289) : Field289 :=
  fun field => if retainedGradient mu field then f field else 0

def effectiveJetLinear : NativeFirstJet →ₗ[ℝ] NativeFirstJet where
  toFun jet := (jet.1, fun mu => restrictGradient mu (jet.2 mu))
  map_add' x y := by
    apply Prod.ext
    · rfl
    funext mu field
    change (if retainedGradient mu field then x.2 mu field + y.2 mu field else 0) =
      (if retainedGradient mu field then x.2 mu field else 0) +
      (if retainedGradient mu field then y.2 mu field else 0)
    split_ifs <;> simp
  map_smul' r x := by
    apply Prod.ext
    · rfl
    funext mu field
    change (if retainedGradient mu field then r * x.2 mu field else 0) =
      r * (if retainedGradient mu field then x.2 mu field else 0)
    split_ifs <;> simp

def effectiveJet : NativeFirstJet →L[ℝ] NativeFirstJet := effectiveJetLinear.toContinuousLinearMap

private theorem retained_scalar (mu : Fin 4) (j : Fin 9) : retainedGradient mu (scalarSlot j) := by
  exact Or.inl j.isLt

private theorem retained_primal (mu : Fin 4) (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    retainedGradient mu (primalSlot part spin color) := by
  simp only [retainedGradient, primalSlot, Fin.val_mk]
  omega

private theorem retained_gauge (mu nu : Fin 4) (a : Fin 12) :
    retainedGradient mu (gaugeSlot nu a) ↔ nu ≠ mu := by
  simp only [retainedGradient, gaugeSlot, Fin.val_mk]
  rw [Fin.ne_iff_vne]
  omega

private theorem retained_lorentz (mu nu : Fin 4) (a : Fin 6) :
    retainedGradient mu (lorentzSlot nu a) ↔ nu ≠ mu := by
  simp only [retainedGradient, lorentzSlot, Fin.val_mk]
  rw [Fin.ne_iff_vne]
  omega

private theorem restrictGradient_scalar (mu : Fin 4) (f : Field289) :
    fieldScalar (restrictGradient mu f) = fieldScalar f := by
  simp only [fieldScalar, restrictGradient, if_pos (retained_scalar mu _)]

private theorem restrictGradient_primal (mu : Fin 4) (f : Field289) (spin : Fin 4) (color : Fin 3) :
    fieldPrimalComplex (restrictGradient mu f) spin color = fieldPrimalComplex f spin color := by
  simp only [fieldPrimalComplex, fieldPrimal, restrictGradient, if_pos (retained_primal mu _ _ _)]

private theorem restrictGradient_gauge (mu nu : Fin 4) (different : nu ≠ mu) (f : Field289) :
    fieldGauge (restrictGradient mu f) nu = fieldGauge f nu := by
  simp only [fieldGauge, restrictGradient, if_pos ((retained_gauge mu nu _).mpr different)]

private theorem restrictGradient_lorentz (mu nu : Fin 4) (different : nu ≠ mu) (f : Field289) :
    fieldLorentz (restrictGradient mu f) nu = fieldLorentz f nu := by
  funext a
  simp only [fieldLorentz, restrictGradient, if_pos ((retained_lorentz mu nu _).mpr different)]

private theorem lorentzInsertion_value (f : Field289) (nu a b : Fin 4) :
    lorentzInsertionCLM f nu a b = lorentzSkewConnectionOfBivectorOneForm (fieldLorentz f) nu a b := rfl

private theorem restrictGradient_lorentzSkew (mu nu : Fin 4) (different : nu ≠ mu)
    (f : Field289) (a b : Fin 4) :
    lorentzInsertionCLM (restrictGradient mu f) nu a b = lorentzInsertionCLM f nu a b := by
  simp only [lorentzInsertion_value, lorentzSkewConnectionOfBivectorOneForm, loweredLorentzBivectorMatrix]
  have same := restrictGradient_lorentz mu nu different f
  have value (pair : Fin 6) := congrArg (fun v : Fin 6 → ℝ => v pair) same
  simp only [value]

private theorem pair_distinct (pair : Fin 6) : pairFirst pair ≠ pairSecond pair := by
  fin_cases pair <;> decide

theorem effectiveJet_value (jet : NativeFirstJet) : (effectiveJet jet).1 = jet.1 := rfl
theorem effectiveJet_gradient (jet : NativeFirstJet) (mu : Fin 4) :
    (effectiveJet jet).2 mu = restrictGradient mu (jet.2 mu) := rfl

theorem nativeJetPoint_effective (jet : NativeFirstJet) :
    nativeJetPoint (effectiveJet jet) = nativeJetPoint jet := by
  apply StageNineContinuumPointField.ext
  · simp only [nativeJetPoint, effectiveJet_value]
  · funext internal pair
    unfold nativeJetPoint nativeGravityCurvature
    dsimp only
    simp only [effectiveJet_value, effectiveJet_gradient]
    rw [restrictGradient_lorentzSkew _ _ (Ne.symm (pair_distinct pair)),
      restrictGradient_lorentzSkew _ _ (pair_distinct pair)]
  · simp only [nativeJetPoint, effectiveJet_value]
  · simp only [nativeJetPoint, effectiveJet_value]
  · funext pair
    unfold nativeJetPoint nativeGaugeCurvature
    dsimp only
    simp only [effectiveJet_value, effectiveJet_gradient]
    rw [restrictGradient_gauge _ _ (Ne.symm (pair_distinct pair)),
      restrictGradient_gauge _ _ (pair_distinct pair)]
  · simp only [nativeJetPoint, effectiveJet_value]
  · simp only [nativeJetPoint, effectiveJet_value]
  · funext mu
    unfold nativeJetPoint nativeScalarCovariant
    dsimp only
    simp only [effectiveJet_value, effectiveJet_gradient, restrictGradient_scalar]
  · simp only [nativeJetPoint, nativeMatterValue, effectiveJet_value]
  · funext mu
    unfold nativeJetPoint nativeMatterCovariant rotatedPrimalDerivative
    dsimp only
    simp only [effectiveJet_value, effectiveJet_gradient, restrictGradient_primal,
      nativeMatterValue]
  · simp only [nativeJetPoint, nativeDualValue, effectiveJet_value]

theorem nativeJetDensity_effective (jet : NativeFirstJet) :
    nativeJetDensity (effectiveJet jet) = nativeJetDensity jet := by
  rw [nativeJetDensity_generated, nativeJetDensity_generated, nativeJetPoint_effective]

def retainedJet (index : NativeJetIndex) : Prop :=
  match index.1 with
  | none => True
  | some mu => retainedGradient mu index.2
instance (index : NativeJetIndex) : Decidable (retainedJet index) := by
  unfold retainedJet
  cases index.1 <;> infer_instance

private theorem finite_order_two : (2 : ℕ∞ω) ≤ ∞ := by
  change ((2:ℕ∞):ℕ∞ω) ≤ ((⊤:ℕ∞):ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

private theorem eventually_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (h : ContDiffAt ℝ ∞ f 0) :
    ∀ᶠ x in 𝓝 (0:E), DifferentiableAt ℝ f x := by
  have smooth : ContDiffAt ℝ 1 f 0 := h.of_le (by simp)
  exact (smooth.eventually (by simp)).mono fun _ hx => hx.differentiableAt (by simp)

private theorem second_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (C : E →L[ℝ] E) (smooth : ContDiffAt ℝ ∞ f 0)
    (same : ∀ x, f (C x) = f x) (a b : E) :
    fderiv ℝ (fderiv ℝ f) 0 (C a) (C b) = fderiv ℝ (fderiv ℝ f) 0 a b := by
  have near := eventually_differentiable f smooth
  have atC : ∀ᶠ x in 𝓝 (0:E), DifferentiableAt ℝ f (C x) := by
    have target : ∀ᶠ y in 𝓝 (C 0), DifferentiableAt ℝ f y := by simpa only [map_zero] using near
    exact C.continuous.continuousAt.eventually target
  have firstEq : (fun x : E => fderiv ℝ f (C x) (C b)) =ᶠ[𝓝 0]
      fun x => fderiv ℝ f x b := by
    filter_upwards [atC] with x hx
    have chain := hx.hasFDerivAt.comp x C.hasFDerivAt
    have values : (fun y => f (C y)) = f := funext same
    change HasFDerivAt (fun y => f (C y)) _ x at chain
    rw [values] at chain
    have value := congrArg (fun T : E →L[ℝ] ℝ => T b) chain.fderiv
    exact value.symm
  have H := (smooth.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have Hc : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (C 0) := by
    simpa only [map_zero] using H
  have left := (Hc.comp 0 C.hasFDerivAt).clm_apply (hasFDerivAt_const (C b) (0:E))
  have right := H.clm_apply (hasFDerivAt_const b (0:E))
  have eqDeriv := firstEq.fderiv_eq (𝕜 := ℝ)
  have eqValue := congrArg (fun T : E →L[ℝ] ℝ => T a) eqDeriv
  change HasFDerivAt (fun x : E => fderiv ℝ f (C x) (C b)) _ 0 at left
  rw [left.fderiv, right.fderiv] at eqValue
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply, zero_apply, add_zero, zero_add, map_zero, Function.comp_apply] using eqValue

theorem nativeHessian_effective (a b : NativeFirstJet) :
    nativeHessian (effectiveJet a) (effectiveJet b) = nativeHessian a b :=
  second_pullback nativeJetDensity effectiveJet nativeJetDensity_smooth nativeJetDensity_effective a b

def effectiveJetIndices : Finset NativeJetIndex := Finset.univ.filter retainedJet

theorem effectiveJetIndices_card : effectiveJetIndices.card = 637 := by
  decide +kernel

theorem nativeJet_reconstruction (jet : NativeFirstJet) :
    jet = ∑ index : NativeJetIndex, nativeJetCoefficient jet index • nativeJetBasis index := by
  apply Prod.ext
  · funext field
    simp [Fintype.sum_prod_type, Fintype.sum_option, nativeJetCoefficient, nativeJetBasis,
      Pi.single_apply, Finset.sum_apply, Prod.fst_sum]
  · funext mu field
    simp [Fintype.sum_prod_type, Fintype.sum_option, nativeJetCoefficient, nativeJetBasis,
      Pi.single_apply, Finset.sum_apply, Prod.snd_sum]

def nativeDensityBlock : Fin 4 → NativeFirstJet → ℝ :=
  ![fun jet => StageNineFormNativeMotherAction.generatedFormNativeGravityBFDensity (nativeJetPoint jet) +
      StageNineFormNativeMotherAction.generatedFormNativeGravityConstraintDensity (nativeJetPoint jet),
    fun jet => StageNineFormNativeMotherAction.generatedFormNativeGaugeDensityAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) (nativeJetPoint jet),
    fun jet => StageNineScalarLocalSpinDensity.generatedDensitizedContinuumScalarDensity
      positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet),
    fun jet => StageNineDiracKineticLocalSpinDensity.generatedDensitizedContinuumMatterKineticDensity
      positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)]

theorem nativeDensityBlock_smooth (block : Fin 4) : ContDiffAt ℝ ∞ (nativeDensityBlock block) 0 := by
  fin_cases block
  · exact nativeGravityDensity_smooth.contDiffAt
  · exact nativeGaugeDensity_smooth
  · exact nativeScalarDensity_smooth
  · exact nativeDiracKinetic_smooth

theorem nativeJetDensity_blocks : nativeJetDensity = fun jet => ∑ block : Fin 4, nativeDensityBlock block jet := by
  funext jet
  rw [nativeJetDensity_generated]
  unfold StageNineDiracDualFormNativeMotherAction.generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    StageNineDiracDualFormNativeMotherAction.generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [nativeYukawaDensity_zero]
  simp only [Fin.sum_univ_four]
  simp [nativeDensityBlock]
  ring

def nativeBlockHessian (block : Fin 4) : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (nativeDensityBlock block)) 0

theorem nativeHessian_blocks (a b : NativeFirstJet) :
    nativeHessian a b = ∑ block : Fin 4, nativeBlockHessian block a b := by
  have source := iteratedFDeriv_fun_sum_apply (n := 2) (𝕜 := ℝ)
    (u := Finset.univ) (fun block _ => (nativeDensityBlock_smooth block).of_le finite_order_two)
  have evaluated := congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => NativeFirstJet) ℝ => D ![a,b]) source
  rw [←nativeJetDensity_blocks] at evaluated
  simp only [sum_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at evaluated
  exact evaluated

open StageNineTopologicalFourFormPairing StageNineTopologicalGravityCurvatureVariancePairing
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open Stage9C.Reduction
open StageNineBlockwiseConstitutive

def gravityCurvatureQuadratic (jet : NativeFirstJet) : PhysicalBivector := fun internal pair =>
  minkowskiInternalSign (pairFirst internal) * ∑ middle : Fin 4,
    (lorentzInsertionCLM jet.1 (pairFirst pair) (pairFirst internal) middle *
      lorentzInsertionCLM jet.1 (pairSecond pair) middle (pairSecond internal) -
    lorentzInsertionCLM jet.1 (pairSecond pair) (pairFirst internal) middle *
      lorentzInsertionCLM jet.1 (pairFirst pair) middle (pairSecond internal))

def gravityCurvatureLinear (jet : NativeFirstJet) : PhysicalBivector :=
  nativeGravityCurvature jet - holonomicGravityCurvature actual 0 - gravityCurvatureQuadratic jet

theorem nativeGravityCurvature_ray (jet : NativeFirstJet) (r : ℝ) :
    nativeGravityCurvature (r • jet) = holonomicGravityCurvature actual 0 +
      r • gravityCurvatureLinear jet + r^2 • gravityCurvatureQuadratic jet := by
  funext internal pair
  simp only [nativeGravityCurvature, gravityCurvatureLinear, gravityCurvatureQuadratic,
    Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, smul_eq_mul, Pi.sub_apply, Pi.add_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Fin.sum_univ_four]
  ring

def coframeWedgeMixed (first second : LorentzianCoframe) : PhysicalBivector :=
  coframeWedge (first+second) - coframeWedge first - coframeWedge second

theorem coframeWedge_ray (first second : LorentzianCoframe) (r : ℝ) :
    coframeWedge (first+r • second) = coframeWedge first +
      r • coframeWedgeMixed first second + r^2 • coframeWedge second := by
  funext internal pair
  simp only [coframeWedge, coframeWedgeMixed, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

def nativeSimplicityFirst (jet : NativeFirstJet) : PhysicalBivector :=
  gravityInternalDualEquiv (coframeWedgeMixed (actual.coframe 0) (fieldCoframe jet.1))

def nativeSimplicitySecond (jet : NativeFirstJet) : PhysicalBivector := physicalIIPlusBivector (fieldCoframe jet.1)

theorem physicalIIPlusBivector_ray (first second : LorentzianCoframe) (r : ℝ) :
    physicalIIPlusBivector (first+r • second) = physicalIIPlusBivector first +
      r • gravityInternalDualEquiv (coframeWedgeMixed first second) +
      r^2 • physicalIIPlusBivector second := by
  change gravityInternalDualEquiv (coframeWedge (first+r • second)) = _
  rw [coframeWedge_ray, map_add, map_add, map_smul, map_smul]
  rfl

def nativeGravityPolynomial (jet : NativeFirstJet) : Fin 4 → ℝ :=
  let B0 := actual.gravityAuxiliary 0
  let B1 := fieldGravityB jet.1
  let L0 := actual.gravitySimplicityMultiplier 0
  let L1 := fieldMultiplier jet.1
  let R0 := holonomicGravityCurvature actual 0
  let R1 := gravityCurvatureLinear jet
  let R2 := gravityCurvatureQuadratic jet
  let residual0 := B0-physicalIIPlusBivector (actual.coframe 0)
  let residual1 := B1-nativeSimplicityFirst jet
  ![gravityTopologicalBFCoefficient B0 R0 - (1/2:ℝ)*gravityTopologicalWedgeCoefficient B0 (gravityInternalDualEquiv B0) +
      gravityTopologicalWedgeCoefficient L0 residual0,
    gravityTopologicalBFCoefficient B1 R0 + gravityTopologicalBFCoefficient B0 R1 -
      (1/2:ℝ)*(gravityTopologicalWedgeCoefficient B1 (gravityInternalDualEquiv B0) +
        gravityTopologicalWedgeCoefficient B0 (gravityInternalDualEquiv B1)) +
      gravityTopologicalWedgeCoefficient L1 residual0 + gravityTopologicalWedgeCoefficient L0 residual1,
    gravityTopologicalBFCoefficient B1 R1 + gravityTopologicalBFCoefficient B0 R2 -
      (1/2:ℝ)*gravityTopologicalWedgeCoefficient B1 (gravityInternalDualEquiv B1) +
      gravityTopologicalWedgeCoefficient L1 residual1 - gravityTopologicalWedgeCoefficient L0 (nativeSimplicitySecond jet),
    gravityTopologicalBFCoefficient B1 R2 - gravityTopologicalWedgeCoefficient L1 (nativeSimplicitySecond jet)]

private theorem wedge_sub_right (a b c : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient a (b-c) =
      gravityTopologicalWedgeCoefficient a b - gravityTopologicalWedgeCoefficient a c := by
  rw [sub_eq_add_neg, gravityTopologicalWedgeCoefficient_add_right,
    show -c=(-1:ℝ) • c by simp, gravityTopologicalWedgeCoefficient_smul_right]
  ring

theorem nativeGravityDensity_polynomial (jet : NativeFirstJet) (r : ℝ) :
    nativeDensityBlock 0 (r • jet) = nativeGravityPolynomial jet 0 + r*nativeGravityPolynomial jet 1 +
      r^2*nativeGravityPolynomial jet 2 + r^3*nativeGravityPolynomial jet 3 := by
  change StageNineFormNativeMotherAction.generatedFormNativeGravityBFDensity (nativeJetPoint (r • jet)) +
    StageNineFormNativeMotherAction.generatedFormNativeGravityConstraintDensity (nativeJetPoint (r • jet)) = _
  unfold StageNineFormNativeMotherAction.generatedFormNativeGravityBFDensity
    StageNineFormNativeMotherAction.generatedFormNativeGravityConstraintDensity generatedGravitySimplicityResidual
  simp only [nativeJetPoint, Prod.fst_smul, fieldGravityB, fieldMultiplier, fieldCoframe, Pi.smul_apply, smul_eq_mul]
  change gravityTopologicalBFCoefficient (actual.gravityAuxiliary 0+r • fieldGravityB jet.1)
      (nativeGravityCurvature (r • jet)) - (1/2:ℝ)*gravityTopologicalWedgeCoefficient
      (actual.gravityAuxiliary 0+r • fieldGravityB jet.1)
      (gravityInternalDualEquiv (actual.gravityAuxiliary 0+r • fieldGravityB jet.1)) +
    gravityTopologicalWedgeCoefficient (actual.gravitySimplicityMultiplier 0+r • fieldMultiplier jet.1)
      (actual.gravityAuxiliary 0+r • fieldGravityB jet.1 - physicalIIPlusBivector (actual.coframe 0+r • fieldCoframe jet.1)) = _
  rw [nativeGravityCurvature_ray, physicalIIPlusBivector_ray]
  simp only [gravityTopologicalBFCoefficient_add_left, gravityTopologicalBFCoefficient_add_right,
    gravityTopologicalBFCoefficient_smul_left, gravityTopologicalBFCoefficient_smul_right,
    gravityTopologicalWedgeCoefficient_add_left, gravityTopologicalWedgeCoefficient_add_right,
    gravityTopologicalWedgeCoefficient_smul_left, gravityTopologicalWedgeCoefficient_smul_right,
    wedge_sub_right, map_add, map_smul]
  simp [nativeGravityPolynomial, nativeSimplicityFirst, nativeSimplicitySecond]
  simp only [wedge_sub_right]
  ring

private theorem cubic_first (c : Fin 4 → ℝ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => c 0+t*c 1+t^2*c 2+t^3*c 3)
      (c 1+2*r*c 2+3*r^2*c 3) r := by
  have generated := (((hasDerivAt_id r).mul_const (c 1)).const_add (c 0) |>.add
    ((hasDerivAt_pow 2 r).mul_const (c 2))).add ((hasDerivAt_pow 3 r).mul_const (c 3))
  convert! generated using 1
  simp only [Nat.cast_ofNat]
  ring

private theorem cubic_first_second (c : Fin 4 → ℝ) :
    HasDerivAt (fun r : ℝ => c 1+2*r*c 2+3*r^2*c 3) (2*c 2) 0 := by
  have generated := ((((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const (c 2)).const_add (c 1)).add
    (((hasDerivAt_pow 2 (0:ℝ)).const_mul 3).mul_const (c 3))
  convert! generated using 1
  norm_num

private theorem cubic_second_coefficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (smooth : ContDiffAt ℝ ∞ f 0) (jet : E) (c : Fin 4 → ℝ)
    (value : ∀ r : ℝ, f (r • jet) = c 0+r*c 1+r^2*c 2+r^3*c 3) :
    fderiv ℝ (fderiv ℝ f) 0 jet jet = 2*c 2 := by
  have line (r : ℝ) : HasDerivAt (fun t : ℝ => t • jet) jet r :=
    by simpa using (hasDerivAt_id r).smul_const jet
  have line0 : HasDerivAt (fun t : ℝ => t • jet) jet 0 := line 0
  have near := eventually_differentiable f smooth
  have atLine : ∀ᶠ r in 𝓝 (0:ℝ), DifferentiableAt ℝ f (r • jet) := by
    have continuousLine : Tendsto (fun r : ℝ => r • jet) (𝓝 0) (𝓝 (0:E)) := by
      simpa only [ContinuousAt, zero_smul] using line0.continuousAt
    exact continuousLine.eventually near
  have firstEq : (fun r : ℝ => fderiv ℝ f (r • jet) jet) =ᶠ[𝓝 0]
      fun r => c 1+2*r*c 2+3*r^2*c 3 := by
    filter_upwards [atLine] with r hr
    have original := hr.hasFDerivAt.comp_hasDerivAt r (line r)
    have polynomial := cubic_first c r
    have functions : (fun t : ℝ => f (t • jet)) = fun t => c 0+t*c 1+t^2*c 2+t^3*c 3 :=
      funext value
    change HasDerivAt (fun t : ℝ => f (t • jet)) _ r at original
    rw [functions] at original
    exact original.unique polynomial
  have sourceH := (smooth.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have sourceLine := sourceH.comp_hasDerivAt_of_eq 0 line0 (by simp)
  have sourceRead := sourceLine.clm_apply (hasDerivAt_const (0:ℝ) jet)
  have target := (cubic_first_second c).congr_of_eventuallyEq firstEq
  have unique := sourceRead.unique target
  simpa only [zero_smul, map_zero, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] using unique

theorem nativeGravitySecond_generated (jet : NativeFirstJet) :
    nativeBlockHessian 0 jet jet = 2*nativeGravityPolynomial jet 2 :=
  cubic_second_coefficient (nativeDensityBlock 0) (nativeDensityBlock_smooth 0)
    jet (nativeGravityPolynomial jet) (nativeGravityDensity_polynomial jet)

/-- The literal source-coordinate quadratic records; every coefficient is a generated
source amplitude.  Their native-action identity is checked below. -/
def literalGravityTerms : List (NativeJetIndex × NativeJetIndex × ℝ) := [
  ((none,57),(none,62),1),((none,57),(none,67),1),((none,57),(none,72),1),((none,57),(none,202),1),((none,57),(none,209),1),((none,57),(none,216),1),
  ((none,58),(none,61),-1),((none,58),(none,207),1),((none,58),(none,212),-1),((none,59),(none,65),-1),((none,59),(none,201),-1),((none,59),(none,211),1),
  ((none,60),(none,69),-1),((none,60),(none,200),1),((none,60),(none,205),-1),((none,61),(none,192),-1),((none,61),(none,197),1),((none,62),(none,67),-lapse),
  ((none,62),(none,72),-lapse),((none,62),(none,188),1),((none,62),(none,195),1),((none,62),(none,202),lapse),((none,63),(none,66),lapse),((none,63),(none,187),-1),
  ((none,63),(none,203),lapse),((none,64),(none,70),lapse),((none,64),(none,193),-1),((none,64),(none,204),lapse),((none,65),(none,186),1),((none,65),(none,196),-1),
  ((none,66),(none,182),-1),((none,66),(none,208),lapse),((none,67),(none,72),-lapse),((none,67),(none,181),1),((none,67),(none,195),1),((none,67),(none,209),lapse),
  ((none,68),(none,71),lapse),((none,68),(none,194),-1),((none,68),(none,210),lapse),((none,69),(none,185),-1),((none,69),(none,190),1),((none,70),(none,183),-1),
  ((none,70),(none,214),lapse),((none,71),(none,189),-1),((none,71),(none,215),lapse),((none,72),(none,181),1),((none,72),(none,188),1),((none,72),(none,216),lapse),
  ((none,121),(none,138),1),((none,121),(none,143),-1),((none,121),(none,156),spinScale),((none,121),(none,161),-spinScale),((none,122),(none,132),-1),((none,122),(none,142),1),
  ((none,122),(none,150),-spinScale),((none,122),(none,160),spinScale),((none,123),(none,131),1),((none,123),(none,136),-1),((none,123),(none,149),spinScale),((none,123),(none,154),-spinScale),
  ((none,124),(none,135),1),((none,124),(none,140),-1),((none,124),(none,174),spinScale),((none,124),(none,179),-spinScale),((none,125),(none,129),-1),((none,125),(none,139),1),
  ((none,125),(none,168),-spinScale),((none,125),(none,178),spinScale),((none,126),(none,128),1),((none,126),(none,133),-1),((none,126),(none,167),spinScale),((none,126),(none,172),-spinScale),
  ((none,127),(none,134),-lapse),((none,127),(none,141),-lapse),((none,127),(none,152),-spinScale),((none,127),(none,159),-spinScale),((none,128),(none,133),lapse),((none,128),(none,146),spinScale),
  ((none,129),(none,139),lapse),((none,129),(none,147),spinScale),((none,130),(none,137),lapse),((none,130),(none,144),lapse),((none,130),(none,170),-spinScale),((none,130),(none,177),-spinScale),
  ((none,131),(none,136),-lapse),((none,131),(none,164),spinScale),((none,132),(none,142),-lapse),((none,132),(none,165),spinScale),((none,133),(none,151),spinScale),((none,134),(none,141),-lapse),
  ((none,134),(none,145),-spinScale),((none,134),(none,159),-spinScale),((none,135),(none,140),lapse),((none,135),(none,153),spinScale),((none,136),(none,169),spinScale),((none,137),(none,144),lapse),
  ((none,137),(none,163),-spinScale),((none,137),(none,177),-spinScale),((none,138),(none,143),-lapse),((none,138),(none,171),spinScale),((none,139),(none,157),spinScale),((none,140),(none,158),spinScale),
  ((none,141),(none,145),-spinScale),((none,141),(none,152),-spinScale),((none,142),(none,175),spinScale),((none,143),(none,176),spinScale),((none,144),(none,163),-spinScale),((none,144),(none,170),-spinScale),
  ((some 0,127),(none,148),1),((some 1,121),(none,148),-1),((some 0,128),(none,154),1),((some 1,122),(none,154),-1),((some 0,129),(none,160),1),((some 1,123),(none,160),-1),
  ((some 0,130),(none,166),1),((some 1,124),(none,166),-1),((some 0,131),(none,172),1),((some 1,125),(none,172),-1),((some 0,132),(none,178),1),((some 1,126),(none,178),-1),
  ((some 0,133),(none,149),1),((some 2,121),(none,149),-1),((some 0,134),(none,155),1),((some 2,122),(none,155),-1),((some 0,135),(none,161),1),((some 2,123),(none,161),-1),
  ((some 0,136),(none,167),1),((some 2,124),(none,167),-1),((some 0,137),(none,173),1),((some 2,125),(none,173),-1),((some 0,138),(none,179),1),((some 2,126),(none,179),-1),
  ((some 0,139),(none,150),1),((some 3,121),(none,150),-1),((some 0,140),(none,156),1),((some 3,122),(none,156),-1),((some 0,141),(none,162),1),((some 3,123),(none,162),-1),
  ((some 0,142),(none,168),1),((some 3,124),(none,168),-1),((some 0,143),(none,174),1),((some 3,125),(none,174),-1),((some 0,144),(none,180),1),((some 3,126),(none,180),-1),
  ((some 2,139),(none,145),1),((some 3,133),(none,145),-1),((some 2,140),(none,151),1),((some 3,134),(none,151),-1),((some 2,141),(none,157),1),((some 3,135),(none,157),-1),
  ((some 2,142),(none,163),1),((some 3,136),(none,163),-1),((some 2,143),(none,169),1),((some 3,137),(none,169),-1),((some 2,144),(none,175),1),((some 3,138),(none,175),-1),
  ((some 3,127),(none,146),1),((some 1,139),(none,146),-1),((some 3,128),(none,152),1),((some 1,140),(none,152),-1),((some 3,129),(none,158),1),((some 1,141),(none,158),-1),
  ((some 3,130),(none,164),1),((some 1,142),(none,164),-1),((some 3,131),(none,170),1),((some 1,143),(none,170),-1),((some 3,132),(none,176),1),((some 1,144),(none,176),-1),
  ((some 1,133),(none,147),1),((some 2,127),(none,147),-1),((some 1,134),(none,153),1),((some 2,128),(none,153),-1),((some 1,135),(none,159),1),((some 2,129),(none,159),-1),
  ((some 1,136),(none,165),1),((some 2,130),(none,165),-1),((some 1,137),(none,171),1),((some 2,131),(none,171),-1),((some 1,138),(none,177),1),((some 2,132),(none,177),-1),
  ((none,145),(none,166),1),((none,145),(none,184),-1),((none,146),(none,167),1),((none,146),(none,185),-1),((none,147),(none,168),1),((none,147),(none,186),-1),
  ((none,148),(none,163),1),((none,148),(none,181),-1),((none,149),(none,164),1),((none,149),(none,182),-1),((none,150),(none,165),1),((none,150),(none,183),-1),
  ((none,151),(none,172),1),((none,151),(none,190),-1),((none,152),(none,173),1),((none,152),(none,191),-1),((none,153),(none,174),1),((none,153),(none,192),-1),
  ((none,154),(none,169),1),((none,154),(none,187),-1),((none,155),(none,170),1),((none,155),(none,188),-1),((none,156),(none,171),1),((none,156),(none,189),-1),
  ((none,157),(none,178),1),((none,157),(none,196),-1),((none,158),(none,179),1),((none,158),(none,197),-1),((none,159),(none,180),1),((none,159),(none,198),-1),
  ((none,160),(none,175),1),((none,160),(none,193),-1),((none,161),(none,176),1),((none,161),(none,194),-1),((none,162),(none,177),1),((none,162),(none,195),-1),
  ((none,163),(none,202),1),((none,164),(none,203),1),((none,165),(none,204),1),((none,166),(none,199),1),((none,167),(none,200),1),((none,168),(none,201),1),
  ((none,169),(none,208),1),((none,170),(none,209),1),((none,171),(none,210),1),((none,172),(none,205),1),((none,173),(none,206),1),((none,174),(none,207),1),
  ((none,175),(none,214),1),((none,176),(none,215),1),((none,177),(none,216),1),((none,178),(none,211),1),((none,179),(none,212),1),((none,180),(none,213),1)]

def literalGravityQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalGravityTerms.map fun term => term.2.2 * nativeJetCoefficient jet term.1 *
    nativeJetCoefficient jet term.2.1).sum

private theorem actualGravityAuxiliary (point : BasePoint) :
    actual.gravityAuxiliary point = physicalIIPlusBivector (Stage9C.Dynamics.Homogeneous.homogeneousCoframe lapse) := by
  unfold actual algebraicCartanReduction
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary]
  rfl

theorem nativeGravityQuadratic_literal (jet : NativeFirstJet) :
    nativeGravityPolynomial jet 2 = literalGravityQuadratic jet := by
  simp [nativeGravityPolynomial, Matrix.cons_val_two,
    nativeSimplicityFirst, nativeSimplicitySecond, gravityCurvatureLinear, gravityCurvatureQuadratic,
    nativeGravityCurvature, actual_gravityConnection, actual_gravityCurvature,
    actual_gravitySimplicityMultiplier, actual_coframe, actualGravityAuxiliary,
    Stage9C.Dynamics.Homogeneous.homogeneousGravityReaction,
    Stage9C.Dynamics.Homogeneous.homogeneousCurvature_components,
    Stage9C.Dynamics.Homogeneous.homogeneousConnection,
    Stage9C.Dynamics.Homogeneous.homogeneousContorsion,
    Stage9C.Dynamics.Homogeneous.homogeneousCoframe,
    gravityTopologicalBFCoefficient_eq_mixed, gravityTopologicalMixedWedgeCoefficient,
    gravityTopologicalWedgeCoefficient, orientedTwoFormWedgeCoefficient_explicit,
    physicalIIPlusBivector, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalDualEquiv, gravityInternalDualLinear,
    StageNineHolonomicGravityCurvatureVarianceNormalization.gravityInternalPairVarianceNormalization,
    coframeWedgeMixed, coframeWedge, lorentzianTwoFormSign, minkowskiInternalSign,
    lorentzInsertion_value, lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix, orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, Fin.sum_univ_four, Fin.sum_univ_six,
    fieldCoframe, fieldLorentz, fieldGravityB, fieldMultiplier, coframeSlot,
    lorentzSlot, gravitySlot, multiplierSlot, Matrix.diagonal_apply,
    literalGravityQuadratic, literalGravityTerms, nativeJetCoefficient]
  ring_nf
  simp only [spinScale_sq]
  ring

def nativeCoefficientLinear (index : NativeJetIndex) : NativeFirstJet →ₗ[ℝ] ℝ where
  toFun jet := nativeJetCoefficient jet index
  map_add' x y := by rcases index with ⟨d,i⟩; cases d <;> rfl
  map_smul' r x := by rcases index with ⟨d,i⟩; cases d <;> rfl

def nativeCoefficientCLM (index : NativeJetIndex) : NativeFirstJet →L[ℝ] ℝ :=
  (nativeCoefficientLinear index).toContinuousLinearMap

def literalGravityHessian : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  (literalGravityTerms.map fun term => term.2.2 •
    ((nativeCoefficientCLM term.1).smulRight (nativeCoefficientCLM term.2.1) +
      (nativeCoefficientCLM term.2.1).smulRight (nativeCoefficientCLM term.1))).sum

theorem literalGravityHessian_value (a b : NativeFirstJet) :
    literalGravityHessian a b = (literalGravityTerms.map fun term => term.2.2 *
      (nativeJetCoefficient a term.1 * nativeJetCoefficient b term.2.1 +
        nativeJetCoefficient a term.2.1 * nativeJetCoefficient b term.1)).sum := by
  unfold literalGravityHessian
  have sumValue (terms : List (NativeJetIndex × NativeJetIndex × ℝ)) :
      ((terms.map fun term => term.2.2 •
        ((nativeCoefficientCLM term.1).smulRight (nativeCoefficientCLM term.2.1) +
          (nativeCoefficientCLM term.2.1).smulRight (nativeCoefficientCLM term.1))).sum) a b =
      (terms.map fun term => term.2.2 *
        (nativeJetCoefficient a term.1 * nativeJetCoefficient b term.2.1 +
          nativeJetCoefficient a term.2.1 * nativeJetCoefficient b term.1)).sum := by
    induction terms with
    | nil => simp
    | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons, add_apply, ih, smul_apply, smul_eq_mul,
        ContinuousLinearMap.smulRight_apply]
      rfl
  exact sumValue literalGravityTerms

private theorem literalGravityHessian_diagonal (jet : NativeFirstJet) :
    literalGravityHessian jet jet = 2*literalGravityQuadratic jet := by
  rw [literalGravityHessian_value]
  unfold literalGravityQuadratic
  rw [←List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro term _
  ring

private theorem literalGravityHessian_symmetric (a b : NativeFirstJet) :
    literalGravityHessian a b = literalGravityHessian b a := by
  rw [literalGravityHessian_value, literalGravityHessian_value]
  congr 1
  apply List.map_congr_left
  intro term _
  ring

theorem nativeBlockHessian_symmetric (block : Fin 4) (a b : NativeFirstJet) :
    nativeBlockHessian block a b = nativeBlockHessian block b a :=
  ((nativeDensityBlock_smooth block).isSymmSndFDerivAt (by simpa using finite_order_two)).eq _ _

private theorem symmetric_diagonal_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (bSym : ∀ x y, B x y=B y x)
    (cSym : ∀ x y, C x y=C y x) (diag : ∀ x, B x x=C x x) (a b : E) :
    B a b = C a b := by
  have h := diag (a+b)
  simp only [map_add, add_apply] at h
  rw [bSym b a, cSym b a, diag a, diag b] at h
  linarith

theorem nativeGravityHessian_literal (a b : NativeFirstJet) :
    nativeBlockHessian 0 a b = literalGravityHessian a b := by
  apply symmetric_diagonal_unique _ _ (nativeBlockHessian_symmetric 0) literalGravityHessian_symmetric
  intro jet
  rw [nativeGravitySecond_generated, nativeGravityQuadratic_literal, literalGravityHessian_diagonal]

private theorem square_factor_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (smooth : ContDiffAt ℝ ∞ f 0) (jet : E)
    (g : ℝ → ℝ) (gSmooth : ContDiffAt ℝ ∞ g 0)
    (value : ∀ r : ℝ, f (r • jet) = r^2*g r) :
    fderiv ℝ (fderiv ℝ f) 0 jet jet = 2*g 0 := by
  have line (r : ℝ) : HasDerivAt (fun t : ℝ => t • jet) jet r := by
    simpa using (hasDerivAt_id r).smul_const jet
  have nearF := eventually_differentiable f smooth
  have nearG := eventually_differentiable g gSmooth
  have atLine : ∀ᶠ r in 𝓝 (0:ℝ), DifferentiableAt ℝ f (r • jet) := by
    have continuousLine : Tendsto (fun r : ℝ => r • jet) (𝓝 0) (𝓝 (0:E)) := by
      simpa only [ContinuousAt, zero_smul] using (line 0).continuousAt
    exact continuousLine.eventually nearF
  have firstEq : (fun r : ℝ => fderiv ℝ f (r • jet) jet) =ᶠ[𝓝 0]
      fun r => 2*r*g r+r^2*deriv g r := by
    filter_upwards [atLine,nearG] with r hf hg
    have original := hf.hasFDerivAt.comp_hasDerivAt r (line r)
    have square := (hasDerivAt_pow 2 r).mul hg.hasDerivAt
    have functions : (fun t : ℝ => f (t • jet)) = fun t => t^2*g t := funext value
    change HasDerivAt (fun t : ℝ => f (t • jet)) _ r at original
    rw [functions] at original
    have eq := original.unique square
    convert! eq using 1
    norm_num
  have gFirst := gSmooth.differentiableAt (by simp) |>.hasDerivAt
  have gSecond := (gSmooth.derivWithin (m := ∞) (by simp)).differentiableAt (by simp) |>.hasDerivAt
  have derivative := (((hasDerivAt_id (0:ℝ)).const_mul 2).mul gFirst).add
    ((hasDerivAt_pow 2 (0:ℝ)).mul gSecond)
  have sourceH := (smooth.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have sourceLine := sourceH.comp_hasDerivAt_of_eq 0 (line 0) (by simp)
  have sourceRead := sourceLine.clm_apply (hasDerivAt_const (0:ℝ) jet)
  have target := derivative.congr_of_eventuallyEq firstEq
  have unique := sourceRead.unique target
  simpa using unique

open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineP286GaugeConnectionVariationDensity
open StageNineScalarLocalSpinDensity StageNineScalarPointwiseEquation StageNineP286GaugeConnectionActionVariation
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def nativeScalarAction := scalarP286ActionBilinear.toContinuousBilinearMap

private theorem scalarActionCoordinate (a : P286LieBlockData) (v : P286CoordinateCarrier)
    (phi : ScalarCoordinateCarrier) :
    scalarMotherLieAction (p286LieBlockEmbed (a+p286CoordinateEquiv.symm v)) phi =
      nativeScalarAction (p286CoordinateEquiv a+v) phi := by
  change scalarMotherLieAction (p286LieBlockEmbed (a+p286CoordinateEquiv.symm v)) phi =
    scalarMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv a+v))) phi
  rw [map_add, LinearEquiv.symm_apply_apply]

private theorem nativeScalarCovariant_coordinate (jet : NativeFirstJet) (mu : Fin 4) :
    nativeScalarCovariant jet mu = fieldScalar (jet.2 mu) +
      nativeScalarAction (p286CoordinateEquiv (actual.gaugeConnection 0 mu) + gaugeCoordinateCLM mu jet.1)
        (actual.scalar 0+fieldScalar jet.1) :=
  congrArg (fun v : ScalarCoordinateCarrier => fieldScalar (jet.2 mu)+v)
    (scalarActionCoordinate (actual.gaugeConnection 0 mu) (gaugeCoordinateCLM mu jet.1)
      (actual.scalar 0+fieldScalar jet.1))

private theorem nativeScalarCovariant_zero : nativeScalarCovariant 0 = 0 := by
  have zeroSignal : affineSignal (0:NativeFirstJet) = fun _ => 0 := by
    funext point
    simp [affineSignal]
  have generated := nativeScalarCovariant_generated (0:NativeFirstJet)
  rw [zeroSignal, nativeConfiguration_zero, actual_scalarCovariantDerivative_zero] at generated
  exact generated.symm

def scalarCovariantQuadratic (jet : NativeFirstJet) (mu : Fin 4) : ScalarCoordinateCarrier :=
  nativeScalarAction (gaugeCoordinateCLM mu jet.1) (fieldScalar jet.1)

def scalarCovariantLinear (jet : NativeFirstJet) (mu : Fin 4) : ScalarCoordinateCarrier :=
  fieldScalar (jet.2 mu) + nativeScalarAction (p286CoordinateEquiv (actual.gaugeConnection 0 mu)) (fieldScalar jet.1) +
    nativeScalarAction (gaugeCoordinateCLM mu jet.1) (actual.scalar 0)

private theorem bilinear_ray {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (B : V →L[ℝ] W →L[ℝ] W)
    (a da : V) (v dv : W) (r : ℝ) (background : B a v=0) :
    B (a+r • da) (v+r • dv) = r • (B a dv+B da v)+r^2 • B da dv := by
  simp only [map_add, map_smul, add_apply, smul_apply, background,
    zero_add, smul_smul, smul_add, pow_two]
  module

theorem nativeScalarCovariant_ray (jet : NativeFirstJet) (r : ℝ) (mu : Fin 4) :
    nativeScalarCovariant (r • jet) mu = r • scalarCovariantLinear jet mu + r^2 • scalarCovariantQuadratic jet mu := by
  have background : nativeScalarAction (p286CoordinateEquiv (actual.gaugeConnection 0 mu)) (actual.scalar 0) = 0 := by
    have source := congrArg (fun q : Fin 4 → ScalarCoordinateCarrier => q mu) nativeScalarCovariant_zero
    rw [nativeScalarCovariant_coordinate] at source
    simpa [fieldScalar, gaugeCoordinateCLM, gaugeCoordinateLinear, fieldGauge] using source
  rw [nativeScalarCovariant_coordinate]
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, fieldScalar_smul, map_smul]
  rw [bilinear_ray nativeScalarAction _ _ _ _ r background]
  simp only [scalarCovariantLinear, scalarCovariantQuadratic, smul_add]
  module

open PointwiseLorentzianCoframeJet
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

def scalarRayCore (jet : NativeFirstJet) (r : ℝ) : ℝ :=
  generatedVolumeDensity (nativeJetPoint (r • jet)) *
    ((1/2:ℝ)*∑ mu : Fin 4, ∑ nu : Fin 4,
      ((lorentzianMetricOfCoframe (nativeJetPoint (r • jet)).coframe)⁻¹ mu nu) *
      scalarCoordinatePairingRe
        (scalarCovariantLinear jet mu+r • scalarCovariantQuadratic jet mu)
        (scalarCovariantLinear jet nu+r • scalarCovariantQuadratic jet nu) -
    scalarCoordinateSquaredNorm (fieldScalar jet.1))

private theorem scalarSquaredNorm_smul (r : ℝ) (v : ScalarCoordinateCarrier) :
    scalarCoordinateSquaredNorm (r • v) = r^2*scalarCoordinateSquaredNorm v := by
  have generated := frameRelativeScalarPotential_expansion 0 0 v r
  simpa [frameRelativeScalarPotential, frameRelativeScalarGradient, scalarCoordinateRealPairing,
    RCLike.real_smul_eq_coe_smul] using generated

private theorem square_sum_factor (r : ℝ) (w q : Fin 4 → Fin 4 → ℝ) :
    (∑ mu : Fin 4, ∑ nu : Fin 4, w mu nu*(r*(r*q mu nu))) =
      r^2*(∑ mu : Fin 4, ∑ nu : Fin 4, w mu nu*q mu nu) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro nu _
  ring

theorem nativeScalarDensity_factor (jet : NativeFirstJet) (r : ℝ) :
    nativeDensityBlock 2 (r • jet) = r^2*scalarRayCore jet r := by
  change generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 0
    (nativeJetPoint (r • jet)) = _
  unfold generatedDensitizedContinuumScalarDensity generatedScalarKineticDensity generatedScalarPotential
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart]
  have potential : (nativeJetPoint (r • jet)).scalar - sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource =
      r • fieldScalar jet.1 := by
    simp only [nativeJetPoint, actual_scalar, Prod.smul_fst, fieldScalar_smul, add_sub_cancel_left]
  rw [potential, scalarSquaredNorm_smul]
  simp only [nativeJetPoint]
  simp only [nativeScalarCovariant_ray, show ∀ mu : Fin 4,
    r • scalarCovariantLinear jet mu+r^2 • scalarCovariantQuadratic jet mu =
      r • (scalarCovariantLinear jet mu+r • scalarCovariantQuadratic jet mu) by
        intro mu; rw [smul_add, smul_smul, pow_two]]
  simp only [scalarCoordinatePairingRe_real_smul_left, scalarCoordinatePairingRe_real_smul_right]
  unfold scalarRayCore
  simp only [nativeJetPoint]
  rw [square_sum_factor]
  ring

private theorem scalarRayCore_smooth (jet : NativeFirstJet) : ContDiffAt ℝ ∞ (scalarRayCore jet) 0 := by
  have line : ContDiff ℝ ∞ (fun r : ℝ => r • jet) := by fun_prop
  have volumeAt : ContDiffAt ℝ ∞ (fun j : NativeFirstJet => generatedVolumeDensity (nativeJetPoint j)) ((0:ℝ) • jet) := by
    simpa only [zero_smul] using nativeVolume_smooth
  have volume := volumeAt.comp 0 line.contDiffAt
  have coframeSmooth := nativeCoframe_smooth.comp line
  have coframeZero : (nativeJetPoint ((0:ℝ) • jet)).coframe = actual.coframe 0 := by
    simp only [zero_smul, nativeCoframe_zero]
  have metric := StageNineCoframeLocalDifferentiability.lorentzianMetric_inv_contDiffAt
    (actual.coframe 0) (actual_nondegenerate 0)
  rw [←coframeZero] at metric
  have metricRay := metric.comp (f := fun r : ℝ => (nativeJetPoint (r • jet)).coframe) 0 coframeSmooth.contDiffAt
  have direction (mu : Fin 4) : ContDiff ℝ ∞ (fun r : ℝ =>
      scalarCovariantLinear jet mu+r • scalarCovariantQuadratic jet mu) := by fun_prop
  let B := scalarCoordinatePairingReBilinear.toContinuousBilinearMap
  have pair (mu nu : Fin 4) : ContDiff ℝ ∞ (fun r : ℝ =>
      scalarCoordinatePairingRe
        (scalarCovariantLinear jet mu+r • scalarCovariantQuadratic jet mu)
        (scalarCovariantLinear jet nu+r • scalarCovariantQuadratic jet nu)) :=
    (B.contDiff.comp (direction mu)).clm_apply (direction nu)
  unfold scalarRayCore
  apply volume.mul
  apply ContDiffAt.sub _ contDiffAt_const
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro mu _
  apply ContDiffAt.sum
  intro nu _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp metricRay mu) nu).mul (pair mu nu).contDiffAt

theorem nativeScalarSecond_generated (jet : NativeFirstJet) :
    nativeBlockHessian 2 jet jet = 2*scalarRayCore jet 0 :=
  square_factor_second (nativeDensityBlock 2) (nativeDensityBlock_smooth 2) jet
    (scalarRayCore jet) (scalarRayCore_smooth jet) (nativeScalarDensity_factor jet)

open PreparationScalarCoordinates PreparationVacuumPrimitiveMatrix PreparationVacuumCoefficientBudget
open PreparationVacuumLowerClassical PreparationCoordinates
open SourceQuantumScalarChart
theorem scalarUnit_reconstruction (phi : ScalarCoordinateCarrier) :
    phi = ∑ j : Fin 70, scalarRealify phi j • scalarUnit j := by
  apply scalarRealify.injective
  ext i
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, scalarUnit_read]
  simp [Pi.single_apply, eq_comm]
def scalarActionReader (a : NativeLie) (i : Fin 70) : ScalarCoordinateCarrier →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (scalarRealify.toLinearMap.comp (scalarP286ActionBilinear a))
theorem scalarAction_originalUnit (a : Fin 12) (phi : ScalarCoordinateCarrier) (i : Fin 70) :
    scalarRealify (action phi (originalUnit a)) i =
      ∑ j : Fin 70, (originalRho a i j : ℝ)*scalarRealify phi j := by
  change scalarActionReader (originalUnit a) i phi = _
  nth_rw 1 [scalarUnit_reconstruction phi]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, RingHom.id_apply]
  apply Finset.sum_congr rfl
  intro j _
  have source := originalRho_source a i j
  change (originalRho a i j : ℝ)=scalarActionReader (originalUnit a) i (scalarUnit j) at source
  rw [←source]
  ring
def originalScalarOrbit (a : Fin 12) (i : Fin 70) : ℚ :=
  ∑ j : Fin 70, originalRho a i j*vacuumColumn j
theorem originalScalarOrbit_source (a : Fin 12) (i : Fin 70) :
    (originalScalarOrbit a i : ℝ) = scalarRealify (orbit (originalUnit a)) i := by
  change _ = scalarRealify (action vacuum (originalUnit a)) i
  rw [scalarAction_originalUnit]
  simp only [originalScalarOrbit]
  push_cast
  simp only [vacuumColumn_source]
theorem scalarInsertion_originalCoordinates (f : Field289) (i : Fin 70) :
    scalarRealify (fieldScalar f) i =
      ∑ j : Fin 9, f (scalarSlot j)*(originalScalarOrbit (originalJColumns j) i : ℝ) := by
  simp only [fieldScalar, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    originalScalarOrbit_source]
theorem scalarAction_rawCoordinates (a : NativeLie) (phi : ScalarCoordinateCarrier) (i : Fin 70) :
    scalarRealify (action phi a) i = ∑ c : Fin 12, ∑ j : Fin 70,
      rawCoordinates a c*(originalRho c i j : ℝ)*scalarRealify phi j := by
  nth_rw 1 [raw_original_expansion a]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [scalarAction_originalUnit]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem gaugeInsertion_originalCoordinates (f : Field289) (mu : Fin 4) (a : Fin 12) :
    rawCoordinates (fieldGauge f mu) a = f (gaugeSlot mu a) := by
  simp only [fieldGauge, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    originalUnit, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply, eq_comm]
def originalGaugeCoordinates (mu : Fin 4) : Fin 12 → ℝ :=
  rawCoordinates (show NativeLie from p286CoordinateEquiv (actual.gaugeConnection 0 mu))
theorem scalarCovariantLinear_originalCoordinates (jet : NativeFirstJet) (mu : Fin 4) (i : Fin 70) :
    scalarRealify (scalarCovariantLinear jet mu) i =
      scalarRealify (fieldScalar (jet.2 mu)) i +
        (∑ c : Fin 12, ∑ j : Fin 70,
          originalGaugeCoordinates mu c*(originalRho c i j : ℝ)*scalarRealify (fieldScalar jet.1) j) +
        (∑ c : Fin 12, jet.1 (gaugeSlot mu c)*(originalScalarOrbit c i : ℝ)) := by
  change scalarRealify (fieldScalar (jet.2 mu) +
    action (fieldScalar jet.1) (show NativeLie from p286CoordinateEquiv (actual.gaugeConnection 0 mu)) +
    action (actual.scalar 0) (show NativeLie from gaugeCoordinateCLM mu jet.1)) i = _
  simp only [map_add, Pi.add_apply]
  rw [scalarAction_rawCoordinates, actual_scalar]
  have vacuumAction : scalarRealify (action vacuum (fieldGauge jet.1 mu)) i =
      ∑ c : Fin 12, jet.1 (gaugeSlot mu c)*(originalScalarOrbit c i : ℝ) := by
    rw [scalarAction_rawCoordinates]
    simp only [gaugeInsertion_originalCoordinates, originalScalarOrbit, Rat.cast_sum,
      Rat.cast_mul, vacuumColumn_source]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact congrArg (fun v : ℝ => scalarRealify (fieldScalar (jet.2 mu)) i +
    (∑ c : Fin 12, ∑ j : Fin 70,
      originalGaugeCoordinates mu c*(originalRho c i j : ℝ)*scalarRealify (fieldScalar jet.1) j) +v) vacuumAction

theorem scalarPair_originalCoordinates (phi psi : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe phi psi = ∑ i : Fin 70, scalarRealify phi i*scalarRealify psi i := by
  rw [original_scalar_pairing, scalar_inner_realified]
theorem scalarSquaredNorm_originalCoordinates (phi : ScalarCoordinateCarrier) :
    scalarCoordinateSquaredNorm phi = ∑ i : Fin 70, (scalarRealify phi i)^2 := by
  rw [←scalarCoordinateRealPairing_self phi]
  change scalarCoordinatePairingRe phi phi = _
  rw [scalarPair_originalCoordinates]
  simp only [pow_two]
private theorem nativeVolume_zero : generatedVolumeDensity (nativeJetPoint 0) = lapse := by
  rw [generatedVolumeDensity, nativeCoframe_zero, actual_coframe,
    Stage9C.Dynamics.Homogeneous.homogeneousCoframe_det, abs_of_pos lapse_pos]
private theorem actualMetricInverse : (lorentzianMetricOfCoframe (actual.coframe 0))⁻¹ =
    Matrix.diagonal ![-(lapse^2)⁻¹,1,1,1] := by
  have metric : lorentzianMetricOfCoframe (actual.coframe 0) = Matrix.diagonal ![-lapse^2,1,1,1] := by
    rw [actual_coframe]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [lorentzianMetricOfCoframe, Stage9C.Dynamics.Homogeneous.homogeneousCoframe,
        minkowskiInternalMetric, Matrix.mul_apply, Matrix.diagonal_apply]
    ring
  apply Matrix.inv_eq_left_inv
  rw [metric, Matrix.diagonal_mul_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [ne_of_gt lapse_pos]
theorem scalarRayCore_originalCoordinates (jet : NativeFirstJet) :
    scalarRayCore jet 0 = lapse *
      (-(lapse^2)⁻¹/2*(∑ i : Fin 70, (scalarRealify (scalarCovariantLinear jet 0) i)^2) +
        (1/2:ℝ)*(∑ i : Fin 70, (scalarRealify (scalarCovariantLinear jet 1) i)^2) +
        (1/2:ℝ)*(∑ i : Fin 70, (scalarRealify (scalarCovariantLinear jet 2) i)^2) +
        (1/2:ℝ)*(∑ i : Fin 70, (scalarRealify (scalarCovariantLinear jet 3) i)^2) -
        (∑ i : Fin 70, (scalarRealify (fieldScalar jet.1) i)^2)) := by
  unfold scalarRayCore
  simp only [zero_smul, add_zero, nativeVolume_zero, nativeCoframe_zero, actualMetricInverse,
    scalarPair_originalCoordinates, scalarSquaredNorm_originalCoordinates]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, pow_two]
  ring_nf
  simp
def colorRawCoordinates : Fin 3 → Fin 12 → ℝ :=
  ![Pi.single 1 (1/2),Pi.single 0 (1/2),Pi.single 6 (1/2)-Pi.single 7 (1/2)]
open SourceQuantumNativeDimensions SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice
private theorem lieval_smul (r : ℝ) (x : SU3BlockLieMatrix) :
    ((r • x : SU3BlockLieMatrix) : Matrix (Fin 3) (Fin 3) ℂ) =
      r • (x : Matrix (Fin 3) (Fin 3) ℂ) := rfl
private theorem lieval_sub (x y : SU3BlockLieMatrix) :
    ((x-y : SU3BlockLieMatrix) : Matrix (Fin 3) (Fin 3) ℂ) =
      (x : Matrix (Fin 3) (Fin 3) ℂ)-(y : Matrix (Fin 3) (Fin 3) ℂ) := rfl
theorem sourceColor_originalCoordinates (g : Fin 3) :
    rawCoordinates (show NativeLie from p286CoordinateEquiv (sourceColorP286Generator g)) = colorRawCoordinates g := by
  change rawRead (show NativeLie from p286CoordinateEquiv (sourceColorP286Generator g)) = _
  unfold rawRead
  rw [nativeCoordinates_apply]
  funext i
  fin_cases g <;> fin_cases i <;>
    simp only [colorRawCoordinates, sourceColorP286Generator, p286LieBracket, suLieBracket,
      colorCartanGenerator, colorCartanRaw, colorMixingGenerator, colorMixingRaw]
  all_goals dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases,
    Fin.induction, Fin.induction.go, Prod.smul_fst, Prod.smul_snd]
  all_goals norm_num only [Matrix.mul_apply, Fin.sum_univ_three, Pi.single_apply]
  all_goals simp only [eq_mpr_eq_cast, cast_eq, lieval_smul, Matrix.smul_apply,
    lieval_sub, Matrix.sub_apply, Matrix.diagonal_apply]
  all_goals norm_num [colorMixingRaw, Pi.single_apply]
  all_goals norm_num [Fin.ext_iff]
def gaugeRawBase : Fin 4 → Fin 12 → ℝ :=
  ![0,gaugeScale • colorRawCoordinates 0,gaugeScale • colorRawCoordinates 1,gaugeScale • colorRawCoordinates 2]
theorem originalGaugeCoordinates_literal (mu : Fin 4) : originalGaugeCoordinates mu = gaugeRawBase mu := by
  unfold originalGaugeCoordinates
  rw [actual_gaugeConnection]
  fin_cases mu <;> simp [gaugePotential, gaugeRawBase, map_smul, sourceColor_originalCoordinates]
def rawOrbitColumn : Fin 12 → Fin 9 := ![0,0,0,1,2,3,4,4,5,6,7,8]
def rationalOriginalOrbit (a : Fin 12) (i : Fin 70) : ℚ :=
  if a.val < 2 then 0 else rationalO i (rawOrbitColumn a)
theorem originalScalarOrbit_code : ∀ (a : Fin 12) (i : Fin 70),
    originalScalarOrbit a i = rationalOriginalOrbit a i := by
  decide +kernel
def scalarRawContraction (a : Fin 12) (i : Fin 70) (k : Fin 9) : ℚ :=
  ∑ j : Fin 70, if rationalO j k=0 then 0 else originalRhoFast a i j*rationalO j k
def rationalScalarPauli : Fin 3 → Fin 70 → Fin 9 → ℚ :=
  ![(fun i k => (1/2)*scalarRawContraction 1 i k),
    (fun i k => (1/2)*scalarRawContraction 0 i k),
    (fun i k => (1/2)*(scalarRawContraction 6 i k-scalarRawContraction 7 i k))]
def literalScalarPauli (g : Fin 3) (i : Fin 70) (k : Fin 9) : ℚ :=
  if i=13 ∨ i=15 then (![Pi.single 1 (1/2),Pi.single 0 (1/2),Pi.single 3 (-1/2)] : Fin 3 → Fin 9 → ℚ) g k else
  if i=23 ∨ i=25 then (![Pi.single 3 (-1/2),Pi.single 2 (1/2),Pi.single 1 (-1/2)] : Fin 3 → Fin 9 → ℚ) g k else
  if i=48 ∨ i=50 then (![Pi.single 0 (1/2),Pi.single 1 (-1/2),Pi.single 2 (-1/2)] : Fin 3 → Fin 9 → ℚ) g k else
  if i=58 ∨ i=60 then (![Pi.single 2 (-1/2),Pi.single 3 (-1/2),Pi.single 0 (-1/2)] : Fin 3 → Fin 9 → ℚ) g k else 0
theorem scalarPauli_code : ∀ (g : Fin 3) (i : Fin 70) (k : Fin 9),
    rationalScalarPauli g i k=literalScalarPauli g i k := by
  decide +kernel
theorem scalarInsertion_literal (f : Field289) (i : Fin 70) :
    scalarRealify (fieldScalar f) i = ∑ k : Fin 9, f (scalarSlot k)*(rationalO i k : ℝ) := by
  rw [scalarInsertion_originalCoordinates]
  simp_rw [originalScalarOrbit_code]
  apply Finset.sum_congr rfl
  intro k _
  fin_cases k <;> rfl
private theorem scalarRawContraction_source (a : Fin 12) (i : Fin 70) (k : Fin 9) :
    (scalarRawContraction a i k : ℝ)=∑ j : Fin 70, (originalRho a i j : ℝ)*(rationalO j k : ℝ) := by
  simp_rw [originalRho_fast]
  unfold scalarRawContraction
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · simp [h]
  · exact Rat.cast_mul _ _
private theorem scalarRawContraction_field (a : Fin 12) (f : Field289) (i : Fin 70) :
    (∑ j : Fin 70, (originalRho a i j : ℝ)*scalarRealify (fieldScalar f) j) =
      ∑ k : Fin 9, f (scalarSlot k)*(scalarRawContraction a i k : ℝ) := by
  simp_rw [scalarInsertion_literal, Finset.mul_sum, scalarRawContraction_source]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
def scalarPauliBase : Fin 4 → Fin 70 → Fin 9 → ℚ :=
  ![0,literalScalarPauli 0,literalScalarPauli 1,literalScalarPauli 2]
theorem scalarCovariantLinear_literal (jet : NativeFirstJet) (mu : Fin 4) (i : Fin 70) :
    scalarRealify (scalarCovariantLinear jet mu) i =
      (∑ k : Fin 9, jet.2 mu (scalarSlot k)*(rationalO i k : ℝ)) +
      gaugeScale*(∑ k : Fin 9, jet.1 (scalarSlot k)*(scalarPauliBase mu i k : ℝ)) +
      (∑ c : Fin 12, jet.1 (gaugeSlot mu c)*(rationalOriginalOrbit c i : ℝ)) := by
  rw [scalarCovariantLinear_originalCoordinates, scalarInsertion_literal]
  simp_rw [originalScalarOrbit_code]
  congr 1
  congr 1
  simp_rw [mul_assoc, ←Finset.mul_sum, scalarRawContraction_field]
  rw [originalGaugeCoordinates_literal]
  fin_cases mu <;> simp [gaugeRawBase, scalarPauliBase, ←scalarPauli_code, rationalScalarPauli,
    colorRawCoordinates, Pi.single_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

def scalarPauliNineMatrix (mu : Fin 4) (r c : Fin 9) : ℚ :=
  if (mu=1 ∧ r=0 ∧ c=3) ∨ (mu=1 ∧ r=2 ∧ c=1) ∨ (mu=2 ∧ r=2 ∧ c=0) ∨ (mu=2 ∧ r=3 ∧ c=1) ∨ (mu=3 ∧ r=0 ∧ c=1) ∨ (mu=3 ∧ r=3 ∧ c=2) then -1/2 else
  if (mu=1 ∧ r=1 ∧ c=2) ∨ (mu=1 ∧ r=3 ∧ c=0) ∨ (mu=2 ∧ r=0 ∧ c=2) ∨ (mu=2 ∧ r=1 ∧ c=3) ∨ (mu=3 ∧ r=1 ∧ c=0) ∨ (mu=3 ∧ r=2 ∧ c=3) then 1/2 else 0

private theorem scalarPauliNine_code : ∀ (mu : Fin 4) (i : Fin 70) (j : Fin 9),
    scalarPauliBase mu i j = ∑ k : Fin 9, scalarPauliNineMatrix mu k j*rationalO i k := by decide +kernel
private theorem scalarPauliNine_field (v : Fin 9 → ℝ) (mu : Fin 4) (i : Fin 70) :
    (∑ j : Fin 9, v j*(scalarPauliBase mu i j : ℝ)) =
      ∑ k : Fin 9, (∑ j : Fin 9, v j*(scalarPauliNineMatrix mu k j : ℝ))*(rationalO i k : ℝ) := by
  have source (j : Fin 9) : (scalarPauliBase mu i j : ℝ)=
      ∑ k : Fin 9, (scalarPauliNineMatrix mu k j : ℝ)*(rationalO i k : ℝ) := by
    exact_mod_cast scalarPauliNine_code mu i j
  simp_rw [source, Finset.mul_sum]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _; ring
private theorem scalarGaugeNine_field (v : Fin 12 → ℝ) (i : Fin 70) :
    (∑ c : Fin 12, v c*(rationalOriginalOrbit c i : ℝ)) =
      ∑ k : Fin 9, (if k=4 then v 6+v 7 else v (originalJColumns k))*(rationalO i k : ℝ) := by
  norm_num [Fin.sum_univ_succ, rationalOriginalOrbit, rawOrbitColumn, originalJColumns]; simp only [Fin.reduceSucc, Fin.reduceEq, Fin.isValue, Fin.reduceFinMk, if_true, if_false]; ring

def scalarShift (jet : NativeFirstJet) (mu : Fin 4) (k : Fin 9) : ℝ :=
  jet.2 mu (scalarSlot k)+(if k=4 then jet.1 (gaugeSlot mu 6)+jet.1 (gaugeSlot mu 7)
    else jet.1 (gaugeSlot mu (originalJColumns k)))+
      gaugeScale*(∑ j : Fin 9, jet.1 (scalarSlot j)*(scalarPauliNineMatrix mu k j : ℝ))
private theorem scalarShift_read (jet : NativeFirstJet) (mu : Fin 4) (i : Fin 70) :
    scalarRealify (scalarCovariantLinear jet mu) i = ∑ k : Fin 9, scalarShift jet mu k*(rationalO i k : ℝ) := by
  rw [scalarCovariantLinear_literal, scalarPauliNine_field, scalarGaugeNine_field]
  simp only [scalarShift, add_mul, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  simp only [mul_assoc]
  ring
private theorem scalarOrbit_squared (v : Fin 9 → ℝ) :
    (∑ i : Fin 70, (∑ k : Fin 9, v k*(rationalO i k : ℝ))^2) =
      2*(∑ k : Fin 9, (v k)^2)-2*v 4*v 7+2*v 4*v 8-2*v 7*v 8 := by
  let x : PreparationChartGuard.NormalCoordinates := WithLp.toLp 2 v
  have lift : PreparationChartGuard.normalBuild x = ∑ k : Fin 9, v k •
      PreparationChartGuard.normalBuild (PreparationVacuumSourceChartBudget.sourceNormal k) := by
    have h := congrArg PreparationVacuumSourceMatrixInverse.normalBuildLinear
      (PreparationVacuumSourceMatrixInverse.sourceNormal_expansion x)
    simp only [map_sum, map_smul] at h
    exact h
  have read (i : Fin 70) : scalarRealify (orbit (PreparationChartGuard.normalBuild x)) i =
      ∑ k : Fin 9, v k*(rationalO i k : ℝ) := by
    rw [lift]; simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ k : Fin 9, v k*sourceO i k)=_
    simp_rw [sourceO_literal, ←rationalO_cast]
  calc
    _ = ‖orbit (PreparationChartGuard.normalBuild x)‖^2 := by
      rw [←real_inner_self_eq_norm_sq, scalar_inner_realified]; simp only [read, pow_two]
    _ = _ := by
      rw [PreparationChartGuard.normal_orbit_squared]
      norm_num only [x, PiLp.toLp_apply, Fin.sum_univ_succ]; simp only [Fin.reduceSucc, Fin.reduceEq, Fin.isValue, Fin.reduceFinMk, if_true, if_false]
      ring
def literalScalarTerms : List (NativeJetIndex × NativeJetIndex × ℝ) := [
  ((none,11),(none,11),(-125/54:ℝ)*lapse),((none,11),(some 0,0),(-125/27:ℝ)*lapse),((none,12),(none,12),(-125/54:ℝ)*lapse),((none,12),(some 0,1),(-125/27:ℝ)*lapse),((none,13),(none,13),(-125/54:ℝ)*lapse),((none,13),(some 0,2),(-125/27:ℝ)*lapse),((none,14),(none,14),(-125/54:ℝ)*lapse),((none,14),(some 0,3),(-125/27:ℝ)*lapse),((none,15),(none,15),(-125/54:ℝ)*lapse),((none,15),(none,16),(-125/27:ℝ)*lapse),((none,15),(none,19),(125/54:ℝ)*lapse),((none,15),(none,20),(-125/54:ℝ)*lapse),
  ((none,15),(some 0,4),(-125/27:ℝ)*lapse),((none,15),(some 0,7),(125/54:ℝ)*lapse),((none,15),(some 0,8),(-125/54:ℝ)*lapse),((none,16),(none,16),(-125/54:ℝ)*lapse),((none,16),(none,19),(125/54:ℝ)*lapse),((none,16),(none,20),(-125/54:ℝ)*lapse),((none,16),(some 0,4),(-125/27:ℝ)*lapse),((none,16),(some 0,7),(125/54:ℝ)*lapse),((none,16),(some 0,8),(-125/54:ℝ)*lapse),((none,17),(none,17),(-125/54:ℝ)*lapse),((none,17),(some 0,5),(-125/27:ℝ)*lapse),((none,18),(none,18),(-125/54:ℝ)*lapse),
  ((none,18),(some 0,6),(-125/27:ℝ)*lapse),((none,19),(none,19),(-125/54:ℝ)*lapse),((none,19),(none,20),(125/54:ℝ)*lapse),((none,19),(some 0,4),(125/54:ℝ)*lapse),((none,19),(some 0,7),(-125/27:ℝ)*lapse),((none,19),(some 0,8),(125/54:ℝ)*lapse),((none,20),(none,20),(-125/54:ℝ)*lapse),((none,20),(some 0,4),(-125/54:ℝ)*lapse),((none,20),(some 0,7),(125/54:ℝ)*lapse),((none,20),(some 0,8),(-125/27:ℝ)*lapse),((none,23),(none,23),lapse),((none,23),(none,3),-lapse*gaugeScale),
  ((none,23),(some 1,0),2*lapse),((none,24),(none,24),lapse),((none,24),(none,2),lapse*gaugeScale),((none,24),(some 1,1),2*lapse),((none,25),(none,25),lapse),((none,25),(none,1),-lapse*gaugeScale),((none,25),(some 1,2),2*lapse),((none,26),(none,26),lapse),((none,26),(none,0),lapse*gaugeScale),((none,26),(some 1,3),2*lapse),((none,27),(none,27),lapse),((none,27),(none,28),2*lapse),
  ((none,27),(none,31),-lapse),((none,27),(none,32),lapse),((none,27),(some 1,4),2*lapse),((none,27),(some 1,7),-lapse),((none,27),(some 1,8),lapse),((none,28),(none,28),lapse),((none,28),(none,31),-lapse),((none,28),(none,32),lapse),((none,28),(some 1,4),2*lapse),((none,28),(some 1,7),-lapse),((none,28),(some 1,8),lapse),((none,29),(none,29),lapse),
  ((none,29),(some 1,5),2*lapse),((none,30),(none,30),lapse),((none,30),(some 1,6),2*lapse),((none,31),(none,31),lapse),((none,31),(none,32),-lapse),((none,31),(some 1,4),-lapse),((none,31),(some 1,7),2*lapse),((none,31),(some 1,8),-lapse),((none,32),(none,32),lapse),((none,32),(some 1,4),lapse),((none,32),(some 1,7),-lapse),((none,32),(some 1,8),2*lapse),
  ((none,35),(none,35),lapse),((none,35),(none,2),lapse*gaugeScale),((none,35),(some 2,0),2*lapse),((none,36),(none,36),lapse),((none,36),(none,3),lapse*gaugeScale),((none,36),(some 2,1),2*lapse),((none,37),(none,37),lapse),((none,37),(none,0),-lapse*gaugeScale),((none,37),(some 2,2),2*lapse),((none,38),(none,38),lapse),((none,38),(none,1),-lapse*gaugeScale),((none,38),(some 2,3),2*lapse),
  ((none,39),(none,39),lapse),((none,39),(none,40),2*lapse),((none,39),(none,43),-lapse),((none,39),(none,44),lapse),((none,39),(some 2,4),2*lapse),((none,39),(some 2,7),-lapse),((none,39),(some 2,8),lapse),((none,40),(none,40),lapse),((none,40),(none,43),-lapse),((none,40),(none,44),lapse),((none,40),(some 2,4),2*lapse),((none,40),(some 2,7),-lapse),
  ((none,40),(some 2,8),lapse),((none,41),(none,41),lapse),((none,41),(some 2,5),2*lapse),((none,42),(none,42),lapse),((none,42),(some 2,6),2*lapse),((none,43),(none,43),lapse),((none,43),(none,44),-lapse),((none,43),(some 2,4),-lapse),((none,43),(some 2,7),2*lapse),((none,43),(some 2,8),-lapse),((none,44),(none,44),lapse),((none,44),(some 2,4),lapse),
  ((none,44),(some 2,7),-lapse),((none,44),(some 2,8),2*lapse),((none,47),(none,47),lapse),((none,47),(none,1),-lapse*gaugeScale),((none,47),(some 3,0),2*lapse),((none,48),(none,48),lapse),((none,48),(none,0),lapse*gaugeScale),((none,48),(some 3,1),2*lapse),((none,49),(none,49),lapse),((none,49),(none,3),lapse*gaugeScale),((none,49),(some 3,2),2*lapse),((none,50),(none,50),lapse),
  ((none,50),(none,2),-lapse*gaugeScale),((none,50),(some 3,3),2*lapse),((none,51),(none,51),lapse),((none,51),(none,52),2*lapse),((none,51),(none,55),-lapse),((none,51),(none,56),lapse),((none,51),(some 3,4),2*lapse),((none,51),(some 3,7),-lapse),((none,51),(some 3,8),lapse),((none,52),(none,52),lapse),((none,52),(none,55),-lapse),((none,52),(none,56),lapse),
  ((none,52),(some 3,4),2*lapse),((none,52),(some 3,7),-lapse),((none,52),(some 3,8),lapse),((none,53),(none,53),lapse),((none,53),(some 3,5),2*lapse),((none,54),(none,54),lapse),((none,54),(some 3,6),2*lapse),((none,55),(none,55),lapse),((none,55),(none,56),-lapse),((none,55),(some 3,4),-lapse),((none,55),(some 3,7),2*lapse),((none,55),(some 3,8),-lapse),
  ((none,56),(none,56),lapse),((none,56),(some 3,4),lapse),((none,56),(some 3,7),-lapse),((none,56),(some 3,8),2*lapse),((none,0),(none,0),(-73/50:ℝ)*lapse),((none,0),(some 1,3),lapse*gaugeScale),((none,0),(some 2,2),-lapse*gaugeScale),((none,0),(some 3,1),lapse*gaugeScale),((none,1),(none,1),(-73/50:ℝ)*lapse),((none,1),(some 1,2),-lapse*gaugeScale),((none,1),(some 2,3),-lapse*gaugeScale),((none,1),(some 3,0),-lapse*gaugeScale),
  ((none,2),(none,2),(-73/50:ℝ)*lapse),((none,2),(some 1,1),lapse*gaugeScale),((none,2),(some 2,0),lapse*gaugeScale),((none,2),(some 3,3),-lapse*gaugeScale),((none,3),(none,3),(-73/50:ℝ)*lapse),((none,3),(some 1,0),-lapse*gaugeScale),((none,3),(some 2,1),lapse*gaugeScale),((none,3),(some 3,2),lapse*gaugeScale),((none,4),(none,4),-2*lapse),((none,4),(none,7),2*lapse),((none,4),(none,8),-2*lapse),((none,5),(none,5),-2*lapse),
  ((none,6),(none,6),-2*lapse),((none,7),(none,7),-2*lapse),((none,7),(none,8),2*lapse),((none,8),(none,8),-2*lapse),((some 0,0),(some 0,0),(-125/54:ℝ)*lapse),((some 0,1),(some 0,1),(-125/54:ℝ)*lapse),((some 0,2),(some 0,2),(-125/54:ℝ)*lapse),((some 0,3),(some 0,3),(-125/54:ℝ)*lapse),((some 0,4),(some 0,4),(-125/54:ℝ)*lapse),((some 0,4),(some 0,7),(125/54:ℝ)*lapse),((some 0,4),(some 0,8),(-125/54:ℝ)*lapse),((some 0,5),(some 0,5),(-125/54:ℝ)*lapse),
  ((some 0,6),(some 0,6),(-125/54:ℝ)*lapse),((some 0,7),(some 0,7),(-125/54:ℝ)*lapse),((some 0,7),(some 0,8),(125/54:ℝ)*lapse),((some 0,8),(some 0,8),(-125/54:ℝ)*lapse),((some 1,0),(some 1,0),lapse),((some 1,1),(some 1,1),lapse),((some 1,2),(some 1,2),lapse),((some 1,3),(some 1,3),lapse),((some 1,4),(some 1,4),lapse),((some 1,4),(some 1,7),-lapse),((some 1,4),(some 1,8),lapse),((some 1,5),(some 1,5),lapse),
  ((some 1,6),(some 1,6),lapse),((some 1,7),(some 1,7),lapse),((some 1,7),(some 1,8),-lapse),((some 1,8),(some 1,8),lapse),((some 2,0),(some 2,0),lapse),((some 2,1),(some 2,1),lapse),((some 2,2),(some 2,2),lapse),((some 2,3),(some 2,3),lapse),((some 2,4),(some 2,4),lapse),((some 2,4),(some 2,7),-lapse),((some 2,4),(some 2,8),lapse),((some 2,5),(some 2,5),lapse),
  ((some 2,6),(some 2,6),lapse),((some 2,7),(some 2,7),lapse),((some 2,7),(some 2,8),-lapse),((some 2,8),(some 2,8),lapse),((some 3,0),(some 3,0),lapse),((some 3,1),(some 3,1),lapse),((some 3,2),(some 3,2),lapse),((some 3,3),(some 3,3),lapse),((some 3,4),(some 3,4),lapse),((some 3,4),(some 3,7),-lapse),((some 3,4),(some 3,8),lapse),((some 3,5),(some 3,5),lapse),
  ((some 3,6),(some 3,6),lapse),((some 3,7),(some 3,7),lapse),((some 3,7),(some 3,8),-lapse),((some 3,8),(some 3,8),lapse)]
def literalScalarQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalScalarTerms.map fun term => term.2.2 * nativeJetCoefficient jet term.1 * nativeJetCoefficient jet term.2.1).sum
set_option maxHeartbeats 6000000 in
theorem nativeScalarQuadratic_literal (jet : NativeFirstJet) : scalarRayCore jet 0 = literalScalarQuadratic jet := by
  have gauge_sq : gaugeScale^2 = 18/25 := by
    simp only [gaugeScale, div_pow, mul_pow, spinScale_sq]; norm_num
  rw [scalarRayCore_originalCoordinates]
  simp_rw [scalarShift_read, scalarInsertion_literal, scalarOrbit_squared]
  simp only [lapse_sq]
  norm_num (config := { maxSteps := 500000 }) [Fin.sum_univ_succ, scalarSlot, gaugeSlot,
    scalarShift, scalarPauliNineMatrix, Pi.single_apply, originalJColumns, literalScalarQuadratic, literalScalarTerms, nativeJetCoefficient]
  simp only [Fin.reduceSucc, Fin.reduceEq, Fin.isValue, Fin.reduceFinMk, if_true, if_false, and_false, false_and, true_and, and_true, or_false, false_or, true_or, or_true]
  dsimp only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  simp only [eq_mpr_eq_cast, cast_eq]
  norm_num only [Fin.val_ofNat, Fin.val_zero, Fin.coe_ofNat_eq_mod, Fin.val_natCast]

  linear_combination (norm := ring_nf!) (3/4:ℝ)*lapse*((jet.1 0)^2+(jet.1 1)^2+(jet.1 2)^2+(jet.1 3)^2)*gauge_sq

def literalScalarHessian : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  (literalScalarTerms.map fun term => term.2.2 •
    ((nativeCoefficientCLM term.1).smulRight (nativeCoefficientCLM term.2.1) +
      (nativeCoefficientCLM term.2.1).smulRight (nativeCoefficientCLM term.1))).sum
private theorem literalScalarHessian_value (a b : NativeFirstJet) : literalScalarHessian a b =
    (literalScalarTerms.map fun term => term.2.2 *
      (nativeJetCoefficient a term.1 * nativeJetCoefficient b term.2.1 +
        nativeJetCoefficient a term.2.1 * nativeJetCoefficient b term.1)).sum := by
  unfold literalScalarHessian
  generalize literalScalarTerms=terms
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp only [List.map_cons, List.sum_cons, add_apply, ih, smul_apply, smul_eq_mul,
      ContinuousLinearMap.smulRight_apply]
    rfl
private theorem literalScalarHessian_diagonal (jet : NativeFirstJet) :
    literalScalarHessian jet jet = 2*literalScalarQuadratic jet := by
  rw [literalScalarHessian_value]
  unfold literalScalarQuadratic
  rw [←List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro term _
  ring
private theorem literalScalarHessian_symmetric (a b : NativeFirstJet) :
    literalScalarHessian a b = literalScalarHessian b a := by
  rw [literalScalarHessian_value, literalScalarHessian_value]
  congr 1
  apply List.map_congr_left
  intro term _
  ring
theorem nativeScalarHessian_literal (a b : NativeFirstJet) :
    nativeBlockHessian 2 a b = literalScalarHessian a b := by
  apply symmetric_diagonal_unique _ _ (nativeBlockHessian_symmetric 2) literalScalarHessian_symmetric
  intro jet
  rw [nativeScalarSecond_generated, nativeScalarQuadratic_literal, literalScalarHessian_diagonal]

def nativeHessianCoefficient (left right : NativeJetIndex) : ℝ :=
  nativeHessian (nativeJetBasis left) (nativeJetBasis right)

theorem nativeHessianCoefficient_symmetric (left right : NativeJetIndex) :
    nativeHessianCoefficient left right = nativeHessianCoefficient right left :=
  nativeHessian_symmetric _ _

theorem nativeSecondDensity_coefficients (jet : NativeFirstJet) :
    nativeSecondDensity jet = (1/2:ℝ) *
      ∑ left : NativeJetIndex, ∑ right : NativeJetIndex,
        nativeJetCoefficient jet left * nativeJetCoefficient jet right * nativeHessianCoefficient left right := by
  unfold nativeSecondDensity
  change (1/2:ℝ) * nativeHessian jet jet = _
  congr 1
  conv_lhs => rw [nativeJet_reconstruction jet]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, nativeHessianCoefficient]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  rw [nativeHessian_symmetric]
  ring

def jetSymbol (derivative : Option (Fin 4)) (p : Fin 4 → ℂ) : ℂ :=
  match derivative with
  | none => 1
  | some mu => p mu

def nativeFourierHessian (H : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ)
    (p : Fin 4 → ℂ) : Matrix (Fin 289) (Fin 289) ℂ := fun row column =>
  ∑ left : Option (Fin 4), ∑ right : Option (Fin 4),
    (H (nativeJetBasis (left,row)) (nativeJetBasis (right,column)):ℂ) *
      jetSymbol left (-p) * jetSymbol right p

def nativeFourierLinear (p : Fin 4 → ℂ) :
    (NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ) →ₗ[ℝ] Matrix (Fin 289) (Fin 289) ℂ where
  toFun H := nativeFourierHessian H p
  map_add' H K := by
    ext row column
    simp only [nativeFourierHessian, add_apply, Complex.ofReal_add, add_mul,
      Finset.sum_add_distrib, Matrix.add_apply]
  map_smul' r H := by
    ext row column
    simp only [nativeFourierHessian, smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Matrix.smul_apply, RCLike.real_smul_eq_coe_smul]
    change _ = (r:ℂ) * _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro left _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro right _
    ring

def nativeBlockJacobi (block : Fin 4) (p : Fin 4 → ℂ) := nativeFourierHessian (nativeBlockHessian block) p

theorem nativeHessian_sum_blocks : nativeHessian = ∑ block : Fin 4, nativeBlockHessian block := by
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  simpa only [sum_apply] using nativeHessian_blocks a b

theorem nativeFourierHessian_blocks (p : Fin 4 → ℂ) :
    nativeFourierHessian nativeHessian p = ∑ block : Fin 4, nativeBlockJacobi block p := by
  rw [nativeHessian_sum_blocks]
  exact map_sum (nativeFourierLinear p) (fun block : Fin 4 => nativeBlockHessian block) Finset.univ

theorem nativeGravityFourier_literal (p : Fin 4 → ℂ) :
    nativeBlockJacobi 0 p = nativeFourierHessian literalGravityHessian p := by
  have H : nativeBlockHessian 0 = literalGravityHessian := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact nativeGravityHessian_literal a b
  rw [nativeBlockJacobi, H]

theorem nativeScalarFourier_literal (p : Fin 4 → ℂ) :
    nativeBlockJacobi 2 p = nativeFourierHessian literalScalarHessian p := by
  have H : nativeBlockHessian 2 = literalScalarHessian := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact nativeScalarHessian_literal a b
  rw [nativeBlockJacobi, H]

/-- The integration-by-parts sign belongs to the left varied derivative exactly once. -/
def nativeJacobi (p : Fin 4 → ℂ) : Matrix (Fin 289) (Fin 289) ℂ := fun row column =>
  ∑ left : Option (Fin 4), ∑ right : Option (Fin 4),
    (nativeHessianCoefficient (left,row) (right,column):ℂ) * jetSymbol left (-p) * jetSymbol right p

theorem nativeJacobi_formalAdjoint (p : Fin 4 → ℂ) : (nativeJacobi (-p)).transpose = nativeJacobi p := by
  ext row column
  simp only [nativeJacobi, Matrix.transpose_apply, neg_neg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  rw [nativeHessianCoefficient_symmetric]
  ring

end LowEnergy.SourcePropagationNativeActionHessian
