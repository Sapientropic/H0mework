import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationCoframeInverseJets

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical PreparationCoordinates
open SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open Filter
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
attribute [local irreducible] Stage9C.Material.SpinPair.actual

def rawGaugePair (x y : Fin 12 → ℝ) : ℝ :=
  2 * (x 0*y 0+x 1*y 1+x 2*y 2+x 3*y 3+x 4*y 4+x 5*y 5+
       x 6*y 6+x 7*y 7+x 8*y 8+x 9*y 9+x 10*y 10) +
    x 6*y 7+x 7*y 6+x 11*y 11

def rawGaugePairRight (x : Fin 12 → ℝ) : (Fin 12 → ℝ) →ₗ[ℝ] ℝ where
  toFun := rawGaugePair x
  map_add' y z := by simp only [rawGaugePair, Pi.add_apply]; ring
  map_smul' r y := by simp only [rawGaugePair, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def rawGaugePairLinear : (Fin 12 → ℝ) →ₗ[ℝ] (Fin 12 → ℝ) →ₗ[ℝ] ℝ where
  toFun := rawGaugePairRight
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change rawGaugePair (x + y) z = rawGaugePair x z + rawGaugePair y z
    simp only [rawGaugePair, Pi.add_apply]
    ring
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    change rawGaugePair (r • x) y = r * rawGaugePair x y
    simp only [rawGaugePair, Pi.smul_apply, smul_eq_mul]
    ring

def rawGaugePairCLM : (Fin 12 → ℝ) →L[ℝ] (Fin 12 → ℝ) →L[ℝ] ℝ :=
  rawGaugePairLinear.toContinuousBilinearMap

theorem rawGaugePair_first (f g : ℝ → Fin 12 → ℝ) (df dg : Fin 12 → ℝ) (r : ℝ)
    (hf : HasDerivAt f df r) (hg : HasDerivAt g dg r) :
    HasDerivAt (fun t => rawGaugePair (f t) (g t))
      (rawGaugePair (f r) dg + rawGaugePair df (g r)) r := by
  convert! (rawGaugePairCLM.hasFDerivAt.comp_hasDerivAt r hf).clm_apply hg using 1
  exact add_comm _ _

theorem rawGaugePair_second (f g : ℝ → Fin 12 → ℝ) (df ddf dg ddg : Fin 12 → ℝ)
    (hf : HasDerivAt f df 0) (hg : HasDerivAt g dg 0)
    (hff : HasDerivAt (deriv f) ddf 0) (hgg : HasDerivAt (deriv g) ddg 0)
    (hnearF : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ f r)
    (hnearG : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ g r) :
    HasDerivAt (deriv (fun r => rawGaugePair (f r) (g r)))
      (rawGaugePair (f 0) ddg + 2 * rawGaugePair df dg + rawGaugePair ddf (g 0)) 0 := by
  have hl := rawGaugePair_first f (deriv g) df ddg 0 hf hgg
  have hr := rawGaugePair_first (deriv f) g ddf dg 0 hff hg
  have heq : deriv (fun r => rawGaugePair (f r) (g r)) =ᶠ[𝓝 (0 : ℝ)]
      fun r => rawGaugePair (f r) (deriv g r) + rawGaugePair (deriv f r) (g r) := by
    filter_upwards [hnearF, hnearG] with r hfR hgR
    exact (rawGaugePair_first f g (deriv f r) (deriv g r) r hfR.hasDerivAt hgR.hasDerivAt).deriv
  have hs : HasDerivAt (fun r => rawGaugePair (f r) (deriv g r) + rawGaugePair (deriv f r) (g r))
      (rawGaugePair (f 0) ddg + 2 * rawGaugePair df dg + rawGaugePair ddf (g 0)) 0 := by
    convert! hl.add hr using 1
    rw [hf.deriv, hg.deriv]
    ring
  exact hs.congr_of_eventuallyEq heq

theorem coordinateQuadratic_derivative (a b c : Fin 12 → ℝ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => a + t • b + t^2 • c) (b + (2*r) • c) r := by
  apply hasDerivAt_pi.mpr
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hl := ((hasDerivAt_id r).mul_const (b i)).const_add (a i)
  have hq := ((hasDerivAt_id r).pow 2).mul_const (c i)
  convert! hl.add hq using 1
  norm_num

theorem coordinateQuadratic_second (a b c : Fin 12 → ℝ) :
    HasDerivAt (deriv (fun t : ℝ => a + t • b + t^2 • c)) ((2 : ℝ) • c) 0 := by
  have heq : deriv (fun t : ℝ => a + t • b + t^2 • c) = fun t => b + (2*t) • c :=
    funext fun t => (coordinateQuadratic_derivative a b c t).deriv
  rw [heq]
  simpa only [id_eq, mul_one] using (((hasDerivAt_id (0 : ℝ)).const_mul 2).smul_const c).const_add b

theorem coordinateAffine_derivative (a b : Fin 12 → ℝ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => a + t • b) b r := by
  simpa only [id_eq, one_smul] using ((hasDerivAt_id r).smul_const b).const_add a

theorem coordinateAffine_second (a b : Fin 12 → ℝ) :
    HasDerivAt (deriv (fun t : ℝ => a + t • b)) 0 0 := by
  have heq : deriv (fun t : ℝ => a + t • b) = fun _ => b :=
    funext fun t => (coordinateAffine_derivative a b t).deriv
  rw [heq]
  exact hasDerivAt_const 0 b

theorem finiteSum_second {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (ddf : ι → ℝ)
    (hdd : ∀ i, HasDerivAt (deriv (f i)) (ddf i) 0)
    (hnear : ∀ i, ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ (f i) r) :
    HasDerivAt (deriv (fun r => ∑ i, f i r)) (∑ i, ddf i) 0 := by
  have hs : HasDerivAt (fun r => ∑ i, deriv (f i) r) (∑ i, ddf i) 0 := by
    convert! HasDerivAt.sum (u := Finset.univ) (fun i _ => hdd i) using 1
    funext r
    simp only [Finset.sum_apply]
  have allNear : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i, DifferentiableAt ℝ (f i) r :=
    eventually_all.mpr hnear
  have sumEq : (∑ i, f i) = fun r => ∑ i, f i r := by
    funext r
    simp only [Finset.sum_apply]
  have heq : deriv (fun r => ∑ i, f i r) =ᶠ[𝓝 (0 : ℝ)] fun r => ∑ i, deriv (f i) r := by
    filter_upwards [allNear] with r hr
    rw [← sumEq]
    exact (HasDerivAt.sum (u := Finset.univ) fun i _ => (hr i).hasDerivAt).deriv
  exact hs.congr_of_eventuallyEq heq

theorem rawGaugePair_source (a b : P286CoordinateCarrier) :
    p286CoordinateLiePairing a b = rawGaugePair (rawCoordinates a) (rawCoordinates b) := by
  have h := PreparationMeasure.original_raw_inner (rawCoordinates a) (rawCoordinates b)
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
  exact h

def sourceGaugeB0 (pair : Fin 6) : Fin 12 → ℝ :=
  rawCoordinates (p286CoordinateEquiv (actual.gaugeAuxiliary 0 pair))

def sourceGaugeCurvature0 (pair : Fin 6) : Fin 12 → ℝ :=
  rawCoordinates (p286CoordinateEquiv (holonomicGaugeCurvature actual 0 pair))

def nativeGaugeRawCurvature (jet : NativeFirstJet) (pair : Fin 6) : Fin 12 → ℝ :=
  rawCoordinates (p286CoordinateEquiv (nativeGaugeCurvature jet pair))

def nativeGaugeQuadraticCurvature (jet : NativeFirstJet) (pair : Fin 6) : Fin 12 → ℝ :=
  rawCoordinates (p286CoordinateEquiv (p286LieBracket
    (p286CoordinateEquiv.symm (fieldGauge jet.1 (pairFirst pair)))
    (p286CoordinateEquiv.symm (fieldGauge jet.1 (pairSecond pair)))))

def nativeGaugeLinearCurvature (jet : NativeFirstJet) (pair : Fin 6) : Fin 12 → ℝ :=
  nativeGaugeRawCurvature jet pair - sourceGaugeCurvature0 pair - nativeGaugeQuadraticCurvature jet pair

theorem gaugeBInsertion_raw (f : Field289) (pair : Fin 6) :
    rawCoordinates (p286CoordinateEquiv (gaugeBInsertion f pair)) = fieldGaugeB f pair := by
  unfold gaugeBInsertion
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_sum, map_smul, originalUnit, LinearEquiv.apply_symm_apply]
  funext i
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]

theorem nativeGaugeAuxiliary_raw (jet : NativeFirstJet) (pair : Fin 6) :
    rawCoordinates (p286CoordinateEquiv ((nativeJetPoint jet).gaugeAuxiliary pair)) =
      sourceGaugeB0 pair + fieldGaugeB jet.1 pair := by
  change rawCoordinates (show NativeLie from p286CoordinateEquiv
    (actual.gaugeAuxiliary 0 pair + gaugeBInsertion jet.1 pair)) = _
  rw [p286CoordinateEquiv.map_add]
  change rawCoordinates ((show NativeLie from p286CoordinateEquiv (actual.gaugeAuxiliary 0 pair)) +
    (show NativeLie from p286CoordinateEquiv (gaugeBInsertion jet.1 pair))) = _
  rw [rawCoordinates.map_add, gaugeBInsertion_raw]
  rfl

def nativeGaugeDensity (jet : NativeFirstJet) : ℝ :=
  StageNineFormNativeMotherAction.generatedFormNativeGaugeDensityAtBoundary
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) (nativeJetPoint jet)

theorem nativeGaugeDensity_smooth_at_zero : ContDiffAt ℝ ∞ nativeGaugeDensity 0 :=
  nativeGaugeDensity_smooth

theorem nativeGaugeRawCurvature_ray (jet : NativeFirstJet) (r : ℝ) (pair : Fin 6) :
    nativeGaugeRawCurvature (r • jet) pair = sourceGaugeCurvature0 pair +
      r • nativeGaugeLinearCurvature jet pair + r^2 • nativeGaugeQuadraticCurvature jet pair := by
  unfold nativeGaugeLinearCurvature nativeGaugeRawCurvature nativeGaugeQuadraticCurvature
    sourceGaugeCurvature0 nativeGaugeCurvature
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, fieldGauge_smul]
  simp only [map_add, map_sub, map_smul, p286LieBracket_smul_left, p286LieBracket_smul_right,
    smul_smul]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem sourceRay_second_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (smooth : ContDiffAt ℝ ∞ f 0) (jet : E) (coefficient : ℝ)
    (ray : HasDerivAt (deriv (fun r : ℝ => f (r • jet))) coefficient 0) :
    fderiv ℝ (fderiv ℝ f) 0 jet jet = coefficient := by
  have line (r : ℝ) : HasDerivAt (fun t : ℝ => t • jet) jet r := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const jet
  have hs : ContDiffAt ℝ 1 f 0 := smooth.of_le (by simp)
  have near : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ f y :=
    (hs.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
  have nearLine : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (r • jet) := by
    have continuousLine : Tendsto (fun r : ℝ => r • jet) (𝓝 0) (𝓝 (0 : E)) := by
      simpa only [ContinuousAt, zero_smul] using (line 0).continuousAt
    exact continuousLine.eventually near
  have heq : (fun r : ℝ => fderiv ℝ f (r • jet) jet) =ᶠ[𝓝 0]
      deriv (fun r : ℝ => f (r • jet)) := by
    filter_upwards [nearLine] with r hr
    exact (hr.hasFDerivAt.comp_hasDerivAt r (line r)).deriv.symm
  have hH := (smooth.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have hline := hH.comp_hasDerivAt_of_eq 0 (line 0) (by simp)
  have hread := hline.clm_apply (hasDerivAt_const (0 : ℝ) jet)
  have unique := hread.unique (ray.congr_of_eventuallyEq heq)
  simpa only [zero_smul, map_zero, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] using unique

theorem nativeHodgeCoefficient_near (jet : NativeFirstJet) (i j : Fin 6) :
    ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (fun t : ℝ => nativeHodgeMatrix (actual.coframe 0 + t • fieldCoframe jet.1) i j) r := by
  have same : (fun r : ℝ => nativeConstitutiveCoefficient 1 i j (r • jet)) =
      fun r => nativeHodgeMatrix (actual.coframe 0 + r • fieldCoframe jet.1) i j := by
    funext r
    simp only [nativeConstitutiveCoefficient_ray, one_mul]
  have h0 : ContDiffAt ℝ ∞ (nativeConstitutiveCoefficient 1 i j) ((0 : ℝ) • jet) := by
    simpa only [zero_smul] using nativeConstitutiveCoefficient_smooth 1 i j
  have hs := h0.comp (f := fun r : ℝ => r • jet) 0 (contDiff_id.smul contDiff_const).contDiffAt
  change ContDiffAt ℝ ∞ (fun r : ℝ => nativeConstitutiveCoefficient 1 i j (r • jet)) 0 at hs
  rw [same] at hs
  have hf : ContDiffAt ℝ 1 (fun r : ℝ =>
      nativeHodgeMatrix (actual.coframe 0 + r • fieldCoframe jet.1) i j) 0 := hs.of_le (by simp)
  exact (hf.eventually (by simp)).mono fun _ hr => hr.differentiableAt (by simp)

theorem commonConstitutive_raw (e : LorentzianCoframe) (sigma : ℝ)
    (B : Fin 6 → P286LieBlockData) (pair : Fin 6) :
    rawCoordinates (show NativeLie from p286CoordinateEquiv
      (StageNineFormNativeGaugeWedge.formNativeP286BlockwiseConstitutive e sigma sigma sigma B pair)) =
      ∑ input : Fin 6, (sigma * nativeHodgeMatrix e pair input) •
        rawCoordinates (show NativeLie from p286CoordinateEquiv (B input)) := by
  have same : StageNineFormNativeGaugeWedge.formNativeP286BlockwiseConstitutive e sigma sigma sigma B =
      liftGaugeTwoFormOperator (sigma • coframeGaugeSpacetimeHodgeLinear e) B := by
    funext output
    apply Prod.ext
    · simp [StageNineFormNativeGaugeWedge.formNativeP286BlockwiseConstitutive,
        liftGaugeTwoFormOperator, Prod.fst_sum, Prod.smul_fst]
    · apply Prod.ext
      · simp [StageNineFormNativeGaugeWedge.formNativeP286BlockwiseConstitutive,
          liftGaugeTwoFormOperator, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst]
      · simp [StageNineFormNativeGaugeWedge.formNativeP286BlockwiseConstitutive,
          liftGaugeTwoFormOperator, Prod.snd_sum, Prod.smul_snd]
  rw [same]
  simp only [liftGaugeTwoFormOperator, map_sum, map_smul]
  congr 1
  funext input
  change (sigma * gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear e) pair input) •
      rawCoordinates (show NativeLie from p286CoordinateEquiv (B input)) = _
  rw [nativeHodgeMatrix_original]

theorem nativeGaugeDensity_raw (jet : NativeFirstJet) :
    nativeGaugeDensity jet =
      (∑ pair : Fin 6, rawGaugePair
        (sourceGaugeB0 pair + fieldGaugeB jet.1 pair)
        (nativeGaugeRawCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair))) -
      (positiveSmoothUnifiedSource.legacy.sigma / 2) *
        ∑ pair : Fin 6, ∑ input : Fin 6,
          nativeHodgeMatrix (nativeJetPoint jet).coframe
            (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
          rawGaugePair (sourceGaugeB0 pair + fieldGaugeB jet.1 pair)
            (sourceGaugeB0 input + fieldGaugeB jet.1 input) := by
  unfold nativeGaugeDensity
  rw [StageNineFormNativeGaugeAuxiliaryVariation.generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  simp only [sourceGeneratedUnifiedCouplings, EmpiricalReferenceScaleCouplingBoundary.positiveUnit]
  unfold StageNineFormNativeGaugeWedge.formNativeP286GaugeWedgeCoefficient
    StageNineTopologicalFourFormPairing.generatedTwoFormWedgeCoefficient
  have pairSource (a b : P286LieBlockData) :
      StageNineFormNativeGaugeWedge.formNativeP286LiePairing a b =
        rawGaugePair (rawCoordinates (show NativeLie from p286CoordinateEquiv a))
          (rawCoordinates (show NativeLie from p286CoordinateEquiv b)) := by
    simpa only [p286CoordinateLiePairing, LinearEquiv.symm_apply_apply, p286LiePairing,
      StageNineFormNativeGaugeWedge.formNativeP286LiePairing] using
      rawGaugePair_source (p286CoordinateEquiv a) (p286CoordinateEquiv b)
  simp_rw [pairSource, commonConstitutive_raw]
  have sum_right (x : Fin 12 → ℝ) (F : Fin 6 → Fin 12 → ℝ) :
      rawGaugePair x (∑ i, F i) = ∑ i, rawGaugePair x (F i) := by
    exact map_sum (rawGaugePairRight x) F Finset.univ
  have smul_right (r : ℝ) (x y : Fin 12 → ℝ) : rawGaugePair x (r • y) = r * rawGaugePair x y :=
    (rawGaugePairRight x).map_smul r y
  simp_rw [sum_right, smul_right]
  have curvature (pair : Fin 6) :
      rawCoordinates (show NativeLie from p286CoordinateEquiv ((nativeJetPoint jet).gaugeCurvature pair)) =
        nativeGaugeRawCurvature jet pair := rfl
  simp only [nativeGaugeAuxiliary_raw, curvature, Units.val_mk0]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

theorem nativeGaugeDensity_ray (jet : NativeFirstJet) (r : ℝ) :
    nativeGaugeDensity (r • jet) =
      (∑ pair : Fin 6, rawGaugePair
        (sourceGaugeB0 pair + r • fieldGaugeB jet.1 pair)
        (sourceGaugeCurvature0 (StageNineTopologicalFourFormPairing.twoFormComplement pair) +
          r • nativeGaugeLinearCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair) +
          r^2 • nativeGaugeQuadraticCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair))) -
      (positiveSmoothUnifiedSource.legacy.sigma / 2) *
        ∑ pair : Fin 6, ∑ input : Fin 6,
          nativeHodgeMatrix (actual.coframe 0 + r • fieldCoframe jet.1)
            (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
          rawGaugePair (sourceGaugeB0 pair + r • fieldGaugeB jet.1 pair)
            (sourceGaugeB0 input + r • fieldGaugeB jet.1 input) := by
  rw [nativeGaugeDensity_raw]
  simp only [nativeCoframe_ray, nativeGaugeRawCurvature_ray, Prod.smul_fst]
  rfl

theorem gaugeBF_second (a b f0 f1 f2 : Fin 12 → ℝ) :
    HasDerivAt (deriv (fun r : ℝ => rawGaugePair (a + r • b) (f0 + r • f1 + r^2 • f2)))
      (2 * (rawGaugePair b f1 + rawGaugePair a f2)) 0 := by
  let B : ℝ → Fin 12 → ℝ := fun r => a + r • b
  let F : ℝ → Fin 12 → ℝ := fun r => f0 + r • f1 + r^2 • f2
  have hB := coordinateAffine_derivative a b 0
  have hF : HasDerivAt F f1 0 := by
    simpa only [mul_zero, zero_smul, add_zero] using coordinateQuadratic_derivative f0 f1 f2 0
  have hBdd := coordinateAffine_second a b
  have hFdd := coordinateQuadratic_second f0 f1 f2
  have nearB : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ B r :=
    Eventually.of_forall fun r => (coordinateAffine_derivative a b r).differentiableAt
  have nearF : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ F r :=
    Eventually.of_forall fun r => (coordinateQuadratic_derivative f0 f1 f2 r).differentiableAt
  have hp := rawGaugePair_second B F b 0 f1 ((2 : ℝ) • f2) hB hF hBdd hFdd nearB nearF
  convert! hp using 1
  simp only [B, F, zero_smul, add_zero, zero_pow (by decide : 2 ≠ 0)]
  have scale : rawGaugePair a ((2 : ℝ) • f2) = 2 * rawGaugePair a f2 :=
    (rawGaugePairRight a).map_smul 2 f2
  rw [scale]
  simp only [rawGaugePair, Pi.zero_apply, zero_mul, add_zero, mul_zero]
  ring

theorem gaugeBB_first (a b c d : Fin 12 → ℝ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => rawGaugePair (a + t • b) (c + t • d))
      (rawGaugePair (a + r • b) d + rawGaugePair b (c + r • d)) r :=
  rawGaugePair_first _ _ b d r (coordinateAffine_derivative a b r) (coordinateAffine_derivative c d r)

theorem gaugeBB_second (a b c d : Fin 12 → ℝ) :
    HasDerivAt (deriv (fun t : ℝ => rawGaugePair (a + t • b) (c + t • d)))
      (2 * rawGaugePair b d) 0 := by
  have hp := rawGaugePair_second (fun t => a + t • b) (fun t => c + t • d) b 0 d 0
    (coordinateAffine_derivative a b 0) (coordinateAffine_derivative c d 0)
    (coordinateAffine_second a b) (coordinateAffine_second c d)
    (Eventually.of_forall fun r => (coordinateAffine_derivative a b r).differentiableAt)
    (Eventually.of_forall fun r => (coordinateAffine_derivative c d r).differentiableAt)
  convert! hp using 1
  simp [rawGaugePair]

theorem nativeGaugeConstitutiveTerm_second (jet : NativeFirstJet) (pair input : Fin 6) :
    HasDerivAt (deriv (fun r : ℝ =>
      nativeHodgeMatrix (actual.coframe 0 + r • fieldCoframe jet.1)
        (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
      rawGaugePair (sourceGaugeB0 pair + r • fieldGaugeB jet.1 pair)
        (sourceGaugeB0 input + r • fieldGaugeB jet.1 input)))
      (2 * (nativeHodgeMatrix (actual.coframe 0)
          (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
          rawGaugePair (fieldGaugeB jet.1 pair) (fieldGaugeB jet.1 input) +
        nativeHodgeFirst (actual.coframe 0) (fieldCoframe jet.1)
          (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
          (rawGaugePair (sourceGaugeB0 pair) (fieldGaugeB jet.1 input) +
            rawGaugePair (fieldGaugeB jet.1 pair) (sourceGaugeB0 input)) +
        nativeHodgeSecond (actual.coframe 0) (fieldCoframe jet.1)
          (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
          rawGaugePair (sourceGaugeB0 pair) (sourceGaugeB0 input))) 0 := by
  let output := StageNineTopologicalFourFormPairing.twoFormComplement pair
  let H : ℝ → ℝ := fun r => nativeConstitutiveCoefficient 1 output input (r • jet)
  let BB : ℝ → ℝ := fun r => rawGaugePair
    (sourceGaugeB0 pair + r • fieldGaugeB jet.1 pair)
    (sourceGaugeB0 input + r • fieldGaugeB jet.1 input)
  have sameH : H = fun r : ℝ => nativeHodgeMatrix (actual.coframe 0 + r • fieldCoframe jet.1) output input := by
    funext r
    simp only [H, nativeConstitutiveCoefficient_ray, one_mul]
  have hH : HasDerivAt H (nativeHodgeFirst (actual.coframe 0) (fieldCoframe jet.1) output input) 0 := by
    rw [sameH]
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp
      (nativeHodgeMatrix_first (actual.coframe 0) (fieldCoframe jet.1) (actual_nondegenerate 0)) output)) input
  have hHdd : HasDerivAt (deriv H)
      ((2 • nativeHodgeSecond (actual.coframe 0) (fieldCoframe jet.1)) output input) 0 := by
    simpa only [one_mul] using nativeConstitutiveCoefficient_second jet 1 output input
  have hBB : HasDerivAt BB
      (rawGaugePair (sourceGaugeB0 pair) (fieldGaugeB jet.1 input) +
        rawGaugePair (fieldGaugeB jet.1 pair) (sourceGaugeB0 input)) 0 := by
    simpa only [zero_smul, add_zero] using gaugeBB_first (sourceGaugeB0 pair) (fieldGaugeB jet.1 pair)
      (sourceGaugeB0 input) (fieldGaugeB jet.1 input) 0
  have hBBdd : HasDerivAt (deriv BB)
      (2 * rawGaugePair (fieldGaugeB jet.1 pair) (fieldGaugeB jet.1 input)) 0 :=
    gaugeBB_second _ _ _ _
  have hHsmooth : ContDiffAt ℝ ∞ H 0 := by
    have ht : ContDiffAt ℝ ∞ (nativeConstitutiveCoefficient 1 output input) ((0 : ℝ) • jet) := by
      simpa only [zero_smul] using nativeConstitutiveCoefficient_smooth 1 output input
    exact ht.comp (f := fun r : ℝ => r • jet) 0 (contDiff_id.smul contDiff_const).contDiffAt
  have hHnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ H r := by
    have ht : ContDiffAt ℝ 1 H 0 := hHsmooth.of_le (by simp)
    exact (ht.eventually (by simp)).mono fun _ hr => hr.differentiableAt (by simp)
  have hBBnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ BB r :=
    Eventually.of_forall fun r => (gaugeBB_first (sourceGaugeB0 pair) (fieldGaugeB jet.1 pair)
      (sourceGaugeB0 input) (fieldGaugeB jet.1 input) r).differentiableAt
  have hp := scalarJet_second_mul H BB
    (nativeHodgeFirst (actual.coframe 0) (fieldCoframe jet.1) output input)
    (rawGaugePair (sourceGaugeB0 pair) (fieldGaugeB jet.1 input) +
      rawGaugePair (fieldGaugeB jet.1 pair) (sourceGaugeB0 input))
    ((2 • nativeHodgeSecond (actual.coframe 0) (fieldCoframe jet.1)) output input)
    (2 * rawGaugePair (fieldGaugeB jet.1 pair) (fieldGaugeB jet.1 input))
    hH hBB hHdd hBBdd hHnear hBBnear
  rw [sameH] at hp
  convert! hp using 1
  simp only [BB, zero_smul, add_zero, two_smul, Matrix.add_apply]
  ring

def nativeGaugeQuadratic (jet : NativeFirstJet) : ℝ :=
  let e := actual.coframe 0
  let h := fieldCoframe jet.1
  let B1 := fieldGaugeB jet.1
  let sigma := positiveSmoothUnifiedSource.legacy.sigma
  let c := StageNineTopologicalFourFormPairing.twoFormComplement
  (∑ pair : Fin 6, (
    rawGaugePair (B1 pair) (nativeGaugeLinearCurvature jet (c pair)) +
    rawGaugePair (sourceGaugeB0 pair) (nativeGaugeQuadraticCurvature jet (c pair)))) -
    (sigma / 2) * ∑ pair : Fin 6, ∑ input : Fin 6, (
      nativeHodgeMatrix e (c pair) input * rawGaugePair (B1 pair) (B1 input) +
      nativeHodgeFirst e h (c pair) input *
        (rawGaugePair (B1 pair) (sourceGaugeB0 input) +
          rawGaugePair (sourceGaugeB0 pair) (B1 input)) +
      nativeHodgeSecond e h (c pair) input * rawGaugePair (sourceGaugeB0 pair) (sourceGaugeB0 input))

def nativeGaugeBFPart (jet : NativeFirstJet) (pair : Fin 6) (r : ℝ) : ℝ :=
  rawGaugePair (sourceGaugeB0 pair + r • fieldGaugeB jet.1 pair)
    (sourceGaugeCurvature0 (StageNineTopologicalFourFormPairing.twoFormComplement pair) +
      r • nativeGaugeLinearCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair) +
      r^2 • nativeGaugeQuadraticCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair))

def nativeGaugeConstitutivePart (jet : NativeFirstJet) (pair input : Fin 6) (r : ℝ) : ℝ :=
  nativeHodgeMatrix (actual.coframe 0 + r • fieldCoframe jet.1)
    (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
  rawGaugePair (sourceGaugeB0 pair + r • fieldGaugeB jet.1 pair)
    (sourceGaugeB0 input + r • fieldGaugeB jet.1 input)

def nativeGaugeConstitutiveQuadraticPart (jet : NativeFirstJet) (pair input : Fin 6) : ℝ :=
  nativeHodgeMatrix (actual.coframe 0)
    (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
    rawGaugePair (fieldGaugeB jet.1 pair) (fieldGaugeB jet.1 input) +
  nativeHodgeFirst (actual.coframe 0) (fieldCoframe jet.1)
    (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
    (rawGaugePair (sourceGaugeB0 pair) (fieldGaugeB jet.1 input) +
      rawGaugePair (fieldGaugeB jet.1 pair) (sourceGaugeB0 input)) +
  nativeHodgeSecond (actual.coframe 0) (fieldCoframe jet.1)
    (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
    rawGaugePair (sourceGaugeB0 pair) (sourceGaugeB0 input)

theorem nativeGaugeBFPart_near (jet : NativeFirstJet) (pair : Fin 6) :
    ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ (nativeGaugeBFPart jet pair) r := by
  apply Eventually.of_forall
  intro r
  exact (rawGaugePair_first _ _ (fieldGaugeB jet.1 pair)
    (nativeGaugeLinearCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair) +
      (2*r) • nativeGaugeQuadraticCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair)) r
    (coordinateAffine_derivative _ _ r) (coordinateQuadratic_derivative _ _ _ r)).differentiableAt

theorem nativeGaugeConstitutivePart_near (jet : NativeFirstJet) (pair input : Fin 6) :
    ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ (nativeGaugeConstitutivePart jet pair input) r := by
  filter_upwards [nativeHodgeCoefficient_near jet
    (StageNineTopologicalFourFormPairing.twoFormComplement pair) input] with r hH
  exact hH.mul (gaugeBB_first (sourceGaugeB0 pair) (fieldGaugeB jet.1 pair)
    (sourceGaugeB0 input) (fieldGaugeB jet.1 input) r).differentiableAt

theorem nativeGaugeDensity_second (jet : NativeFirstJet) :
    HasDerivAt (deriv (fun r : ℝ => nativeGaugeDensity (r • jet)))
      (2 * nativeGaugeQuadratic jet) 0 := by
  let BF : ℝ → ℝ := fun r => ∑ pair, nativeGaugeBFPart jet pair r
  let C : ℝ → ℝ := fun r => ∑ pair, ∑ input, nativeGaugeConstitutivePart jet pair input r
  let dBF : Fin 6 → ℝ := fun pair => 2 *
    (rawGaugePair (fieldGaugeB jet.1 pair)
      (nativeGaugeLinearCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair)) +
      rawGaugePair (sourceGaugeB0 pair)
        (nativeGaugeQuadraticCurvature jet (StageNineTopologicalFourFormPairing.twoFormComplement pair)))
  let dC : Fin 6 → Fin 6 → ℝ := fun pair input => 2 * nativeGaugeConstitutiveQuadraticPart jet pair input
  have hBF : HasDerivAt (deriv BF) (∑ pair, dBF pair) 0 :=
    finiteSum_second (nativeGaugeBFPart jet) dBF
      (fun pair => gaugeBF_second _ _ _ _ _) (nativeGaugeBFPart_near jet)
  have hCinner (pair : Fin 6) : HasDerivAt
      (deriv (fun r => ∑ input, nativeGaugeConstitutivePart jet pair input r)) (∑ input, dC pair input) 0 :=
    finiteSum_second (nativeGaugeConstitutivePart jet pair) (dC pair)
      (fun input => nativeGaugeConstitutiveTerm_second jet pair input)
      (nativeGaugeConstitutivePart_near jet pair)
  have hCnear (pair : Fin 6) : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (fun t => ∑ input, nativeGaugeConstitutivePart jet pair input t) r := by
    have allNear : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ input,
        DifferentiableAt ℝ (nativeGaugeConstitutivePart jet pair input) r :=
      eventually_all.mpr (nativeGaugeConstitutivePart_near jet pair)
    filter_upwards [allNear] with r hr
    exact DifferentiableAt.fun_sum fun input _ => hr input
  have hC : HasDerivAt (deriv C) (∑ pair, ∑ input, dC pair input) 0 :=
    finiteSum_second (fun pair r => ∑ input, nativeGaugeConstitutivePart jet pair input r)
      (fun pair => ∑ input, dC pair input) hCinner hCnear
  let sigma := positiveSmoothUnifiedSource.legacy.sigma / 2
  have hd := hBF.sub (hC.const_mul sigma)
  have nearBF : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ BF r := by
    have allNear : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ pair,
        DifferentiableAt ℝ (nativeGaugeBFPart jet pair) r := eventually_all.mpr (nativeGaugeBFPart_near jet)
    filter_upwards [allNear] with r hr
    exact DifferentiableAt.fun_sum fun pair _ => hr pair
  have nearC : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ C r := by
    filter_upwards [eventually_all.mpr hCnear] with r hr
    exact DifferentiableAt.fun_sum fun pair _ => hr pair
  have same : (fun r : ℝ => nativeGaugeDensity (r • jet)) = fun r => BF r - sigma * C r :=
    funext fun r => nativeGaugeDensity_ray jet r
  have eqDeriv : deriv (fun r => nativeGaugeDensity (r • jet)) =ᶠ[𝓝 (0 : ℝ)]
      fun r => deriv BF r - sigma * deriv C r := by
    filter_upwards [nearBF, nearC] with r hrB hrC
    rw [same]
    exact (hrB.hasDerivAt.sub (hrC.hasDerivAt.const_mul sigma)).deriv
  convert! hd.congr_of_eventuallyEq eqDeriv using 1
  simp only [dBF, dC, nativeGaugeQuadratic, nativeGaugeConstitutiveQuadraticPart]
  simp_rw [← Finset.mul_sum]
  dsimp only [sigma]
  simp only [add_comm]
  ring

theorem nativeGaugeHessian_generated (jet : NativeFirstJet) :
    fderiv ℝ (fderiv ℝ nativeGaugeDensity) 0 jet jet = 2 * nativeGaugeQuadratic jet :=
  sourceRay_second_hessian nativeGaugeDensity nativeGaugeDensity_smooth_at_zero jet
    (2 * nativeGaugeQuadratic jet) (nativeGaugeDensity_second jet)

end LowEnergy.SourcePropagationNativeActionHessian
