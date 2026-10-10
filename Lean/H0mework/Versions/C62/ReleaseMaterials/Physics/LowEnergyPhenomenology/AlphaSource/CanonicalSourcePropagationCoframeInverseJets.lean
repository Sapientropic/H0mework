import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeActionJets

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineCoframeVariation
open Filter
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
local instance h0meworkCoframeInverseJetsNormedAddCommGroup : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance h0meworkCoframeInverseJetsSeminormedAddCommGroup : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance h0meworkCoframeInverseJetsNormedSpace : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

theorem matrixRay_mul_derivative {n m k : Type*}
    [Fintype n] [Fintype m] [Fintype k]
    (f : ℝ → Matrix n m ℝ) (g : ℝ → Matrix m k ℝ)
    (df : Matrix n m ℝ) (dg : Matrix m k ℝ) (r : ℝ)
    (hf : HasDerivAt f df r) (hg : HasDerivAt g dg r) :
    HasDerivAt (fun t => f t * g t) (f r * dg + df * g r) r := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  have hs : HasDerivAt (fun t => Finset.sum Finset.univ (fun x : m => f t i x * g t x j))
      (Finset.sum Finset.univ (fun x : m => df i x * g r x j + f r i x * dg x j)) r := by
    convert! HasDerivAt.sum (u := Finset.univ) (fun x _ =>
        ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) x).mul
          ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hg x)) j)) using 1
    funext t
    simp only [Finset.sum_apply, Pi.mul_apply]
  convert! hs using 1
  show Finset.sum Finset.univ (fun x : m => f r i x * dg x j) +
    Finset.sum Finset.univ (fun x : m => df i x * g r x j) =
    Finset.sum Finset.univ (fun x : m => df i x * g r x j + f r i x * dg x j)
  rw [Finset.sum_add_distrib]
  exact add_comm _ _

theorem coframeRay_derivative (e h : LorentzianCoframe) (r : ℝ) :
    HasDerivAt (fun t : ℝ => e + t • h) h r := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [id_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul] using
    ((hasDerivAt_id r).mul_const (h i j)).const_add (e i j)

theorem coframeRay_inverse_derivative (e h : LorentzianCoframe) (r : ℝ)
    (hne : Matrix.det (e + r • h) ≠ 0) :
    HasDerivAt (fun t : ℝ => (e + t • h)⁻¹)
      (-((e + r • h)⁻¹ * h * (e + r • h)⁻¹)) r := by
  let N : ℝ → LorentzianCoframe := fun t => (e + t • h)⁻¹
  have hM := coframeRay_derivative e h r
  have hN : DifferentiableAt ℝ N r :=
    ((coframe_inv_contDiffAt (e + r • h) hne).differentiableAt
      (by simp)).comp r hM.differentiableAt
  have hd := matrixRay_mul_derivative (fun t => e + t • h) N h (deriv N r) r
    hM hN.hasDerivAt
  have hnear : ∀ᶠ t in 𝓝 r, Matrix.det (e + t • h) ≠ 0 :=
    (coframe_det_contDiff.continuous.continuousAt.comp hM.continuousAt).eventually_ne hne
  have hid : (fun t => (e + t • h) * N t) =ᶠ[𝓝 r] fun _ => 1 := by
    filter_upwards [hnear] with t ht
    exact Matrix.mul_nonsing_inv (e + t • h) (isUnit_iff_ne_zero.mpr ht)
  have hzero : (e + r • h) * deriv N r + h * N r = 0 :=
    (hd.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_const r 1)
  have hleft : N r * (e + r • h) = 1 :=
    Matrix.nonsing_inv_mul (e + r • h) (isUnit_iff_ne_zero.mpr hne)
  have hv : deriv N r = -(N r * h * N r) := by
    have hp := congrArg (fun m : LorentzianCoframe => N r * m) hzero
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hleft, Matrix.one_mul, Matrix.mul_zero,
      ← Matrix.mul_assoc] at hp
    exact eq_neg_of_add_eq_zero_left hp
  exact hv ▸ hN.hasDerivAt

theorem coframeRay_inverse_second (e h : LorentzianCoframe)
    (hne : Matrix.det e ≠ 0) :
    HasDerivAt (deriv (fun t : ℝ => (e + t • h)⁻¹))
      (2 • (e⁻¹ * h * e⁻¹ * h * e⁻¹)) 0 := by
  let N : ℝ → LorentzianCoframe := fun t => (e + t • h)⁻¹
  have hfirst : HasDerivAt N (-(e⁻¹ * h * e⁻¹)) 0 := by
    simpa only [zero_smul, add_zero] using coframeRay_inverse_derivative e h 0
      (by simpa only [zero_smul, add_zero] using hne)
  have hmul := matrixRay_mul_derivative N (fun _ => h) (-(e⁻¹ * h * e⁻¹)) 0 0
    hfirst (hasDerivAt_const 0 h)
  have hmul2 := matrixRay_mul_derivative (fun t => N t * h) N
    (N 0 * 0 + -(e⁻¹ * h * e⁻¹) * h) (-(e⁻¹ * h * e⁻¹)) 0 hmul hfirst
  have hrhs : HasDerivAt (fun t => -(N t * h * N t))
      (2 • (e⁻¹ * h * e⁻¹ * h * e⁻¹)) 0 := by
    convert! hmul2.neg using 1
    dsimp only [N]
    simp only [zero_smul, add_zero, Matrix.mul_zero, zero_add]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_add, neg_neg, two_smul,
      Matrix.mul_assoc]
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), Matrix.det (e + t • h) ≠ 0 := by
    exact (coframe_det_contDiff.continuous.continuousAt.comp
      (coframeRay_derivative e h 0).continuousAt).eventually_ne
        (by simpa only [Function.comp_apply, zero_smul, add_zero] using hne)
  have heq : deriv N =ᶠ[𝓝 (0 : ℝ)] fun t => -(N t * h * N t) := by
    filter_upwards [hnear] with t ht
    exact (coframeRay_inverse_derivative e h t ht).deriv
  exact hrhs.congr_of_eventuallyEq heq

theorem fieldCoframe_scale (r : ℝ) (f : PreparationVacuumMixedFieldReturn.Field289) :
    PreparationVacuumMixedFieldReturn.fieldCoframe (r • f) =
      r • PreparationVacuumMixedFieldReturn.fieldCoframe f := rfl

theorem nativeCoframeInverse_first (jet : NativeFirstJet) :
    HasDerivAt (fun r : ℝ => (nativeJetPoint (r • jet)).coframe⁻¹)
      (-((Stage9C.Material.SpinPair.actual.coframe 0)⁻¹ *
        PreparationVacuumMixedFieldReturn.fieldCoframe jet.1 *
        (Stage9C.Material.SpinPair.actual.coframe 0)⁻¹)) 0 := by
  simpa only [nativeJetPoint, Prod.smul_fst,
    fieldCoframe_scale, zero_smul, add_zero] using
    coframeRay_inverse_derivative (Stage9C.Material.SpinPair.actual.coframe 0)
      (PreparationVacuumMixedFieldReturn.fieldCoframe jet.1) 0
      (by simpa only [zero_smul, add_zero] using Stage9C.Material.SpinPair.actual_nondegenerate 0)

theorem nativeCoframeInverse_second (jet : NativeFirstJet) :
    HasDerivAt (deriv (fun r : ℝ => (nativeJetPoint (r • jet)).coframe⁻¹))
      (2 • ((Stage9C.Material.SpinPair.actual.coframe 0)⁻¹ *
        PreparationVacuumMixedFieldReturn.fieldCoframe jet.1 *
        (Stage9C.Material.SpinPair.actual.coframe 0)⁻¹ *
        PreparationVacuumMixedFieldReturn.fieldCoframe jet.1 *
        (Stage9C.Material.SpinPair.actual.coframe 0)⁻¹)) 0 := by
  simpa only [nativeJetPoint, Prod.smul_fst,
    fieldCoframe_scale] using
    coframeRay_inverse_second (Stage9C.Material.SpinPair.actual.coframe 0)
      (PreparationVacuumMixedFieldReturn.fieldCoframe jet.1)
      (Stage9C.Material.SpinPair.actual_nondegenerate 0)

theorem scalarJet_second_mul (f g : ℝ → ℝ) (fp gp fpp gpp : ℝ)
    (hf : HasDerivAt f fp 0) (hg : HasDerivAt g gp 0)
    (hff : HasDerivAt (deriv f) fpp 0) (hgg : HasDerivAt (deriv g) gpp 0)
    (hnearF : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ f r)
    (hnearG : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ g r) :
    HasDerivAt (deriv (fun r => f r * g r))
      (fpp * g 0 + 2 * fp * gp + f 0 * gpp) 0 := by
  have hd := (hff.mul hg).add (hf.mul hgg)
  have heq : deriv (fun r => f r * g r) =ᶠ[𝓝 (0 : ℝ)]
      fun r => deriv f r * g r + f r * deriv g r := by
    filter_upwards [hnearF, hnearG] with r hrF hrG
    exact (hrF.hasDerivAt.mul hrG.hasDerivAt).deriv
  have target : HasDerivAt (fun r => deriv f r * g r + f r * deriv g r)
      (fpp * g 0 + 2 * fp * gp + f 0 * gpp) 0 := by
    convert! hd using 1
    rw [hf.deriv, hg.deriv]
    ring
  exact target.congr_of_eventuallyEq heq

theorem matrixRay_entry_second {n m : Type*} [Fintype n] [Fintype m]
    (f : ℝ → Matrix n m ℝ) (df ddf : Matrix n m ℝ)
    (_hf : HasDerivAt f df 0) (hff : HasDerivAt (deriv f) ddf 0)
    (hnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ f r) (i : n) (j : m) :
    HasDerivAt (deriv (fun r => f r i j)) (ddf i j) 0 := by
  have hs := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hff i)) j
  have heq : deriv (fun r => f r i j) =ᶠ[𝓝 (0 : ℝ)] fun r => deriv f r i j := by
    filter_upwards [hnear] with r hr
    exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hr.hasDerivAt i)) j).deriv
  exact hs.congr_of_eventuallyEq heq

def exteriorMatrix (e : LorentzianCoframe) : Matrix (Fin 6) (Fin 6) ℝ := coframeWedge e

def exteriorTangent (e h : LorentzianCoframe) : Matrix (Fin 6) (Fin 6) ℝ :=
  StageNineCartanTangentSimplicityResponse.coframeWedgeTangent e h

def coframeHodgeMatrixConst : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => StageNineGlobalIntegratedAction.gaugeOperatorCoefficient
    EmpiricalReferenceScaleCouplingBoundary.lorentzianCoframeHodgeEquiv.toLinearMap i j

def nativeHodgeMatrix (e : LorentzianCoframe) : Matrix (Fin 6) (Fin 6) ℝ :=
  exteriorMatrix e⁻¹ * coframeHodgeMatrixConst * exteriorMatrix e

theorem nativeHodgeMatrix_original (e : LorentzianCoframe) (i j : Fin 6) :
    nativeHodgeMatrix e i j = StageNineGlobalIntegratedAction.gaugeOperatorCoefficient
      (StageNineGlobalIntegratedAction.coframeGaugeSpacetimeHodgeLinear e) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [nativeHodgeMatrix, exteriorMatrix, coframeHodgeMatrixConst,
      StageNineGlobalIntegratedAction.gaugeOperatorCoefficient,
      StageNineGlobalIntegratedAction.coframeGaugeSpacetimeHodgeLinear,
      StageNineGlobalIntegratedAction.inverseCoframeTwoFormLinear,
      StageNineGlobalIntegratedAction.coframeTwoFormLinear, LinearMap.comp_apply,
      EmpiricalReferenceScaleCouplingBoundary.lorentzianCoframeHodgeEquiv,
      lorentzianCoframeHodge, Matrix.mul_apply, Fin.sum_univ_six] <;> ring

def nativeHodgeFirst (e h : LorentzianCoframe) : Matrix (Fin 6) (Fin 6) ℝ :=
  let J : Matrix (Fin 6) (Fin 6) ℝ := coframeHodgeMatrixConst
  exteriorTangent e⁻¹ (-(e⁻¹ * h * e⁻¹)) *
    J * exteriorMatrix e + exteriorMatrix e⁻¹ * J *
      exteriorTangent e h

def nativeHodgeSecond (e h : LorentzianCoframe) : Matrix (Fin 6) (Fin 6) ℝ :=
  let J : Matrix (Fin 6) (Fin 6) ℝ := coframeHodgeMatrixConst
  (exteriorTangent e⁻¹
      (e⁻¹ * h * e⁻¹ * h * e⁻¹) + exteriorMatrix (-(e⁻¹ * h * e⁻¹))) * J * exteriorMatrix e +
    exteriorTangent e⁻¹ (-(e⁻¹ * h * e⁻¹)) * J *
      exteriorTangent e h +
    exteriorMatrix e⁻¹ * J * exteriorMatrix h

theorem coframeWedge_ray_first (f : ℝ → LorentzianCoframe) (df : LorentzianCoframe)
    (r : ℝ) (hf : HasDerivAt f df r) :
    HasDerivAt (fun t => coframeWedge (f t))
      (StageNineCartanTangentSimplicityResponse.coframeWedgeTangent (f r) df) r := by
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro b
  have entry (i j : Fin 4) := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) j
  convert! ((entry (pairFirst a) (pairFirst b)).mul
    (entry (pairSecond a) (pairSecond b))).sub
    ((entry (pairFirst a) (pairSecond b)).mul
      (entry (pairSecond a) (pairFirst b))) using 1
  unfold StageNineCartanTangentSimplicityResponse.coframeWedgeTangent
  ring

theorem coframeWedge_ray_second (f : ℝ → LorentzianCoframe) (df ddf : LorentzianCoframe)
    (hf : HasDerivAt f df 0) (hff : HasDerivAt (deriv f) ddf 0)
    (hnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ f r) :
    HasDerivAt (deriv (fun t => coframeWedge (f t)))
      (StageNineCartanTangentSimplicityResponse.coframeWedgeTangent (f 0) ddf +
        2 • coframeWedge df) 0 := by
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro b
  have entry (i j : Fin 4) := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) j
  have second (i j : Fin 4) := matrixRay_entry_second f df ddf hf hff hnear i j
  have near (i j : Fin 4) : ∀ᶠ r in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (fun t => f t i j) r := by
    filter_upwards [hnear] with r hr
    exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hr.hasDerivAt i)) j).differentiableAt
  let p := pairFirst a
  let q := pairSecond a
  let u := pairFirst b
  let v := pairSecond b
  have ha := scalarJet_second_mul (fun r => f r p u) (fun r => f r q v)
    (df p u) (df q v) (ddf p u) (ddf q v)
    (entry p u) (entry q v) (second p u) (second q v) (near p u) (near q v)
  have hb := scalarJet_second_mul (fun r => f r p v) (fun r => f r q u)
    (df p v) (df q u) (ddf p v) (ddf q u)
    (entry p v) (entry q u) (second p v) (second q u) (near p v) (near q u)
  have hs := ha.sub hb
  have heq : (fun r => deriv (fun t => coframeWedge (f t)) r a b) =ᶠ[𝓝 (0 : ℝ)]
      fun r => deriv (fun t => f t p u * f t q v) r -
        deriv (fun t => f t p v * f t q u) r := by
    filter_upwards [hnear] with r hr
    have hw := coframeWedge_ray_first f (deriv f r) r hr.hasDerivAt
    have hp := ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hr.hasDerivAt p)) u).mul
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hr.hasDerivAt q)) v)
    have hq := ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hr.hasDerivAt p)) v).mul
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hr.hasDerivAt q)) u)
    change HasDerivAt (fun t => f t p u * f t q v) _ r at hp
    change HasDerivAt (fun t => f t p v * f t q u) _ r at hq
    rw [hw.deriv, hp.deriv, hq.deriv]
    unfold StageNineCartanTangentSimplicityResponse.coframeWedgeTangent
    dsimp only [p, q, u, v]
    ring
  convert! hs.congr_of_eventuallyEq heq using 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    StageNineCartanTangentSimplicityResponse.coframeWedgeTangent, coframeWedge]
  ring

theorem matrixRay_mul_second {n m k : Type*}
    [Fintype n] [Fintype m] [Fintype k]
    (f : ℝ → Matrix n m ℝ) (g : ℝ → Matrix m k ℝ)
    (df ddf : Matrix n m ℝ) (dg ddg : Matrix m k ℝ)
    (hf : HasDerivAt f df 0) (hg : HasDerivAt g dg 0)
    (hff : HasDerivAt (deriv f) ddf 0) (hgg : HasDerivAt (deriv g) ddg 0)
    (hnearF : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ f r)
    (hnearG : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ g r) :
    HasDerivAt (deriv (fun r => f r * g r))
      (f 0 * ddg + 2 • (df * dg) + ddf * g 0) 0 := by
  have hl := matrixRay_mul_derivative f (deriv g) df ddg 0 hf hgg
  have hr := matrixRay_mul_derivative (deriv f) g ddf dg 0 hff hg
  have heq : deriv (fun r => f r * g r) =ᶠ[𝓝 (0 : ℝ)]
      fun r => f r * deriv g r + deriv f r * g r := by
    filter_upwards [hnearF, hnearG] with r hfR hgR
    exact (matrixRay_mul_derivative f g (deriv f r) (deriv g r) r
      hfR.hasDerivAt hgR.hasDerivAt).deriv
  have hs : HasDerivAt (fun r => f r * deriv g r + deriv f r * g r)
      (f 0 * ddg + 2 • (df * dg) + ddf * g 0) 0 := by
    convert! hl.add hr using 1
    rw [hf.deriv, hg.deriv]
    rw [two_smul]
    abel
  exact hs.congr_of_eventuallyEq heq

theorem nativeHodgeMatrix_first (e h : LorentzianCoframe) (hne : Matrix.det e ≠ 0) :
    HasDerivAt (fun r : ℝ => nativeHodgeMatrix (e + r • h)) (nativeHodgeFirst e h) 0 := by
  let E : ℝ → LorentzianCoframe := fun r => e + r • h
  let N : ℝ → LorentzianCoframe := fun r => (E r)⁻¹
  let J : Matrix (Fin 6) (Fin 6) ℝ := coframeHodgeMatrixConst
  have hE : HasDerivAt E h 0 := coframeRay_derivative e h 0
  have hN : HasDerivAt N (-(e⁻¹ * h * e⁻¹)) 0 := by
    simpa only [zero_smul, add_zero] using coframeRay_inverse_derivative e h 0
      (by simpa only [zero_smul, add_zero] using hne)
  have hWE : HasDerivAt (fun r => exteriorMatrix (E r)) (exteriorTangent (E 0) h) 0 :=
    coframeWedge_ray_first E h 0 hE
  have hWN : HasDerivAt (fun r => exteriorMatrix (N r))
      (exteriorTangent (N 0) (-(e⁻¹ * h * e⁻¹))) 0 :=
    coframeWedge_ray_first N (-(e⁻¹ * h * e⁻¹)) 0 hN
  have hNJ := matrixRay_mul_derivative (fun r => exteriorMatrix (N r)) (fun _ => J)
    (exteriorTangent (N 0) (-(e⁻¹ * h * e⁻¹)))
    0 0 hWN (hasDerivAt_const 0 J)
  have hh := matrixRay_mul_derivative (fun r => exteriorMatrix (N r) * J)
    (fun r => exteriorMatrix (E r))
    (exteriorMatrix (N 0) * 0 +
      exteriorTangent (N 0) (-(e⁻¹ * h * e⁻¹)) * J)
    (exteriorTangent (E 0) h) 0 hNJ hWE
  convert! hh using 1
  simp only [E, N, zero_smul, add_zero, Matrix.mul_zero, zero_add, nativeHodgeFirst]
  exact add_comm _ _

theorem exteriorTangent_add (e h k : LorentzianCoframe) :
    exteriorTangent e (h + k) = exteriorTangent e h + exteriorTangent e k := by
  ext i j
  simp only [exteriorTangent, StageNineCartanTangentSimplicityResponse.coframeWedgeTangent,
    Matrix.add_apply]
  ring

theorem exteriorTangent_zero (e : LorentzianCoframe) : exteriorTangent e 0 = 0 := by
  ext i j
  simp [exteriorTangent, StageNineCartanTangentSimplicityResponse.coframeWedgeTangent]

theorem nativeHodgeMatrix_second (e h : LorentzianCoframe) (hne : Matrix.det e ≠ 0) :
    HasDerivAt (deriv (fun r : ℝ => nativeHodgeMatrix (e + r • h)))
      (2 • nativeHodgeSecond e h) 0 := by
  let E : ℝ → LorentzianCoframe := fun r => e + r • h
  let N : ℝ → LorentzianCoframe := fun r => (E r)⁻¹
  let J := coframeHodgeMatrixConst
  let n1 := -(e⁻¹ * h * e⁻¹)
  let n2 := e⁻¹ * h * e⁻¹ * h * e⁻¹
  have hE : HasDerivAt E h 0 := coframeRay_derivative e h 0
  have hN : HasDerivAt N n1 0 := by
    simpa only [zero_smul, add_zero] using coframeRay_inverse_derivative e h 0
      (by simpa only [zero_smul, add_zero] using hne)
  have hEdd : HasDerivAt (deriv E) 0 0 := by
    have hd : deriv E = fun _ => h := funext fun r => (coframeRay_derivative e h r).deriv
    rw [hd]
    exact hasDerivAt_const 0 h
  have hNdd : HasDerivAt (deriv N) (2 • n2) 0 := coframeRay_inverse_second e h hne
  have hEnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ E r :=
    Eventually.of_forall fun r => (coframeRay_derivative e h r).differentiableAt
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), Matrix.det (E r) ≠ 0 :=
    (coframe_det_contDiff.continuous.continuousAt.comp hE.continuousAt).eventually_ne
      (by simpa only [Function.comp_apply, E, zero_smul, add_zero] using hne)
  have hNnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ N r := by
    filter_upwards [hnear] with r hr
    exact (coframeRay_inverse_derivative e h r hr).differentiableAt
  have hWE : HasDerivAt (fun r => exteriorMatrix (E r)) (exteriorTangent e h) 0 := by
    have ht : HasDerivAt (fun r => exteriorMatrix (E r)) (exteriorTangent (E 0) h) 0 :=
      coframeWedge_ray_first E h 0 hE
    simpa only [E, zero_smul, add_zero] using ht
  have hWN : HasDerivAt (fun r => exteriorMatrix (N r)) (exteriorTangent e⁻¹ n1) 0 := by
    have ht : HasDerivAt (fun r => exteriorMatrix (N r)) (exteriorTangent (N 0) n1) 0 :=
      coframeWedge_ray_first N n1 0 hN
    simpa only [E, N, zero_smul, add_zero] using ht
  have hWEdd : HasDerivAt (deriv (fun r => exteriorMatrix (E r)))
      (2 • exteriorMatrix h) 0 := by
    have ht : HasDerivAt (deriv (fun r => exteriorMatrix (E r)))
        (exteriorTangent (E 0) 0 + 2 • exteriorMatrix h) 0 :=
      coframeWedge_ray_second E h 0 hE hEdd hEnear
    simpa only [E, zero_smul, add_zero, exteriorTangent_zero, zero_add] using ht
  have hWNdd : HasDerivAt (deriv (fun r => exteriorMatrix (N r)))
      (exteriorTangent e⁻¹ (2 • n2) + 2 • exteriorMatrix n1) 0 := by
    have ht : HasDerivAt (deriv (fun r => exteriorMatrix (N r)))
        (exteriorTangent (N 0) (2 • n2) + 2 • exteriorMatrix n1) 0 :=
      coframeWedge_ray_second N n1 (2 • n2) hN hNdd hNnear
    simpa only [E, N, zero_smul, add_zero] using ht
  have hWEnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => exteriorMatrix (E t)) r := by
    filter_upwards [hEnear] with r hr
    exact (coframeWedge_ray_first E (deriv E r) r hr.hasDerivAt).differentiableAt
  have hWNnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => exteriorMatrix (N t)) r := by
    filter_upwards [hNnear] with r hr
    exact (coframeWedge_ray_first N (deriv N r) r hr.hasDerivAt).differentiableAt
  have hJ : HasDerivAt (fun _ : ℝ => J) 0 0 := hasDerivAt_const 0 J
  have hJdd : HasDerivAt (deriv (fun _ : ℝ => J)) 0 0 := by
    have ht := hasDerivAt_const (0 : ℝ) (0 : Matrix (Fin 6) (Fin 6) ℝ)
    convert! ht using 1
    funext r
    exact (hasDerivAt_const r J).deriv
  have hNJ : HasDerivAt (fun r => exteriorMatrix (N r) * J) (exteriorTangent e⁻¹ n1 * J) 0 := by
    simpa only [Matrix.mul_zero, zero_add] using
      matrixRay_mul_derivative (fun r => exteriorMatrix (N r)) (fun _ => J)
        (exteriorTangent e⁻¹ n1) 0 0 hWN hJ
  have hNJdd : HasDerivAt (deriv (fun r => exteriorMatrix (N r) * J))
      ((exteriorTangent e⁻¹ (2 • n2) + 2 • exteriorMatrix n1) * J) 0 := by
    simpa only [Matrix.mul_zero, smul_zero, zero_add] using
      matrixRay_mul_second (fun r => exteriorMatrix (N r)) (fun _ => J)
        (exteriorTangent e⁻¹ n1) (exteriorTangent e⁻¹ (2 • n2) + 2 • exteriorMatrix n1)
        0 0 hWN hJ hWNdd hJdd hWNnear (Eventually.of_forall fun r => differentiableAt_const J)
  have hNJnear : ∀ᶠ r in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (fun t => exteriorMatrix (N t) * J) r := by
    filter_upwards [hWNnear] with r hr
    exact (matrixRay_mul_derivative (fun t => exteriorMatrix (N t)) (fun _ => J)
      (deriv (fun t => exteriorMatrix (N t)) r) 0 r hr.hasDerivAt (hasDerivAt_const r J)).differentiableAt
  have hh := matrixRay_mul_second (fun r => exteriorMatrix (N r) * J) (fun r => exteriorMatrix (E r))
    (exteriorTangent e⁻¹ n1 * J)
    ((exteriorTangent e⁻¹ (2 • n2) + 2 • exteriorMatrix n1) * J)
    (exteriorTangent e h) (2 • exteriorMatrix h) hNJ hWE hNJdd hWEdd hNJnear hWEnear
  convert! hh using 1
  simp only [E, N, zero_smul, add_zero, nativeHodgeSecond]
  dsimp only [J, n1, n2]
  simp only [two_smul, exteriorTangent_add, Matrix.add_mul, Matrix.mul_add]
  abel

theorem nativeHodgeMatrix_smooth (e : LorentzianCoframe) (hne : Matrix.det e ≠ 0) :
    ContDiffAt ℝ ∞ nativeHodgeMatrix e := by
  apply contDiffAt_pi'
  intro i
  apply contDiffAt_pi'
  intro j
  rw [show (fun u => nativeHodgeMatrix u i j) = fun u =>
      StageNineGlobalIntegratedAction.gaugeOperatorCoefficient
        (StageNineGlobalIntegratedAction.coframeGaugeSpacetimeHodgeLinear u) i j from
      funext fun u => nativeHodgeMatrix_original u i j]
  exact StageNineCoframeLocalDifferentiability.coframeHodgeOperatorCoefficient_contDiffAt e hne i j

theorem nativeCoframe_ray (jet : NativeFirstJet) (r : ℝ) :
    (nativeJetPoint (r • jet)).coframe = Stage9C.Material.SpinPair.actual.coframe 0 +
      r • PreparationVacuumMixedFieldReturn.fieldCoframe jet.1 := by
  simp only [nativeJetPoint, Prod.smul_fst, fieldCoframe_scale]

theorem nativeConstitutiveCoefficient_ray (jet : NativeFirstJet) (r coupling : ℝ) (i j : Fin 6) :
    nativeConstitutiveCoefficient coupling i j (r • jet) = coupling *
      nativeHodgeMatrix (Stage9C.Material.SpinPair.actual.coframe 0 +
        r • PreparationVacuumMixedFieldReturn.fieldCoframe jet.1) i j := by
  change coupling * StageNineGlobalIntegratedAction.gaugeOperatorCoefficient
    (StageNineGlobalIntegratedAction.coframeGaugeSpacetimeHodgeLinear
      (nativeJetPoint (r • jet)).coframe) i j = _
  rw [nativeCoframe_ray]
  exact congrArg (coupling * ·) (nativeHodgeMatrix_original _ i j).symm

theorem nativeConstitutiveCoefficient_second (jet : NativeFirstJet) (coupling : ℝ) (i j : Fin 6) :
    HasDerivAt (deriv (fun r : ℝ => nativeConstitutiveCoefficient coupling i j (r • jet)))
      (coupling * (2 • nativeHodgeSecond (Stage9C.Material.SpinPair.actual.coframe 0)
        (PreparationVacuumMixedFieldReturn.fieldCoframe jet.1)) i j) 0 := by
  let e := Stage9C.Material.SpinPair.actual.coframe 0
  let h := PreparationVacuumMixedFieldReturn.fieldCoframe jet.1
  let M : ℝ → Matrix (Fin 6) (Fin 6) ℝ := fun r => nativeHodgeMatrix (e + r • h)
  have hne : Matrix.det e ≠ 0 := Stage9C.Material.SpinPair.actual_nondegenerate 0
  have hm : HasDerivAt M (nativeHodgeFirst e h) 0 := nativeHodgeMatrix_first e h hne
  have hmm : HasDerivAt (deriv M) (2 • nativeHodgeSecond e h) 0 := nativeHodgeMatrix_second e h hne
  have he : ContDiff ℝ ∞ (fun r : ℝ => e + r • h) := by
    apply contDiff_pi'
    intro a
    apply contDiff_pi'
    intro b
    change ContDiff ℝ ∞ (fun r : ℝ => e a b + r * h a b)
    fun_prop
  have hms : ContDiffAt ℝ ∞ M 0 := by
    have hs : ContDiffAt ℝ ∞ nativeHodgeMatrix (e + (0 : ℝ) • h) := by
      simpa only [zero_smul, add_zero] using nativeHodgeMatrix_smooth e hne
    exact hs.comp (f := fun r : ℝ => e + r • h) 0 he.contDiffAt
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ M r := by
    have hs : ContDiffAt ℝ 1 M 0 := hms.of_le (by simp)
    exact (hs.eventually (by simp)).mono fun _ hx => hx.differentiableAt (by simp)
  have first := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hm i)) j
  have second := matrixRay_entry_second M (nativeHodgeFirst e h)
    (2 • nativeHodgeSecond e h) hm hmm hnear i j
  have near : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => M t i j) r := by
    filter_upwards [hnear] with r hr
    exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hr.hasDerivAt i)) j).differentiableAt
  have constSecond : HasDerivAt (deriv (fun _ : ℝ => coupling)) 0 0 := by
    convert! hasDerivAt_const (0 : ℝ) (0 : ℝ) using 1
    funext r
    exact (hasDerivAt_const r coupling).deriv
  have hp := scalarJet_second_mul (fun _ : ℝ => coupling) (fun r => M r i j)
    0 (nativeHodgeFirst e h i j) 0 ((2 • nativeHodgeSecond e h) i j)
    (hasDerivAt_const 0 coupling) first constSecond second
    (Eventually.of_forall fun _ => differentiableAt_const coupling) near
  have same : (fun r : ℝ => nativeConstitutiveCoefficient coupling i j (r • jet)) =
      fun r => coupling * M r i j := funext fun r => nativeConstitutiveCoefficient_ray jet r coupling i j
  rw [same]
  simpa only [zero_mul, mul_zero, zero_add, add_zero] using hp

end LowEnergy.SourcePropagationNativeActionHessian
