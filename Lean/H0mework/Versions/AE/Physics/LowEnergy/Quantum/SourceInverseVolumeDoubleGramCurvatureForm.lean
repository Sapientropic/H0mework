import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeMixedCurvatureReduction
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeBrokenGaussCurvatureCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeMomentumCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceDoubleGramCurvatureForm
open GaussLiveMomentum GaussCoreDifferential GaussCoreHilbert GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussNativeMatter GaussFockPair
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceElectricColumns SourceNativeMixedCurvatureReduction
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeAuxiliaryVariation
open StageNineCoframeGravityGaugeRegularity SourceQuantumResidualGaugeSlice StageNineP286LinkedActiveGaugeBFAlgebra
open scoped InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem scalar_skew (a : NativeLie) (x y : Scalar) :
    inner ℝ (scalarP286ActionBilinear a x) y+inner ℝ x (scalarP286ActionBilinear a y)=0 := by
  have h := StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a)) x y
  rw [original_scalar_pairing,original_scalar_pairing] at h
  exact h

private theorem native_skew (a b c : NativeLie) :
    inner ℝ (SourceCartanCubic.nativeBracket a b) c+
      inner ℝ b (SourceCartanCubic.nativeBracket a c)=0 := by
  change p286CoordinateLiePairing (jointP286CoordinateLieBracket a b) c+
    p286CoordinateLiePairing b (jointP286CoordinateLieBracket a c)=0
  exact p286CoordinateLiePairing_adjoint_skew a b c

def scalarRotation (v : Ambient) (j i : ScalarIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (scalarBasis j) (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i))

def gaugeRotation (r : ScalarIndex) (b a : LieIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (lieBasis b) (SourceCartanCubic.nativeBracket (inverseL z (scalarDirection r)).1 (lieBasis a))

private theorem scalar_rotation_smooth (v : Ambient) (j i : ScalarIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (scalarRotation v j i) z.val := by
  let L : NativeLie →L[ℝ] Scalar := (SourceQuantumScalarChart.action (scalarBasis i)).toContinuousLinearMap
  exact contDiffAt_const.inner ℝ (L.contDiff.contDiffAt.comp z.val
    (((inverse_smooth z).clm_apply (contDiffAt_const (c := v))).fst))

private theorem gauge_rotation_smooth (r : ScalarIndex) (b a : LieIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (gaugeRotation r b a) z.val := by
  let L : NativeLie →L[ℝ] NativeLie := (SourceCartanCubic.nativeBracket.flip (lieBasis a)).toContinuousLinearMap
  exact contDiffAt_const.inner ℝ (L.contDiff.contDiffAt.comp z.val
    (((inverse_smooth z).clm_apply (contDiffAt_const (c := scalarDirection r))).fst))

def scalarRotationAction (v : Ambient) (j i : ScalarIndex) : End :=
  multiply (scalarRotation v j i) (scalar_rotation_smooth v j i)

def gaugeRotationAction (r : ScalarIndex) (b a : LieIndex) : End :=
  multiply (gaugeRotation r b a) (gauge_rotation_smooth r b a)

private theorem scalar_rotation_skew (v : Ambient) (j i : ScalarIndex) (z : SourceCoordinateSlice) :
    scalarRotation v j i z= -scalarRotation v i j z := by
  have h := scalar_skew (inverseL z v).1 (scalarBasis i) (scalarBasis j)
  rw [real_inner_comm (scalarBasis j) (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i))] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem gauge_rotation_skew (r : ScalarIndex) (b a : LieIndex) (z : SourceCoordinateSlice) :
    gaugeRotation r b a z= -gaugeRotation r a b z := by
  have h := native_skew (inverseL z (scalarDirection r)).1 (lieBasis a) (lieBasis b)
  rw [real_inner_comm (lieBasis b) (SourceCartanCubic.nativeBracket (inverseL z (scalarDirection r)).1 (lieBasis a))] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem scalar_rotation_action_skew (v : Ambient) (j i : ScalarIndex) :
    scalarRotationAction v j i= -scalarRotationAction v i j := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (scalarRotation v j i z : ℂ) • f z= -((scalarRotation v i j z : ℂ) • f z)
  rw [scalar_rotation_skew,Complex.ofReal_neg,neg_smul]

private theorem gauge_rotation_action_skew (r : ScalarIndex) (b a : LieIndex) :
    gaugeRotationAction r b a= -gaugeRotationAction r a b := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (gaugeRotation r b a z : ℂ) • f z= -((gaugeRotation r a b z : ℂ) • f z)
  rw [gauge_rotation_skew,Complex.ofReal_neg,neg_smul]

private theorem real_fock_smul (r : ℝ) (f : FockFiber) : r • f=(r : ℂ) • f := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem scalar_rotation_momentum (v : Ambient) (i : ScalarIndex) (z : SourceCoordinateSlice) (f : QuantumTest) :
    covariantMomentum (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i),0) f z=
      ∑ j : ScalarIndex,(scalarRotation v j i z : ℂ) • covariantMomentum (scalarDirection j) f z := by
  have he : (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i), (0 : Gauge))=
      ∑ j : ScalarIndex,scalarRotation v j i z • scalarDirection j := by
    apply Prod.ext
    · simpa only [Prod.fst_sum,Prod.smul_fst,scalarDirection,scalarRotation] using
        (scalarBasis.sum_repr' (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i))).symm
    · simp only [Prod.snd_sum,Prod.smul_snd,scalarDirection,smul_zero,Finset.sum_const_zero]
  have hp := congrArg (pointMomentum f z) he
  simp only [map_sum,map_smul,real_fock_smul] at hp
  change covariantMomentum (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i),0) f z=
      ∑ j : ScalarIndex,(scalarRotation v j i z : ℂ) • covariantMomentum (scalarDirection j) f z at hp
  exact hp

private def gaugeInsert (j : Fin 3) : NativeLie →ₗ[ℝ] Gauge :=
  gaugeCoordinates.symm.toLinearMap.comp (LinearMap.single ℝ (fun _ : Fin 3 => NativeLie) j)

private theorem gauge_insert_bracket (j : Fin 3) (a b : NativeLie) :
    nativeGauge a (gaugeInsert j b)=gaugeInsert j (SourceCartanCubic.nativeBracket a b) := by
  apply gaugeCoordinates.injective
  funext k
  have hg (x : NativeLie) : gaugeCoordinates (gaugeInsert j x)=Pi.single j x := by
    change gaugeCoordinates (gaugeCoordinates.symm (Pi.single j x))=_
    rw [gaugeCoordinates.apply_symm_apply]
  have hn (x : Gauge) : gaugeCoordinates (nativeGauge a x) k=
      SourceCartanCubic.nativeBracket a (gaugeCoordinates x k) := rfl
  rw [hn,hg,hg]
  by_cases h : k=j
  · subst k
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h,map_zero]

private theorem gauge_rotation_momentum (r : ScalarIndex) (j : Fin 3) (a : LieIndex)
    (z : SourceCoordinateSlice) (f : QuantumTest) :
    covariantMomentum (0,nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2) f z=
      ∑ b : LieIndex,(gaugeRotation r b a z : ℂ) • covariantMomentum (gaugeDirection j b) f z := by
  have hg : nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2=
      ∑ b : LieIndex,gaugeRotation r b a z • (gaugeDirection j b).2 := by
    change nativeGauge (inverseL z (scalarDirection r)).1 (gaugeInsert j (lieBasis a))=_
    rw [gauge_insert_bracket]
    have h := congrArg (gaugeInsert j) (lieBasis.sum_repr'
      (SourceCartanCubic.nativeBracket (inverseL z (scalarDirection r)).1 (lieBasis a)))
    simp only [map_sum,map_smul] at h
    exact h.symm
  have he : ((0,nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2) : Ambient)=
      ∑ b : LieIndex,gaugeRotation r b a z • gaugeDirection j b := by
    apply Prod.ext
    · simp only [Prod.fst_sum,Prod.smul_fst,gaugeDirection,smul_zero,Finset.sum_const_zero]
    · simpa only [Prod.snd_sum,Prod.smul_snd] using hg
  have hp := congrArg (pointMomentum f z) he
  simp only [map_sum,map_smul,real_fock_smul] at hp
  change covariantMomentum (0,nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2) f z=
      ∑ b : LieIndex,(gaugeRotation r b a z : ℂ) • covariantMomentum (gaugeDirection j b) f z at hp
  exact hp

private theorem real_multiplier_current (u : Ambient) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) (z : physicalChart) :
    covariantMomentum u (multiply c hc f) z.val-multiply c hc (covariantMomentum u f) z.val=
      (-Complex.I) • ((fderiv ℝ c z.val (direction u z.val) : ℂ) • f z.val) := by
  have he : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
    funext x
    exact (real_fock_smul _ _).symm
  have hd : directional u (multiply c hc f) z.val=(c z.val : ℂ) • directional u f z.val+
      (fderiv ℝ c z.val (direction u z.val) : ℂ) • f z.val := by
    rw [directional_apply,he,fderiv_fun_smul ((hc z).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt]
    change c z.val • fderiv ℝ f z.val (direction u z.val)+fderiv ℝ c z.val (direction u z.val) • f z.val=_
    rw [real_fock_smul,real_fock_smul]
    rfl
  change (-Complex.I) • (directional u (multiply c hc f) z.val+connection u z.val ((c z.val : ℂ) • f z.val))-
    (c z.val : ℂ) • ((-Complex.I) • (directional u f z.val+connection u z.val (f z.val)))=_
  rw [hd,map_smul]
  module

open SourceNativeMomentumCurvature

private theorem curvature_frame (r : ScalarIndex) (j : Fin 3) (a : LieIndex) :
    curvatureRow (scalarDirection r) (gaugeDirection j a)=
      Complex.I • ∑ i : ScalarIndex,scalarRotationAction (gaugeDirection j a) i r*covariantMomentum (scalarDirection i)+
      (-Complex.I) • ∑ b : LieIndex,gaugeRotationAction r b a*covariantMomentum (gaugeDirection j b) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have h := original_scalar_gauge_curvature ⟨z,hz⟩ (scalarBasis r) (gaugeDirection j a).2 f
    have ha := scalar_rotation_momentum (gaugeDirection j a) r z f
    change covariantMomentum (scalarP286ActionBilinear (inverseL z (0,(gaugeDirection j a).2)).1 (scalarBasis r),0) f z=_ at ha
    rw [original_gauge_inverse ⟨z,hz⟩] at ha
    rw [ha] at h
    change covariantMomentum (scalarDirection r) (covariantMomentum (gaugeDirection j a) f) z-
      covariantMomentum (gaugeDirection j a) (covariantMomentum (scalarDirection r) f) z=
      (-Complex.I) • (-(∑ i : ScalarIndex,(scalarRotation (gaugeDirection j a) i r z : ℂ) • covariantMomentum (scalarDirection i) f z)+
        covariantMomentum (0,nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2) f z) at h
    rw [gauge_rotation_momentum] at h
    simp only [curvatureRow,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.add_apply,
      LinearMap.smul_apply,LinearMap.sum_apply,add_apply,smul_apply,sum_apply,
      scalarRotationAction,gaugeRotationAction,multiply_apply]
    change covariantMomentum (scalarDirection r) (covariantMomentum (gaugeDirection j a) f) z-
      covariantMomentum (gaugeDirection j a) (covariantMomentum (scalarDirection r) f) z=_ at h
    change covariantMomentum (scalarDirection r) (covariantMomentum (gaugeDirection j a) f) z-
      covariantMomentum (gaugeDirection j a) (covariantMomentum (scalarDirection r) f) z=_
    linear_combination (norm := module) h
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem positive_rotation_row (P D C B : End) :
    (P-Complex.I • D)*(Complex.I • (C*B))+(Complex.I • (C*B))*P=
      Complex.I • (C*(P*B+B*P))+(Complex.I • (P*C-C*P)+D*C)*B := by
  simp only [sub_mul,smul_mul_assoc,mul_smul_comm,smul_smul,Complex.I_mul_I,neg_one_smul,
    mul_add,add_mul,smul_sub,mul_assoc]
  module

private theorem negative_rotation_row (P D C B : End) :
    (P-Complex.I • D)*((-Complex.I) • (C*B))+((-Complex.I) • (C*B))*P=
      (-Complex.I) • (C*(P*B+B*P))+((-Complex.I) • (P*C-C*P)-D*C)*B := by
  have h := positive_rotation_row P D C B
  simp only [neg_smul,mul_neg,neg_mul,sub_mul]
  simp only [sub_mul,add_mul] at h
  linear_combination (norm := module) -h

/-- Exact zero-order density contact from the already generated native and transpose curvature. -/
def densityContact (u v : Ambient) : End := curvatureRow u v-transposeCurvatureRow u v

def scalarGram : End := ∑ i : ScalarIndex,GaussMomentumAdjoint.adjoint (scalarDirection i)*covariantMomentum (scalarDirection i)

def scalarCoefficientCurrent (v : Ambient) (j i : ScalarIndex) : End :=
  covariantMomentum (scalarDirection i)*scalarRotationAction v j i-
    scalarRotationAction v j i*covariantMomentum (scalarDirection i)

def gaugeCoefficientCurrent (r : ScalarIndex) (b a : LieIndex) : End :=
  covariantMomentum (scalarDirection r)*gaugeRotationAction r b a-
    gaugeRotationAction r b a*covariantMomentum (scalarDirection r)

def scalarGaugeLowerRow (r : ScalarIndex) (j : Fin 3) (a : LieIndex) : End :=
  (∑ i : ScalarIndex,(Complex.I • scalarCoefficientCurrent (gaugeDirection j a) i r+
      divergenceAction (scalarDirection r)*scalarRotationAction (gaugeDirection j a) i r)*covariantMomentum (scalarDirection i))+
  (∑ b : LieIndex,((-Complex.I) • gaugeCoefficientCurrent r b a-
      divergenceAction (scalarDirection r)*gaugeRotationAction r b a)*covariantMomentum (gaugeDirection j b))+
  densityContact (gaugeDirection j a) (scalarDirection r)*covariantMomentum (scalarDirection r)

private theorem scalar_gram_row (r : ScalarIndex) (j : Fin 3) (a : LieIndex) :
    (GaussMomentumAdjoint.adjoint (scalarDirection r)*covariantMomentum (scalarDirection r))*covariantMomentum (gaugeDirection j a)-
      covariantMomentum (gaugeDirection j a)*(GaussMomentumAdjoint.adjoint (scalarDirection r)*covariantMomentum (scalarDirection r))=
      Complex.I • ∑ i : ScalarIndex,scalarRotationAction (gaugeDirection j a) i r*
        (covariantMomentum (scalarDirection r)*covariantMomentum (scalarDirection i)+
          covariantMomentum (scalarDirection i)*covariantMomentum (scalarDirection r))+
      (-Complex.I) • ∑ b : LieIndex,gaugeRotationAction r b a*
        (covariantMomentum (scalarDirection r)*covariantMomentum (gaugeDirection j b)+
          covariantMomentum (gaugeDirection j b)*covariantMomentum (scalarDirection r))+
      scalarGaugeLowerRow r j a := by
  have he : (GaussMomentumAdjoint.adjoint (scalarDirection r)*covariantMomentum (scalarDirection r))*covariantMomentum (gaugeDirection j a)-
      covariantMomentum (gaugeDirection j a)*(GaussMomentumAdjoint.adjoint (scalarDirection r)*covariantMomentum (scalarDirection r))=
      GaussMomentumAdjoint.adjoint (scalarDirection r)*curvatureRow (scalarDirection r) (gaugeDirection j a)+
        curvatureRow (scalarDirection r) (gaugeDirection j a)*covariantMomentum (scalarDirection r)+
        densityContact (gaugeDirection j a) (scalarDirection r)*covariantMomentum (scalarDirection r) := by
    unfold densityContact curvatureRow transposeCurvatureRow
    noncomm_ring
  rw [he,curvature_frame,original_adjoint_divergence]
  have ha := Finset.sum_congr (s₁ := (Finset.univ : Finset ScalarIndex)) rfl (fun i _ =>
    positive_rotation_row (covariantMomentum (scalarDirection r)) (divergenceAction (scalarDirection r))
      (scalarRotationAction (gaugeDirection j a) i r) (covariantMomentum (scalarDirection i)))
  have hb := Finset.sum_congr (s₁ := (Finset.univ : Finset LieIndex)) rfl (fun b _ =>
    negative_rotation_row (covariantMomentum (scalarDirection r)) (divergenceAction (scalarDirection r))
      (gaugeRotationAction r b a) (covariantMomentum (gaugeDirection j b)))
  simp only [Finset.sum_add_distrib,←Finset.smul_sum] at ha hb
  unfold scalarGaugeLowerRow scalarCoefficientCurrent gaugeCoefficientCurrent
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,←Finset.smul_sum] at ha hb ⊢
  linear_combination (norm := module) ha+hb

private theorem scalar_rotation_casimir (v : Ambient) :
    (∑ r : ScalarIndex,∑ i : ScalarIndex,scalarRotationAction v i r*
      (covariantMomentum (scalarDirection r)*covariantMomentum (scalarDirection i)+
        covariantMomentum (scalarDirection i)*covariantMomentum (scalarDirection r)))=0 := by
  let S := ∑ r : ScalarIndex,∑ i : ScalarIndex,scalarRotationAction v i r*
      (covariantMomentum (scalarDirection r)*covariantMomentum (scalarDirection i)+
        covariantMomentum (scalarDirection i)*covariantMomentum (scalarDirection r))
  have he : S= -S := by
    calc
      _ = ∑ i : ScalarIndex,∑ r : ScalarIndex,scalarRotationAction v i r*
        (covariantMomentum (scalarDirection r)*covariantMomentum (scalarDirection i)+
          covariantMomentum (scalarDirection i)*covariantMomentum (scalarDirection r)) := Finset.sum_comm
      _ = _ := by
        simp only [S,←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro i _
        rw [scalar_rotation_action_skew v r i,neg_mul,add_comm (covariantMomentum (scalarDirection i)*covariantMomentum (scalarDirection r))]
  have hz : (2 : ℂ) • S=0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp he
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The complete scalar rotation leaves the mixed Gram current before any estimate. -/
theorem original_scalar_gram_gauge_current (j : Fin 3) (a : LieIndex) :
    scalarGram*covariantMomentum (gaugeDirection j a)-covariantMomentum (gaugeDirection j a)*scalarGram=
      (-Complex.I) • (∑ r : ScalarIndex,∑ b : LieIndex,gaugeRotationAction r b a*
        (covariantMomentum (scalarDirection r)*covariantMomentum (gaugeDirection j b)+
          covariantMomentum (gaugeDirection j b)*covariantMomentum (scalarDirection r)))+
      ∑ r : ScalarIndex,scalarGaugeLowerRow r j a := by
  simp only [scalarGram,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,scalar_gram_row,
    Finset.sum_add_distrib,←Finset.smul_sum,scalar_rotation_casimir,smul_zero,zero_add]

private theorem pair_add (p q r : QuantumTest) : sourcePair p (q+r)=sourcePair p q+sourcePair p r := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_neg (p q : QuantumTest) : sourcePair p (-q)= -sourcePair p q := by
  simp only [sourcePair,map_neg,inner_neg_right]

private theorem skew_gram_form {ι : Type*} [Fintype ι] (A AD : End) (B : ι → End) (M : ι → ι → End)
    (hA : ∀ p q,sourcePair (A p) q=sourcePair p (AD q))
    (hM : ∀ i j p q,sourcePair p (M i j q)=sourcePair (M i j p) q)
    (hskew : ∀ i j,M i j= -M j i) (f : QuantumTest) :
    (∑ i : ι,∑ j : ι,sourcePair (B i f) (M i j (A (B j f)+B j (A f)))).re=
      -(∑ i : ι,∑ j : ι,sourcePair (B i f) ((AD*M i j-M i j*A) (B j f))).re-
      (∑ i : ι,∑ j : ι,sourcePair (B i f) (M i j ((A*B j-B j*A) f))).re := by
  let T₁ := ∑ i : ι,∑ j : ι,sourcePair (B i f) (M i j (A (B j f)))
  let T₂ := ∑ i : ι,∑ j : ι,sourcePair (B i f) (M i j (B j (A f)))
  let S := ∑ i : ι,∑ j : ι,sourcePair (B i f) ((AD*M i j-M i j*A) (B j f))
  let C := ∑ i : ι,∑ j : ι,sourcePair (B i f) (M i j ((A*B j-B j*A) f))
  have hc : C=T₁-T₂ := by
    simp only [C,T₁,T₂,LinearMap.sub_apply,Module.End.mul_apply,map_sub,pair_sub,Finset.sum_sub_distrib]
  have hs : S+T₁=∑ i : ι,∑ j : ι,sourcePair (B i f) (AD (M i j (B j f))) := by
    simp only [S,T₁,LinearMap.sub_apply,Module.End.mul_apply,pair_sub,Finset.sum_sub_distrib]
    abel
  have ht : star T₁= -(S+T₁) := by
    calc
      _ = ∑ i : ι,∑ j : ι,sourcePair (M i j (A (B j f))) (B i f) := by
        simp only [T₁,star_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact pair_conjugate _ _
      _ = ∑ i : ι,∑ j : ι,sourcePair (B j f) (AD (M i j (B i f))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [←hM,hA]
      _ = ∑ j : ι,∑ i : ι,sourcePair (B j f) (AD (M i j (B i f))) := Finset.sum_comm
      _ = -(∑ i : ι,∑ j : ι,sourcePair (B i f) (AD (M i j (B j f)))) := by
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [hskew j i,LinearMap.neg_apply,map_neg,pair_neg]
      _ = -(S+T₁) := congrArg Neg.neg hs.symm
  have hreal := congrArg Complex.re ht
  simp only [Complex.star_def,Complex.conj_re,Complex.neg_re,Complex.add_re] at hreal
  have hcReal := congrArg Complex.re hc
  simp only [Complex.sub_re] at hcReal
  have hleft : (∑ i : ι,∑ j : ι,sourcePair (B i f) (M i j (A (B j f)+B j (A f))))=T₁+T₂ := by
    simp only [map_add,pair_add,Finset.sum_add_distrib,T₁,T₂]
  rw [hleft]
  change (T₁+T₂).re= -S.re-C.re
  rw [Complex.add_re]
  linarith

abbrev GaugeRow := Fin 3 × LieIndex

def gaugeMomentum (i : GaugeRow) : End := covariantMomentum (gaugeDirection i.1 i.2)

def weightedGaugeRotation (r : ScalarIndex) (i j : GaugeRow) : End :=
  multiply (fun z => gaugeWeight z i.1 j.1*gaugeRotation r j.2 i.2 z)
    (fun z => (gaugeWeight_smooth i.1 j.1 z).mul (gauge_rotation_smooth r j.2 i.2 z))

def weightedGaugeContact (r : ScalarIndex) (i j : GaugeRow) : End :=
  GaussMomentumAdjoint.adjoint (scalarDirection r)*weightedGaugeRotation r i j-
    weightedGaugeRotation r i j*covariantMomentum (scalarDirection r)

private theorem weighted_gauge_rotation_skew (r : ScalarIndex) (i j : GaugeRow) :
    weightedGaugeRotation r i j= -weightedGaugeRotation r j i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((gaugeWeight z i.1 j.1*gaugeRotation r j.2 i.2 z : ℝ) : ℂ) • f z=
    -(((gaugeWeight z j.1 i.1*gaugeRotation r i.2 j.2 z : ℝ) : ℂ) • f z)
  rw [gaugeWeight_symmetric z i.1 j.1,gauge_rotation_skew r j.2 i.2,mul_neg,Complex.ofReal_neg,neg_smul]

/-- The gauge rotation's third-order anticommutator is replaced by its true transpose contact and native curvature. -/
theorem original_gauge_rotation_form (r : ScalarIndex) (f : QuantumTest) :
    (∑ i : GaugeRow,∑ j : GaugeRow,sourcePair (gaugeMomentum i f)
      (weightedGaugeRotation r i j (covariantMomentum (scalarDirection r) (gaugeMomentum j f)+
        gaugeMomentum j (covariantMomentum (scalarDirection r) f)))).re=
      -(∑ i : GaugeRow,∑ j : GaugeRow,sourcePair (gaugeMomentum i f)
        (weightedGaugeContact r i j (gaugeMomentum j f))).re-
      (∑ i : GaugeRow,∑ j : GaugeRow,sourcePair (gaugeMomentum i f)
        (weightedGaugeRotation r i j (curvatureRow (scalarDirection r) (gaugeDirection j.1 j.2) f))).re := by
  exact skew_gram_form (covariantMomentum (scalarDirection r)) (GaussMomentumAdjoint.adjoint (scalarDirection r))
    gaugeMomentum (weightedGaugeRotation r)
    (fun p q => (GaussNativeForm.adjoint_pair _ p q).symm)
    (fun i j p q => multiply_pair _ _ p q) (weighted_gauge_rotation_skew r) f

private theorem metric_derivative (z : physicalChart) (u : Ambient) (i j : Fin 3) :
    fderiv ℝ (fun x => gaugeWeight x i j) z.val (direction u z.val)=0 := by
  have hf := ((gaugeWeight_smooth i j z).differentiableAt (by simp)).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ => z.val+t • direction u z.val) (direction u z.val) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (direction u z.val)).const_add z.val
  have hd := hf.comp_hasDerivAt_of_eq 0 ht (by simp)
  have he : (fun t : ℝ => gaugeWeight (z.val+t • direction u z.val) i j)=fun _ : ℝ => gaugeWeight z.val i j := by
    funext t
    simp only [gaugeWeight,volume,inverseSpatial,direction,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
  change HasDerivAt (fun t : ℝ => gaugeWeight (z.val+t • direction u z.val) i j)
    (fderiv ℝ (fun x => gaugeWeight x i j) z.val (direction u z.val)) 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 _)

private theorem momentum_metric (u : Ambient) (i j : Fin 3) :
    Commute (covariantMomentum u) (GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · let M := GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
    have he : (M f : SourceCoordinateSlice → FockFiber)=fun x => gaugeWeight x i j • f x := by
      funext x
      exact (real_fock_smul _ _).symm
    have hd : directional u (M f) z=(gaugeWeight z i j : ℂ) • directional u f z := by
      rw [directional_apply,he,fderiv_fun_smul ((gaugeWeight_smooth i j ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change gaugeWeight z i j • fderiv ℝ f z (direction u z)+
        fderiv ℝ (fun x => gaugeWeight x i j) z (direction u z) • f z=_
      rw [metric_derivative ⟨z,hz⟩,zero_smul,add_zero,real_fock_smul]
      rfl
    change (-Complex.I) • (directional u (M f) z+connection u z ((gaugeWeight z i j : ℂ) • f z))=
      (gaugeWeight z i j : ℂ) • ((-Complex.I) • (directional u f z+connection u z (f z)))
    rw [hd,map_smul,←smul_add,smul_comm]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm


private theorem scalar_gram_pair (f g : QuantumTest) : sourcePair f (scalarGram g)=sourcePair (scalarGram f) g := by
  simp only [scalarGram,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact (GaussNativeForm.adjoint_pair _ _ _).trans (GaussMomentumAdjoint.momentum_pair _ _ _)

private theorem adjoint_metric (u : Ambient) (i j : Fin 3) :
    Commute (GaussMomentumAdjoint.adjoint u) (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
  apply LinearMap.ext
  intro q
  apply SourceCoframeVolume.pair_ext
  intro p
  change sourcePair p (GaussMomentumAdjoint.adjoint u (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) q))=
    sourcePair p (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) (GaussMomentumAdjoint.adjoint u q))
  rw [GaussNativeForm.adjoint_pair,multiply_pair,multiply_pair,GaussNativeForm.adjoint_pair]
  exact congrArg (fun x => sourcePair x q) (LinearMap.congr_fun (momentum_metric u i j).eq.symm p)

private theorem scalar_gram_metric (i j : Fin 3) :
    Commute scalarGram (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
  apply Commute.sum_left
  intro r _
  exact (adjoint_metric (scalarDirection r) i j).mul_left (momentum_metric (scalarDirection r) i j)

private theorem pair_sub_left (p q r : QuantumTest) : sourcePair (p-q) r=sourcePair p r-sourcePair q r := by
  simp only [sourcePair,map_sub,inner_sub_left]

private theorem scalar_current_transpose (v : Ambient) (f g : QuantumTest) :
    sourcePair f ((scalarGram*GaussMomentumAdjoint.adjoint v-GaussMomentumAdjoint.adjoint v*scalarGram) g)=
      -sourcePair ((scalarGram*covariantMomentum v-covariantMomentum v*scalarGram) f) g := by
  simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub,pair_sub_left]
  rw [scalar_gram_pair,GaussNativeForm.adjoint_pair,GaussNativeForm.adjoint_pair,scalar_gram_pair]
  ring

def gramGaugePair (f : QuantumTest) : ℂ := ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
  sourcePair (covariantMomentum (gaugeDirection i a) f)
    (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
      ((scalarGram*covariantMomentum (gaugeDirection j a)-covariantMomentum (gaugeDirection j a)*scalarGram) f))

private theorem gauge_metric_symmetric (i j : Fin 3) :
    multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)=
      multiply (fun z => gaugeWeight z j i) (gaugeWeight_smooth j i) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun c : ℝ => (c : ℂ) • f z) (gaugeWeight_symmetric z i j)

private theorem reverse_gram_pair (f : QuantumTest) :
    (∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
      sourcePair ((scalarGram*covariantMomentum (gaugeDirection i a)-covariantMomentum (gaugeDirection i a)*scalarGram) f)
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) (covariantMomentum (gaugeDirection j a) f)))=
      star (gramGaugePair f) := by
  simp only [gramGaugePair,star_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gauge_metric_symmetric j i,multiply_pair]
  exact (pair_conjugate _ _).symm

private theorem scalar_gauge_pair (f : QuantumTest) :
    sourcePair f ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) f)=
      (1/2 : ℂ)*(gramGaugePair f-star (gramGaugePair f)) := by
  have he : scalarGram*gaugeKinetic-gaugeKinetic*scalarGram=
      (1/2 : ℂ) • ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
        ((scalarGram*GaussMomentumAdjoint.adjoint (gaugeDirection i a)-GaussMomentumAdjoint.adjoint (gaugeDirection i a)*scalarGram)*
          multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)+
          GaussMomentumAdjoint.adjoint (gaugeDirection i a)*multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*
          (scalarGram*covariantMomentum (gaugeDirection j a)-covariantMomentum (gaugeDirection j a)*scalarGram)) := by
    simp only [gaugeKinetic,mul_smul_comm,smul_mul_assoc,←smul_sub,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hm := (scalar_gram_metric i j).eq
    change scalarGram*(GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))-
      (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))*scalarGram=_
    linear_combination (norm := noncomm_ring) GaussMomentumAdjoint.adjoint (gaugeDirection i a)*hm*covariantMomentum (gaugeDirection j a)
  rw [he]
  have hp (c : ℂ) (q : QuantumTest) : sourcePair f (c • q)=c*sourcePair f q := by
    simp only [sourcePair,map_smul,inner_smul_right]
  have hs {ι : Type} [Fintype ι] (q : ι → QuantumTest) : sourcePair f (∑ i,q i)=∑ i,sourcePair f (q i) := by
    simp only [sourcePair,map_sum,inner_sum]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,Module.End.mul_apply,hp,hs,pair_add,
    scalar_current_transpose,GaussNativeForm.adjoint_pair,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  rw [reverse_gram_pair]
  change (1/2 : ℂ)*(-star (gramGaugePair f)+gramGaugePair f)=_
  ring

/-- The original signed mixed Gram current reads the same two actual electric slots. -/
theorem original_scalar_gauge_form (f : QuantumTest) :
    (sourcePair f ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) f)).im/2=(gramGaugePair f).im/2 := by
  rw [scalar_gauge_pair]
  simp only [Complex.mul_im,Complex.sub_im,Complex.star_def,Complex.conj_im]
  norm_num
  ring

def gaugeRotationPair (r : ScalarIndex) (f : QuantumTest) : ℂ := ∑ i : GaugeRow,∑ j : GaugeRow,
  sourcePair (gaugeMomentum i f) (weightedGaugeRotation r i j
    (covariantMomentum (scalarDirection r) (gaugeMomentum j f)+gaugeMomentum j (covariantMomentum (scalarDirection r) f)))

def gaugeContactPair (r : ScalarIndex) (f : QuantumTest) : ℂ := ∑ i : GaugeRow,∑ j : GaugeRow,
  sourcePair (gaugeMomentum i f) (weightedGaugeContact r i j (gaugeMomentum j f))

def gaugeCurvaturePair (r : ScalarIndex) (f : QuantumTest) : ℂ := ∑ i : GaugeRow,∑ j : GaugeRow,
  sourcePair (gaugeMomentum i f) (weightedGaugeRotation r i j
    (curvatureRow (scalarDirection r) (gaugeDirection j.1 j.2) f))

def lowerGaugePair (f : QuantumTest) : ℂ := ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,∑ r : ScalarIndex,
  sourcePair (covariantMomentum (gaugeDirection i a) f)
    (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) (scalarGaugeLowerRow r j a f))

private theorem weighted_rotation_value (r : ScalarIndex) (a b : LieIndex) (i j : Fin 3) (q : QuantumTest) :
    multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) (gaugeRotationAction r b a q)=
      weightedGaugeRotation r (i,a) (j,b) q := by
  apply DFunLike.ext
  intro z
  change (gaugeWeight z i j : ℂ) • ((gaugeRotation r b a z : ℂ) • q z)=
    ((gaugeWeight z i j*gaugeRotation r b a z : ℝ) : ℂ) • q z
  rw [smul_smul,Complex.ofReal_mul]

private theorem pair_sum {ι : Type} [Fintype ι] (p : QuantumTest) (q : ι → QuantumTest) :
    sourcePair p (∑ i,q i)=∑ i,sourcePair p (q i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem pair_smul (p q : QuantumTest) (c : ℂ) : sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem rotation_pair_shuffle (h : ScalarIndex → Fin 3 → LieIndex → Fin 3 → LieIndex → ℂ) :
    (∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,∑ r : ScalarIndex,∑ b : LieIndex,h r i a j b)=
      ∑ r : ScalarIndex,∑ i : Fin 3,∑ a : LieIndex,∑ j : Fin 3,∑ b : LieIndex,h r i a j b := by
  calc
    _ = ∑ a : LieIndex,∑ i : Fin 3,∑ r : ScalarIndex,∑ j : Fin 3,∑ b : LieIndex,h r i a j b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ a : LieIndex,∑ r : ScalarIndex,∑ i : Fin 3,∑ j : Fin 3,∑ b : LieIndex,h r i a j b :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ r : ScalarIndex,∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,∑ b : LieIndex,h r i a j b := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun r _ => Finset.sum_comm)

private theorem gram_gauge_pair_split (f : QuantumTest) :
    gramGaugePair f=(-Complex.I)*(∑ r : ScalarIndex,gaugeRotationPair r f)+lowerGaugePair f := by
  have hp (a : LieIndex) (i j : Fin 3) :
      sourcePair (covariantMomentum (gaugeDirection i a) f)
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
          ((scalarGram*covariantMomentum (gaugeDirection j a)-covariantMomentum (gaugeDirection j a)*scalarGram) f))=
      (-Complex.I)*(∑ r : ScalarIndex,∑ b : LieIndex,
        sourcePair (covariantMomentum (gaugeDirection i a) f)
          (weightedGaugeRotation r (i,a) (j,b)
            (covariantMomentum (scalarDirection r) (covariantMomentum (gaugeDirection j b) f)+
              covariantMomentum (gaugeDirection j b) (covariantMomentum (scalarDirection r) f))))+
      ∑ r : ScalarIndex,sourcePair (covariantMomentum (gaugeDirection i a) f)
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) (scalarGaugeLowerRow r j a f)) := by
    rw [original_scalar_gram_gauge_current]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply,
      map_add,map_smul,map_sum,pair_add,pair_smul,pair_sum,weighted_rotation_value]
  simp only [gramGaugePair,hp,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [rotation_pair_shuffle]
  simp only [gaugeRotationPair,Fintype.sum_prod_type,gaugeMomentum,lowerGaugePair]

/-- The mixed signed Gram form now has only source contacts and one native derivative on each paired leg. -/
def mixedEnergyForm (f : QuantumTest) : ℝ := (lowerGaugePair f).im/2+
  (∑ r : ScalarIndex,((gaugeContactPair r f).re+(gaugeCurvaturePair r f).re))/2

/-- Both full source rotations are consumed together; no third-order principal current remains. -/
theorem original_mixed_gram_energy_form (f : QuantumTest) :
    (sourcePair f ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) f)).im/2=mixedEnergyForm f := by
  rw [original_scalar_gauge_form,gram_gauge_pair_split]
  have hr (r : ScalarIndex) : (gaugeRotationPair r f).re= -(gaugeContactPair r f).re-(gaugeCurvaturePair r f).re :=
    original_gauge_rotation_form r f
  simp only [Complex.add_im,Complex.mul_im,Complex.neg_im,Complex.I_re,Complex.I_im,
    zero_mul,neg_mul,one_mul,Complex.re_sum,hr,mixedEnergyForm]
  rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib,Finset.sum_add_distrib]
  ring

section Density
open GaussScalarTransport GaussDensityCore
private theorem coefficient_density_smooth (N : ℕ) (v : Ambient) (i : FrameIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val :=
  (complexDensity_smooth N z).mul (coefficient_smooth v i z)

private theorem field_transpose_value (N : ℕ) (v : Ambient) (f : ScalarTest) (z : physicalChart) :
    fieldTranspose N v f z.val=
      -fieldDerivative v f z.val-divergenceCoefficient N v z.val*f z.val := by
  have hr : complexDensity N z.val≠0 := by
    change (density N z.val : ℂ)≠0
    exact_mod_cast (density_pos N z).ne'
  have hterm (i : FrameIndex) :
      weightedTranspose N (frame i) (multiplyCoefficient v i f) z.val=
        -(coefficient v i z.val : ℂ)*derivative (frame i) f z.val-
          ((complexDensity N z.val)⁻¹*fderiv ℝ
            (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val (frame i))*f z.val := by
    rw [weightedTranspose_apply]
    have he : (fun x => complexDensity N x*(multiplyCoefficient v i f) x)=
        fun x => (complexDensity N x*(coefficient v i x : ℂ))*f x := by
      funext x
      change complexDensity N x*((coefficient v i x : ℂ)*f x)=(complexDensity N x*(coefficient v i x : ℂ))*f x
      ring
    rw [he,fderiv_fun_mul ((coefficient_density_smooth N v i z).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt,derivative_apply]
    change -(complexDensity N z.val)⁻¹*
      ((complexDensity N z.val*(coefficient v i z.val : ℂ))*fderiv ℝ f z.val (frame i)+
        f z.val*fderiv ℝ (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val (frame i))=_
    field_simp [hr]
    ring
  simp only [fieldTranspose,fieldDerivative,LinearMap.sum_apply,LinearMap.comp_apply,sum_apply,
    hterm,divergenceCoefficient,Finset.sum_sub_distrib,Finset.sum_mul,neg_mul,Finset.sum_neg_distrib]
  rfl

private theorem derivative_transpose_component (v : Ambient) (f : QuantumTest) (word : Occupation) (z : physicalChart) :
    GaussMomentumAdjoint.derivativeTranspose v f z.val word=
      fieldTranspose word.card v (component word f) z.val := by
  have h := congrArg (fun x : H => x word) (GaussMomentumAdjoint.transpose_embed v f)
  change embed (GaussMomentumAdjoint.derivativeTranspose v f) word=
    scalarLp word.card (fieldTranspose word.card v (component word f)) at h
  have he : (fun x : physicalChart => GaussMomentumAdjoint.derivativeTranspose v f x.val word)=ᵐ[GaussHistoryHilbert.numberMeasure word.card]
      (fun x : physicalChart => fieldTranspose word.card v (component word f) x.val) :=
    (embed_ae (GaussMomentumAdjoint.derivativeTranspose v f) word).symm.trans
      (h.symm ▸ scalarLp_ae word.card (fieldTranspose word.card v (component word f)))
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq he
    ((component word (GaussMomentumAdjoint.derivativeTranspose v f)).continuous.comp continuous_subtype_val)
    ((fieldTranspose word.card v (component word f)).continuous.comp continuous_subtype_val)) z

private theorem divergence_value (v : Ambient) (f : QuantumTest) (z : physicalChart) :
    divergenceAction v f z.val=
      GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (f z.val) := by
  apply PiLp.ext
  intro word
  change -(GaussMomentumAdjoint.derivativeTranspose v f z.val word+directional v f z.val word)=_
  rw [derivative_transpose_component,field_transpose_value]
  have hd := congrArg (fun q : ScalarTest => q z.val) (GaussMomentumAdjoint.component_directional v f word)
  change directional v f z.val word=fieldDerivative v (component word f) z.val at hd
  rw [hd,GaussFockWeights.weight_apply]
  change -(-fieldDerivative v (component word f) z.val-
    divergenceCoefficient word.card v z.val*f z.val word+fieldDerivative v (component word f) z.val)=_
  ring


end Density

private theorem transpose_multiplier_value (u : Ambient) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) (z : physicalChart) :
    GaussMomentumAdjoint.adjoint u (multiply c hc f) z.val-multiply c hc (covariantMomentum u f) z.val=
      (-Complex.I) • GaussFockWeights.weight
        (fun N => (fderiv ℝ c z.val (direction u z.val) : ℂ)+(c z.val : ℂ)*divergenceCoefficient N u z.val) (f z.val) := by
  rw [original_adjoint_divergence]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sub_apply,smul_apply]
  rw [divergence_value]
  have h := real_multiplier_current u c hc f z
  apply PiLp.ext
  intro word
  have hh := congrArg (fun x : FockFiber => x word) h
  change covariantMomentum u (multiply c hc f) z.val word-
      Complex.I*(GaussFockWeights.weight (fun N => divergenceCoefficient N u z.val) (multiply c hc f z.val)) word-
      multiply c hc (covariantMomentum u f) z.val word=_
  rw [GaussFockWeights.weight_apply]
  change covariantMomentum u (multiply c hc f) z.val word-
      Complex.I*(divergenceCoefficient word.card u z.val*((c z.val : ℂ)*f z.val word))-
      multiply c hc (covariantMomentum u f) z.val word=
      (-Complex.I)*(((fderiv ℝ c z.val (direction u z.val) : ℂ)+(c z.val : ℂ)*divergenceCoefficient word.card u z.val)*f z.val word)
  change covariantMomentum u (multiply c hc f) z.val word-multiply c hc (covariantMomentum u f) z.val word=
    (-Complex.I)*((fderiv ℝ c z.val (direction u z.val) : ℂ)*f z.val word) at hh
  linear_combination hh

/-- The surviving transpose coefficient is the explicit source zero-order density contact. -/
theorem original_weighted_gauge_contact (r : ScalarIndex) (i j : GaugeRow) (f : QuantumTest) (z : physicalChart) :
    weightedGaugeContact r i j f z.val=(-Complex.I) • GaussFockWeights.weight
      (fun N => (fderiv ℝ (fun x => gaugeWeight x i.1 j.1*gaugeRotation r j.2 i.2 x) z.val
          (direction (scalarDirection r) z.val) : ℂ)+
        ((gaugeWeight z.val i.1 j.1*gaugeRotation r j.2 i.2 z.val : ℝ) : ℂ)*
          divergenceCoefficient N (scalarDirection r) z.val) (f z.val) :=
  transpose_multiplier_value (scalarDirection r) _ _ f z

open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceHamiltonianVolume

private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem gram_inverse : Commute scalarGram inverseVolumeAction := by
  apply Commute.sum_left
  intro i _
  exact (inverse_commute _ (native_adjoint_volume (scalarDirection i))).mul_left
    (inverse_commute _ (native_momentum_volume (scalarDirection i)))

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0 : ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (scalarWeight z : ℂ) • f z=(-(sourceTime 0 : ℂ)) • ((reciprocalVolume z : ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem scalar_kinetic_gram : scalarKinetic=(-(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*scalarGram) := by
  have hr (i : ScalarIndex) : sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth=
      (-(sourceTime 0 : ℂ)) • (inverseVolumeAction*(GaussMomentumAdjoint.adjoint (scalarDirection i)*covariantMomentum (scalarDirection i))) := by
    change GaussMomentumAdjoint.adjoint (scalarDirection i)*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection i))=_
    rw [weight_inverse,smul_mul_assoc,mul_smul_comm,←mul_assoc,
      (inverse_commute _ (native_adjoint_volume (scalarDirection i))).eq,mul_assoc]
  simp only [scalarKinetic,hr,←Finset.smul_sum,←Finset.mul_sum,smul_smul,scalarGram]
  congr 1
  ring

/-- The original negative scalar weight and mixed44 current consume the complete two-Gram energy form. -/
theorem original_mixed_bulk_energy_form (f : QuantumTest) :
    (sourcePair f (((44 : ℂ) • (inverseVolumeAction*(scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic))) f)).im/2=
      -22*sourceTime 0*mixedEnergyForm (inverseVolumeAction f) := by
  have hg := inverse_commute _ gauge_kinetic_volume
  have hC := (gram_inverse.mul_left hg).sub_left (hg.mul_left gram_inverse)
  have he : (44 : ℂ) • (inverseVolumeAction*(scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic))=
      ((-22*sourceTime 0 : ℝ) : ℂ) •
        (inverseVolumeAction*(inverseVolumeAction*(scalarGram*gaugeKinetic-gaugeKinetic*scalarGram))) := by
    rw [scalar_kinetic_gram]
    simp only [smul_mul_assoc,mul_smul_comm,←smul_sub,mul_assoc]
    rw [←mul_assoc gaugeKinetic inverseVolumeAction,hg.eq,mul_assoc]
    simp only [←mul_sub,smul_smul]
    congr 1
    push_cast
    ring
  have hp : sourcePair f ((inverseVolumeAction*(inverseVolumeAction*(scalarGram*gaugeKinetic-gaugeKinetic*scalarGram))) f)=
      sourcePair (inverseVolumeAction f) ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) (inverseVolumeAction f)) := by
    change sourcePair f (inverseVolumeAction (inverseVolumeAction ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) f)))=_
    rw [show sourcePair f (inverseVolumeAction (inverseVolumeAction ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) f)))=
      sourcePair (inverseVolumeAction f) (inverseVolumeAction ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) f)) from multiply_pair _ _ _ _]
    exact congrArg (sourcePair (inverseVolumeAction f)) (LinearMap.congr_fun hC.eq.symm f)
  rw [he]
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]
  change (((-22*sourceTime 0 : ℝ) : ℂ)*sourcePair f
    ((inverseVolumeAction*(inverseVolumeAction*(scalarGram*gaugeKinetic-gaugeKinetic*scalarGram))) f)).im/2=_
  rw [hp,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  rw [mul_div_assoc,original_mixed_gram_energy_form]

private theorem positive_coefficient_value (u : Ambient) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (q : QuantumTest) (z : physicalChart) :
    ((Complex.I • (covariantMomentum u*multiply c hc-multiply c hc*covariantMomentum u)+
      divergenceAction u*multiply c hc) q) z.val=
      GaussFockWeights.weight (fun N => (fderiv ℝ c z.val (direction u z.val) : ℂ)+
        divergenceCoefficient N u z.val*(c z.val : ℂ)) (q z.val) := by
  change Complex.I • (covariantMomentum u (multiply c hc q) z.val-multiply c hc (covariantMomentum u q) z.val)+
    divergenceAction u (multiply c hc q) z.val=_
  rw [real_multiplier_current,divergence_value,multiply_apply,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul,map_smul]
  apply PiLp.ext
  intro word
  change (fderiv ℝ c z.val (direction u z.val) : ℂ)*q z.val word+
    (c z.val : ℂ)*(divergenceCoefficient word.card u z.val*q z.val word)=
      ((fderiv ℝ c z.val (direction u z.val) : ℂ)+divergenceCoefficient word.card u z.val*(c z.val : ℂ))*q z.val word
  ring

private theorem negative_coefficient_value (u : Ambient) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (q : QuantumTest) (z : physicalChart) :
    (((-Complex.I) • (covariantMomentum u*multiply c hc-multiply c hc*covariantMomentum u)-
      divergenceAction u*multiply c hc) q) z.val=
      GaussFockWeights.weight (fun N => -(fderiv ℝ c z.val (direction u z.val) : ℂ)-
        divergenceCoefficient N u z.val*(c z.val : ℂ)) (q z.val) := by
  have he : (((-Complex.I) • (covariantMomentum u*multiply c hc-multiply c hc*covariantMomentum u)-
      divergenceAction u*multiply c hc) q) z.val=
      -((Complex.I • (covariantMomentum u*multiply c hc-multiply c hc*covariantMomentum u)+
        divergenceAction u*multiply c hc) q) z.val := by
    change (-Complex.I) • (covariantMomentum u (multiply c hc q) z.val-multiply c hc (covariantMomentum u q) z.val)-
      divergenceAction u (multiply c hc q) z.val=
      -(Complex.I • (covariantMomentum u (multiply c hc q) z.val-multiply c hc (covariantMomentum u q) z.val)+
        divergenceAction u (multiply c hc q) z.val)
    module
  rw [he,positive_coefficient_value]
  apply PiLp.ext
  intro word
  change -(((fderiv ℝ c z.val (direction u z.val) : ℂ)+divergenceCoefficient word.card u z.val*(c z.val : ℂ))*q z.val word)=
    (-(fderiv ℝ c z.val (direction u z.val) : ℂ)-divergenceCoefficient word.card u z.val*(c z.val : ℂ))*q z.val word
  ring

private theorem density_contact_value (u v : Ambient) (q : QuantumTest) (z : physicalChart) :
    densityContact u v q z.val=GaussFockWeights.weight
      (fun N => fderiv ℝ (divergenceCoefficient N v) z.val (direction u z.val)) (q z.val) := by
  change (covariantMomentum u (covariantMomentum v q) z.val-covariantMomentum v (covariantMomentum u q) z.val)-
    (covariantMomentum u (GaussMomentumAdjoint.adjoint v q) z.val-GaussMomentumAdjoint.adjoint v (covariantMomentum u q) z.val)=_
  rw [original_native_momentum_curvature,original_native_adjoint_curvature]
  module

/-- Every remaining lower row is explicitly one source momentum multiplied by generated zero-order coefficients. -/
theorem original_scalar_lower_row (r : ScalarIndex) (j : Fin 3) (a : LieIndex) (f : QuantumTest) (z : physicalChart) :
    scalarGaugeLowerRow r j a f z.val=
      (∑ i : ScalarIndex,GaussFockWeights.weight (fun N =>
        (fderiv ℝ (scalarRotation (gaugeDirection j a) i r) z.val (direction (scalarDirection r) z.val) : ℂ)+
          divergenceCoefficient N (scalarDirection r) z.val*(scalarRotation (gaugeDirection j a) i r z.val : ℂ))
            (covariantMomentum (scalarDirection i) f z.val))+
      (∑ b : LieIndex,GaussFockWeights.weight (fun N =>
        -(fderiv ℝ (gaugeRotation r b a) z.val (direction (scalarDirection r) z.val) : ℂ)-
          divergenceCoefficient N (scalarDirection r) z.val*(gaugeRotation r b a z.val : ℂ))
            (covariantMomentum (gaugeDirection j b) f z.val))+
      GaussFockWeights.weight (fun N => fderiv ℝ (divergenceCoefficient N (scalarDirection r)) z.val
        (direction (gaugeDirection j a) z.val)) (covariantMomentum (scalarDirection r) f z.val) := by
  simp only [scalarGaugeLowerRow,LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,add_apply,sum_apply]
  apply congrArg₂ (fun x y : FockFiber => x+y)
  · apply congrArg₂ (fun x y : FockFiber => x+y)
    · apply Finset.sum_congr rfl
      intro i _
      exact positive_coefficient_value (scalarDirection r) _ _ _ z
    · apply Finset.sum_congr rfl
      intro b _
      exact negative_coefficient_value (scalarDirection r) _ _ _ z
  · exact density_contact_value (gaugeDirection j a) (scalarDirection r) (covariantMomentum (scalarDirection r) f) z

end LowEnergy.SourceDoubleGramCurvatureForm
