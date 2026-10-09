import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeScaleTransport
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeBulk
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCoframeForwardCore
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeEnergy GaussNativeForm GaussLiveMomentum GaussCoframeCore SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent
open MeasureTheory Set Function
open scoped ContDiff Topology Distributions InnerProductSpace
abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest

def forwardRatio (t:ℝ) (z:SourceCoordinateSlice):ℝ:=(GaussNativeEnergy.volume z+18*t)/GaussNativeEnergy.volume z
def backwardRatio (t:ℝ) (z:SourceCoordinateSlice):ℝ:=(GaussNativeEnergy.volume z-18*t)/GaussNativeEnergy.volume z
def forwardPoint (t:ℝ) (z:SourceCoordinateSlice):SourceCoordinateSlice:=
  scale ((forwardRatio t z)^(1/3:ℝ)) z
def backwardPoint (t:ℝ) (z:SourceCoordinateSlice):SourceCoordinateSlice:=
  scale ((backwardRatio t z)^(1/3:ℝ)) z
theorem forward_ratio_pos (t:ℝ) (ht:0 ≤ t) (z:physicalChart):0<forwardRatio t z.val:=by
  unfold forwardRatio
  exact div_pos (by linarith [volume_pos z]) (volume_pos z)
theorem backward_ratio_pos (t:ℝ) (ht:0 ≤ t) (z:SourceCoordinateSlice) (hz:18*t<GaussNativeEnergy.volume z):
    0<backwardRatio t z:=by
  exact div_pos (sub_pos.mpr hz) (by linarith)
theorem cube_root_cube (x:ℝ) (hx:0 ≤ x):(x^(1/3:ℝ))^3=x:=by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx]
  norm_num
theorem forward_volume (t:ℝ) (ht:0 ≤ t) (z:physicalChart):
    GaussNativeEnergy.volume (forwardPoint t z.val)=GaussNativeEnergy.volume z.val+18*t:=by
  rw [forwardPoint,volume_scale,cube_root_cube _ (forward_ratio_pos t ht z).le]
  unfold forwardRatio
  exact div_mul_cancel₀ _ (volume_pos z).ne'
theorem backward_volume (t:ℝ) (ht:0 ≤ t) (z:SourceCoordinateSlice) (hz:18*t<GaussNativeEnergy.volume z):
    GaussNativeEnergy.volume (backwardPoint t z)=GaussNativeEnergy.volume z-18*t:=by
  rw [backwardPoint,volume_scale,cube_root_cube _ (backward_ratio_pos t ht z hz).le]
  unfold backwardRatio
  exact div_mul_cancel₀ _ (by linarith : GaussNativeEnergy.volume z≠0)
theorem forward_chart (t:ℝ) (ht:0 ≤ t) (z:physicalChart):forwardPoint t z.val∈physicalChart:=
  (SourceCoframeScaleTransport.scale_chart_iff _ (Real.rpow_pos_of_pos (forward_ratio_pos t ht z) _) _).mpr z.property
theorem forward_above (t:ℝ) (ht:0 ≤ t) (z:physicalChart):18*t<GaussNativeEnergy.volume (forwardPoint t z.val):=by
  rw [forward_volume t ht z]
  linarith [volume_pos z]
theorem backward_chart (t:ℝ) (ht:0 ≤ t) (z:physicalChart) (hz:18*t<GaussNativeEnergy.volume z.val):
    backwardPoint t z.val∈physicalChart:=
  (SourceCoframeScaleTransport.scale_chart_iff _ (Real.rpow_pos_of_pos (backward_ratio_pos t ht z.val hz) _) _).mpr z.property
private theorem scale_scale (a b:ℝ) (z:SourceCoordinateSlice):scale a (scale b z)=scale (a*b) z:=by
  simp only [scale,smul_smul]
theorem forward_backward (t:ℝ) (ht:0 ≤ t) (z:SourceCoordinateSlice) (hz:18*t<GaussNativeEnergy.volume z):
    forwardPoint t (backwardPoint t z)=z:=by
  have hv:0<GaussNativeEnergy.volume z:=by linarith
  have hb:=backward_ratio_pos t ht z hz
  have hp:forwardRatio t (backwardPoint t z)*backwardRatio t z=1:=by
    unfold forwardRatio backwardRatio
    rw [backward_volume t ht z hz]
    field_simp [hv.ne',(sub_pos.mpr hz).ne']
    ring
  have hf:0<forwardRatio t (backwardPoint t z):=by
    unfold forwardRatio
    rw [backward_volume t ht z hz]
    exact div_pos (by linarith) (sub_pos.mpr hz)
  change scale ((forwardRatio t (backwardPoint t z))^(1/3:ℝ))
    (scale ((backwardRatio t z)^(1/3:ℝ)) z)=z
  rw [scale_scale,←Real.mul_rpow hf.le hb.le,hp,Real.one_rpow]
  simp [scale]
theorem backward_forward (t:ℝ) (ht:0 ≤ t) (z:physicalChart):
    backwardPoint t (forwardPoint t z.val)=z.val:=by
  have hf:=forward_ratio_pos t ht z
  have hz:=forward_above t ht z
  have hb:=backward_ratio_pos t ht _ hz
  have hp:backwardRatio t (forwardPoint t z.val)*forwardRatio t z.val=1:=by
    unfold forwardRatio backwardRatio
    rw [forward_volume t ht z]
    field_simp [(volume_pos z).ne',show GaussNativeEnergy.volume z.val+18*t≠0 by linarith [volume_pos z]]
    ring
  change scale ((backwardRatio t (forwardPoint t z.val))^(1/3:ℝ))
    (scale ((forwardRatio t z.val)^(1/3:ℝ)) z.val)=z.val
  rw [scale_scale,←Real.mul_rpow hb.le hf.le,hp,Real.one_rpow]
  simp [scale]
theorem forward_smooth (t:ℝ) (ht:0 ≤ t) (z:physicalChart):
    ContDiffAt ℝ ∞ (forwardPoint t) z.val:=by
  have hr:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  have hl:=hr.rpow_const_of_ne (p:=(1/3:ℝ)) (forward_ratio_pos t ht z).ne'
  exact (hl.smul (contDiffAt_fst)).prodMk contDiffAt_snd
theorem backward_smooth (t:ℝ) (ht:0 ≤ t) (z:SourceCoordinateSlice) (hz:18*t<GaussNativeEnergy.volume z):
    ContDiffAt ℝ ∞ (backwardPoint t) z:=by
  have hv:GaussNativeEnergy.volume z≠0:=by linarith
  have hr:ContDiffAt ℝ ∞ (backwardRatio t) z:=
    (volume_smooth.contDiffAt.sub contDiffAt_const).div volume_smooth.contDiffAt hv
  have hl:=hr.rpow_const_of_ne (p:=(1/3:ℝ)) (backward_ratio_pos t ht z hz).ne'
  exact (hl.smul contDiffAt_fst).prodMk contDiffAt_snd

def forwardValue (t:ℝ) (f:QuantumTest) (z:SourceCoordinateSlice):FockFiber:=
  if 18*t<GaussNativeEnergy.volume z then WithLp.toLp 2 (fun word=>
    (Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*f (backwardPoint t z) word) else 0
def movedSupport (t:ℝ) (f:QuantumTest):Set SourceCoordinateSlice:=forwardPoint t '' tsupport f
private theorem movedSupport_compact (t:ℝ) (ht:0 ≤ t) (f:QuantumTest):IsCompact (movedSupport t f):=by
  apply f.hasCompactSupport.image_of_continuousOn
  intro z hz
  exact (forward_smooth t ht ⟨z,f.tsupport_subset hz⟩).continuousAt.continuousWithinAt
private theorem movedSupport_chart (t:ℝ) (ht:0 ≤ t) (f:QuantumTest):movedSupport t f⊆physicalChart:=by
  rintro z ⟨x,hx,rfl⟩
  exact forward_chart t ht ⟨x,f.tsupport_subset hx⟩
private theorem movedSupport_above (t:ℝ) (ht:0 ≤ t) (f:QuantumTest) (z:SourceCoordinateSlice)
    (hz:z∈movedSupport t f):18*t<GaussNativeEnergy.volume z:=by
  obtain ⟨x,hx,rfl⟩:=hz
  exact forward_above t ht ⟨x,f.tsupport_subset hx⟩
theorem forward_support (t:ℝ) (ht:0 ≤ t) (f:QuantumTest):tsupport (forwardValue t f)⊆movedSupport t f:=by
  apply closure_minimal _ (movedSupport_compact t ht f).isClosed
  intro z hz
  by_cases hv:18*t<GaussNativeEnergy.volume z
  · have hn:f (backwardPoint t z)≠0:=by
      intro hf
      exact hz (by ext word;simp [forwardValue,hv,hf])
    exact ⟨backwardPoint t z,subset_tsupport f hn,forward_backward t ht z hv⟩
  · exact False.elim (hz (by simp only [forwardValue,if_neg hv]))
private theorem forward_zero (t:ℝ) (ht:0 ≤ t) (f:QuantumTest) (z:SourceCoordinateSlice)
    (hz:z∉movedSupport t f):forwardValue t f z=0:=
  image_eq_zero_of_notMem_tsupport (fun h=>hz (forward_support t ht f h))
private theorem forward_value_smooth (t:ℝ) (ht:0 ≤ t) (f:QuantumTest):ContDiff ℝ ∞ (forwardValue t f):=by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz:z∈movedSupport t f
  · have hv:=movedSupport_above t ht f z hz
    have hratio:ContDiffAt ℝ ∞ (backwardRatio t) z:=
      (volume_smooth.contDiffAt.sub contDiffAt_const).div volume_smooth.contDiffAt (by linarith)
    have hmap:=backward_smooth t ht z hv
    have hf:=f.contDiff.contDiffAt.comp z hmap
    have hlocal:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>WithLp.toLp 2 (fun word=>
        (Real.rpow (backwardRatio t x) ((word.card+3:ℝ)/2):ℂ)*f (backwardPoint t x) word)) z:=by
      apply (contDiffAt_piLp 2).2
      intro word
      have ha:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(Real.rpow (backwardRatio t x) ((word.card+3:ℝ)/2):ℂ)) z:=
        Complex.ofRealCLM.contDiff.contDiffAt.comp z (hratio.rpow_const_of_ne (backward_ratio_pos t ht z hv).ne')
      exact ha.mul ((contDiffAt_piLp 2).1 hf word)
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const volume_smooth.continuous).mem_nhds hv] with x hx
    simp only [forwardValue,if_pos hx]
  · apply (contDiffAt_const (c:=(0:FockFiber))).congr_of_eventuallyEq
    filter_upwards [(movedSupport_compact t ht f).isClosed.isOpen_compl.mem_nhds hz] with x hx
    exact forward_zero t ht f x hx

def sourceForwardCore (t:ℝ) (ht:0 ≤ t):End where
  toFun f:=
    { toFun:=forwardValue t f
      contDiff':=forward_value_smooth t ht f
      hasCompactSupport':=(movedSupport_compact t ht f).of_isClosed_subset isClosed_closure (forward_support t ht f)
      tsupport_subset':=(forward_support t ht f).trans (movedSupport_chart t ht f) }
  map_add' f g:=by
    apply DFunLike.ext
    intro z
    change forwardValue t (f+g) z=forwardValue t f z+forwardValue t g z
    by_cases hv:18*t<GaussNativeEnergy.volume z
    · simp only [forwardValue,if_pos hv]
      apply PiLp.ext
      intro word
      change (Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*
        (f (backwardPoint t z) word+g (backwardPoint t z) word)=_
      exact mul_add _ _ _
    · simp only [forwardValue,if_neg hv,add_zero]
  map_smul' c f:=by
    apply DFunLike.ext
    intro z
    change forwardValue t (c • f) z=c • forwardValue t f z
    by_cases hv:18*t<GaussNativeEnergy.volume z
    · simp only [forwardValue,if_pos hv]
      apply PiLp.ext
      intro word
      change (Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*
        (c*f (backwardPoint t z) word)=c*((Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*f (backwardPoint t z) word)
      ring
    · simp only [forwardValue,if_neg hv,smul_zero]

private theorem ratio_forward_inverse (t:ℝ) (ht:0 ≤ t) (z:physicalChart):
    backwardRatio t (forwardPoint t z.val)=(forwardRatio t z.val)⁻¹:=by
  unfold backwardRatio forwardRatio
  rw [forward_volume t ht z]
  field_simp [(volume_pos z).ne',show GaussNativeEnergy.volume z.val+18*t≠0 by linarith [volume_pos z]]
  ring

theorem forwardCore_apply (t:ℝ) (ht:0 ≤ t) (f:QuantumTest) (z:physicalChart) (word:Occupation):
    sourceForwardCore t ht f (forwardPoint t z.val) word=
      (Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*f z.val word:=by
  change forwardValue t f (forwardPoint t z.val) word=_
  rw [forwardValue,if_pos (forward_above t ht z)]
  change (Real.rpow (backwardRatio t (forwardPoint t z.val)) ((word.card+3:ℝ)/2):ℂ)*
    f (backwardPoint t (forwardPoint t z.val)) word=_
  rw [backward_forward t ht z,ratio_forward_inverse t ht z]
  simp only [Real.rpow_eq_pow,←Real.rpow_neg_eq_inv_rpow]

theorem forwardCore_zero (f:QuantumTest):sourceForwardCore 0 (by norm_num) f=f:=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · apply PiLp.ext
    intro word
    change forwardValue 0 f z word=f z word
    rw [forwardValue,if_pos (by simpa using volume_pos ⟨z,hz⟩)]
    change (Real.rpow (backwardRatio 0 z) ((word.card+3:ℝ)/2):ℂ)*f (backwardPoint 0 z) word=f z word
    have hr:backwardRatio 0 z=1:=by unfold backwardRatio;simp [(volume_pos ⟨z,hz⟩).ne']
    have hb:backwardPoint 0 z=z:=by simp [backwardPoint,hr,scale]
    rw [hr,hb]
    simp only [Real.rpow_eq_pow,Real.one_rpow,Complex.ofReal_one,one_mul]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    have hg:sourceForwardCore 0 (by norm_num) f z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>hz ((sourceForwardCore 0 (by norm_num) f).tsupport_subset h))
    exact hg.trans hf.symm

private theorem density_forward (N:ℕ) (t:ℝ) (ht:0 ≤ t) (z:physicalChart):
    GaussDensityCore.density N (forwardPoint t z.val)=
      (forwardRatio t z.val)^(N+2)*GaussDensityCore.density N z.val:=by
  rw [forwardPoint,density_scale,pow_mul,cube_root_cube _ (forward_ratio_pos t ht z).le]

private theorem density_amplitude (R:ℝ) (hR:0<R) (N:ℕ):
    (Real.rpow R (-((N+3:ℝ)/2)))^2*R^(N+2)=R⁻¹:=by
  simp only [Real.rpow_eq_pow]
  rw [←Real.rpow_natCast,←Real.rpow_mul hR.le]
  have he:(-((N+3:ℝ)/2))*(2:ℝ)=-(N+3:ℝ):=by ring
  norm_num only [Nat.cast_ofNat]
  rw [he,←Real.rpow_natCast,←Real.rpow_add hR]
  have he2:-(N+3:ℝ)+((N+2:ℕ):ℝ)=(-1:ℝ):=by push_cast;ring
  rw [he2,Real.rpow_neg_one]

theorem forwardDensity_return (t:ℝ) (ht:0 ≤ t) (f g:QuantumTest) (z:physicalChart):
    densityPair (sourceForwardCore t ht f) (sourceForwardCore t ht g) (forwardPoint t z.val)=
      (forwardRatio t z.val)⁻¹ • densityPair f g z.val:=by
  simp only [densityPair_sum,forwardCore_apply,Finset.smul_sum,
    GaussDensityCore.complexDensity,
    star_mul,Complex.star_def,Complex.conj_ofReal,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro word _
  rw [density_forward word.card t ht z,Complex.ofReal_mul,Complex.ofReal_pow]
  have hp:=density_amplitude (forwardRatio t z.val) (forward_ratio_pos t ht z) word.card
  have hc:=congrArg Complex.ofReal hp
  simp only [Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_inv] at hc
  calc
    _=((Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)^2*
      (forwardRatio t z.val:ℂ)^(word.card+2))*(GaussDensityCore.density word.card z.val:ℂ)*
      star (f z.val word)*g z.val word:=by simp only [Complex.star_def];ring
    _=_:=by rw [hc];simp only [Complex.star_def,Complex.ofReal_inv];ring

private theorem determinant_rank_one (scaleFactor:ℝ) (hscaleFactor:scaleFactor≠0) (u v:Fin 6→ℝ):
    (scaleFactor • (1:Matrix (Fin 6) (Fin 6) ℝ)+Matrix.vecMulVec u v).det=
      scaleFactor^6*(1+scaleFactor⁻¹*∑i:Fin 6,v i*u i):=by
  have he:scaleFactor • (1:Matrix (Fin 6) (Fin 6) ℝ)+Matrix.vecMulVec u v=
      scaleFactor • (1+Matrix.replicateCol Unit u*Matrix.replicateRow Unit (fun i=>scaleFactor⁻¹*v i)):=by
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul,
      ←Matrix.vecMulVec_eq Unit]
    field_simp [hscaleFactor]
  rw [he,Matrix.det_smul,Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [Fintype.card_fin,dotProduct,mul_assoc]
  rw [←Finset.mul_sum]
private theorem volume_euler_sum (z:SourceCoordinateSlice):
    (∑i:Fin 6,volumeGradient z i*z.1 i)=3*GaussNativeEnergy.volume z:=by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,volumeGradient,
    Matrix.cons_val_zero,Matrix.cons_val_succ,zero_mul,add_zero]
  rw [show (Fin.succ (Fin.succ (0:Fin 4)):Fin 6)=2 by rfl,
    show (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))):Fin 6)=5 by rfl]
  unfold GaussNativeEnergy.volume
  ring

def coframeJacobianMatrix (t:ℝ) (z:SourceCoordinateSlice):Matrix (Fin 6) (Fin 6) ℝ:=
  let a:ℝ:=(forwardRatio t z)^(1/3:ℝ)
  a • 1+Matrix.vecMulVec (fun i=>z.1 i)
    (fun j=>(-6*t/(GaussNativeEnergy.volume z^2*a^2))*volumeGradient z j)

theorem actual_coframe_jacobian_matrix (t:ℝ) (ht:0 ≤ t) (z:physicalChart):
    (coframeJacobianMatrix t z.val).det=forwardRatio t z.val:=by
  let a:ℝ:=(forwardRatio t z.val)^(1/3:ℝ)
  have ha:0<a:=Real.rpow_pos_of_pos (forward_ratio_pos t ht z) _
  have ha3:a^3=forwardRatio t z.val:=cube_root_cube _ (forward_ratio_pos t ht z).le
  have hv:=volume_pos z
  unfold coframeJacobianMatrix
  change (a • (1:Matrix (Fin 6) (Fin 6) ℝ)+Matrix.vecMulVec (fun i=>z.val.1 i)
    (fun j=>(-6*t/(GaussNativeEnergy.volume z.val^2*a^2))*volumeGradient z.val j)).det=_
  rw [determinant_rank_one a ha.ne']
  simp only [mul_assoc,←Finset.mul_sum,volume_euler_sum]
  have hp:a^6=(forwardRatio t z.val)^2:=by
    calc a^6=(a^3)^2:=by ring
         _=(forwardRatio t z.val)^2:=by rw [ha3]
  rw [hp]
  unfold forwardRatio at ha3 ⊢
  field_simp [ha.ne',hv.ne']
  have hA:a^3*GaussNativeEnergy.volume z.val=GaussNativeEnergy.volume z.val+18*t:=(eq_div_iff hv.ne').mp ha3
  have hAv:=congrArg (fun x:ℝ=>GaussNativeEnergy.volume z.val*x) hA
  nlinarith [hA,hAv]

private theorem forwardRatio_derivative (t:ℝ) (_ht:0 ≤ t) (z:physicalChart):
    HasFDerivAt (forwardRatio t) ((-18*t/(GaussNativeEnergy.volume z.val)^2) • fderiv ℝ GaussNativeEnergy.volume z.val) z.val:=by
  have hv:HasFDerivAt GaussNativeEnergy.volume (fderiv ℝ GaussNativeEnergy.volume z.val) z.val:=
    (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hr:HasDerivAt (fun v:ℝ=>(v+18*t)/v) (-18*t/(GaussNativeEnergy.volume z.val)^2) (GaussNativeEnergy.volume z.val):=by
    have h:=((hasDerivAt_id (GaussNativeEnergy.volume z.val)).add_const (18*t)).div
      (hasDerivAt_id (GaussNativeEnergy.volume z.val)) (volume_pos z).ne'
    have hd:(1*GaussNativeEnergy.volume z.val-(GaussNativeEnergy.volume z.val+18*t)*1)/
        (GaussNativeEnergy.volume z.val)^2=(-18*t/(GaussNativeEnergy.volume z.val)^2):=by ring
    exact h.congr_deriv hd
  exact hr.comp_hasFDerivAt z.val hv
private theorem forwardScale_derivative (t:ℝ) (ht:0 ≤ t) (z:physicalChart):
    HasFDerivAt (fun x:SourceCoordinateSlice=>(forwardRatio t x)^(1/3:ℝ))
      ((-6*t/(GaussNativeEnergy.volume z.val^2*((forwardRatio t z.val)^(1/3:ℝ))^2)) • fderiv ℝ GaussNativeEnergy.volume z.val) z.val:=by
  have hR:=forward_ratio_pos t ht z
  have h:HasFDerivAt (fun x:SourceCoordinateSlice=>(forwardRatio t x)^(1/3:ℝ))
      (((1/3:ℝ)*(forwardRatio t z.val)^((1/3:ℝ)-1)) •
        ((-18*t/(GaussNativeEnergy.volume z.val)^2) • fderiv ℝ GaussNativeEnergy.volume z.val)) z.val:=
    (forwardRatio_derivative t ht z).rpow_const (Or.inl hR.ne')
  have hp:(forwardRatio t z.val)^((1/3:ℝ)-1)=(((forwardRatio t z.val)^(1/3:ℝ))^2)⁻¹:=by
    rw [show (1/3:ℝ)-1=-((1/3:ℝ)*2) by ring,Real.rpow_neg hR.le,
      Real.rpow_mul hR.le,Real.rpow_two]
  rw [hp,smul_smul] at h
  convert h using 1
  congr 1
  field_simp
  ring

def forwardPointDerivative (t:ℝ) (z:SourceCoordinateSlice):SourceCoordinateSlice→L[ℝ]SourceCoordinateSlice:=
  (((forwardRatio t z)^(1/3:ℝ)) • (ContinuousLinearMap.fst ℝ Coframe Slice)+
    ((-6*t/(GaussNativeEnergy.volume z^2*((forwardRatio t z)^(1/3:ℝ))^2)) • fderiv ℝ GaussNativeEnergy.volume z).smulRight z.1).prod
      (ContinuousLinearMap.snd ℝ Coframe Slice)

theorem actual_forwardPoint_derivative (t:ℝ) (ht:0 ≤ t) (z:physicalChart):
    HasFDerivAt (forwardPoint t) (forwardPointDerivative t z.val) z.val:=by
  have h:=((forwardScale_derivative t ht z).smul
    (ContinuousLinearMap.fst ℝ Coframe Slice).hasFDerivAt).prodMk
    (ContinuousLinearMap.snd ℝ Coframe Slice).hasFDerivAt
  exact h

theorem actual_coframe_matrix_reads_DF (t:ℝ) (_ht:0 ≤ t) (z:physicalChart) (i j:Fin 6):
    (forwardPointDerivative t z.val (coframeDirection j)).1 i=coframeJacobianMatrix t z.val i j:=by
  simp only [forwardPointDerivative,ContinuousLinearMap.prod_apply,add_apply,smul_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,volume_coordinate_derivative,
    coframeJacobianMatrix,Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
    smul_eq_mul,PiLp.add_apply,PiLp.smul_apply]
  unfold coframeDirection
  simp only [PiLp.single_apply]
  change (forwardRatio t z.val)^(1/3:ℝ)*(if i=j then 1 else 0)+
      ((-6*t/(GaussNativeEnergy.volume z.val^2*((forwardRatio t z.val)^(1/3:ℝ))^2))*volumeGradient z.val j)*z.val.1 i=
    (forwardRatio t z.val)^(1/3:ℝ)*(1:Matrix (Fin 6) (Fin 6) ℝ) i j+
      z.val.1 i*((-6*t/(GaussNativeEnergy.volume z.val^2*((forwardRatio t z.val)^(1/3:ℝ))^2))*volumeGradient z.val j)
  rw [Matrix.one_apply]
  split_ifs <;> ring

theorem forwardCurvePoint_smooth (p:ℝ×SourceCoordinateSlice) (hp:p.2∈physicalChart):
    ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>forwardPoint (q.1^2) q.2) p:=by
  have hv:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>GaussNativeEnergy.volume q.2) p:=
    volume_smooth.contDiffAt.comp p contDiffAt_snd
  have he:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>q.1^2) p:=by fun_prop
  have hr:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>forwardRatio (q.1^2) q.2) p:=
    (hv.add (contDiffAt_const.mul he)).div hv (volume_pos ⟨p.2,hp⟩).ne'
  have ha:=hr.rpow_const_of_ne (p:=(1/3:ℝ)) (forward_ratio_pos (p.1^2) (sq_nonneg _) ⟨p.2,hp⟩).ne'
  exact (ha.smul (contDiffAt_fst.comp p contDiffAt_snd)).prodMk (contDiffAt_snd.comp p contDiffAt_snd)
def forwardCommonSupport (R:ℝ) (f:QuantumTest):Set SourceCoordinateSlice:=
  (fun p:ℝ×SourceCoordinateSlice=>forwardPoint (p.1^2) p.2) '' (Icc (-R) R×ˢtsupport f)
theorem forwardCommonSupport_compact (R:ℝ) (f:QuantumTest):IsCompact (forwardCommonSupport R f):=by
  apply (isCompact_Icc.prod f.hasCompactSupport).image_of_continuousOn
  intro p hp
  exact (forwardCurvePoint_smooth p (f.tsupport_subset hp.2)).continuousAt.continuousWithinAt
theorem forwardCommonSupport_chart (R:ℝ) (f:QuantumTest):forwardCommonSupport R f⊆physicalChart:=by
  rintro z ⟨p,hp,rfl⟩
  exact forward_chart (p.1^2) (sq_nonneg _) ⟨p.2,f.tsupport_subset hp.2⟩
theorem forward_common_support (R:ℝ) (f:QuantumTest) (e:ℝ) (he:e∈Icc (-R) R):
    tsupport (sourceForwardCore (e^2) (sq_nonneg _) f)⊆forwardCommonSupport R f:=by
  intro z hz
  obtain ⟨x,hx,rfl⟩:=forward_support (e^2) (sq_nonneg _) f hz
  exact ⟨(e,x),⟨he,hx⟩,rfl⟩
private def forwardProductSupport (e:ℝ) (f:QuantumTest):Set (ℝ×SourceCoordinateSlice):=
  (fun p:ℝ×SourceCoordinateSlice=>(p.1,forwardPoint (p.1^2) p.2)) ''
    (Icc (e-1) (e+1)×ˢtsupport f)
private theorem forwardProductSupport_compact (e:ℝ) (f:QuantumTest):IsCompact (forwardProductSupport e f):=by
  apply (isCompact_Icc.prod f.hasCompactSupport).image_of_continuousOn
  intro p hp
  exact (contDiffAt_fst.prodMk (forwardCurvePoint_smooth p (f.tsupport_subset hp.2))).continuousAt.continuousWithinAt
theorem forwardCurve_joint_smooth (f:QuantumTest):
    ContDiff ℝ ∞ (fun p:ℝ×SourceCoordinateSlice=>forwardValue (p.1^2) f p.2):=by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hv:18*p.1^2<GaussNativeEnergy.volume p.2
  · have hvol:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>GaussNativeEnergy.volume q.2) p:=
      volume_smooth.contDiffAt.comp p contDiffAt_snd
    have hs:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>q.1^2) p:=by fun_prop
    have hr:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>backwardRatio (q.1^2) q.2) p:=
      (hvol.sub (contDiffAt_const.mul hs)).div hvol (by nlinarith [sq_nonneg p.1])
    have ha:=hr.rpow_const_of_ne (p:=(1/3:ℝ))
      (backward_ratio_pos (p.1^2) (sq_nonneg _) p.2 hv).ne'
    have hm:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>backwardPoint (q.1^2) q.2) p:=
      (ha.smul (contDiffAt_fst.comp p contDiffAt_snd)).prodMk (contDiffAt_snd.comp p contDiffAt_snd)
    have hf:=f.contDiff.contDiffAt.comp p hm
    have hh:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>WithLp.toLp 2 (fun word=>
        (Real.rpow (backwardRatio (q.1^2) q.2) ((word.card+3:ℝ)/2):ℂ)*f (backwardPoint (q.1^2) q.2) word)) p:=by
      apply (contDiffAt_piLp 2).2
      intro word
      have hx:=Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (hr.rpow_const_of_ne (p:=((word.card+3:ℝ)/2)) (backward_ratio_pos (p.1^2) (sq_nonneg _) p.2 hv).ne')
      exact hx.mul ((contDiffAt_piLp 2).1 hf word)
    apply hh.congr_of_eventuallyEq
    have ho:IsOpen {q:ℝ×SourceCoordinateSlice|18*q.1^2<GaussNativeEnergy.volume q.2}:=by
      apply isOpen_lt
      · fun_prop
      · exact volume_smooth.continuous.comp continuous_snd
    filter_upwards [ho.mem_nhds hv] with q hq
    simp only [forwardValue,if_pos hq]
  · have hn:p∉forwardProductSupport p.1 f:=by
      rintro ⟨q,hq,heq⟩
      have heq':(q.1,forwardPoint (q.1^2) q.2)=(p.1,p.2):=heq
      have he:q.1=p.1:=(Prod.mk_inj.1 heq').1
      have hz:forwardPoint (q.1^2) q.2=p.2:=(Prod.mk_inj.1 heq').2
      have hab:=forward_above (q.1^2) (sq_nonneg _) ⟨q.2,f.tsupport_subset hq.2⟩
      rw [hz,he] at hab
      exact hv hab
    apply (contDiffAt_const (c:=(0:FockFiber))).congr_of_eventuallyEq
    have hnear:∀ᶠ q:ℝ×SourceCoordinateSlice in 𝓝 p,q.1∈Icc (p.1-1) (p.1+1):=by
      have hc:=continuous_fst.tendsto p
      exact hc.eventually (Icc_mem_nhds (by linarith) (by linarith))
    filter_upwards [(forwardProductSupport_compact p.1 f).isClosed.isOpen_compl.mem_nhds hn,hnear] with q hq he
    apply forward_zero (q.1^2) (sq_nonneg _) f q.2
    rintro ⟨x,hx,hval⟩
    exact hq ⟨(q.1,x),⟨he,hx⟩,by apply Prod.ext;rfl;exact hval⟩

open SourcePhysicalKineticSquare

def forwardGenerator : End :=
  (-9*Complex.I) • (inverseVolumeAction*dilation)+(9:ℂ) • inverseVolumeAction
private theorem dilation_inverse_current :
    dilation*inverseVolumeAction-inverseVolumeAction*dilation=(2*Complex.I) • inverseVolumeAction := by
  have h:=congrArg (fun A:End=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) •
    (dilation*inverseVolumeAction-inverseVolumeAction*dilation))=
    (-2*Complex.I/3) • ((-3:ℂ) • inverseVolumeAction) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=1:=by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring

theorem forwardGenerator_original :
    forwardGenerator=(-9*Complex.I) • (dilation*inverseVolumeAction)-(9:ℂ) • inverseVolumeAction := by
  have h:=congrArg (fun A:End=>(-9*Complex.I) • A) dilation_inverse_current
  simp only [smul_sub,smul_smul] at h
  have hi:(-9*Complex.I)*(2*Complex.I)=18:=by
    calc _= -18*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi] at h
  change (-9*Complex.I) • (inverseVolumeAction*dilation)+(9:ℂ) • inverseVolumeAction=
    (-9*Complex.I) • (dilation*inverseVolumeAction)-(9:ℂ) • inverseVolumeAction
  rw [eq_add_of_sub_eq h]
  module

private theorem forwardGenerator_component (f:QuantumTest) (z:physicalChart) (word:Occupation):
    forwardGenerator f z.val word=
      (-6:ℂ)*(reciprocalVolume z.val:ℂ)*fderiv ℝ (component word f) z.val (euler z.val)-
      (9:ℂ)*(word.card+3:ℂ)*(reciprocalVolume z.val:ℂ)*f z.val word := by
  change (-9*Complex.I)*((reciprocalVolume z.val:ℂ)*dilation f z.val word)+
    9*((reciprocalVolume z.val:ℂ)*f z.val word)=_
  rw [dilation_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem backward_ratio_zero (z:physicalChart):backwardRatio 0 z.val=1:=by
  simp [backwardRatio,(volume_pos z).ne']
private theorem backward_point_zero (z:physicalChart):backwardPoint 0 z.val=z.val:=by
  simp [backwardPoint,backward_ratio_zero z,scale]
private theorem backward_point_zero_jet (z:physicalChart):
    HasDerivAt (fun t:ℝ=>backwardPoint t z.val)
      ((-6*reciprocalVolume z.val) • euler z.val) 0 := by
  have hr:HasDerivAt (fun t:ℝ=>backwardRatio t z.val) (-18/GaussNativeEnergy.volume z.val) 0:=by
    simpa only [backwardRatio,id_eq,mul_one,zero_sub,Pi.sub_apply] using!
      ((hasDerivAt_const (0:ℝ) (GaussNativeEnergy.volume z.val)).sub
        ((hasDerivAt_id (0:ℝ)).const_mul 18)).div_const (GaussNativeEnergy.volume z.val)
  have hs:=hr.rpow_const (p:=(1/3:ℝ)) (Or.inl (by rw [backward_ratio_zero];norm_num))
  rw [backward_ratio_zero,Real.one_rpow] at hs
  have hh:HasDerivAt (fun t:ℝ=>backwardPoint t z.val)
      (((-18/GaussNativeEnergy.volume z.val)*(1/3)) • z.val.1,0) 0:=by
    simpa only [backwardPoint,scale,mul_one] using (hs.smul_const z.val.1).prodMk
      (hasDerivAt_const (0:ℝ) z.val.2)
  convert hh using 1
  simp only [euler,Prod.smul_mk,smul_zero]
  congr 1
  unfold reciprocalVolume
  ring

theorem forward_value_zero_jet (f:QuantumTest) (z:physicalChart) (word:Occupation):
    HasDerivAt (fun t:ℝ=>forwardValue t f z.val word)
      (forwardGenerator f z.val word) 0 := by
  have hr:HasDerivAt (fun t:ℝ=>backwardRatio t z.val) (-18/GaussNativeEnergy.volume z.val) 0:=by
    simpa only [backwardRatio,id_eq,mul_one,zero_sub,Pi.sub_apply] using!
      ((hasDerivAt_const (0:ℝ) (GaussNativeEnergy.volume z.val)).sub
        ((hasDerivAt_id (0:ℝ)).const_mul 18)).div_const (GaussNativeEnergy.volume z.val)
  have ha:=hr.rpow_const (p:=((word.card+3:ℝ)/2)) (Or.inl (by rw [backward_ratio_zero];norm_num))
  have hc:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) ha
  have hf:=((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    0 (backward_point_zero_jet z) (backward_point_zero z).symm
  have h:=hc.mul hf
  simp only [backward_ratio_zero,Real.one_rpow,Function.comp_def,Complex.ofRealCLM_apply,
    backward_point_zero,component_apply,map_smul,Complex.real_smul] at h
  simp only [mul_one,Complex.ofReal_one,one_mul] at h
  have hd:(((-18/GaussNativeEnergy.volume z.val)*((word.card+3:ℝ)/2):ℝ):ℂ)*f z.val word+
      ((-6*reciprocalVolume z.val:ℝ):ℂ)*fderiv ℝ (component word f) z.val (euler z.val)=
      forwardGenerator f z.val word := by
    rw [forwardGenerator_component]
    unfold reciprocalVolume
    push_cast
    ring
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  have ho:IsOpen {t:ℝ|18*t<GaussNativeEnergy.volume z.val}:=isOpen_lt (by fun_prop) continuous_const
  filter_upwards [ho.mem_nhds (by simpa using volume_pos z)] with t ht
  simp only [forwardValue,if_pos ht]
  rfl

private theorem square_second_jet (g:ℝ→ℂ) (v:ℂ)
    (hg:ContDiffAt ℝ ∞ g 0) (hd:HasDerivAt g v 0):
    HasDerivAt (deriv (fun e:ℝ=>g (e^2))) (2*v) 0 := by
  have hgd:ContDiffAt ℝ 1 (deriv g) 0:=hg.derivWithin (m:=1) (by norm_num;exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hs:HasDerivAt (fun e:ℝ=>e^2) 0 0:=by simpa using hasDerivAt_pow 2 (0:ℝ)
  have hh:=hgd.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hs (by simp)
  have hh':HasDerivAt (fun e:ℝ=>deriv g (e^2)) 0 0:=by
    simpa only [Function.comp_def,map_zero] using hh
  have hl:HasDerivAt (fun e:ℝ=>((2*e:ℝ):ℂ)) 2 0:=by
    simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,mul_one,Complex.ofReal_ofNat,Complex.ofReal_mul] using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_id (0:ℝ)).const_mul 2)
  have hp:=hl.mul hh'
  simp at hp
  rw [hd.deriv] at hp
  apply hp.congr_of_eventuallyEq
  have hc:∀ᶠ x:ℝ in 𝓝 0,DifferentiableAt ℝ g x:=
    ((hg.of_le (show (1:ℕ∞ω)≤∞ by norm_num)).eventually (by norm_num)).mono
      (fun x hx=>hx.differentiableAt (by norm_num))
  have hst:Filter.Tendsto (fun e:ℝ=>e^2) (𝓝 0) (𝓝 0):=by simpa using hs.continuousAt.tendsto
  have he:∀ᶠ e:ℝ in 𝓝 0,DifferentiableAt ℝ g (e^2):=hst.eventually hc
  filter_upwards [he] with e he
  have hm:=he.hasDerivAt.scomp (h:=fun u:ℝ=>u^2) e (hasDerivAt_pow 2 e)
  simpa [Function.comp_def,Complex.real_smul] using hm.deriv

private theorem forward_value_zero_smooth (f:QuantumTest) (z:physicalChart) (word:Occupation):
    ContDiffAt ℝ ∞ (fun t:ℝ=>forwardValue t f z.val word) 0 := by
  have hr:ContDiffAt ℝ ∞ (fun t:ℝ=>backwardRatio t z.val) 0:=by
    unfold backwardRatio
    fun_prop
  have hm:ContDiffAt ℝ ∞ (fun t:ℝ=>backwardPoint t z.val) 0:=
    ((hr.rpow_const_of_ne (p:=(1/3:ℝ)) (by rw [backward_ratio_zero];norm_num)).smul
      contDiffAt_const).prodMk contDiffAt_const
  have ha:ContDiffAt ℝ ∞ (fun t:ℝ=>(Real.rpow (backwardRatio t z.val) ((word.card+3:ℝ)/2):ℂ)) 0:=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0
      (hr.rpow_const_of_ne (p:=((word.card+3:ℝ)/2)) (by rw [backward_ratio_zero];norm_num))
  have h:=ha.mul ((component word f).contDiff.contDiffAt.comp 0 hm)
  apply h.congr_of_eventuallyEq
  have ho:IsOpen {t:ℝ|18*t<GaussNativeEnergy.volume z.val}:=isOpen_lt (by fun_prop) continuous_const
  filter_upwards [ho.mem_nhds (by simpa using volume_pos z)] with t ht
  simp only [forwardValue,if_pos ht]
  rfl

theorem forward_curve_second_point_jet (f:QuantumTest) (z:physicalChart) (word:Occupation):
    HasDerivAt (deriv (fun e:ℝ=>sourceForwardCore (e^2) (sq_nonneg _) f z.val word))
      (2*forwardGenerator f z.val word) 0 :=
  square_second_jet _ _ (forward_value_zero_smooth f z word) (forward_value_zero_jet f z word)

private theorem density_continuous (N:ℕ):Continuous (GaussDensityCore.complexDensity N):=by
  have hg:Continuous (fun z:SourceCoordinateSlice=>(z.2.2:Gauge)):=by fun_prop
  have hv:Continuous (fun z:SourceCoordinateSlice=>z.1 0*z.1 2*z.1 5):=by fun_prop
  exact Complex.continuous_ofReal.comp
    ((GaussHistoryHilbert.jacobian_continuous.comp hg).mul (hv.pow _))

private def curveComponent (f:QuantumTest) (word:Occupation) (p:ℝ×SourceCoordinateSlice):ℂ:=
  forwardValue (p.1^2) f p.2 word
private theorem curveComponent_smooth (f:QuantumTest) (word:Occupation):
    ContDiff ℝ ∞ (curveComponent f word):=by
  rw [contDiff_iff_contDiffAt]
  intro p
  exact (contDiffAt_piLp 2).1 (forwardCurve_joint_smooth f).contDiffAt word
def parameterJet (F:(ℝ×SourceCoordinateSlice)→ℂ) (p:ℝ×SourceCoordinateSlice):ℂ:=
  fderiv ℝ F p (1,0)
theorem parameterJet_smooth (F:(ℝ×SourceCoordinateSlice)→ℂ) (hF:ContDiff ℝ ∞ F):
    ContDiff ℝ ∞ (parameterJet F):=by
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const
theorem parameterJet_derivative (F:(ℝ×SourceCoordinateSlice)→ℂ) (hF:ContDiff ℝ ∞ F)
    (e:ℝ) (z:SourceCoordinateSlice):
    HasDerivAt (fun u:ℝ=>F (u,z)) (parameterJet F (e,z)) e:=by
  have h:=((hF.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=(e,z))).comp_hasDerivAt
    e ((hasDerivAt_id e).prodMk (hasDerivAt_const e z))
  simpa only [Function.comp_def,parameterJet,id_eq] using! h
private def curveFirst (f:QuantumTest) (word:Occupation):=(parameterJet (curveComponent f word))
private def curveSecond (f:QuantumTest) (word:Occupation):=(parameterJet (curveFirst f word))
private theorem curveFirst_smooth (f:QuantumTest) (word:Occupation):ContDiff ℝ ∞ (curveFirst f word):=
  parameterJet_smooth _ (curveComponent_smooth f word)
private theorem curveSecond_smooth (f:QuantumTest) (word:Occupation):ContDiff ℝ ∞ (curveSecond f word):=
  parameterJet_smooth _ (curveFirst_smooth f word)
private theorem curve_second_zero (f:QuantumTest) (word:Occupation) (z:physicalChart):
    curveSecond f word (0,z.val)=2*forwardGenerator f z.val word:=by
  have hfirst:(fun e:ℝ=>curveFirst f word (e,z.val))=
      deriv (fun e:ℝ=>sourceForwardCore (e^2) (sq_nonneg _) f z.val word):=by
    funext e
    exact (parameterJet_derivative _ (curveComponent_smooth f word) e z.val).deriv.symm
  have hsecond:=parameterJet_derivative _ (curveFirst_smooth f word) 0 z.val
  rw [hfirst] at hsecond
  exact hsecond.unique (forward_curve_second_point_jet f z word)
def fixedKernel (p:QuantumTest) (F:Occupation→(ℝ×SourceCoordinateSlice)→ℂ)
    (q:ℝ×SourceCoordinateSlice):ℂ:=
  ∑word:Occupation,GaussDensityCore.complexDensity word.card q.2*star (p q.2 word)*F word q
private theorem fixedKernel_continuous (p:QuantumTest) (F:Occupation→(ℝ×SourceCoordinateSlice)→ℂ)
    (hF:∀word,Continuous (F word)):Continuous (fixedKernel p F):=by
  apply continuous_finsetSum
  intro word _
  exact (((density_continuous word.card).comp continuous_snd).mul
    (((component word p).continuous.comp continuous_snd).star)).mul (hF word)
private theorem fixedKernel_zero (p:QuantumTest) (F:Occupation→(ℝ×SourceCoordinateSlice)→ℂ)
    (e:ℝ) (z:SourceCoordinateSlice) (hz:z∉tsupport p):fixedKernel p F (e,z)=0:=by
  have hp:p z=0:=image_eq_zero_of_notMem_tsupport hz
  simp [fixedKernel,hp]
private theorem fixedKernel_derivative (p:QuantumTest)
    (F G:Occupation→(ℝ×SourceCoordinateSlice)→ℂ)
    (h:∀word e z,HasDerivAt (fun u:ℝ=>F word (u,z)) (G word (e,z)) e)
    (e:ℝ) (z:SourceCoordinateSlice):
    HasDerivAt (fun u:ℝ=>fixedKernel p F (u,z)) (fixedKernel p G (e,z)) e:=by
  have hh:=HasDerivAt.sum (u:=(Finset.univ:Finset Occupation)) (fun word _=>(h word e z).const_mul
    (GaussDensityCore.complexDensity word.card z*star (p z word)))
  convert! hh using 1
  funext u
  simp only [fixedKernel,Finset.sum_apply]
theorem fixedKernel_integral_derivative (p:QuantumTest)
    (F G:Occupation→(ℝ×SourceCoordinateSlice)→ℂ)
    (hF:∀word,Continuous (F word)) (hG:∀word,Continuous (G word))
    (h:∀word e z,HasDerivAt (fun u:ℝ=>F word (u,z)) (G word (e,z)) e) (e:ℝ):
    HasDerivAt (fun u:ℝ=>∫z,fixedKernel p F (u,z) ∂GaussHistoryHilbert.configurationMeasure)
      (∫z,fixedKernel p G (e,z) ∂GaussHistoryHilbert.configurationMeasure) e:=by
  have hcF:=fixedKernel_continuous p F hF
  have hcG:=fixedKernel_continuous p G hG
  obtain ⟨C,hC⟩:=(isCompact_Icc.prod p.hasCompactSupport).exists_bound_of_continuousOn
    (hcG.continuousOn:ContinuousOn (fixedKernel p G) (Icc (e-1) (e+1)×ˢtsupport p))
  let bound:SourceCoordinateSlice→ℝ:=(tsupport p).indicator (fun _=>C)
  have hb:Integrable bound GaussHistoryHilbert.configurationMeasure:=
    (integrableOn_const (μ:=GaussHistoryHilbert.configurationMeasure) (C:=C)
      p.hasCompactSupport.measure_ne_top).integrable_indicator (isClosed_tsupport p).measurableSet
  have hi (A:Occupation→(ℝ×SourceCoordinateSlice)→ℂ) (hA:∀word,Continuous (A word)) (u:ℝ):
      Integrable (fun z=>fixedKernel p A (u,z)) GaussHistoryHilbert.configurationMeasure:=by
    apply ((fixedKernel_continuous p A hA).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact p.hasCompactSupport
    intro z hz
    by_contra hn
    exact hz (fixedKernel_zero p A u z hn)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=GaussHistoryHilbert.configurationMeasure)
    (F:=fun u z=>fixedKernel p F (u,z)) (F':=fun u z=>fixedKernel p G (u,z)) (bound:=bound)
    (Ioo_mem_nhds (by linarith:e-1<e) (by linarith:e<e+1))
    (Filter.Eventually.of_forall (fun u=>(hi F hF u).aestronglyMeasurable))
    (hi F hF e)
    ((hcG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z=>by
      intro u hu
      by_cases hz:z∈tsupport p
      · change ‖fixedKernel p G (u,z)‖≤(tsupport p).indicator (fun _=>C) z
        rw [Set.indicator_of_mem hz]
        exact hC (u,z) ⟨⟨hu.1.le,hu.2.le⟩,hz⟩
      · change ‖fixedKernel p G (u,z)‖≤(tsupport p).indicator (fun _=>C) z
        rw [fixedKernel_zero p G u z hz,Set.indicator_of_notMem hz,norm_zero]))
    hb (Filter.Eventually.of_forall (fun z u _=>fixedKernel_derivative p F G h u z))).2

theorem forward_curve_weak_second_jet (p f:QuantumTest):
    HasDerivAt (deriv (fun e:ℝ=>sourcePair p (sourceForwardCore (e^2) (sq_nonneg _) f)))
      (2*sourcePair p (forwardGenerator f)) 0:=by
  have h0(e:ℝ):=fixedKernel_integral_derivative p (curveComponent f) (curveFirst f)
    (fun word=>(curveComponent_smooth f word).continuous) (fun word=>(curveFirst_smooth f word).continuous)
    (fun word u z=>parameterJet_derivative _ (curveComponent_smooth f word) u z) e
  have h1:=fixedKernel_integral_derivative p (curveFirst f) (curveSecond f)
    (fun word=>(curveFirst_smooth f word).continuous) (fun word=>(curveSecond_smooth f word).continuous)
    (fun word u z=>parameterJet_derivative _ (curveFirst_smooth f word) u z) 0
  have hk (e:ℝ) (z:SourceCoordinateSlice):fixedKernel p (curveComponent f) (e,z)=
      densityPair p (sourceForwardCore (e^2) (sq_nonneg _) f) z:=by
    simpa only [fixedKernel,curveComponent] using!
      (densityPair_sum p (sourceForwardCore (e^2) (sq_nonneg _) f) z).symm
  have he:(fun e:ℝ=>∫z,fixedKernel p (curveFirst f) (e,z) ∂GaussHistoryHilbert.configurationMeasure)=
      deriv (fun e:ℝ=>sourcePair p (sourceForwardCore (e^2) (sq_nonneg _) f)):=by
    funext e
    have h:=h0 e
    simp_rw [hk,←sourcePair_integral] at h
    exact h.deriv.symm
  rw [he] at h1
  have hz(z:SourceCoordinateSlice):fixedKernel p (curveSecond f) (0,z)=
      2*densityPair p (forwardGenerator f) z:=by
    by_cases hc:z∈physicalChart
    · change (∑word:Occupation,GaussDensityCore.complexDensity word.card z*star (p z word)*curveSecond f word (0,z))=_
      rw [densityPair_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      rw [curve_second_zero f word ⟨z,hc⟩]
      ring
    · have hp:p z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hc (p.tsupport_subset h))
      simp [fixedKernel,densityPair_sum,hp]
  simp_rw [hz] at h1
  rw [integral_const_mul,←sourcePair_integral] at h1
  exact h1

end LowEnergy.SourceClockPhiCoframeForwardCore
