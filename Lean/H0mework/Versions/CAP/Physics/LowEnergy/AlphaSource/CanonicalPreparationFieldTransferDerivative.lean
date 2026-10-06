import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldSourceDerivative
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldPerturbation
open GaussCoreHilbert SourceFiniteUnitary FullYSourceCutoffVolterra CanonicalGradedVariation
open scoped Topology InnerProductSpace Interval

namespace Blocks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev End (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] := E →L[ℂ] E
abbrev Channel (E : Type*) := WithLp 2 (E×E)
local instance : Fact ((1:ENNReal) ≤ 2) := ⟨by norm_num⟩
local instance : NormedAddCommGroup (Channel E) := WithLp.instProdNormedAddCommGroup 2 E E
local instance : NormedSpace ℂ (Channel E) := WithLp.instProdNormedSpace 2 ℂ E E
local instance : InnerProductSpace ℂ (Channel E) := WithLp.instProdInnerProductSpace
abbrev ChannelOp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] := Channel E →L[ℂ] Channel E
local instance : NormedAlgebra ℚ (ChannelOp E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (ChannelOp E) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (End E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (End E) := NormedAlgebra.restrictScalars ℝ ℂ _
 def channelEquiv : (Channel E) ≃L[ℂ] E×E := WithLp.prodContinuousLinearEquiv 2 ℂ E E
 def injectOut : E →L[ℂ] (Channel E) := channelEquiv.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ E E)
 def injectIn : E →L[ℂ] (Channel E) := channelEquiv.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℂ E E)
 def projectOut : (Channel E) →L[ℂ] E := WithLp.fstL 2 ℂ E E
 def projectIn : (Channel E) →L[ℂ] E := WithLp.sndL 2 ℂ E E

 def blockMap (left : E →L[ℂ] (Channel E)) (right : (Channel E) →L[ℂ] E) : (End E) →L[ℂ] (ChannelOp E) :=
  (ContinuousLinearMap.compL ℂ (Channel E) E (Channel E) left).comp
    ((ContinuousLinearMap.compL ℂ (Channel E) E E).flip right)

 def upper (A : (End E)) : (ChannelOp E) := blockMap injectOut projectIn A
 def diagonal (A B : (End E)) : (ChannelOp E) :=blockMap injectOut projectOut A+blockMap injectIn projectIn B

 def diagonalMap : ((End E)×(End E)) →L[ℂ] (ChannelOp E) :=
  (blockMap injectOut projectOut).comp (ContinuousLinearMap.fst ℂ (End E) (End E))+
    (blockMap injectIn projectIn).comp (ContinuousLinearMap.snd ℂ (End E) (End E))

 def corner : (ChannelOp E) →L[ℂ] (End E) :=
  ((ContinuousLinearMap.compL ℂ E (Channel E) E projectOut).comp
    ((ContinuousLinearMap.compL ℂ E (Channel E) (Channel E)).flip injectIn))

 theorem diagonal_apply (A B : (End E)) (x : (Channel E)) :
    diagonal A B x=WithLp.toLp 2 (A x.fst,B x.snd) := by
  apply (WithLp.equiv 2 (E×E)).injective
  apply Prod.ext <;> simp [diagonal,blockMap,injectOut,injectIn,channelEquiv,projectOut,projectIn]

 theorem upper_apply (A : (End E)) (x : (Channel E)) :
    upper A x=WithLp.toLp 2 (A x.snd,0) := by
  rfl

 theorem diagonal_mul (A B C D : (End E)) : diagonal A B*diagonal C D=diagonal (A*C) (B*D) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp,diagonal_apply,WithLp.toLp_fst,WithLp.toLp_snd]

 theorem diagonal_add (A B C D : (End E)) : diagonal A B+diagonal C D=diagonal (A+C) (B+D) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply,diagonal_apply,←WithLp.toLp_add,Prod.mk_add_mk]

 theorem diagonal_smul (a : ℂ) (A B : (End E)) : a • diagonal A B=diagonal (a • A) (a • B) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply,diagonal_apply,←WithLp.toLp_smul,Prod.smul_mk]

 theorem diagonal_one : diagonal 1 1=(1:(ChannelOp E)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [diagonal_apply]
  exact (WithLp.toLp_ofLp 2 x)

 theorem diagonal_upper (A B C : (End E)) : diagonal A B*upper C=upper (A*C) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp,diagonal_apply,upper_apply,WithLp.toLp_fst,WithLp.toLp_snd,map_zero]

 theorem upper_diagonal (A B C : (End E)) : upper A*diagonal B C=upper (A*C) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp,diagonal_apply,upper_apply,WithLp.toLp_snd]

 theorem upper_square (A B : (End E)) : upper A*upper B=0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp,upper_apply,WithLp.toLp_snd,map_zero,zero_apply]
  rfl

 theorem corner_diagonal (A B : (End E)) : corner (diagonal A B)=0 := by
  apply ContinuousLinearMap.ext
  intro x
  change projectOut (diagonal A B (injectIn x))=0
  rw [diagonal_apply]
  simp [projectOut,injectIn,channelEquiv]

 theorem corner_upper (A : (End E)) : corner (upper A)=A := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

 theorem upper_add (A B : (End E)) : upper (A+B)=upper A+upper B := (blockMap injectOut projectIn).map_add A B
 theorem upper_smul (r : ℂ) (A : (End E)) : upper (r • A)=r • upper A := (blockMap injectOut projectIn).map_smul r A

 theorem diagonal_time (A B : (End E)) (t : ℝ) :
    time (diagonal A B) t=diagonal (time A t) (time B t) := by
  have derivative (s : ℝ) : HasDerivAt (fun t=>diagonal (time A t) (time B t))
      (diagonal (time A s) (time B s)*((-Complex.I) • diagonal A B)) s := by
    have h:=((diagonalMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      ((time_operator_derivative A s).prodMk (time_operator_derivative B s)))
    have algebra : diagonal (time A s*((-Complex.I) • A)) (time B s*((-Complex.I) • B))=
        diagonal (time A s) (time B s)*((-Complex.I) • diagonal A B) := by
      rw [diagonal_smul,diagonal_mul]
    exact h.congr_deriv algebra
  have initial : diagonal (time A 0) (time B 0)=1 := by rw [time_zero,time_zero,diagonal_one]
  exact (autonomous_evolution_unique _ _ derivative initial t).symm

 def crossPrimitive (A B D : (End E)) (t : ℝ) : (End E) :=
  ∫ s in (0:ℝ)..t,time A s*((-Complex.I) • D)*time B (-s)

 def crossTime (A B D : (End E)) (t : ℝ) : (End E) :=crossPrimitive A B D t*time B t

 theorem crossTime_derivative (A B D : (End E)) (t : ℝ) :
    HasDerivAt (crossTime A B D)
      (crossTime A B D t*((-Complex.I) • B)+time A t*((-Complex.I) • D)) t := by
  have continuous : Continuous (fun s=>time A s*((-Complex.I) • D)*time B (-s)) :=
    ((time_continuous A).mul continuous_const).mul ((time_continuous B).comp continuous_neg)
  have primitive : HasDerivAt (crossPrimitive A B D) (time A t*((-Complex.I) • D)*time B (-t)) t :=
    (continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h:=primitive.mul (time_operator_derivative B t)
  have inverse : time B (-t)*time B t=1 := by rw [←time_add,neg_add_cancel,time_zero]
  convert! h using 1
  simp only [crossTime,mul_assoc,inverse,mul_one]
  abel

 theorem crossTime_zero (A B D : (End E)) : crossTime A B D 0=0 := by
  simp only [crossTime,crossPrimitive,intervalIntegral.integral_same,zero_mul]

 theorem triangular_time (A B D : (End E)) (r : ℂ) (t : ℝ) :
    time (diagonal A B+r • upper D) t=
      diagonal (time A t) (time B t)+r • upper (crossTime A B D t) := by
  let U:=fun s=>diagonal (time A s) (time B s)+r • upper (crossTime A B D s)
  have derivative (s : ℝ) : HasDerivAt U (U s*((-Complex.I) • (diagonal A B+r • upper D))) s := by
    have hd : HasDerivAt (fun t : ℝ=>diagonal (time A t) (time B t))
        (diagonal (time A s) (time B s)*((-Complex.I) • diagonal A B)) s := by
      have h:=time_operator_derivative (diagonal A B) s
      rw [diagonal_time A B s] at h
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t=>(diagonal_time A B t).symm))
    have hu : HasDerivAt (fun t : ℝ=>upper (crossTime A B D t))
        (upper (crossTime A B D s*((-Complex.I) • B)+time A s*((-Complex.I) • D))) s :=
      ((blockMap (E:=E) injectOut projectIn).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (crossTime_derivative A B D s)
    have h:=hd.add (hu.const_smul r)
    apply h.congr_deriv
    simp only [U,smul_add,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,
      diagonal_upper,upper_diagonal,upper_square,upper_add,upper_smul]
    module
  have initial : U 0=1 := by
    simp only [U,time_zero,diagonal_one,crossTime_zero,upper,map_zero]
    module
  exact (autonomous_evolution_unique _ _ derivative initial t).symm


 theorem crossTime_integral (A B D : (End E)) (t : ℝ) :
    crossTime A B D t=∫ s in (0:ℝ)..t,time A s*((-Complex.I) • D)*time B (t-s) := by
  let f:=fun s=>time A s*((-Complex.I) • D)*time B (-s)
  have continuous : Continuous f :=
    ((time_continuous A).mul continuous_const).mul ((time_continuous B).comp continuous_neg)
  let R : (End E) →L[ℂ] (End E) := (ContinuousLinearMap.mul ℂ (End E)).flip (time B t)
  calc
    _ = R (∫ s in (0:ℝ)..t,f s) := rfl
    _ = ∫ s in (0:ℝ)..t,R (f s) := (R.intervalIntegral_comp_comm (continuous.intervalIntegrable 0 t)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      change (time A s*((-Complex.I) • D)*time B (-s))*time B t=_
      rw [mul_assoc,←time_add,show -s+t=t-s by ring]

 theorem crossTime_forward (A B D : (End E)) (t : ℝ) :
    crossTime A B D t=(-Complex.I) • ∫ s in (0:ℝ)..t,time A (t-s)*D*time B s := by
  rw [crossTime_integral]
  have reflection := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ=>time A u*((-Complex.I) • D)*time B (t-u)) t (a:=0) (b:=t)
  simp only [sub_self,sub_zero,sub_sub_cancel] at reflection
  rw [←reflection,←intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [mul_smul_comm,smul_mul_assoc]

theorem crossTime_backward (A B D : (End E)) (t : ℝ) :
    crossTime A B D (-t)=Complex.I • ∫ s in (0:ℝ)..t,time A (-s)*D*time B (s-t) := by
  rw [crossTime_integral]
  have reflection := intervalIntegral.integral_comp_neg
    (fun u : ℝ=>time A u*((-Complex.I) • D)*time B (-t-u)) (a:=0) (b:=t)
  rw [neg_zero] at reflection
  have same : (∫ s in (0:ℝ)..-t,time A s*((-Complex.I) • D)*time B (-t-s))=
      -(∫ s in (0:ℝ)..t,time A (-s)*((-Complex.I) • D)*time B (-t-(-s))) := by
    rw [reflection,intervalIntegral.integral_symm]
  have pointwise : (fun s : ℝ=>-(time A (-s)*((-Complex.I) • D)*time B (-t-(-s))))=
      (fun s : ℝ=>Complex.I • (time A (-s)*D*time B (s-t))) := by
    funext s
    rw [show -t-(-s)=s-t by ring]
    rw [neg_smul,mul_neg,neg_mul,neg_neg,mul_smul_comm,smul_mul_assoc]
  rw [same,←intervalIntegral.integral_neg,pointwise,intervalIntegral.integral_smul]

theorem corner_three (U0 U1 V0 V1 A0 A1 X Y D : (End E)) (r : ℂ) :
    corner ((diagonal U0 U1+r • upper X)*(diagonal A0 A1+r • upper D)*(diagonal V0 V1+r • upper Y))=
      (r:ℂ) • (X*A1*V1+U0*D*V1+U0*A0*Y) := by
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,diagonal_mul,diagonal_upper,upper_diagonal,
    upper_square,map_add,map_smul,corner_diagonal,corner_upper,smul_zero,zero_mul,map_zero]
  module

theorem integral_mul_right (f : ℝ→(End E)) (a : (End E)) (t : ℝ) (hf : Continuous f) :
    (∫ s in (0:ℝ)..t,f s)*a=∫ s in (0:ℝ)..t,f s*a :=
  ((ContinuousLinearMap.mul ℂ (End E)).flip a).intervalIntegral_comp_comm (hf.intervalIntegrable 0 t) |>.symm

theorem integral_mul_left (f : ℝ→(End E)) (a : (End E)) (t : ℝ) (hf : Continuous f) :
    a*(∫ s in (0:ℝ)..t,f s)=∫ s in (0:ℝ)..t,a*f s :=
  (ContinuousLinearMap.mul ℂ (End E) a).intervalIntegral_comp_comm (hf.intervalIntegrable 0 t) |>.symm

def transferCoefficient (O0 O1 I0 I1 A0 A1 B0 B1 D : (End E)) (t : ℝ) : (End E) :=
  crossTime O0 O1 B0 (-t)*A1*time I1 t+
    time O0 (-t)*D*time I1 t+
      time O0 (-t)*A0*crossTime I0 I1 B1 t

theorem transferCoefficient_integral (O0 O1 I0 I1 A0 A1 B0 B1 D : (End E)) (t : ℝ) :
    transferCoefficient O0 O1 I0 I1 A0 A1 B0 B1 D t=
      (∫ s in (0:ℝ)..t,Complex.I •
        (time O0 (-s)*B0*time O1 (s-t)*A1*time I1 t-
          time O0 (-t)*A0*time I0 (t-s)*B1*time I1 s))+
        time O0 (-t)*D*time I1 t := by
  let rev:=fun s : ℝ=>time O0 (-s)*B0*time O1 (s-t)
  let fwd:=fun s : ℝ=>time I0 (t-s)*B1*time I1 s
  have hr : Continuous rev :=
    (((time_continuous O0).comp continuous_neg).mul continuous_const).mul
      ((time_continuous O1).comp (continuous_id.sub continuous_const))
  have hf : Continuous fwd :=
    (((time_continuous I0).comp (continuous_const.sub continuous_id)).mul continuous_const).mul (time_continuous I1)
  have left : crossTime O0 O1 B0 (-t)*A1*time I1 t=
      Complex.I • ∫ s in (0:ℝ)..t,rev s*A1*time I1 t := by
    rw [crossTime_backward,smul_mul_assoc,smul_mul_assoc,
      integral_mul_right rev A1 t hr,integral_mul_right (fun s=>rev s*A1) (time I1 t) t (hr.mul continuous_const)]
  have right : time O0 (-t)*A0*crossTime I0 I1 B1 t=
      (-Complex.I) • ∫ s in (0:ℝ)..t,(time O0 (-t)*A0)*fwd s := by
    rw [crossTime_forward,mul_smul_comm,integral_mul_left _ _ t hf]
  unfold transferCoefficient
  rw [left,right,←intervalIntegral.integral_smul,←intervalIntegral.integral_smul]
  have hleft : IntervalIntegrable (fun s : ℝ=>Complex.I • (rev s*A1*time I1 t)) MeasureTheory.volume 0 t :=
    (((hr.mul continuous_const).mul continuous_const).const_smul Complex.I).intervalIntegrable 0 t
  have hright : IntervalIntegrable (fun s : ℝ=>(-Complex.I) • ((time O0 (-t)*A0)*fwd s)) MeasureTheory.volume 0 t :=
    ((continuous_const.mul hf).const_smul (-Complex.I)).intervalIntegrable 0 t
  rw [add_right_comm,←intervalIntegral.integral_add hleft hright]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [rev,fwd,mul_assoc]
  module

theorem triangular_observable (O0 O1 I0 I1 A0 A1 B0 B1 D : End E) (r t : ℝ) :
    corner (time (diagonal O0 O1+(r:ℂ) • upper B0) (-t)*
      (diagonal A0 A1+(r:ℂ) • upper D)*time (diagonal I0 I1+(r:ℂ) • upper B1) t)=
      r • ((∫ s in (0:ℝ)..t,Complex.I •
        (time O0 (-s)*B0*time O1 (s-t)*A1*time I1 t-
          time O0 (-t)*A0*time I0 (t-s)*B1*time I1 s))+
        time O0 (-t)*D*time I1 t) := by
  rw [triangular_time,triangular_time,corner_three]
  change (r:ℂ) • transferCoefficient O0 O1 I0 I1 A0 A1 B0 B1 D t=_
  rw [transferCoefficient_integral]
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) r _).symm

end Blocks
open Blocks
local instance : Fact ((1:ENNReal) ≤ 2) := ⟨by norm_num⟩
local instance : NormedAddCommGroup (Channel H) := WithLp.instProdNormedAddCommGroup 2 H H
local instance : NormedSpace ℂ (Channel H) := WithLp.instProdNormedSpace 2 ℂ H H
local instance : InnerProductSpace ℂ (Channel H) := WithLp.instProdInnerProductSpace
local instance : NormedAlgebra ℚ (ChannelOp H) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (ChannelOp H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
open CanonicalPhysicalSpatial CanonicalPhysicalLaplace CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumCausalFieldResponse GaussUnitaryHistory SourceFamilyOperator SourceFamilyHilbert

/-- The two physical transfer channels are the first-variation restriction of the
original Fourier source. Their diagonal times are the original finite generators. -/
def finiteTransferCurve (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (r t : ℝ) : Op :=
  corner (time (diagonal (compression (p+k+ell) F+cutoff cut) (compression (p+k) F+cutoff cut)+
      (r:ℂ) • upper (forceGauss g (p+k) psi)) (-t)*
    (diagonal (localizedGauss f (p+ell) phi) (localizedGauss f p phi)+
      (r:ℂ) • upper (contactGauss f g p (contactLocalizer phi psi)))*
    time (diagonal (compression (p+ell) F+cutoff cut) (compression p F+cutoff cut)+
      (r:ℂ) • upper (forceGauss g p psi)) t)

def finiteTransferDerivative (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) : Op :=
  (∫ s in (0:ℝ)..t,actualKernel cut F f g phi psi p k ell t s)+
    finiteContact cut F f g (contactLocalizer phi psi) p k ell t

theorem finiteTransfer_exact (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (r t : ℝ) :
    finiteTransferCurve cut F f g phi psi p k ell r t=
      r • finiteTransferDerivative cut F f g phi psi p k ell t := by
  exact triangular_observable (compression (p+k+ell) F+cutoff cut) (compression (p+k) F+cutoff cut)
    (compression (p+ell) F+cutoff cut) (compression p F+cutoff cut)
    (localizedGauss f (p+ell) phi) (localizedGauss f p phi)
    (forceGauss g (p+k) psi) (forceGauss g p psi)
    (contactGauss f g p (contactLocalizer phi psi)) r t

def channelRead (p ell : PhysicalMomentum) (v : FourierSection) : Channel H :=
  WithLp.toLp 2 (v (p+ell),v p)

theorem actual_reader_channels (f : Field289) (phi : Localizer) (p k ell : PhysicalMomentum)
    (v : FourierSection) :
    diagonal (localizedGauss f (p+ell) phi) (localizedGauss f p phi) (channelRead p ell v)=
      channelRead (p+k) ell (PreparationVacuumCausalFieldResponse.fieldCurrent f phi k v) := by
  have route : p+k+ell-k=p+ell := by abel
  simp only [diagonal_apply,channelRead,WithLp.toLp_fst,WithLp.toLp_snd,PreparationVacuumCausalFieldResponse.fieldCurrent,route,add_sub_cancel_right]

theorem actual_time_channels (cut : ℕ) (F : Index) (p ell : PhysicalMomentum)
    (v : FourierSection) (t : ℝ) :
    time (diagonal (compression (p+ell) F+cutoff cut) (compression p F+cutoff cut)) t (channelRead p ell v)=
      channelRead p ell (fullTime cut F t v) := by
  rw [diagonal_time,diagonal_apply]
  rfl

theorem actual_forcing_channel (g : Field289) (psi : Localizer) (p ell : PhysicalMomentum)
    (v : FourierSection) :
    projectOut (upper (forceGauss g p psi) (channelRead p ell v))=
      -PreparationVacuumCausalFieldResponse.fieldCurrent g psi ell v (p+ell) := by
  change forceGauss g p psi (v p)=_
  rw [forceGauss_generated]
  simp only [neg_apply,PreparationVacuumCausalFieldResponse.fieldCurrent,add_sub_cancel_right]

def crossBound (cut : ℕ) (D : Op) (t : ℝ) : ℝ := |t| *(timeBound cut |t|)^2*‖D‖

theorem crossBound_nonneg (cut : ℕ) (D : Op) (t : ℝ) : 0 ≤ crossBound cut D t := by
  unfold crossBound
  positivity

theorem crossTime_source_bound (p q : PhysicalMomentum) (F : Index) (cut : ℕ) (D : Op) (t : ℝ) :
    ‖crossTime (compression p F+cutoff cut) (compression q F+cutoff cut) D t‖ ≤ crossBound cut D t := by
  rw [crossTime_forward,norm_smul,norm_neg,Complex.norm_I,one_mul]
  have estimate : ∀ s∈Set.uIoc 0 t,
      ‖time (compression p F+cutoff cut) (t-s)*D*time (compression q F+cutoff cut) s‖ ≤
        timeBound cut |t| *‖D‖*timeBound cut |t| := by
    intro s hs
    obtain ⟨hs1,hs2⟩:=interval_times hs
    exact (norm_mul_le _ _).trans (mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (original_time_window p F cut |t| (t-s) (abs_nonneg t) hs2) (norm_nonneg D)))
      (original_time_window q F cut |t| s (abs_nonneg t) hs1) (norm_nonneg _)
      (mul_nonneg (timeBound_nonneg _ _) (norm_nonneg D)))
  exact (intervalIntegral.norm_integral_le_of_norm_le_const estimate).trans_eq (by simp only [sub_zero];unfold crossBound;ring)

def transferBound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) : ℝ :=
  crossBound cut (forceGauss g (p+k) psi) t*‖localizedGauss f p phi‖*timeBound cut |t|+
    timeBound cut |t| *‖contactGauss f g p (contactLocalizer phi psi)‖*timeBound cut |t|+
      timeBound cut |t| *‖localizedGauss f (p+ell) phi‖*crossBound cut (forceGauss g p psi) t

theorem transferBound_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) : 0 ≤ transferBound cut f g phi psi p k ell t := by
  exact add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (crossBound_nonneg cut (forceGauss g (p+k) psi) t) (norm_nonneg _)) (timeBound_nonneg cut |t|))
    (mul_nonneg (mul_nonneg (timeBound_nonneg cut |t|) (norm_nonneg _)) (timeBound_nonneg cut |t|)))
    (mul_nonneg (mul_nonneg (timeBound_nonneg cut |t|) (norm_nonneg _)) (crossBound_nonneg cut (forceGauss g p psi) t))

theorem finiteTransfer_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) :
    ‖finiteTransferDerivative cut F f g phi psi p k ell t‖ ≤ transferBound cut f g phi psi p k ell t := by
  have same : finiteTransferDerivative cut F f g phi psi p k ell t=
      transferCoefficient (compression (p+k+ell) F+cutoff cut) (compression (p+k) F+cutoff cut)
        (compression (p+ell) F+cutoff cut) (compression p F+cutoff cut)
        (localizedGauss f (p+ell) phi) (localizedGauss f p phi)
        (forceGauss g (p+k) psi) (forceGauss g p psi)
        (contactGauss f g p (contactLocalizer phi psi)) t := by
    rw [transferCoefficient_integral]
    rfl
  rw [same]
  have base := original_time_window p F cut |t| t (abs_nonneg t) le_rfl
  have outer := original_time_window (p+k+ell) F cut |t| (-t) (abs_nonneg t) (by rw [abs_neg])
  have reverse := crossTime_source_bound (p+k+ell) (p+k) F cut (forceGauss g (p+k) psi) (-t)
  have forward := crossTime_source_bound (p+ell) p F cut (forceGauss g p psi) t
  have reflected : crossBound cut (forceGauss g (p+k) psi) (-t)=crossBound cut (forceGauss g (p+k) psi) t := by
    simp only [crossBound,abs_neg]
  rw [reflected] at reverse
  have P:=timeBound_nonneg cut |t|
  have Q:=crossBound_nonneg cut (forceGauss g (p+k) psi) t
  unfold transferCoefficient transferBound
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right reverse (norm_nonneg _))) base (norm_nonneg _)
          (mul_nonneg Q (norm_nonneg _)))
    · exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right outer (norm_nonneg _))) base (norm_nonneg _)
          (mul_nonneg P (norm_nonneg _)))
  · exact (norm_mul_le _ _).trans (mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right outer (norm_nonneg _))) forward (norm_nonneg _)
        (mul_nonneg P (norm_nonneg _)))

def transferDerivativeFamily (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) : Operator Index H where
  component F:=finiteTransferDerivative cut F f g phi psi p k ell t
  bounded:=⟨transferBound cut f g phi psi p k ell t,transferBound_nonneg cut f g phi psi p k ell t,
    fun F v=>((finiteTransferDerivative cut F f g phi psi p k ell t).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (finiteTransfer_bound cut F f g phi psi p k ell t) (norm_nonneg v))⟩

def transferCurveFamily (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (r t : ℝ) : Operator Index H where
  component F:=finiteTransferCurve cut F f g phi psi p k ell r t
  bounded:=⟨|r| *transferBound cut f g phi psi p k ell t,
    mul_nonneg (abs_nonneg r) (transferBound_nonneg cut f g phi psi p k ell t),fun F v=>by
    rw [finiteTransfer_exact,smul_apply,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |r| *(transferBound cut f g phi psi p k ell t*‖v‖) :=
        mul_le_mul_of_nonneg_left (((finiteTransferDerivative cut F f g phi psi p k ell t).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (finiteTransfer_bound cut F f g phi psi p k ell t) (norm_nonneg v))) (abs_nonneg r)
      _ = _ := by ring⟩

def transferredDerivative (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (transferDerivativeFamily cut f g phi psi p k ell t)

def transferredCurve (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (r t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (transferCurveFamily cut f g phi psi p k ell r t)

theorem sourceFilter_transfer_exact (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (r t : ℝ) :
    transferredCurve cut f g phi psi p k ell r t=r • transferredDerivative cut f g phi psi p k ell t := by
  change lift sourceFilter (transferCurveFamily cut f g phi psi p k ell r t)=
    r • lift sourceFilter (transferDerivativeFamily cut f g phi psi p k ell t)
  apply SourceFamilyOperator.ext sourceFilter
  intro v
  rw [smul_apply,lift_coe,lift_coe,←UniformSpace.Completion.coe_smul]
  congr 1
  apply Family.ext
  funext F
  change finiteTransferCurve cut F f g phi psi p k ell r t (value v F)=
    r • (finiteTransferDerivative cut F f g phi psi p k ell t (value v F))
  rw [finiteTransfer_exact,smul_apply]

theorem sourceFilter_transfer_derivative (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>transferredCurve cut f g phi psi p k ell r t)
      (transferredDerivative cut f g phi psi p k ell t) 0 := by
  simp only [sourceFilter_transfer_exact]
  convert! (hasDerivAt_id (0:ℝ)).smul_const (transferredDerivative cut f g phi psi p k ell t) using 1
  simp only [one_smul]

open GaussComposite GaussComposite.SourceGraph

theorem prepared_transfer_derivative (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    HasDerivAt (fun r : ℝ=>SourceGraph.response (transferredCurve cut f g phi psi p k ell r t) left right lc ls rc rs u v)
      (SourceGraph.response (transferredDerivative cut f g phi psi p k ell t) left right lc ls rc rs u v) 0 :=
  (preparationRead left right lc ls rc rs u v).hasFDerivAt.comp_hasDerivAt 0
    (sourceFilter_transfer_derivative cut f g phi psi p k ell t)

theorem transferredDerivative_bound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) :
    ‖transferredDerivative cut f g phi psi p k ell t‖ ≤ transferBound cut f g phi psi p k ell t :=
  lift_bound sourceFilter _ _ (transferBound_nonneg cut f g phi psi p k ell t)
    (fun F=>finiteTransfer_bound cut F f g phi psi p k ell t)

 theorem prepared_transfer_bound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    ‖SourceGraph.response (transferredDerivative cut f g phi psi p k ell t) left right lc ls rc rs u v‖ ≤
      legBound^2*transferBound cut f g phi psi p k ell t*‖u‖*‖v‖ := by
  apply (SourceGraph.response_bound _ left right lc ls rc rs u v).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (transferredDerivative_bound cut f g phi psi p k ell t) (sq_nonneg _)) (norm_nonneg u)) (norm_nonneg v)

open CanonicalPreparationCore.Completed CanonicalPreparationCreation PreparationVacuumNativeClosure
open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation

 theorem original_prepared_transfer (x : zeroLocalizedSpace actualNativeLocalizer)
    (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p k ell : PhysicalMomentum) (t : ℝ)
    (left right : Bool) (lc ls rc rs : Fin 2) :
    (∃ h : prepared (zeroLocalizedProfile actualNativeLocalizer x)∈GaussRadialDomain.closedY.domain,
      ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared (zeroLocalizedProfile actualNativeLocalizer x),h⟩-
        cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer x))‖ ≤
          (915/916:ℝ)^(n+1)*916*GaussYukawaCoefficient.bound*‖x‖) ∧
    HasDerivAt (fun r : ℝ=>SourceGraph.response (transferredCurve cut f g phi psi p k ell r t) left right lc ls rc rs
      (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x))
      (SourceGraph.response (transferredDerivative cut f g phi psi p k ell t) left right lc ls rc rs
        (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x)) 0 := by
  obtain ⟨h,_,bound⟩:=PreparationVacuumLocalizedYukawa.original_prepared_Y_domain x
  exact ⟨⟨h,bound⟩,prepared_transfer_derivative cut f g phi psi p k ell t left right lc ls rc rs _ _⟩

end LowEnergy.PreparationVacuumFieldPerturbation
