import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseHessian
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusSignedClockBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockSourceTail
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarPositiveBulkWard
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiSecondPressure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusClockSturm
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open GaussNativePotential GaussYukawaCoefficient GaussRadialMomentum GaussNativeMatter GaussQuantumMultiplier
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourcePhysicalKineticSquare SourceClockAcceleration SourceClockReflectedForm
open SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarInverseBulk
open SourceScalarDoubleCurrent SourceScalarPairedTransport
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusResponseNativeBudget
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] SourceClockYukawaCubicCurrent.resolventCore
  compressionCore defectAction diagonalAction
private abbrev U : End := inverseVolumeAction
private abbrev J : End := clockCurrent
private abbrev E : End := SourceScalarVirialBulk.phiEulerAction

def clockMean : End := (1/2 : ℂ) • (U*J+J*U)

private theorem inverse_pair (f g : QuantumTest) :
    sourcePair f (U g)=sourcePair (U f) g := multiply_pair _ _ f g

private theorem clock_pair (f g : QuantumTest) :
    sourcePair f (J g)=sourcePair (J f) g :=
  SourceClockFixedInputSeed.original_clock_current_pair f g

private theorem inverse_dilation : dilation*U-U*dilation=(2*Complex.I) • U := by
  have h := congrArg (fun A : End => (-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (dilation*U-U*dilation))=
    (-2*Complex.I/3) • ((-3 : ℂ) • U) at h
  simp only [smul_smul] at h
  have hi : (-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring

private theorem clock_volume_contact : J*U-U*J=
    (3*Complex.I*(sourceTime 0 : ℂ)/2) • (U*U) := by
  have h := congrArg (fun A : End => U*A+A*U) inverse_dilation
  change clockCurrent*U-U*clockCurrent=(3*Complex.I*(sourceTime 0:ℂ)/2) • (U*U)
  rw [SourceClockAcceleration.original_clock_current]
  linear_combination (norm := (noncomm_ring;module)) (3*(sourceTime 0 : ℂ)/8) • h

private theorem clock_mean_contact : clockMean=U*J+
    (3*Complex.I*(sourceTime 0 : ℂ)/4) • (U*U) := by
  have h := clock_volume_contact
  unfold clockMean
  linear_combination (norm := module) (1/2 : ℂ) • h

theorem clock_mean_pair (f g : QuantumTest) :
    sourcePair f (clockMean g)=sourcePair (clockMean f) g := by
  have h1 := inverse_pair f (J g)
  have h2 := clock_pair (U f) g
  have h3 := clock_pair f (U g)
  have h4 := inverse_pair (J f) g
  simp only [clockMean,LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,
    sourcePair,map_smul,map_add,inner_smul_left,inner_smul_right,inner_add_left,inner_add_right]
  change (1/2 : ℂ)*(sourcePair f (U (J g))+sourcePair f (J (U g)))=
    (starRingEnd ℂ (1/2 : ℂ))*(sourcePair (U (J f)) g+sourcePair (J (U f)) g)
  rw [h1,h2,h3,h4]
  norm_num only [map_div₀,map_ofNat,map_one]
  ring

private theorem euler_inverse : Commute E U := by
  have h := SourceScalarInverseBulk.inverse_phi
  change E*U-U*E=0 at h
  exact sub_eq_zero.mp h

private theorem euler_dilation : Commute E dilation := by
  have h := SourceScalarPositiveBulkWard.original_dilation_phi
  change E*dilation-dilation*E=0 at h
  exact sub_eq_zero.mp h

private theorem euler_clock : Commute E J := by
  change Commute E clockCurrent
  rw [SourceClockAcceleration.original_clock_current]
  exact ((euler_inverse.mul_right euler_dilation).add_right
    (euler_dilation.mul_right euler_inverse)).smul_right _

theorem euler_clock_mean : Commute E clockMean :=
  ((euler_inverse.mul_right euler_clock).add_right
    (euler_clock.mul_right euler_inverse)).smul_right _

private theorem whole_scalar_clock_pair (a v : QuantumTest) :
    2*(sourcePair (U a) (J v)).im+
      (sourceTime 0/2)*(sourcePair (U v) (U a)).re=
    2*(sourcePair a (clockMean v)).im-
      sourceTime 0*(sourcePair a ((U*U) v)).re := by
  have hp := inverse_pair a (J v)
  have hU := inverse_pair a (U v)
  have hc := pair_conjugate (U a) (U v)
  have hm := LinearMap.congr_fun clock_mean_contact v
  rw [hm]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_add,map_smul,inner_add_right,inner_smul_right,
    Complex.add_im,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im] at hp hU hc ⊢
  have hr := congrArg Complex.re hc
  simp only [Complex.conj_re] at hr
  norm_num at hp hU hr ⊢
  rw [hp,hU,←hr]
  ring

private theorem phi_pair (f g : QuantumTest) :
    sourcePair f (SourceScalarAffineScaleTransport.generator g)=
      -sourcePair (SourceScalarAffineScaleTransport.generator f) g := by
  have hd (q : QuantumTest) : HasDerivAt
      (fun t : ℝ => embed (SourceScalarAffineScaleTransport.coreFlow t q))
      (embed (SourceScalarAffineScaleTransport.generator q)) 0 := by
    simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0
  have h := (hd f).inner ℂ (hd g)
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero] at h
  have he : (fun t : ℝ => inner ℂ
      (embed (SourceScalarAffineScaleTransport.coreFlow t f))
      (embed (SourceScalarAffineScaleTransport.coreFlow t g)))=
      fun _ => sourcePair f g :=
    funext (fun t => SourceScalarAffineScaleTransport.coreFlow_pair t f g)
  rw [he] at h
  have heq := h.unique (hasDerivAt_const (0 : ℝ) (sourcePair f g))
  change sourcePair f (SourceScalarAffineScaleTransport.generator g)+
    sourcePair (SourceScalarAffineScaleTransport.generator f) g=0 at heq
  exact eq_neg_of_add_eq_zero_left heq

private theorem phi_euler_pair_shift (f g : QuantumTest) :
    sourcePair f (E g)= -sourcePair (E f) g-(61:ℂ)*sourcePair f g := by
  have h := phi_pair f g
  change sourcePair f ((E+(61/2:ℂ) • 1) g)=
    -sourcePair ((E+(61/2:ℂ) • 1) f) g at h
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_add_left,inner_smul_right,inner_smul_left] at h ⊢
  norm_num only [map_div₀,map_ofNat,map_one] at h
  linear_combination (norm:=ring) h

private theorem shifted_euler_left (f g : QuantumTest) :
    sourcePair ((E+(61:ℂ) • 1) f) g= -sourcePair f (E g) := by
  have h := phi_euler_pair_shift f g
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,sourcePair,map_add,map_smul,
    inner_add_left,inner_smul_left] at h ⊢
  norm_num only [map_ofNat] at h ⊢
  linear_combination (norm:=ring) h

private theorem scalar_clock_sturm_pair (s v : QuantumTest) :
    2*(sourcePair (U ((-(sourceTime 0:ℂ)/4) • ((E+(61:ℂ) • 1) s))) (J v)).im+
      (sourceTime 0/2)*(sourcePair (U v)
        (U ((-(sourceTime 0:ℂ)/4) • ((E+(61:ℂ) • 1) s)))).re=
    (sourceTime 0/2)*(sourcePair s (clockMean (E v))).im-
      (sourceTime 0)^2/4*(sourcePair s ((U*U) (E v))).re := by
  rw [whole_scalar_clock_pair]
  have hK := shifted_euler_left s (clockMean v)
  have hU := shifted_euler_left s ((U*U) v)
  have heK := LinearMap.congr_fun euler_clock_mean.eq v
  have heU := LinearMap.congr_fun (euler_inverse.mul_right euler_inverse).eq v
  change E (clockMean v)=clockMean (E v) at heK
  change E ((U*U) v)=(U*U) (E v) at heU
  rw [heK] at hK
  rw [heU] at hU
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    sourcePair,map_smul,map_add,inner_add_left,inner_smul_left,
    Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,
    map_neg,map_div₀,map_ofNat,Complex.conj_ofReal,Complex.div_re,Complex.div_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im] at hK hU ⊢
  have hKi := congrArg Complex.im hK
  have hUr := congrArg Complex.re hU
  simp only [Complex.neg_im,Complex.neg_re] at hKi hUr
  norm_num at hKi hUr ⊢
  rw [hKi,hUr]
  ring

private abbrev r : End := phiRadiusAction
private abbrev S : End := phiInverseAction
private abbrev Q : End := 1-S

private theorem radius_real (f : QuantumTest) :
    (r f : SourceCoordinateSlice → FockFiber)=fun z => phiRadius z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem radius_coframe_derivative (z : SourceCoordinateSlice) (i : Fin 6) :
    fderiv ℝ phiRadius z (GaussCoframeCore.coframeDirection i)=0 := by
  have hp : HasDerivAt (fun t : ℝ => z+t • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const (GaussCoframeCore.coframeDirection i) |>.const_add z
  have hd : HasFDerivAt phiRadius (fderiv ℝ phiRadius z) z :=
    (SourceClockRadiusResponseAffine.affine_radius_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hh := hd.comp_hasDerivAt_of_eq 0 hp (by simp)
  have he : (fun t : ℝ => phiRadius (z+t • GaussCoframeCore.coframeDirection i))=
      fun _ => phiRadius z := by
    funext t
    unfold phiRadius SourceClockRadiusResponseAffine.affineRadius scalarField
    simp only [GaussCoframeCore.coframeDirection,Prod.smul_mk,Prod.snd_add,
      smul_zero,add_zero]
  change HasDerivAt (fun t : ℝ => phiRadius (z+t • GaussCoframeCore.coframeDirection i))
    (fderiv ℝ phiRadius z (GaussCoframeCore.coframeDirection i)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)

private theorem coframe_derivative_radius (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) r := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (r f) z=
    r (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f) z
  rw [GaussCoframeCore.derivative_apply,radius_real,
    fderiv_fun_smul (SourceClockRadiusResponseAffine.affine_radius_smooth.differentiable
      (by simp)).differentiableAt (f.contDiff.differentiable (by simp)).differentiableAt]
  change phiRadius z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
    fderiv ℝ phiRadius z (GaussCoframeCore.coframeDirection i) • f z=_
  rw [radius_coframe_derivative,zero_smul,add_zero,radius_real]
  dsimp only
  rw [GaussCoframeCore.derivative_apply]

private theorem real_radius (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ a z.val) : Commute (multiply a smooth) r := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (a z:ℂ) (phiRadius z:ℂ) (f z)

private theorem number_radius : Commute GaussCoframeForm.number r := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussQuantumMultiplier.quantized _ ((phiRadius z:ℂ) • f z)=
    (phiRadius z:ℂ) • GaussQuantumMultiplier.quantized _ (f z)
  exact map_smul _ _ _

private theorem coframe_euler_radius : Commute SourceCoframeDilation.eulerAction r := by
  apply Commute.sum_left
  intro i _
  exact (real_radius _ _).mul_left (coframe_derivative_radius i)

private theorem dilation_radius : Commute dilation r := by
  rw [SourceCoframeDilation.dilation_operator]
  exact ((((coframe_euler_radius.smul_left (2/3:ℂ)).add_left number_radius).add_left
    ((Commute.one_left r).smul_left (4:ℂ))).smul_left (-Complex.I))

private theorem clock_radius : Commute J r := by
  change Commute clockCurrent r
  rw [SourceClockAcceleration.original_clock_current]
  exact (((real_radius _ _).mul_left dilation_radius).add_left
    (dilation_radius.mul_left (real_radius _ _))).smul_left _

theorem clock_mean_radius : Commute clockMean r :=
  (((real_radius _ _).mul_left clock_radius).add_left
    (clock_radius.mul_left (real_radius _ _))).smul_left _

private theorem radius_inverse : r*S=(1:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'

private theorem inverse_radius : S*r=(1:End) :=
  (real_radius _ _).eq.trans radius_inverse

theorem clock_mean_inverse : Commute clockMean S := by
  have h := congrArg (fun A : End => S*A*S) clock_mean_radius.eq
  have hleft : S*(clockMean*r)*S=S*clockMean := by
    calc _=S*clockMean*(r*S) := by noncomm_ring
         _=_ := by rw [radius_inverse,mul_one]
  have hright : S*(r*clockMean)*S=clockMean*S := by
    calc _=(S*r)*clockMean*S := by noncomm_ring
         _=_ := by rw [inverse_radius,one_mul]
  rw [hleft,hright] at h
  exact h.symm

private theorem clock_mean_theta (m ell : ℕ) : Commute clockMean (phiThetaAction m ell) :=
  (((Commute.one_right clockMean).sub_right clock_mean_inverse).pow_right (m+1)).sub_right
    (((Commute.one_right clockMean).sub_right clock_mean_inverse).pow_right (ell+1))

private abbrev profileS : End := SourceClockPhiRadiusSourceCurrent.phiInverseAction
private abbrev profileR : End := SourceClockPhiRadiusSourceCurrent.phiRadiusAction
private abbrev profileQ : End := 1-profileS
private abbrev profileTheta (m ell : ℕ) : End :=
  SourceClockRadiusAffineCutoff.phiThetaAction m ell
private abbrev profileFirst (m ell : ℕ) : End :=
  SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell
private abbrev profileSecond (m ell : ℕ) : End :=
  SourceClockPhiRadiusResponseHessian.phiSecondPeak m ell
private abbrev profileDelta : End := profileS^3-profileS

private theorem phi_profile_inverse_radius : profileS*profileR=(1:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  have hp : 0 < phiRadius z := by
    unfold phiRadius SourceClockRadiusResponseAffine.affineRadius
    positivity
  rw [smul_smul]
  have he : (phiReciprocal z:ℂ)*(phiRadius z:ℂ)=1 := by
    unfold phiReciprocal
    push_cast
    field_simp [hp.ne']
  rw [he,one_smul]

private theorem phi_profile_radius_inverse : profileR*profileS=(1:End) := by
  have hc : Commute profileR profileS := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (phiRadius z:ℂ) (phiReciprocal z:ℂ) (f z)
  exact hc.eq.trans phi_profile_inverse_radius

private theorem phi_profile_bracket_product (A B C : End) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by
  unfold bracket
  noncomm_ring

private theorem phi_profile_bracket_sub (A B C : End) :
    bracket A (B-C)=bracket A B-bracket A C := by
  unfold bracket
  noncomm_ring

private theorem phi_profile_bracket_smul (A B : End) (k : ℂ) :
    bracket A (k • B)=k • bracket A B := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]

private theorem phi_profile_euler_inverse : bracket E profileS=profileDelta := by
  have hr : bracket E profileR=profileR-profileS :=
    SourceClockPhiRadiusSourceCurrent.original_phi_euler_radius
  have hi : bracket E profileS= -(profileS*bracket E profileR*profileS) := by
    have h1 : profileS*E*profileR*profileS=profileS*E := by
      calc
        _=profileS*E*(profileR*profileS) := by noncomm_ring
        _=_ := by rw [phi_profile_radius_inverse,mul_one]
    have h2 : profileS*profileR*E*profileS=E*profileS := by
      rw [phi_profile_inverse_radius,one_mul]
    calc
      _= -(profileS*E*profileR*profileS-profileS*profileR*E*profileS) := by
        rw [h1,h2]
        unfold bracket
        abel
      _=_ := by unfold bracket;noncomm_ring
  rw [hi,hr]
  change -(profileS*(profileR-profileS)*profileS)=profileS^3-profileS
  calc
    _= -((profileS*profileR)*profileS)+profileS^3 := by noncomm_ring
    _=_ := by rw [phi_profile_inverse_radius,one_mul];abel

private theorem phi_profile_euler_Q : bracket E profileQ= -profileDelta := by
  change bracket E (1-profileS)= -profileDelta
  rw [phi_profile_bracket_sub,phi_profile_euler_inverse]
  simp only [bracket,mul_one,one_mul,sub_self,zero_sub]

private theorem phi_profile_Q_delta : Commute profileQ profileDelta :=
  (((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_right 3).sub_right
    ((Commute.one_left profileS).sub_left (Commute.refl profileS))

private theorem phi_profile_euler_geometric_successor (n : ℕ) :
    bracket E (profileQ^(n+1))=(-(n+1:ℂ)) • (profileQ^n*profileDelta) := by
  induction n with
  | zero =>
    simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul,one_smul,neg_smul]
      using phi_profile_euler_Q
  | succ n ih =>
    have hm : (profileQ^n*profileDelta)*profileQ=profileQ^(n+1)*profileDelta := by
      rw [mul_assoc,←phi_profile_Q_delta.eq,←mul_assoc,←pow_succ]
    rw [show n+1+1=(n+1)+1 from rfl,pow_succ,phi_profile_bracket_product,ih,phi_profile_euler_Q]
    simp only [smul_mul_assoc,mul_neg]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module

private theorem phi_profile_euler_geometric (n : ℕ) :
    bracket E (profileQ^n)=(-(n:ℂ)) • (profileQ^(n-1)*profileDelta) := by
  cases n with
  | zero => simp [bracket]
  | succ n =>
    simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
      using phi_profile_euler_geometric_successor n

private theorem phi_profile_euler_theta (m ell : ℕ) :
    bracket E (profileTheta m ell)=profileFirst m ell*profileDelta := by
  change bracket E (profileQ^(m+1)-profileQ^(ell+1))=profileFirst m ell*profileDelta
  rw [phi_profile_bracket_sub,phi_profile_euler_geometric_successor,
    phi_profile_euler_geometric_successor]
  change _=((ell+1:ℂ) • profileQ^ell-(m+1:ℂ) • profileQ^m)*profileDelta
  simp only [sub_mul,smul_mul_assoc]
  module

private theorem phi_profile_euler_first_peak (m ell : ℕ) :
    bracket E (profileFirst m ell)=profileSecond m ell*profileDelta := by
  change bracket E ((ell+1:ℂ) • profileQ^ell-(m+1:ℂ) • profileQ^m)=profileSecond m ell*profileDelta
  rw [phi_profile_bracket_sub,phi_profile_bracket_smul,phi_profile_bracket_smul,
    phi_profile_euler_geometric,phi_profile_euler_geometric]
  change _=((m*(m+1):ℂ) • profileQ^(m-1)-(ell*(ell+1):ℂ) • profileQ^(ell-1))*profileDelta
  simp only [sub_mul,smul_mul_assoc,smul_smul]
  module

private theorem phi_profile_euler_power (n : ℕ) :
    bracket E (profileS^n)=(n:ℂ) • (profileS^n*(profileS^2-1)) := by
  induction n with
  | zero => simp [bracket]
  | succ n ih =>
    rw [pow_succ,phi_profile_bracket_product,ih,phi_profile_euler_inverse]
    have he : profileS^n*profileDelta=profileS^(n+1)*(profileS^2-1) := by
      rw [pow_succ]
      change profileS^n*(profileS^3-profileS)=_
      noncomm_ring
    have hn : (profileS^n*(profileS^2-1))*profileS=profileS^(n+1)*(profileS^2-1) := by
      rw [pow_succ]
      noncomm_ring
    simp only [Nat.cast_succ,add_smul,one_smul,smul_mul_assoc]
    rw [he,hn]
    simp only [pow_succ]

private theorem phi_profile_theta_S (m ell : ℕ) : Commute (profileTheta m ell) profileS :=
  (((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left (m+1)).sub_left
    (((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left (ell+1))

private theorem phi_profile_first_S (m ell : ℕ) : Commute (profileFirst m ell) profileS :=
  ((((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left ell).smul_left _).sub_left
    ((((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left m).smul_left _)

private theorem phi_profile_second_S (m ell : ℕ) : Commute (profileSecond m ell) profileS :=
  ((((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left (m-1)).smul_left _).sub_left
    ((((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left (ell-1)).smul_left _)

private theorem phi_profile_theta_first (m ell : ℕ) :
    Commute (profileTheta m ell) (profileFirst m ell) := by
  have hQ : Commute (profileTheta m ell) profileQ :=
    (Commute.one_right _).sub_right (phi_profile_theta_S m ell)
  exact ((hQ.pow_right ell).smul_right _).sub_right ((hQ.pow_right m).smul_right _)

private theorem phi_profile_theta_second (m ell : ℕ) :
    Commute (profileTheta m ell) (profileSecond m ell) := by
  have hQ : Commute (profileTheta m ell) profileQ :=
    (Commute.one_right _).sub_right (phi_profile_theta_S m ell)
  exact ((hQ.pow_right (m-1)).smul_right _).sub_right ((hQ.pow_right (ell-1)).smul_right _)

def profileC (m ell : ℕ) : End := profileS*(profileTheta m ell)^2
def profileM (m ell : ℕ) : End := profileFirst m ell*profileS^3*profileTheta m ell

theorem phi_profile_euler_c (m ell : ℕ) :
    bracket E (profileC m ell)+(61:ℂ) • profileC m ell=
      profileS*(profileTheta m ell)^2*((60:ℂ) • 1+profileS^2)-
        (2:ℂ) • (profileFirst m ell*profileTheta m ell*profileS^2*(1-profileS^2)) := by
  unfold profileC
  rw [phi_profile_bracket_product,phi_profile_euler_inverse]
  have hT : bracket E ((profileTheta m ell)^2)=
      profileFirst m ell*profileDelta*profileTheta m ell+
        profileTheta m ell*(profileFirst m ell*profileDelta) := by
    rw [pow_two,phi_profile_bracket_product,phi_profile_euler_theta]
  rw [hT]
  change (profileS^3-profileS)*(profileTheta m ell)^2+
    profileS*(profileFirst m ell*(profileS^3-profileS)*profileTheta m ell+
      profileTheta m ell*(profileFirst m ell*(profileS^3-profileS)))+
    (61:ℂ) • (profileS*(profileTheta m ell)^2)=_
  have ht (A : End) : profileTheta m ell*(profileS*A)=profileS*(profileTheta m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_S m ell).eq,mul_assoc]
  have hb (A : End) : profileFirst m ell*(profileS*A)=profileS*(profileFirst m ell*A) := by
    rw [←mul_assoc,(phi_profile_first_S m ell).eq,mul_assoc]
  have hbt (A : End) : profileFirst m ell*(profileTheta m ell*A)=profileTheta m ell*(profileFirst m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_first m ell).symm.eq,mul_assoc]
  noncomm_ring [ht,hb,hbt,(phi_profile_theta_S m ell).eq,(phi_profile_first_S m ell).eq,
    (phi_profile_theta_first m ell).symm.eq]
  module

theorem phi_profile_euler_M (m ell : ℕ) :
    bracket E (profileM m ell)+(61:ℂ) • profileM m ell=
      -((profileFirst m ell)^2+profileTheta m ell*profileSecond m ell)*
        profileS^4*(1-profileS^2)+
      profileFirst m ell*profileTheta m ell*profileS^3*((58:ℂ) • 1+(3:ℂ) • profileS^2) := by
  unfold profileM
  rw [phi_profile_bracket_product,phi_profile_bracket_product,
    phi_profile_euler_first_peak,phi_profile_euler_power,phi_profile_euler_theta]
  change (profileSecond m ell*(profileS^3-profileS)*profileS^3+
      profileFirst m ell*((3:ℂ) • (profileS^3*(profileS^2-1))))*profileTheta m ell+
    profileFirst m ell*profileS^3*(profileFirst m ell*(profileS^3-profileS))+
    (61:ℂ) • (profileFirst m ell*profileS^3*profileTheta m ell)=_
  have ht (A : End) : profileTheta m ell*(profileS*A)=profileS*(profileTheta m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_S m ell).eq,mul_assoc]
  have hb (A : End) : profileFirst m ell*(profileS*A)=profileS*(profileFirst m ell*A) := by
    rw [←mul_assoc,(phi_profile_first_S m ell).eq,mul_assoc]
  have hc (A : End) : profileSecond m ell*(profileS*A)=profileS*(profileSecond m ell*A) := by
    rw [←mul_assoc,(phi_profile_second_S m ell).eq,mul_assoc]
  have hbt (A : End) : profileFirst m ell*(profileTheta m ell*A)=profileTheta m ell*(profileFirst m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_first m ell).symm.eq,mul_assoc]
  have hct (A : End) : profileSecond m ell*(profileTheta m ell*A)=profileTheta m ell*(profileSecond m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_second m ell).symm.eq,mul_assoc]
  noncomm_ring [ht,hb,hc,hbt,hct,(phi_profile_theta_S m ell).eq,(phi_profile_first_S m ell).eq,
    (phi_profile_second_S m ell).eq,(phi_profile_theta_first m ell).symm.eq,
    (phi_profile_theta_second m ell).symm.eq]
  module

theorem phi_profile_paired_derivative (A : End) (p q : QuantumTest) :
    sourcePair p (A (E q))= -sourcePair (E p) (A q)-
      sourcePair p ((bracket E A+(61:ℂ) • A) q) := by
  have h := phi_euler_pair_shift p (A q)
  have he : E (A q)=A (E q)+bracket E A q := by
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
    module
  rw [he] at h
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right] at h ⊢
  linear_combination (norm := ring) h

private theorem phi_profile_c_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (profileC m ell (E q))= -sourcePair (E p) (profileC m ell q)-
      sourcePair p ((profileS*(profileTheta m ell)^2*((60:ℂ) • 1+profileS^2)-
        (2:ℂ) • (profileFirst m ell*profileTheta m ell*profileS^2*(1-profileS^2)) : End) q) := by
  rw [phi_profile_paired_derivative,phi_profile_euler_c]

private theorem phi_profile_M_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (profileM m ell (E q))= -sourcePair (E p) (profileM m ell q)-
      sourcePair p ((-((profileFirst m ell)^2+profileTheta m ell*profileSecond m ell)*
        profileS^4*(1-profileS^2)+
        profileFirst m ell*profileTheta m ell*profileS^3*((58:ℂ) • 1+(3:ℂ) • profileS^2) : End) q) := by
  rw [phi_profile_paired_derivative,phi_profile_euler_M]

open SourceScalarFlatJoint SourceHamiltonianVolume SourceClockYukawaCubicCurrent

private abbrev nativeW : End := multiply scalarWeight scalarWeight_smooth
private abbrev nativeP (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev nativePa (a : ScalarIndex) : End := GaussMomentumAdjoint.adjoint (scalarDirection a)
private abbrev nativeD (a : ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev nativeFirst (m ell : ℕ) : End :=
  SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell

private def phiNativeColumn (a : ScalarIndex) : End :=
  multiply (fun z => inner ℝ (scalarField z) (scalarBasis a))
    (fun _ => (scalarField_smooth.inner ℝ contDiff_const).contDiffAt)
private def phiNativeMomentum : End := ∑ a : ScalarIndex,phiNativeColumn a*nativeP a
private def phiNativeAdjoint : End := ∑ a : ScalarIndex,nativePa a*phiNativeColumn a

private theorem phi_native_expansion (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,inner ℝ (scalarField z) (scalarBasis a) • scalarDirection a)=
      (scalarField z,0) := by
  apply Prod.ext
  · simp only [Prod.fst_sum,Prod.smul_fst]
    simpa only [scalarDirection,OrthonormalBasis.repr_apply_apply,real_inner_comm] using
      scalarBasis.sum_repr (scalarField z)
  · simp [scalarDirection,Prod.snd_sum]

private theorem phi_native_momentum_contraction : phiNativeMomentum=(-Complex.I) • E := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have he := congrArg (SourceElectricColumns.pointMomentum f z) (phi_native_expansion z)
    simp only [map_sum,map_smul] at he
    have hs : phiNativeMomentum f z=∑ a : ScalarIndex,inner ℝ (scalarField z) (scalarBasis a) •
        SourceElectricColumns.pointMomentum f z (scalarDirection a) := by
      simp only [phiNativeMomentum,LinearMap.sum_apply,sum_apply,Module.End.mul_apply]
      apply Finset.sum_congr rfl
      intro a _
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    rw [hs,he]
    let v : scalarSlice := vacuumSlice+z.2.1
    have hi := native_scalar_slice_inverse ⟨z,hz⟩ v
    have hd : direction (scalarField z,0) z=phiEuler z := by
      change (0,(inverseL z (v.val,0)).2)=_
      rw [hi]
      rfl
    have hc : connection (scalarField z,0) z=0 := by
      change GaussNativeMatter.nativeFock (inverseL z (v.val,0)).1=0
      rw [hi,map_zero]
    change (-Complex.I) • (fderiv ℝ f z (direction (scalarField z,0) z)+
      connection (scalarField z,0) z (f z))=(-Complex.I) • phiEulerAction f z
    rw [hd,hc,zero_apply,add_zero,phi_euler_apply]
  · exact (image_eq_zero_of_notMem_tsupport (fun h => hz ((phiNativeMomentum f).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h => hz (((-Complex.I) • E f).tsupport_subset h))).symm

private theorem phi_native_adjoint_contraction :
    phiNativeAdjoint=(-Complex.I) • (E+(61:ℂ) • (1:End)) := by
  have hp (f g : QuantumTest) : sourcePair f (phiNativeAdjoint g)=sourcePair (phiNativeMomentum f) g := by
    simp only [phiNativeAdjoint,phiNativeMomentum,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
    apply Finset.sum_congr rfl
    intro a _
    change sourcePair f (nativePa a (phiNativeColumn a g))=sourcePair (phiNativeColumn a (nativeP a f)) g
    exact (adjoint_pair _ _ _).trans (multiply_pair _ _ _ _)
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have h := phi_euler_pair_shift f g
  rw [hp,phi_native_momentum_contraction]
  simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.one_apply,sourcePair,map_smul,map_add,
    inner_smul_left,inner_smul_right,inner_add_right,map_neg,Complex.conj_I,neg_neg] at h ⊢
  linear_combination (norm := ring) Complex.I*h

private theorem phi_native_inverse_volume (f : QuantumTest) : U (volumeAction f)=f := by
  have hc : Commute U volumeAction := SourceHamiltonianVolume.real_volume _ _
  exact (LinearMap.congr_fun hc.eq f).trans (volume_inverse f)

private theorem phi_native_adjoint_inverse (a : ScalarIndex) : Commute (nativePa a) U := by
  have h := SourceHamiltonianVolume.native_adjoint_volume (scalarDirection a)
  apply LinearMap.ext
  intro f
  have he := congrArg U (LinearMap.congr_fun h.eq (U f))
  simpa only [Module.End.mul_apply,volume_inverse,phi_native_inverse_volume] using! he.symm

/-- The same original two inputs generate T; the second input is literally rho*g. -/
private def phiRadialInput (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  (nativeFirst m ell*S-phiThetaAction m ell) (resolventCore F z hz (coreEquiv.symm g))-
    (nativeFirst m ell*S^2) (resolventCore F z hz (r (coreEquiv.symm g)))

private theorem phi_native_direction (a : ScalarIndex) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    phiNativeVector a m ell F z hz g=nativeD a (phiRadialInput m ell F z hz g) := by
  have hQ : Commute S (1-S) := (Commute.one_right S).sub_right (Commute.refl S)
  have hf : Commute S (nativeFirst m ell) :=
    ((hQ.pow_right ell).smul_right _).sub_right ((hQ.pow_right m).smul_right _)
  have hR : coreEquiv.symm (phiRadiusSource g)=r (coreEquiv.symm g) :=
    coreEquiv.symm_apply_apply _
  have hB : (ell+1:ℂ) • (S*(1-S)^ell)-(m+1:ℂ) • (S*(1-S)^m)=nativeFirst m ell*S := by
    have hb (n : ℕ) : (n+1:ℂ) • (S*(1-S)^n)=S*((n+1:ℂ) • (1-S)^n) := by
      rw [mul_smul_comm]
    rw [hb,hb,←mul_sub,←hf.eq]
    rfl
  have hSB : S*(nativeFirst m ell*S)=nativeFirst m ell*S^2 := by
    calc
      _=(S*nativeFirst m ell)*S := by noncomm_ring
      _=(nativeFirst m ell*S)*S := by rw [hf.eq]
      _=_ := by rw [pow_two];noncomm_ring
  unfold phiNativeVector
  change nativeD a
      (((ell+1:ℂ) • (S*(1-S)^ell)-(m+1:ℂ) • (S*(1-S)^m)-phiThetaAction m ell)
        (resolventCore F z hz (coreEquiv.symm g))-
        S (((ell+1:ℂ) • (S*(1-S)^ell)-(m+1:ℂ) • (S*(1-S)^m))
          (resolventCore F z hz (coreEquiv.symm (phiRadiusSource g)))))=_
  rw [hR,hB]
  congr 1
  change (nativeFirst m ell*S-phiThetaAction m ell) (resolventCore F z hz (coreEquiv.symm g))-
      (S*(nativeFirst m ell*S)) (resolventCore F z hz (r (coreEquiv.symm g)))=_
  rw [hSB]
  rfl

private theorem phi_native_weight_direction (a : ScalarIndex) :
    nativeW*nativeD a=((sourceTime 0:ℂ)/4) • (U*phiNativeColumn a*S) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (scalarWeight x:ℂ) • ((phiDirectionWeight (scalarBasis a) x:ℂ) • f x)=
    ((sourceTime 0:ℂ)/4) • ((reciprocalVolume x:ℂ) •
      ((inner ℝ (scalarField x) (scalarBasis a):ℂ) • ((phiReciprocal x:ℂ) • f x)))
  simp only [smul_smul]
  congr 1
  unfold scalarWeight phiDirectionWeight phiReciprocal reciprocalVolume
  push_cast
  ring

/-- True native Pa† and inverseL generate the 61-density Euler on the same response T. -/
private theorem actual_phi_native_euler_source (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    phiNativeDivergence m ell F z hz g=
      (-(sourceTime 0:ℂ)/4) •
        U ((E+(61:ℂ) • (1:End)) (S (phiRadialInput m ell F z hz g))) := by
  have hrow (a : ScalarIndex) :
      nativePa a (nativeW (phiNativeVector a m ell F z hz g))=
      ((sourceTime 0:ℂ)/4) • U
        ((nativePa a*phiNativeColumn a) (S (phiRadialInput m ell F z hz g))) := by
    rw [phi_native_direction]
    have he := LinearMap.congr_fun (phi_native_weight_direction a) (phiRadialInput m ell F z hz g)
    change nativeW (nativeD a (phiRadialInput m ell F z hz g))=_ at he
    rw [he]
    simp only [LinearMap.smul_apply,Module.End.mul_apply,map_smul]
    have hu := LinearMap.congr_fun (phi_native_adjoint_inverse a).eq
      (phiNativeColumn a (S (phiRadialInput m ell F z hz g)))
    exact congrArg (fun f : QuantumTest => ((sourceTime 0:ℂ)/4) • f) hu
  unfold phiNativeDivergence
  change (-Complex.I) • (∑ a : ScalarIndex,nativePa a
    (nativeW (phiNativeVector a m ell F z hz g)))=_
  simp only [hrow,←Finset.smul_sum,←map_sum,←LinearMap.sum_apply]
  change (-Complex.I) • (((sourceTime 0:ℂ)/4) •
    U (phiNativeAdjoint (S (phiRadialInput m ell F z hz g))))=_
  rw [phi_native_adjoint_contraction]
  simp only [LinearMap.smul_apply,map_smul,smul_smul]
  congr 1
  calc
    (-Complex.I)*(((sourceTime 0:ℂ)/4)*(-Complex.I))=
        (Complex.I*Complex.I)*((sourceTime 0:ℂ)/4) := by ring
    _=_ := by rw [Complex.I_mul_I];ring

private theorem actual_phi_native_euler_pair (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (p : QuantumTest) :
    sourcePair p (phiNativeDivergence m ell F z hz g)=
      ((sourceTime 0:ℂ)/4)*sourcePair (E p) (U (S (phiRadialInput m ell F z hz g))) := by
  rw [actual_phi_native_euler_source]
  have hc : Commute (E+(61:ℂ) • (1:End)) U :=
    euler_inverse.add_left ((Commute.one_left U).smul_left (61:ℂ))
  have he := LinearMap.congr_fun hc.eq (S (phiRadialInput m ell F z hz g))
  have hp := phi_euler_pair_shift p (U (S (phiRadialInput m ell F z hz g)))
  change sourcePair p ((-(sourceTime 0:ℂ)/4) •
    U ((E+(61:ℂ) • (1:End)) (S (phiRadialInput m ell F z hz g))))=_
  change (E+(61:ℂ) • (1:End)) (U (S (phiRadialInput m ell F z hz g)))=
    U ((E+(61:ℂ) • (1:End)) (S (phiRadialInput m ell F z hz g))) at he
  rw [←he]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,sourcePair,
    map_add,map_smul,inner_add_right,inner_smul_right] at hp ⊢
  linear_combination (norm := ring) (-(sourceTime 0:ℂ)/4)*hp

private theorem phi_inverse_radius_commute : Commute S r := by
  change S*r=r*S
  rw [inverse_radius,radius_inverse]

private theorem phi_first_radius (m ell : ℕ) : Commute (profileFirst m ell) r :=
  (((((Commute.one_left r).sub_left phi_inverse_radius_commute).pow_left ell).smul_left _).sub_left
    ((((Commute.one_left r).sub_left phi_inverse_radius_commute).pow_left m).smul_left _))

private theorem phi_second_radius (m ell : ℕ) : Commute (profileSecond m ell) r :=
  (((((Commute.one_left r).sub_left phi_inverse_radius_commute).pow_left (m-1)).smul_left _).sub_left
    ((((Commute.one_left r).sub_left phi_inverse_radius_commute).pow_left (ell-1)).smul_left _))

private theorem phi_radius_power (n : ℕ) : r*S^(n+1)=S^n := by
  rw [pow_succ',←mul_assoc,radius_inverse,one_mul]

def phiSturmCross (m ell : ℕ) : End :=
  (-1/2:ℂ) • (profileFirst m ell*(S^2-S^4))+
    (1/4:ℂ) • (phiThetaAction m ell*((60:ℂ) • S+S^3))

/-- The actual phi Hessian cross eliminates its complete second boundary peak. -/
theorem original_phi_hessian_cross (m ell : ℕ) :
    SourceClockPhiRadiusResponseHessian.bandHessian m ell-
      r*SourceClockPhiRadiusResponseHessian.thetaHessian m ell=phiSturmCross m ell := by
  have hf (k : ℕ) : r*(profileFirst m ell*S^(k+1))=profileFirst m ell*S^k := by
    rw [←mul_assoc,←(phi_first_radius m ell).eq,mul_assoc,phi_radius_power]
  have hs (k : ℕ) : r*(profileSecond m ell*S^(k+1))=profileSecond m ell*S^k := by
    rw [←mul_assoc,←(phi_second_radius m ell).eq,mul_assoc,phi_radius_power]
  unfold SourceClockPhiRadiusResponseHessian.bandHessian
    SourceClockPhiRadiusResponseHessian.thetaHessian phiSturmCross
  change (1/4:ℂ) • (profileSecond m ell*(S^3-S^5)-
    profileFirst m ell*((60:ℂ) • S^2+S^4)+
      phiThetaAction m ell*((60:ℂ) • S+S^3))-
    r*((1/4:ℂ) • (profileSecond m ell*(S^4-S^6)-
      profileFirst m ell*((58:ℂ) • S^3+(3:ℂ) • S^5)))=_
  simp only [mul_smul_comm,mul_add,mul_sub]
  rw [hf 2,hf 4,hs 3,hs 5]
  module

private theorem phi_radius_point (f : QuantumTest) (x : SourceCoordinateSlice) :
    r f x=(phiRadius x:ℂ) • f x := rfl

private theorem phi_inverse_point (f : QuantumTest) (x : SourceCoordinateSlice) :
    S f x=(phiReciprocal x:ℂ) • f x := rfl

private theorem phi_inverse_power_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    (S^n) f x=(phiReciprocal x:ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (phiReciprocal x:ℂ) • (((S^n) f) x)=_
    rw [ih,pow_succ',mul_smul]

private theorem phi_geometric_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    (Q^n) f x=((1-phiReciprocal x:ℝ):ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((Q^n) f) x-(phiReciprocal x:ℂ) • (((Q^n) f) x)=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module

private theorem phi_theta_point (m ell : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    phiThetaAction m ell f x=
      (((1-phiReciprocal x)^(m+1)-(1-phiReciprocal x)^(ell+1):ℝ):ℂ) • f x := by
  change ((Q^(m+1)) f) x-((Q^(ell+1)) f) x=_
  rw [phi_geometric_point,phi_geometric_point]
  push_cast
  module

private theorem phi_first_point (m ell : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    profileFirst m ell f x=
      (((ell+1:ℝ)*(1-phiReciprocal x)^ell-(m+1:ℝ)*(1-phiReciprocal x)^m):ℂ) • f x := by
  change (ell+1:ℂ) • ((Q^ell) f) x-(m+1:ℂ) • ((Q^m) f) x=_
  rw [phi_geometric_point,phi_geometric_point]
  push_cast
  module

def phiFixedEuler (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  phiThetaAction m ell (r (E (resolventCore F z hz (coreEquiv.symm g)))-
    E (resolventCore F z hz (r (coreEquiv.symm g))))

private theorem phi_euler_response (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    E (phiResponseCore m ell F z hz g)=phiFixedEuler m ell F z hz g-
      (r^2-(1:End)) (S (phiRadialInput m ell F z hz g)) := by
  let q := resolventCore F z hz (coreEquiv.symm g)
  let h := resolventCore F z hz (r (coreEquiv.symm g))
  have ht := LinearMap.congr_fun (phi_profile_euler_theta m ell) (r q-h)
  have hr := LinearMap.congr_fun original_phi_euler_radius q
  change E (phiThetaAction m ell (r q-h))-
    phiThetaAction m ell (E (r q-h))=(profileFirst m ell*(S^3-S)) (r q-h) at ht
  change E (r q)-r (E q)=(r-S) q at hr
  have he : E (phiThetaAction m ell (r q-h))=
      phiThetaAction m ell (r (E q)-E h)+
      phiThetaAction m ell ((r-S) q)+
      (profileFirst m ell*(S^3-S)) (r q-h) := by
    have hrt := congrArg (phiThetaAction m ell) hr
    simp only [map_sub] at ht hrt ⊢
    linear_combination (norm:=module) ht+hrt
  have hc : phiThetaAction m ell ((r-S) q)+
      (profileFirst m ell*(S^3-S)) (r q-h)=
      -(r^2-(1:End)) (S ((profileFirst m ell*S-phiThetaAction m ell) q-
        (profileFirst m ell*S^2) h)) := by
    apply DFunLike.ext
    intro x
    have ha (f k : QuantumTest) : (f+k) x=f x+k x := rfl
    have hs (f k : QuantumTest) : (f-k) x=f x-k x := rfl
    have hn (f : QuantumTest) : (-f) x=-(f x) := rfl
    have hr2 (f : QuantumTest) : (r^2) f x=(phiRadius x:ℂ)^2 • f x := by
      rw [pow_two]
      change r (r f) x=_
      rw [phi_radius_point,phi_radius_point,smul_smul,pow_two]
    simp only [LinearMap.sub_apply,Module.End.mul_apply,Module.End.one_apply,ha,hs,hn,
      phi_theta_point,phi_first_point,phi_inverse_power_point,phi_inverse_point,phi_radius_point,hr2]
    apply PiLp.ext
    intro word
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.neg_apply,smul_eq_mul]
    unfold phiReciprocal
    push_cast
    field_simp [(show (phiRadius x:ℂ)≠0 by
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne')]
    ring
  change E (phiThetaAction m ell (r q-h))=_
  rw [he,add_assoc,hc]
  rfl

private abbrev Htheta (m ell : ℕ) : End :=
  SourceClockPhiRadiusResponseHessian.thetaHessian m ell
private abbrev Hband (m ell : ℕ) : End :=
  SourceClockPhiRadiusResponseHessian.bandHessian m ell

private theorem phi_pair_one : GaussCoframeForm.Paired (1:End) 1 := by intro p q;rfl
private theorem phi_pair_add {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A+B) (A+B) := by
  intro p q
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_left,inner_add_right]
  exact congrArg₂ (·+·) (hA p q) (hB p q)
private theorem phi_pair_sub {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A-B) (A-B) := by
  intro p q
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right]
  exact congrArg₂ (·-·) (hA p q) (hB p q)
private theorem phi_pair_real {A : End} (c : ℝ) (hA : GaussCoframeForm.Paired A A) :
    GaussCoframeForm.Paired ((c:ℂ) • A) ((c:ℂ) • A) := by
  intro p q
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  exact congrArg ((c:ℂ)*·) (hA p q)
private theorem phi_pair_mul {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) (hAB : Commute A B) :
    GaussCoframeForm.Paired (A*B) (A*B) := by
  intro p q
  change sourcePair p (A (B q))=sourcePair (A (B p)) q
  have hc := LinearMap.congr_fun hAB.eq p
  change A (B p)=B (A p) at hc
  rw [hA,hB,←hc]
private theorem phi_pair_pow {A : End} (hA : GaussCoframeForm.Paired A A) (n : ℕ) :
    GaussCoframeForm.Paired (A^n) (A^n) := by
  induction n with
  | zero => simpa only [pow_zero] using phi_pair_one
  | succ n ih =>
    rw [pow_succ]
    exact phi_pair_mul ih hA ((Commute.refl A).pow_left n)

private theorem phi_S_pair : GaussCoframeForm.Paired S S := multiply_pair _ _
private theorem phi_r_pair : GaussCoframeForm.Paired r r := multiply_pair _ _
private theorem phi_Q_pair : GaussCoframeForm.Paired Q Q := phi_pair_sub phi_pair_one phi_S_pair
private theorem phi_theta_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (phiThetaAction m ell) (phiThetaAction m ell) :=
  phi_pair_sub (phi_pair_pow phi_Q_pair (m+1)) (phi_pair_pow phi_Q_pair (ell+1))
private theorem phi_first_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (profileFirst m ell) (profileFirst m ell) := by
  unfold profileFirst SourceClockPhiRadiusResponseHessian.phiFirstPeak
  change GaussCoframeForm.Paired
    (((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m) : End)
    (((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m) : End)
  have h := phi_pair_sub (phi_pair_real (ell+1:ℝ) (phi_pair_pow phi_Q_pair ell))
    (phi_pair_real (m+1:ℝ) (phi_pair_pow phi_Q_pair m))
  simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one] using h
private theorem phi_second_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (profileSecond m ell) (profileSecond m ell) := by
  unfold profileSecond SourceClockPhiRadiusResponseHessian.phiSecondPeak
  change GaussCoframeForm.Paired
    (((m*(m+1):ℂ) • Q^(m-1)-(ell*(ell+1):ℂ) • Q^(ell-1)) : End)
    (((m*(m+1):ℂ) • Q^(m-1)-(ell*(ell+1):ℂ) • Q^(ell-1)) : End)
  have h := phi_pair_sub (phi_pair_real ((m:ℝ)*(m+1)) (phi_pair_pow phi_Q_pair (m-1)))
    (phi_pair_real ((ell:ℝ)*(ell+1)) (phi_pair_pow phi_Q_pair (ell-1)))
  simpa only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one] using h

private theorem phi_first_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (profileFirst m ell) A :=
  ((((Commute.one_left A).sub_left h).pow_left ell).smul_left _).sub_left
    ((((Commute.one_left A).sub_left h).pow_left m).smul_left _)
private theorem phi_second_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (profileSecond m ell) A :=
  ((((Commute.one_left A).sub_left h).pow_left (m-1)).smul_left _).sub_left
    ((((Commute.one_left A).sub_left h).pow_left (ell-1)).smul_left _)
private theorem phi_theta_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (phiThetaAction m ell) A :=
  (((Commute.one_left A).sub_left h).pow_left (m+1)).sub_left
    (((Commute.one_left A).sub_left h).pow_left (ell+1))
private theorem phi_HT_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (Htheta m ell) A := by
  exact (((phi_second_commute h m ell).mul_left ((h.pow_left 4).sub_left (h.pow_left 6))).sub_left
    ((phi_first_commute h m ell).mul_left
      (((h.pow_left 3).smul_left (58:ℂ)).add_left ((h.pow_left 5).smul_left (3:ℂ))))).smul_left (1/4:ℂ)
private theorem phi_HB_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (Hband m ell) A := by
  exact ((((phi_second_commute h m ell).mul_left ((h.pow_left 3).sub_left (h.pow_left 5))).sub_left
    ((phi_first_commute h m ell).mul_left
      (((h.pow_left 2).smul_left (60:ℂ)).add_left (h.pow_left 4)))).add_left
    ((phi_theta_commute h m ell).mul_left ((h.smul_left (60:ℂ)).add_left (h.pow_left 3)))).smul_left (1/4:ℂ)

private theorem phi_HT_pair (m ell : ℕ) : GaussCoframeForm.Paired (Htheta m ell) (Htheta m ell) := by
  unfold Htheta SourceClockPhiRadiusResponseHessian.thetaHessian
  change GaussCoframeForm.Paired
    ((1/4:ℂ) • (profileSecond m ell*(S^4-S^6)-
      profileFirst m ell*((58:ℂ) • S^3+(3:ℂ) • S^5)) : End)
    ((1/4:ℂ) • (profileSecond m ell*(S^4-S^6)-
      profileFirst m ell*((58:ℂ) • S^3+(3:ℂ) • S^5)) : End)
  have h1 := phi_pair_mul (phi_second_pair m ell)
    (phi_pair_sub (phi_pair_pow phi_S_pair 4) (phi_pair_pow phi_S_pair 6))
    (((phi_profile_second_S m ell).pow_right 4).sub_right ((phi_profile_second_S m ell).pow_right 6))
  have h2 := phi_pair_mul (phi_first_pair m ell)
    (phi_pair_add (phi_pair_real (58:ℝ) (phi_pair_pow phi_S_pair 3))
      (phi_pair_real (3:ℝ) (phi_pair_pow phi_S_pair 5)))
    ((((phi_profile_first_S m ell).pow_right 3).smul_right (58:ℂ)).add_right
      (((phi_profile_first_S m ell).pow_right 5).smul_right (3:ℂ)))
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
    phi_pair_real (1/4:ℝ) (phi_pair_sub h1 h2)
private theorem phi_HB_pair (m ell : ℕ) : GaussCoframeForm.Paired (Hband m ell) (Hband m ell) := by
  unfold Hband SourceClockPhiRadiusResponseHessian.bandHessian
  change GaussCoframeForm.Paired
    ((1/4:ℂ) • (profileSecond m ell*(S^3-S^5)-
      profileFirst m ell*((60:ℂ) • S^2+S^4)+
      phiThetaAction m ell*((60:ℂ) • S+S^3)) : End)
    ((1/4:ℂ) • (profileSecond m ell*(S^3-S^5)-
      profileFirst m ell*((60:ℂ) • S^2+S^4)+
      phiThetaAction m ell*((60:ℂ) • S+S^3)) : End)
  have h1 := phi_pair_mul (phi_second_pair m ell)
    (phi_pair_sub (phi_pair_pow phi_S_pair 3) (phi_pair_pow phi_S_pair 5))
    (((phi_profile_second_S m ell).pow_right 3).sub_right ((phi_profile_second_S m ell).pow_right 5))
  have h2 := phi_pair_mul (phi_first_pair m ell)
    (phi_pair_add (phi_pair_real (60:ℝ) (phi_pair_pow phi_S_pair 2)) (phi_pair_pow phi_S_pair 4))
    ((((phi_profile_first_S m ell).pow_right 2).smul_right (60:ℂ)).add_right
      ((phi_profile_first_S m ell).pow_right 4))
  have h3 := phi_pair_mul (phi_theta_pair m ell)
    (phi_pair_add (phi_pair_real (60:ℝ) phi_S_pair) (phi_pair_pow phi_S_pair 3))
    (((phi_profile_theta_S m ell).smul_right (60:ℂ)).add_right ((phi_profile_theta_S m ell).pow_right 3))
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
    phi_pair_real (1/4:ℝ) (phi_pair_add (phi_pair_sub h1 h2) h3)

private theorem phi_paired_self_im {A : End} (hA : GaussCoframeForm.Paired A A) (p : QuantumTest) :
    (sourcePair p (A p)).im=0 := by
  have h := congrArg Complex.im (pair_conjugate p (A p))
  rw [←hA p p] at h
  simp only [Complex.conj_im] at h
  linarith only [h]
private theorem phi_paired_diagonal_im {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) (hAB : Commute A B) (p : QuantumTest) :
    (sourcePair (A p) (B p)).im=0 := by
  rw [←hA p (B p)]
  exact phi_paired_self_im (phi_pair_mul hA hB hAB) p
private theorem phi_paired_cross_conjugate {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) (hAB : Commute A B) (p q : QuantumTest) :
    sourcePair (A q) (B p)=(starRingEnd ℂ) (sourcePair (A p) (B q)) := by
  have hc := LinearMap.congr_fun hAB.eq p
  change A (B p)=B (A p) at hc
  rw [pair_conjugate,←hB q (A p),←hc,hA q (B p)]

/-- The actual paired radial Hessians kill both diagonal terms under the true K. -/
private theorem phi_zero_clock_pair (m ell : ℕ) (q h : QuantumTest) :
    (sourcePair (phiThetaAction m ell (r q-h))
      (clockMean (Hband m ell q-Htheta m ell h))).im=
      (sourcePair (phiThetaAction m ell q) (clockMean (phiSturmCross m ell h))).im := by
  let T : End := phiThetaAction m ell
  let B : End := Hband m ell
  let C : End := Htheta m ell
  have hT := phi_theta_pair m ell
  have hB := phi_HB_pair m ell
  have hC := phi_HT_pair m ell
  have htr : Commute T r := phi_theta_commute phi_inverse_radius_commute m ell
  have htk : Commute T clockMean := (clock_mean_theta m ell).symm
  have htb : Commute T B := (phi_HB_commute (phi_profile_theta_S m ell).symm m ell).symm
  have htc : Commute T C := (phi_HT_commute (phi_profile_theta_S m ell).symm m ell).symm
  have hrb : Commute r B := (phi_HB_commute phi_inverse_radius_commute m ell).symm
  have hkb : Commute clockMean B := (phi_HB_commute clock_mean_inverse.symm m ell).symm
  have hkc : Commute clockMean C := (phi_HT_commute clock_mean_inverse.symm m ell).symm
  have hdiagq := phi_paired_diagonal_im (phi_pair_mul hT phi_r_pair htr)
    (phi_pair_mul clock_mean_pair hB hkb)
    ((htk.mul_right htb).mul_left (clock_mean_radius.symm.mul_right hrb)) q
  have hdiagh := phi_paired_diagonal_im hT (phi_pair_mul clock_mean_pair hC hkc)
    (htk.mul_right htc) h
  have hcross := congrArg Complex.im
    (phi_paired_cross_conjugate hT (phi_pair_mul clock_mean_pair hB hkb) (htk.mul_right htb) q h)
  have hmove : sourcePair (T (r q)) (clockMean (C h))=
      sourcePair (T q) (clockMean ((r*C) h)) := by
    have htrq := LinearMap.congr_fun htr.eq q
    change T (r q)=r (T q) at htrq
    have hkr := LinearMap.congr_fun clock_mean_radius.eq (C h)
    change clockMean (r (C h))=r (clockMean (C h)) at hkr
    rw [htrq,←phi_r_pair (T q) (clockMean (C h)),←hkr]
    rfl
  have hcoef : B-r*C=phiSturmCross m ell := original_phi_hessian_cross m ell
  change (sourcePair (T (r q-h)) (clockMean (B q-C h))).im=_
  rw [←hcoef]
  simp only [map_sub,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,
    inner_sub_left,inner_sub_right,Complex.sub_im] at hdiagq hdiagh hcross hmove ⊢
  simp only [Complex.conj_im] at hcross
  have hm := congrArg Complex.im hmove
  linarith only [hdiagq,hdiagh,hcross,hm]

private theorem phi_moment_clock_self_im (s : QuantumTest) :
    (sourcePair s (clockMean ((r^2-(1:End)) s))).im=0 := by
  have hp := phi_pair_sub (phi_pair_pow phi_r_pair 2) phi_pair_one
  have hc : Commute clockMean (r^2-(1:End)) :=
    (clock_mean_radius.pow_right 2).sub_right (Commute.one_right clockMean)
  exact phi_paired_self_im (phi_pair_mul clock_mean_pair hp hc) s

private def phiScalarResponseForce (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  phiNativeDivergence m ell F z hz g+
    (-(sourceTime 0:ℂ)/2) • U (SourceClockPhiRadiusResponseHessian.zeroVector m ell F z hz g)

def phiScalarSturmWord (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  let q : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
  let h : QuantumTest := resolventCore F z hz (r (coreEquiv.symm g))
  let s : QuantumTest := S (phiRadialInput m ell F z hz g)
  let v : QuantumTest := phiResponseCore m ell F z hz g
  let e : QuantumTest := phiFixedEuler m ell F z hz g
  let zero : QuantumTest := SourceClockPhiRadiusResponseHessian.zeroVector m ell F z hz g
  (sourceTime 0/2)*(sourcePair s (clockMean e)).im-
    (sourceTime 0)^2/4*(sourcePair s ((U*U) e)).re+
    (sourceTime 0)^2/4*(sourcePair s ((U*U) ((r^2-(1:End)) s))).re+
    sourceTime 0*(sourcePair (phiThetaAction m ell q) (clockMean (phiSturmCross m ell h))).im+
    (sourceTime 0)^2/2*(sourcePair zero ((U*U) v)).re

/-- Actual native G, both actual Hessians and true K reduce before any estimate. -/
theorem actual_phi_scalar_sturm_pair (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    2*(sourcePair (phiScalarResponseForce m ell F z hz g)
      (J (phiResponseCore m ell F z hz g))).im+
      (sourceTime 0/2)*(sourcePair (U (phiResponseCore m ell F z hz g))
        (phiScalarResponseForce m ell F z hz g)).re=phiScalarSturmWord m ell F z hz g := by
  let q : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
  let h : QuantumTest := resolventCore F z hz (r (coreEquiv.symm g))
  let s : QuantumTest := S (phiRadialInput m ell F z hz g)
  let v : QuantumTest := phiResponseCore m ell F z hz g
  let e : QuantumTest := phiFixedEuler m ell F z hz g
  let zero : QuantumTest := SourceClockPhiRadiusResponseHessian.zeroVector m ell F z hz g
  have he : E v=e-(r^2-(1:End)) s := phi_euler_response m ell F z hz g
  have hs := scalar_clock_sturm_pair s v
  rw [he] at hs
  have hself := phi_moment_clock_self_im s
  have hzpair := whole_scalar_clock_pair ((-(sourceTime 0:ℂ)/2) • zero) v
  have hzero := phi_zero_clock_pair m ell q h
  have hv : v=phiThetaAction m ell (r q-h) := rfl
  have hZ : zero=Hband m ell q-Htheta m ell h := rfl
  have hconj := congrArg Complex.im (pair_conjugate v (clockMean zero))
  rw [←clock_mean_pair zero v] at hconj
  simp only [Complex.conj_im] at hconj
  rw [←hv,←hZ] at hzero
  have hforce : phiScalarResponseForce m ell F z hz g=
      U ((-(sourceTime 0:ℂ)/4) • ((E+(61:ℂ) • (1:End)) s))+
        U ((-(sourceTime 0:ℂ)/2) • zero) := by
    unfold phiScalarResponseForce
    rw [actual_phi_native_euler_source]
    simp only [map_smul]
    rfl
  have hword : phiScalarSturmWord m ell F z hz g=
      (sourceTime 0/2)*(sourcePair s (clockMean e)).im-
        (sourceTime 0)^2/4*(sourcePair s ((U*U) e)).re+
        (sourceTime 0)^2/4*(sourcePair s ((U*U) ((r^2-(1:End)) s))).re+
        sourceTime 0*(sourcePair (phiThetaAction m ell q) (clockMean (phiSturmCross m ell h))).im+
        (sourceTime 0)^2/2*(sourcePair zero ((U*U) v)).re := rfl
  have hvdef : phiResponseCore m ell F z hz g=v := rfl
  simp only [hforce,hword,hvdef]
  simp only [map_add,map_sub,map_smul,sourcePair,inner_add_left,inner_add_right,
    inner_sub_right,inner_smul_left,inner_smul_right,
    Complex.add_im,Complex.add_re,Complex.sub_im,Complex.sub_re,
    Complex.mul_im,Complex.mul_re,map_neg,map_div₀,map_ofNat,
    Complex.conj_ofReal] at hs hzpair hself hzero hconj ⊢
  norm_num at hs hzpair hself ⊢
  simp only [inner_sub_right,Complex.sub_im,Complex.sub_re] at hs
  rw [hself] at hs
  linear_combination (norm := ring) hs+hzpair+
    (sourceTime 0)*hzero+(sourceTime 0)*hconj

/-- The true full source inserts this scalar word beside its entire coherent defect. -/
theorem actual_phi_full_sturm_source (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    phiResponseSource m ell F z hz g=
      phiScalarResponseForce m ell F z hz g+
        SourceClockPhiRadiusResponseHessian.phiCoherentDefect m ell F z hz g := by
  rw [SourceClockPhiRadiusResponseHessian.actual_phi_response_forcing]
  rfl

end LowEnergy.SourceClockPhiRadiusClockSturm
