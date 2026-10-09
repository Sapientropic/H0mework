import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMagneticElectricPayment
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarAffineMixedJets
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentElectricSuccessor
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarPositiveBulkWard
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceDilationKinetic
open SourceGaugeRadius SourceGaugeRadiusMetric SourceGaugeRadialCurrent SourcePhysicalKineticSquare
open SourceGaugeRadialPair SourceCornerWeight SourceDilationAlgebra GaussCoframeForm
open SourceClockPhiMatchedElectricSource SourceClockPhiNativeMatchedSource SourceClockPhiCombinedScalePressure
open FirstCurrentGeometricPayer
open scoped ContDiff InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev V : End := volumeAction
private abbrev Dc : End := dilation
private abbrev D : End := combinedGenerator
private abbrev Ggen : End := SourceGaugeScaleTransport.generator
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev VP : End := multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
private abbrev Hc : End := GaussCoframeForm.coframeAction-VP
private abbrev CE : End := fullElectricCurrent
private abbrev E : End := electricAction
private abbrev M : End := matchedTester
private abbrev W : End := magneticVolumeWeight
private abbrev X : End := weightedElectricCurrent
private abbrev Z : End := D+(3*Complex.I:ℂ) • Dc
attribute [local irreducible] sourcePair embed diagonalAction dilation combinedGenerator matchedTester
private theorem electric_smooth_local(z:physicalChart):ContDiffAt ℝ ∞ electricWeight z.val:=
  (reciprocal_volume_smooth z).mul (SourceGaugeRadialCurrent.electric_square_smooth z)
private theorem electric_formula(z:SourceCoordinateSlice):electricWeight z=
    n/(sourceSigma*(volume z)^2)*gaugeSquare z:=by
  unfold electricWeight SourceGaugeRadiusMetric.electricSquare reciprocalVolume
  ring
private theorem real_multiply(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest):
    (multiply c hc f:SourceCoordinateSlice→FockFiber)=(fun z=>c z • f z):=by
  funext z;apply PiLp.ext;intro word
  exact Complex.real_smul.symm
private theorem real_commute(c d:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)
private theorem connection_coframe_scale(r:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):
    connectionField (SourceCoframeVolume.scale r z) i=connectionField z i:=by
  unfold connectionField SourceCoframeVolume.scale
  rfl
private theorem electric_coframe_scale(r:ℝ)(hr:r≠0)(z:physicalChart):
    electricWeight (SourceCoframeVolume.scale r z.val)=r^(-4:ℤ)*electricWeight z.val := by
  have hrow(i:Fin 3):gaugeRow (SourceCoframeVolume.scale r z.val) i=r • gaugeRow z.val i:=by
    simp only [gaugeRow,connection_coframe_scale]
    fin_cases i <;> simp [SourceCoframeVolume.scale,smul_smul,smul_add]
  have hT:gaugeSquare (SourceCoframeVolume.scale r z.val)=r^2*gaugeSquare z.val:=by
    simp only [gaugeSquare,hrow,real_inner_smul_left,real_inner_smul_right,pow_two,
      Finset.mul_sum,mul_assoc]
  rw [electric_formula,volume_scale,hT,electric_formula]
  simp only [zpow_neg]
  field_simp [hr,(volume_pos z).ne',source_sigma_nonzero]
private theorem electric_dilation:bracket Dc electricAction=(8*Complex.I/3) • electricAction := by
  have hd(z:physicalChart):fderiv ℝ electricWeight z.val (euler z.val)=(-4:ℝ)*electricWeight z.val:=by
    simpa only [Int.cast_neg,Int.cast_ofNat] using SourceKineticScale.euler_of_scale electricWeight (-4) z (electric_smooth_local z) (fun r hr=>electric_coframe_scale r hr z)
  have h:=SourceDilationMultiplier.homogeneous_multiplier electricWeight electric_smooth_local (-4) hd
  change bracket Dc electricAction=((-2*Complex.I/3)*((-4:ℝ):ℂ)) • electricAction at h
  convert h using 1
  congr 1
  norm_num
  ring
private theorem electric_gauge_derivative(z:physicalChart):
    fderiv ℝ electricWeight z.val (gaugeEuler z.val)=2*electricWeight z.val := by
  have hc:=((electric_smooth_local z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (gauge_scale_derivative z.val 1) (gauge_scale_one z.val).symm
  have hs(r:ℝ):electricWeight (gaugeScale r z.val)=r^2*electricWeight z.val:=by
    unfold electricWeight
    rw [electric_square_scale]
    change reciprocalVolume z.val*(r^2*electricSquare z.val)=_
    ring
  have ht:HasDerivAt (fun r:ℝ=>electricWeight (gaugeScale r z.val)) (2*electricWeight z.val) 1:=by
    simpa only [hs,id_eq,Pi.pow_apply,one_pow,mul_one,Nat.cast_ofNat,Nat.reduceSub] using!
      ((hasDerivAt_id (1:ℝ)).pow 2).mul_const (electricWeight z.val)
  exact hc.unique ht
private theorem electric_gauge:bracket Ggen electricAction=(2:ℂ) • electricAction := by
  have h:bracket gaugeEulerAction electricAction=(2:ℂ) • electricAction:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    by_cases hz:z∈physicalChart
    · change gaugeEulerAction (electricAction f) z-(electricWeight z:ℂ) • gaugeEulerAction f z=(2:ℂ) • ((electricWeight z:ℂ) • f z)
      rw [gauge_euler_apply]
      change fderiv ℝ (multiply electricWeight electric_smooth_local f) z (gaugeEuler z)-_=_
      rw [real_multiply,
        fderiv_fun_smul ((electric_smooth_local ⟨z,hz⟩).differentiableAt (by simp))
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change electricWeight z • fderiv ℝ f z (gaugeEuler z)+
        fderiv ℝ electricWeight z (gaugeEuler z) • f z-(electricWeight z:ℂ) • gaugeEulerAction f z=_
      rw [electric_gauge_derivative ⟨z,hz⟩,gauge_euler_apply]
      apply PiLp.ext;intro word
      simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
      push_cast
      ring
    · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
      exact (h0 _).trans (h0 _).symm
  unfold Ggen SourceGaugeScaleTransport.generator bracket at *
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  linear_combination (norm:=module) h
private theorem electric_scalar_weight (t : ℝ) (z : SourceCoordinateSlice) :
    electricWeight (SourceScalarAffineScaleTransport.scaleEquiv t z) = electricWeight z := rfl
private theorem electric_scalar_flow (t : ℝ) (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    SourceScalarAffineScaleTransport.coreFlow t (E f) z word =
      (electricWeight z : ℂ) * SourceScalarAffineScaleTransport.coreFlow t f z word := by
  rw [SourceScalarAffineScaleTransport.coreFlow_apply, SourceScalarAffineScaleTransport.coreFlow_apply]
  change _ * ((electricWeight (SourceScalarAffineScaleTransport.scaleEquiv t z) : ℂ) *
    f (SourceScalarAffineScaleTransport.scaleEquiv t z) word) = _
  rw [electric_scalar_weight]
  ring
private theorem electric_phi_generator : Commute E SourceScalarAffineScaleTransport.generator := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have h1 := SourceScalarAffineScaleTransport.component_flow_derivative (E f) z word 0
  have h2 := (SourceScalarAffineScaleTransport.component_flow_derivative f z word 0).const_mul
    (electricWeight z : ℂ)
  have he : (fun t : ℝ => SourceScalarAffineScaleTransport.coreFlow t (E f) z word) =
      (fun t : ℝ => (electricWeight z : ℂ) * SourceScalarAffineScaleTransport.coreFlow t f z word) :=
    funext (fun t => electric_scalar_flow t f z word)
  rw [he] at h1
  have h := h1.unique h2
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero] at h
  exact h.symm

private theorem bracket_add(A B C:End):bracket (A+B) C=bracket A C+bracket B C:=by
  unfold bracket;noncomm_ring
private theorem bracket_smul(a:ℂ)(A B:End):bracket (a • A) B=a • bracket A B:=by
  unfold bracket
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_jacobi(A B C:End):
    bracket A (bracket B C)=bracket (bracket A B) C+bracket B (bracket A C):=by
  unfold bracket;noncomm_ring
private theorem bracket_product(A B C:End):bracket A (B*C)=bracket A B*C+B*bracket A C:=by
  unfold bracket;noncomm_ring
private theorem bracket_smul_r(a:ℂ)(A B:End):bracket A (a • B)=a • bracket A B:=by
  unfold bracket
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem combined_delta(T:End):bracket D T=deltaPhi T-deltaGauge T:=by
  unfold D combinedGenerator bracket
  have hp:=SourceScalarAffineScaleTransport.generator_commutator T
  have hg:=SourceGaugeScaleTransport.generator_commutator T
  linear_combination (norm:=noncomm_ring) hp-hg
private theorem coframe_dilation:bracket Dc Hc=(2*Complex.I:ℂ) • Hc:=by
  have hH:Hc=GaussCoframeKinetic.kinetic+currentAction+(∑a:Fin 7,spinSquare a)+numberShift:=by
    unfold Hc GaussCoframeForm.coframeAction VP
    abel
  rw [hH]
  exact homogeneous_add _ _ _ _ (homogeneous_add _ _ _ _
    (homogeneous_add _ _ _ _ coframe_kinetic_current coframe_current_current)
    (homogeneous_sum _ _ _ spin_square_current)) number_shift_current
private theorem Z_coframe:bracket Z Hc=(-6:ℂ) • Hc:=by
  have hc:bracket D GaussCoframeForm.coframeAction=0:=by
    rw [combined_delta,original_coframe_phi,original_coframe_gauge,sub_self]
  have hV:bracket D VP=0:=by
    rw [combined_delta]
    have h:=original_coframe_local_phi_gauge VP
      (fun q=>(GaussCoframeForm.volumePotential (q,(0:Slice)):ℂ) • ContinuousLinearMap.id ℂ FockFiber)
      (fun _ _=>rfl)
    rw [h.1,h.2,sub_self]
  have hb:bracket D Hc=0:=by
    unfold Hc bracket at *
    linear_combination (norm:=noncomm_ring) hc-hV
  rw [Z,bracket_add,hb,bracket_smul,coframe_dilation,zero_add,smul_smul]
  congr 1
  calc (3*Complex.I)*(2*Complex.I)=6*(Complex.I*Complex.I):=by ring
       _= -6:=by rw [Complex.I_mul_I];ring
private theorem Z_electric:bracket Z E=(-10:ℂ) • E:=by
  have hp:bracket Phi E=0:=sub_eq_zero.mpr electric_phi_generator.eq.symm
  have hd:bracket D E=(-2:ℂ) • E:=by
    unfold D combinedGenerator bracket at *
    have hg:=electric_gauge
    unfold bracket at hg
    linear_combination (norm:=(noncomm_ring;module)) hp-hg
  rw [Z,bracket_add,hd,bracket_smul,electric_dilation,smul_smul,←add_smul]
  congr 1
  calc (-2:ℂ)+(3*Complex.I)*(8*Complex.I/3)= -2+8*(Complex.I*Complex.I):=by ring
       _= -10:=by rw [Complex.I_mul_I];ring
private theorem Z_gauge:bracket Z Ggen=0:=by
  have hp:=SourceScalarAffineMixedJets.generators_affine_gauge.eq
  have hg:=SourceGaugeScaleTransport.generator_commutator Dc
  have hd:=original_dilation_gauge
  rw [hd] at hg
  change Ggen*Dc-Dc*Ggen=0 at hg
  unfold Z D combinedGenerator bracket
  linear_combination (norm:=(noncomm_ring;module)) hp-(3*Complex.I) • hg
private theorem combined_volume:Commute D V:=by
  apply sub_eq_zero.mp
  rw [←show bracket D V=D*V-V*D from rfl,combined_delta,original_volume_phi,original_volume_gauge,sub_self]
private theorem UV:U*V=(1:End):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)=f z
    rw [smul_smul,←Complex.ofReal_mul]
    simp [reciprocalVolume,(volume_pos ⟨z,hz⟩).ne']
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem VU:V*U=(1:End):=(real_commute _ _ _ _).eq.trans UV
private theorem Z_volume:bracket Z V=(6:ℂ) • V:=by
  have hd:=volume_scale_current
  change bracket Dc V=(-2*Complex.I) • V at hd
  have hc:bracket D V=0:=sub_eq_zero.mpr combined_volume.eq
  rw [Z,bracket_add,hc,zero_add,bracket_smul,hd,smul_smul]
  congr 1
  calc (3*Complex.I)*(-2*Complex.I)= -6*(Complex.I*Complex.I):=by ring
       _=6:=by rw [Complex.I_mul_I];ring
private theorem Z_inverse:bracket Z U=(-6:ℂ) • U:=by
  have hv:=Z_volume
  unfold bracket at hv ⊢
  have h:U*(Z*V-V*Z)*U=(6:ℂ) • U:=by
    rw [hv]
    simp only[mul_smul_comm,smul_mul_assoc,mul_assoc,VU,mul_one]
  have hL:U*(Z*V-V*Z)*U=U*Z-Z*U:=by
    noncomm_ring
    simp only[VU,mul_one,←mul_assoc,UV,one_mul]
  rw [hL] at h
  linear_combination (norm:=(noncomm_ring;module)) -h
private theorem matched_return:M=U*(Z-(4:ℂ) • (1:End)):=by
  have hd:=congrArg (fun A:End=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at hd
  simp only[smul_smul] at hd
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=(1:ℂ):=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  have hj:(-2*Complex.I/3)*(-3:ℂ)=2*Complex.I:=by ring
  rw [hi,hj,one_smul] at hd
  have h:=congrArg (fun A:End=>(3*Complex.I) • A) hd
  simp only[smul_smul] at h
  have hi2:(3*Complex.I)*(2*Complex.I)=(-6:ℂ):=by
    calc _=6*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi2] at h
  unfold M matchedTester matchedColumn Z
  linear_combination (norm:=(noncomm_ring;module)) h
private theorem electric_return(F:Index)(g:diagonal.domain):CE=coframeElectricCurrent-U*Ggen:=
  (actual_matched_electric_source 0 0 F Complex.I (by simp) g).1
private theorem Z_current(F:Index)(g:diagonal.domain):
    bracket Z CE=(-16:ℂ) • CE-(10:ℂ) • (U*Ggen):=by
  have hc:bracket Z coframeElectricCurrent=(-16:ℂ) • coframeElectricCurrent:=by
    have hE:bracket VP E=0:=sub_eq_zero.mpr (real_commute _ _ _ _).eq
    have he:coframeElectricCurrent=(1/2:ℂ) • bracket Hc E:=by
      unfold coframeElectricCurrent Hc bracket at *
      linear_combination (norm:=(noncomm_ring;module)) (1/2:ℂ) • hE
    rw [he]
    rw [bracket_smul_r,bracket_jacobi,Z_coframe,Z_electric,bracket_smul,bracket_smul_r]
    module
  have hu:bracket Z (U*Ggen)=(-6:ℂ) • (U*Ggen):=by
    rw [bracket_product,Z_inverse,Z_gauge]
    simp only[smul_mul_assoc,mul_zero,add_zero]
  rw [electric_return F g]
  unfold bracket at hc hu ⊢
  linear_combination (norm:=(noncomm_ring;module)) hc-hu
private theorem current_inverse:bracket CE U=(-(n:ℂ)) • (U*U*E):=by
  have hv:=original_electric_positive_current.1
  change CE*V-V*CE=(n:ℂ) • E at hv
  have he:Commute U E:=real_commute _ _ _ _
  have h:U*(CE*V-V*CE)*U=(n:ℂ) • (U*E*U):=by
    rw [hv]
    simp only[mul_smul_comm,smul_mul_assoc]
  have hL:U*(CE*V-V*CE)*U=U*CE-CE*U:=by
    noncomm_ring
    simp only[VU,mul_one,←mul_assoc,UV,one_mul]
  rw [hL] at h
  unfold bracket
  linear_combination (norm:=(noncomm_ring;module)) -h+(n:ℂ) • (U*he.eq)
/-- The entire actual matched tester transports along the original electric current. -/
theorem actual_matched_electric_current(F:Index)(g:diagonal.domain):
    bracket M CE=(n:ℂ) • (U*E*M)-(16:ℂ) • (U*CE)-(10:ℂ) • (U*U*Ggen):=by
  have hz:=Z_current F g
  have hu:=current_inverse
  have hm:=matched_return
  have he:Commute U E:=real_commute _ _ _ _
  rw [hm]
  unfold bracket at hz hu ⊢
  linear_combination (norm:=(noncomm_ring;module)) U*hz-hu*(Z-(4:ℂ) • (1:End))+(n:ℂ) • (U*he.eq*(Z-(4:ℂ) • (1:End)))

private theorem matched_volume:bracket M V=(6:ℂ) • (1:End):=by
  have hz:=Z_volume
  have hc:Commute U V:=real_commute _ _ _ _
  have h:bracket M V=(6:ℂ) • (U*V):=by
    rw [matched_return]
    unfold bracket at hz ⊢
    linear_combination (norm:=noncomm_ring) U*hz+hc.eq*(Z-(4:ℂ) • (1:End))
  simpa only[UV] using h
private theorem matched_electric:bracket M E=(-10:ℂ) • (U*E):=by
  have hz:=Z_electric
  have hc:Commute U E:=real_commute _ _ _ _
  rw [matched_return]
  unfold bracket at hz ⊢
  linear_combination (norm:=noncomm_ring) U*hz+hc.eq*(Z-(4:ℂ) • (1:End))
private theorem weight_power:W=V^3:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change ((volume z^3:ℝ):ℂ) • f z=(volume z:ℂ) • ((volume z:ℂ) • ((volume z:ℂ) • f z))
  simp only[smul_smul]
  congr 1
  push_cast
  ring
private theorem current_volume_square:bracket CE (V*V)=(2*(n:ℂ)) • (V*E):=by
  have h:=original_electric_positive_current.1
  have he:Commute E V:=real_commute _ _ _ _
  change bracket CE V=(n:ℂ) • E at h
  rw [bracket_product,h]
  simp only[smul_mul_assoc,mul_smul_comm,he.eq]
  module
private theorem current_volume_cube:bracket CE (V^3)=(3*(n:ℂ)) • (V^2*E):=by
  have h:=original_electric_positive_current.1
  have he:Commute E V:=real_commute _ _ _ _
  change bracket CE V=(n:ℂ) • E at h
  rw [show V^3=(V*V)*V by noncomm_ring,bracket_product,current_volume_square,h]
  simp only[smul_mul_assoc,mul_smul_comm,mul_assoc,he.eq]
  noncomm_ring
  module
private theorem current_weight_return:X=V^3*CE+(3*(n:ℂ)/2) • (V^2*E):=by
  have h:=current_volume_cube
  change (1/2:ℂ) • (W*CE+CE*W)=_
  rw [weight_power]
  unfold bracket at h
  linear_combination (norm:=(noncomm_ring;module)) (1/2:ℂ) • h
private theorem matched_volume_square:bracket M (V*V)=(12:ℂ) • V:=by
  rw [bracket_product,matched_volume]
  simp only[smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  module
private theorem matched_volume_cube:bracket M (V^3)=(18:ℂ) • (V^2):=by
  rw [show V^3=(V*V)*V by noncomm_ring,bracket_product,matched_volume_square,matched_volume]
  simp only[smul_mul_assoc,mul_smul_comm,mul_one,pow_two]
  module
private theorem cube_inverse:V^3*U=V^2:=by
  calc V^3*U=(V*V)*(V*U):=by noncomm_ring
       _=V^2:=by rw [VU,mul_one];rfl
private theorem inverse_cube:U*V^3=V^2:=by
  calc U*V^3=(U*V)*(V*V):=by noncomm_ring
       _=V^2:=by rw [UV,one_mul];rfl
private theorem square_inverse:V^2*U=V:=by
  calc V^2*U=V*(V*U):=by noncomm_ring
       _=V:=by rw [VU,mul_one]
private theorem inverse_square:U*V^2=V:=by
  calc U*V^2=(U*V)*V:=by noncomm_ring
       _=V:=by rw [UV,one_mul]
private theorem matched_weighted_electric:bracket M (V^2*E)=(2:ℂ) • (V*E):=by
  rw [bracket_product,show V^2=V*V from pow_two V,matched_volume_square,matched_electric]
  simp only[smul_mul_assoc,mul_smul_comm,←mul_assoc]
  rw [←pow_two,square_inverse]
  module
/-- The same weighted CE update closes the full matched current on X, M and the original gauge generator. -/
theorem actual_matched_weighted_electric_current(F:Index)(g:diagonal.domain):
    bracket M X=(2:ℂ) • (U*X)+(n:ℂ) • (V^2*E*M)-(10:ℂ) • (V*Ggen):=by
  have hx:bracket M X=(2:ℂ) • (V^2*CE)+(n:ℂ) • (V^2*E*M)-
      (10:ℂ) • (V*Ggen)+(3*(n:ℂ)) • (V*E):=by
    rw [current_weight_return]
    have ha(A B C:End):bracket A (B+C)=bracket A B+bracket A C:=by unfold bracket;noncomm_ring
    rw [ha,bracket_product,matched_volume_cube,actual_matched_electric_current F g,
      bracket_smul_r,matched_weighted_electric]
    simp only[mul_sub,mul_smul_comm,smul_mul_assoc,smul_smul,←mul_assoc,
      cube_inverse,square_inverse]
    module
  rw [hx,current_weight_return]
  simp only[mul_add,mul_smul_comm,smul_add,smul_smul,←mul_assoc,inverse_cube,inverse_square]
  module

attribute [local irreducible] weightedElectricCurrent magneticVolumeWeight electricAction fullElectricCurrent
  SourceGaugeScaleTransport.generator volumeAction inverseVolumeAction
/-- This successor is generated by the original source Lie action, including its gauge remainder. -/
def matchedElectricSuccessor(w:QuantumTest):QuantumTest:=
  X (M w)+(2:ℂ) • U (X w)+(n:ℂ) • (V^2*E) (M w)-(10:ℂ) • V (Ggen w)
private theorem successor_return(F:Index)(g:diagonal.domain)(w:QuantumTest):M (X w)=matchedElectricSuccessor w:=by
  have h:=LinearMap.congr_fun (actual_matched_weighted_electric_current F g) w
  simp only[bracket,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply] at h
  unfold matchedElectricSuccessor
  simp only[Module.End.mul_apply]
  linear_combination (norm:=module) h
/-- The unchanged matched debit at both actual midpoint restrictions has this exact generated successor. -/
theorem actual_matched_electric_endpoint(F:Index)(g:diagonal.domain)(h:ℝ)(forward:Bool)(w:QuantumTest):
    M (weightedElectricEndpoint h forward w)=
      M w+(if forward then -(h:ℂ) else (h:ℂ)) • matchedElectricSuccessor w:=by
  change M (w+(if forward then -(h:ℂ) else (h:ℂ)) • X w)=_
  rw [map_add,map_smul,successor_return F g]
/-- Symmetric actual endpoints retain the old negative square and generate a second, signed source debit. -/
theorem actual_matched_electric_square_debit(F:Index)(g:diagonal.domain)(h:ℝ)(w:QuantumTest):
    -(n/96)*(‖embed (M (weightedElectricEndpoint h true w))‖^2+
      ‖embed (M (weightedElectricEndpoint h false w))‖^2)=
      -(n/48)*‖embed (M w)‖^2-(n*h^2/48)*‖embed (matchedElectricSuccessor w)‖^2:=by
  rw [actual_matched_electric_endpoint F g,actual_matched_electric_endpoint F g]
  simp only[ite_true,Bool.false_eq_true,ite_false,map_add,map_smul]
  have hn(a b:H)(r:ℝ):‖a+(-(r:ℂ)) • b‖^2+‖a+(r:ℂ) • b‖^2=
      2*‖a‖^2+2*r^2*‖b‖^2:=by
    rw [norm_add_sq (𝕜:=ℂ),norm_add_sq (𝕜:=ℂ)]
    simp only[norm_smul,norm_neg,Complex.norm_real,Real.norm_eq_abs,inner_smul_right,RCLike.re_eq_complex_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im]
    nlinarith [sq_abs r]
  rw [hn]
  ring
end LowEnergy.FirstCurrentElectricSuccessor
