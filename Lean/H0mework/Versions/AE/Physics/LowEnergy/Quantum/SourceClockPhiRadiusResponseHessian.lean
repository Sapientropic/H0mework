import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusAcceleration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusResponseHessian
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceHamiltonianVolume
open SourceScalarRadialContact SourceScalarFlatJoint SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarPairedTransport
open SourceScalarPositiveBulkWard SourceScalarDoubleCurrent SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusResponseNativeBudget
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Pa (a : ScalarIndex) : End := GaussMomentumAdjoint.adjoint (scalarDirection a)
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev Q : End := 1-S
private abbrev D (a : ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev d (a : ScalarIndex) : End := D a*S^2
attribute [local irreducible] resolventCore compressionCore defectAction diagonalAction

private def phiColumn (a : ScalarIndex) : End :=
  multiply (fun z => inner ℝ (scalarField z) (scalarBasis a))
    (fun _ => (scalarField_smooth.inner ℝ contDiff_const).contDiffAt)
private def phiMomentum : End := ∑ a : ScalarIndex,phiColumn a*P a
private def phiAdjoint : End := ∑ a : ScalarIndex,Pa a*phiColumn a

private theorem phi_expansion (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,inner ℝ (scalarField z) (scalarBasis a) • scalarDirection a)=
      (scalarField z,0) := by
  apply Prod.ext
  · simp only [Prod.fst_sum,Prod.smul_fst]
    simpa only [scalarDirection,OrthonormalBasis.repr_apply_apply,real_inner_comm] using
      scalarBasis.sum_repr (scalarField z)
  · simp [scalarDirection,Prod.snd_sum]

private theorem phi_native_contraction : phiMomentum=(-Complex.I) • phiEulerAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have he := congrArg (SourceElectricColumns.pointMomentum f z) (phi_expansion z)
    simp only [map_sum,map_smul] at he
    have hs : phiMomentum f z=∑ a : ScalarIndex,inner ℝ (scalarField z) (scalarBasis a) •
        SourceElectricColumns.pointMomentum f z (scalarDirection a) := by
      simp only [phiMomentum,LinearMap.sum_apply,sum_apply,Module.End.mul_apply]
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
  · exact (image_eq_zero_of_notMem_tsupport (fun h => hz ((phiMomentum f).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h => hz (((-Complex.I) • phiEulerAction f).tsupport_subset h))).symm

private theorem flow_pair_generator (flow : ℝ → End) (G : End)
    (hzero : ∀ f,flow 0 f=f)
    (hpair : ∀ t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv : ∀ f,HasDerivAt (fun t : ℝ => embed (flow t f)) (embed (G f)) 0)
    (f g : QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  have h := (hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he : (fun t : ℝ => inner ℂ (embed (flow t f)) (embed (flow t g)))=
      fun _ => sourcePair f g := funext (fun t => hpair t f g)
  rw [he] at h
  have heq := h.unique (hasDerivAt_const (0 : ℝ) (sourcePair f g))
  change sourcePair f (G g)+sourcePair (G f) g=0 at heq
  exact eq_neg_of_add_eq_zero_left heq

private theorem phi_pair (f g : QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem phi_euler_pair_shift (f g : QuantumTest) :
    sourcePair f (phiEulerAction g)= -sourcePair (phiEulerAction f) g-(61:ℂ)*sourcePair f g := by
  have h := phi_pair f g
  change sourcePair f ((phiEulerAction+(61/2:ℂ) • 1) g)=
    -sourcePair ((phiEulerAction+(61/2:ℂ) • 1) f) g at h
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_add_left,inner_smul_right,inner_smul_left] at h ⊢
  norm_num only [map_div₀,map_ofNat,map_one] at h
  linear_combination (norm:=ring) h

private theorem phi_adjoint_contraction :
    phiAdjoint=(-Complex.I) • (phiEulerAction+(61:ℂ) • 1) := by
  have hp (f g : QuantumTest) : sourcePair f (phiAdjoint g)=sourcePair (phiMomentum f) g := by
    simp only [phiAdjoint,phiMomentum,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
    apply Finset.sum_congr rfl
    intro a _
    change sourcePair f (Pa a (phiColumn a g))=sourcePair (phiColumn a (P a f)) g
    exact (adjoint_pair _ _ _).trans (multiply_pair _ _ _ _)
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have h := phi_euler_pair_shift f g
  rw [hp,phi_native_contraction]
  simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.one_apply,sourcePair,map_smul,map_add,
    inner_smul_left,inner_smul_right,inner_add_right,map_neg,Complex.conj_I,neg_neg] at h ⊢
  linear_combination (norm:=ring) Complex.I*h


private theorem phi_pos (z : SourceCoordinateSlice) : 0 < phiRadius z := by
  unfold phiRadius SourceClockRadiusResponseAffine.affineRadius
  positivity
private theorem real_commute (c b : SourceCoordinateSlice → ℝ)
    (hc : ∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hb : ∀z:physicalChart,ContDiffAt ℝ ∞ b z.val) : Commute (multiply c hc) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (b z:ℂ) (f z)
private theorem real_radius (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z:physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) r := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (phiRadius z:ℂ) (f z)
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul]
  have h : (phiReciprocal z:ℂ)*(phiRadius z:ℂ)=1 := by
    unfold phiReciprocal
    push_cast
    field_simp [(phi_pos z).ne']
  rw [h,one_smul]
private theorem radius_inverse : r*S=(1:End) := (real_radius _ _).eq.symm.trans inverse_radius
private theorem inverse_D (a : ScalarIndex) : Commute S (D a) := real_commute _ _ _ _
private theorem inverse_W : Commute S W := real_commute _ _ _ _
private theorem inverse_U : Commute S inverseVolumeAction := real_commute _ _ _ _
private theorem D_W (a : ScalarIndex) : Commute (D a) W := real_commute _ _ _ _
private theorem weight_inverse : W=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1
private theorem native_inverse (a : ScalarIndex) :
    bracket (P a) S=(-Complex.I) • d a ∧ bracket (Pa a) S=(-Complex.I) • d a := by
  have step (A : End) (h : bracket A r=Complex.I • D a) : bracket A S=(-Complex.I) • d a := by
    have hm : bracket A S= -(S*bracket A r*S) := by
      have h1 : S*A*r*S=S*A := by
        calc _=S*A*(r*S) := by noncomm_ring
             _=_ := by rw [radius_inverse,mul_one]
      have h2 : S*r*A*S=A*S := by rw [inverse_radius,one_mul]
      calc _= -(S*A*r*S-S*r*A*S) := by rw [h1,h2];unfold bracket;abel
           _=_ := by unfold bracket;noncomm_ring
    rw [hm,h]
    have hd : S*D a*S=d a := by
      rw [(inverse_D a).eq]
      change D a*S*S=D a*S^2
      rw [pow_two,mul_assoc]
    simp only [mul_smul_comm,smul_mul_assoc,neg_smul,hd]
  exact ⟨step _ (original_phi_radius_native_jet (scalarDirection a)).1,
    step _ (original_phi_radius_native_jet (scalarDirection a)).2⟩
private theorem inverse_native (A : End) (h:Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hu : inverseVolumeAction*volumeAction=(1:End) :=
    (real_volume _ _).eq.trans (LinearMap.ext volume_inverse)
  have hv : volumeAction*inverseVolumeAction=(1:End) := LinearMap.ext volume_inverse
  change A*inverseVolumeAction=inverseVolumeAction*A
  have h1 := congrArg (fun T:End=>inverseVolumeAction*T*inverseVolumeAction) h.eq
  simp only [mul_assoc,hv,mul_one] at h1
  simpa only [←mul_assoc,hu,one_mul] using h1.symm
private theorem Pa_W (a : ScalarIndex) : Commute (Pa a) W := by
  rw [weight_inverse]
  exact (inverse_native _ (native_adjoint_volume (scalarDirection a))).smul_right _
private theorem real_d (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z:physicalChart,ContDiffAt ℝ ∞ c z.val) (a:ScalarIndex) : Commute (multiply c hc) (d a) :=
  ((real_commute _ _ _ _).mul_right ((real_commute _ _ _ _).pow_right 2))
private theorem inverse_d (a:ScalarIndex) : Commute S (d a) :=
  (inverse_D a).mul_right (Commute.refl S |>.pow_right 2)

private theorem inverse_power_apply (n:ℕ) (f:QuantumTest) (z:SourceCoordinateSlice) :
    (S^n) f z=(phiReciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (phiReciprocal z:ℂ) • ((S^n) f z)=_
    rw [ih,pow_succ',mul_smul]
private theorem direction_square_end : (∑a:ScalarIndex,D a*D a)=(1/4:ℂ) • ((1:End)-S^2) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,
    Module.End.one_apply,sum_apply]
  change (∑a:ScalarIndex,(phiDirectionWeight (scalarBasis a) z:ℂ) •
    ((phiDirectionWeight (scalarBasis a) z:ℂ) • f z))=(1/4:ℂ) • (f z-(S^2) f z)
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  have hs : (∑a:ScalarIndex,(phiDirectionWeight (scalarBasis a) z)^2)=(1-(phiReciprocal z)^2)/4 := by
    simp only [phiDirectionWeight,neg_div,neg_sq,div_pow,←Finset.sum_div]
    rw [scalarBasis.sum_sq_inner_left]
    have hr : phiRadius z^2=1+‖scalarField z‖^2/4 := Real.sq_sqrt (by positivity)
    unfold phiReciprocal
    field_simp [(phi_pos z).ne']
    nlinarith only [hr]
  rw [hs,inverse_power_apply]
  push_cast
  module
private theorem inverse_column (a:ScalarIndex) : D a=(-1/4:ℂ) • (S*phiColumn a) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiDirectionWeight (scalarBasis a) z:ℂ) • f z=
    (-1/4:ℂ) • ((phiReciprocal z:ℂ) • ((inner ℝ (scalarField z) (scalarBasis a):ℂ) • f z))
  simp only [smul_smul]
  congr 1
  unfold phiDirectionWeight phiReciprocal
  push_cast
  field_simp
private theorem inverse_column_sum : (∑a:ScalarIndex,d a*phiColumn a)=-(S-S^3) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  simp only [LinearMap.sum_apply,Module.End.mul_apply,sum_apply,LinearMap.neg_apply,
    LinearMap.sub_apply]
  change (∑a:ScalarIndex,(phiDirectionWeight (scalarBasis a) z:ℂ) • ((S^2) (phiColumn a f) z))=
    -((phiReciprocal z:ℂ) • f z-(S^3) f z)
  simp only [inverse_power_apply]
  change (∑a:ScalarIndex,(phiDirectionWeight (scalarBasis a) z:ℂ) •
    ((phiReciprocal z:ℂ)^2 • ((inner ℝ (scalarField z) (scalarBasis a):ℂ) • f z)))=
    -((phiReciprocal z:ℂ) • f z-(phiReciprocal z:ℂ)^3 • f z)
  simp only [smul_smul,←Finset.sum_smul,←Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_sum]
  have hs : (∑a:ScalarIndex,phiDirectionWeight (scalarBasis a) z*(phiReciprocal z^2*
    inner ℝ (scalarField z) (scalarBasis a)))= -(phiReciprocal z-phiReciprocal z^3) := by
    simp only [phiDirectionWeight]
    have hm (a:ScalarIndex) : (-inner ℝ (scalarField z) (scalarBasis a)/(4*phiRadius z)) *
      (phiReciprocal z^2*inner ℝ (scalarField z) (scalarBasis a))=
      -(phiReciprocal z^3/4)*(inner ℝ (scalarField z) (scalarBasis a))^2 := by
      unfold phiReciprocal
      field_simp
    simp_rw [hm]
    rw [←Finset.mul_sum,scalarBasis.sum_sq_inner_left]
    have hr : phiRadius z^2=1+‖scalarField z‖^2/4 := Real.sq_sqrt (by positivity)
    unfold phiReciprocal
    field_simp [(phi_pos z).ne']
    nlinarith only [hr]
  rw [hs]
  push_cast
  module

private def radiusZeroCore (a:ScalarIndex) : End := D a*W*P a-Pa a*W*D a
private def inverseZeroCore (a:ScalarIndex) : End := d a*W*P a-Pa a*W*d a

private theorem radius_hessian_source : (∑a:ScalarIndex,radiusZeroCore a)=
    (Complex.I*(sourceTime 0:ℂ)/4) • (inverseVolumeAction*((60:ℂ) • S+S^3)) := by
  have hrow (a:ScalarIndex) : radiusZeroCore a=(1/4:ℂ) •
    (W*(S*(Pa a*phiColumn a-phiColumn a*P a)+bracket (Pa a) S*phiColumn a)) := by
    unfold radiusZeroCore
    rw [inverse_column]
    have hp := (Pa_W a).eq
    have hw : Commute (phiColumn a) W := real_commute _ _ _ _
    have he : S*phiColumn a*W*P a-Pa a*W*S*phiColumn a=
        -W*(S*(Pa a*phiColumn a-phiColumn a*P a)+bracket (Pa a) S*phiColumn a) := by
      unfold bracket
      linear_combination (norm:=noncomm_ring) S*hw.eq*P a-hp*S*phiColumn a+inverse_W.eq*phiColumn a*P a
    simp only [smul_mul_assoc,mul_smul_comm,←smul_sub]
    rw [←mul_assoc (Pa a*W) S (phiColumn a),he]
    simp only [neg_mul]
    module
  simp_rw [hrow]
  rw [←Finset.smul_sum,←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,
    Finset.sum_sub_distrib]
  change _=(Complex.I*(sourceTime 0:ℂ)/4) • (inverseVolumeAction*((60:ℂ) • S+S^3))
  have hb : (∑a:ScalarIndex,bracket (Pa a) S*phiColumn a)=(-Complex.I) • ∑a:ScalarIndex,d a*phiColumn a := by
    simp_rw [(native_inverse _).2,smul_mul_assoc]
    rw [Finset.smul_sum]
  rw [hb,inverse_column_sum]
  change (1/4:ℂ) • (W*(S*(phiAdjoint-phiMomentum)+(-Complex.I) • (-(S-S^3))))=_
  rw [phi_adjoint_contraction,phi_native_contraction,weight_inverse]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_add,mul_sub,mul_one,
    smul_add,smul_sub,mul_neg,neg_mul,neg_sub,mul_assoc]
  module

private theorem adjoint_inverse_square (a:ScalarIndex) : bracket (Pa a) (S^2)=
    (-2*Complex.I:ℂ) • (S*d a) := by
  have he : bracket (Pa a) (S^2)=bracket (Pa a) S*S+S*bracket (Pa a) S := by
    unfold bracket;noncomm_ring
  rw [he,(native_inverse a).2]
  simp only [smul_mul_assoc,mul_smul_comm]
  rw [(inverse_d a).symm.eq]
  module
private theorem inverse_zero_row (a:ScalarIndex) : inverseZeroCore a=
    S^2*radiusZeroCore a+(2*Complex.I:ℂ) • (W*S^3*(D a*D a)) := by
  have hd : d a=S^2*D a := ((inverse_D a).pow_left 2).eq.symm
  have hw := (inverse_W.pow_left 2).eq
  have he : inverseZeroCore a=S^2*radiusZeroCore a-bracket (Pa a) (S^2)*W*D a := by
    unfold inverseZeroCore radiusZeroCore
    rw [hd]
    unfold bracket
    linear_combination (norm:=noncomm_ring) Pa a*hw*D a
  rw [he,adjoint_inverse_square]
  have hm : S*d a*W*D a=W*S^3*(D a*D a) := by
    rw [hd]
    have hw1 : Commute (S^3) W := inverse_W.pow_left 3
    have hdw := (D_W a).eq
    calc _=S*S^2*(D a*W)*D a := by noncomm_ring
         _=S*S^2*(W*D a)*D a := by rw [hdw]
         _=S^3*W*(D a*D a) := by rw [←pow_succ'];noncomm_ring
         _=_ := by rw [hw1.eq]
  simp only [smul_mul_assoc,sub_neg_eq_add,neg_smul,neg_mul,hm]

theorem original_phi_inverse_hessian_source : (∑a:ScalarIndex,inverseZeroCore a)=
    (Complex.I*(sourceTime 0:ℂ)/4) •
      (inverseVolumeAction*((58:ℂ) • S^3+(3:ℂ) • S^5)) := by
  simp_rw [inverse_zero_row]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.smul_sum,←Finset.mul_sum,
    radius_hessian_source,direction_square_end,weight_inverse]
  have hu := (inverse_U.pow_left 2).eq
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [←mul_assoc,hu,mul_assoc]
  simp only [mul_assoc,mul_add,mul_sub,mul_smul_comm,mul_one,←pow_add,←pow_succ,smul_add,smul_sub,smul_smul]
  module

def phiFirstPeak (m ell:ℕ) : End := (ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m
def phiSecondPeak (m ell:ℕ) : End := (m*(m+1):ℂ) • Q^(m-1)-(ell*(ell+1):ℂ) • Q^(ell-1)
private def dt (a:ScalarIndex) (m ell:ℕ) : End := phiFirstPeak m ell*d a
private def thetaZero (a:ScalarIndex) (m ell:ℕ) : End := dt a m ell*W*P a-Pa a*W*dt a m ell
private theorem Q_commute {A : End} (h : Commute S A) : Commute Q A :=
  (Commute.one_left A).sub_left h
private theorem first_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (phiFirstPeak m ell) A :=
  (((Q_commute h).pow_left ell).smul_left _).sub_left (((Q_commute h).pow_left m).smul_left _)
private theorem second_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (phiSecondPeak m ell) A :=
  (((Q_commute h).pow_left (m-1)).smul_left _).sub_left (((Q_commute h).pow_left (ell-1)).smul_left _)
private theorem theta_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (phiThetaAction m ell) A :=
  ((Q_commute h).pow_left (m+1)).sub_left ((Q_commute h).pow_left (ell+1))

private theorem bracket_product (A B C : End) : bracket A (B*C)=bracket A B*C+B*bracket A C := by unfold bracket;noncomm_ring
private theorem bracket_smul (A B : End) (c : ℂ) : bracket A (c • B)=c • bracket A B := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bracket_sub (A B C : End) : bracket A (B-C)=bracket A B-bracket A C := by unfold bracket;noncomm_ring

private theorem adjoint_inverse (a:ScalarIndex) : bracket (Pa a) S=(-Complex.I) • d a := (native_inverse a).2

private theorem adjoint_Q (a : ScalarIndex) : bracket (Pa a) Q=Complex.I • d a := by
  rw [bracket_sub]
  have hz : bracket (Pa a) (1:End)=0 := by simp [bracket]
  rw [hz,adjoint_inverse,zero_sub,neg_smul,neg_neg]

private theorem adjoint_geometric_successor (a : ScalarIndex) (n : ℕ) :
    bracket (Pa a) (Q^(n+1))=((n+1:ℂ)*Complex.I) • (Q^n*d a) := by
  induction n with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul] using adjoint_Q a
  | succ n ih =>
    rw [show n+1+1=(n+1)+1 from rfl,pow_succ,bracket_product,ih,adjoint_Q]
    have hm : (Q^n*d a)*Q=Q^(n+1)*d a := by
      rw [mul_assoc,(Q_commute (inverse_d a)).symm.eq,←mul_assoc,←pow_succ]
    simp only [smul_mul_assoc,mul_smul_comm]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module

private theorem adjoint_geometric (a : ScalarIndex) (n : ℕ) :
    bracket (Pa a) (Q^n)=((n:ℂ)*Complex.I) • (Q^(n-1)*d a) := by
  cases n with
  | zero => simp [bracket]
  | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using adjoint_geometric_successor a n

private theorem adjoint_first_peak (a : ScalarIndex) (m ell : ℕ) :
    bracket (Pa a) (phiFirstPeak m ell)=(-Complex.I) • (phiSecondPeak m ell*d a) := by
  rw [phiFirstPeak,bracket_sub,bracket_smul,bracket_smul,adjoint_geometric,adjoint_geometric]
  simp only [phiSecondPeak,sub_mul,smul_mul_assoc,smul_sub,smul_smul]
  module


private theorem derivative_square_sum : (∑a:ScalarIndex,(d a)^2)=(1/4:ℂ) • (S^4-S^6) := by
  have hrow (a:ScalarIndex) : (d a)^2=S^4*(D a*D a) := by
    rw [pow_two]
    change (D a*S^2)*(D a*S^2)=_
    calc _=D a*(S^2*D a)*S^2 := by noncomm_ring
         _=D a*(D a*S^2)*S^2 := by rw [((inverse_D a).pow_left 2).eq]
         _=D a*D a*(S^2*S^2) := by noncomm_ring
         _=D a*D a*S^4 := by rw [←pow_add]
         _=_ := (((inverse_D a).mul_right (inverse_D a)).pow_left 4).eq.symm
  simp_rw [hrow]
  rw [←Finset.mul_sum,direction_square_end,mul_smul_comm,mul_sub,mul_one,←pow_add]

private theorem theta_gradient_peaks (a:ScalarIndex) (m ell:ℕ) : dt a m ell=phiFirstPeak m ell*d a := rfl
private theorem theta_zero_row (a : ScalarIndex) (m ell : ℕ) :
    thetaZero a m ell=phiFirstPeak m ell*inverseZeroCore a+Complex.I • (W*phiSecondPeak m ell*(d a)^2) := by
  have hb := (first_commute inverse_W m ell).eq
  have hd := (real_d scalarWeight scalarWeight_smooth a).eq
  have he : phiFirstPeak m ell*d a*W*P a-Pa a*W*(phiFirstPeak m ell*d a)=
      phiFirstPeak m ell*(d a*W*P a-Pa a*W*d a)-bracket (Pa a) (phiFirstPeak m ell)*W*d a := by
    unfold bracket
    linear_combination (norm := noncomm_ring) Pa a*hb*d a
  unfold thetaZero
  change dt a m ell*W*P a-Pa a*W*dt a m ell=_
  rw [theta_gradient_peaks,he,adjoint_first_peak]
  change _=phiFirstPeak m ell*(d a*W*P a-Pa a*W*d a)+Complex.I • (W*phiSecondPeak m ell*(d a)^2)
  have hx : phiSecondPeak m ell*d a*W*d a=W*phiSecondPeak m ell*(d a)^2 := by
    calc
      _=phiSecondPeak m ell*(d a*W)*d a := by noncomm_ring
      _=phiSecondPeak m ell*(W*d a)*d a := by rw [hd.symm]
      _=(phiSecondPeak m ell*W)*(d a)^2 := by noncomm_ring
      _=_ := by rw [(second_commute inverse_W m ell).eq]
  simp only [neg_smul,neg_mul,smul_mul_assoc,sub_neg_eq_add,hx]

/-- Both genuine boundary derivatives retain their scalar61 Hessian contraction. -/
def thetaHessian (m ell : ℕ) : End := (1/4:ℂ) •
  (phiSecondPeak m ell*(S^4-S^6)-
    phiFirstPeak m ell*((58:ℂ) • S^3+(3:ℂ) • S^5))
def bandHessian (m ell : ℕ) : End := (1/4:ℂ) •
  (phiSecondPeak m ell*(S^3-S^5)-
    phiFirstPeak m ell*((60:ℂ) • S^2+S^4)+
    phiThetaAction m ell*((60:ℂ) • S+S^3))

theorem original_phi_theta_hessian_source (m ell : ℕ) :
    (∑ a : ScalarIndex,thetaZero a m ell)=Complex.I • (W*thetaHessian m ell) := by
  simp_rw [theta_zero_row]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.smul_sum,←Finset.mul_sum,
    original_phi_inverse_hessian_source,derivative_square_sum]
  have hU := inverse_U
  have hB := (first_commute hU m ell).eq
  rw [thetaHessian,weight_inverse]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_sub,mul_add,smul_sub,smul_add]
  have h3 : phiFirstPeak m ell*(inverseVolumeAction*S^3)=inverseVolumeAction*(phiFirstPeak m ell*S^3) := by
    rw [←mul_assoc,hB,mul_assoc]
  have h5 : phiFirstPeak m ell*(inverseVolumeAction*S^5)=inverseVolumeAction*(phiFirstPeak m ell*S^5) := by
    rw [←mul_assoc,hB,mul_assoc]
  simp only [mul_assoc,h3,h5]
  module

private theorem mixed_direction_square : (∑ a : ScalarIndex,d a*D a)=
    (1/4:ℂ) • (S^2-S^4) := by
  have h (a : ScalarIndex) : d a*D a=S^2*(D a*D a) := by
    change (D a*S^2)*D a=_
    rw [((inverse_D a).pow_left 2).symm.eq,mul_assoc]
  simp_rw [h]
  rw [←Finset.mul_sum,direction_square_end,mul_smul_comm,mul_sub,mul_one,←pow_add]

private theorem weight_D (a : ScalarIndex) : Commute W (D a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (scalarWeight z:ℂ) (phiDirectionWeight (scalarBasis a) z:ℂ) (f z)
private theorem theta_cross_sum (m ell : ℕ) :
    (∑ a : ScalarIndex,dt a m ell*W*D a)=
      (1/4:ℂ) • (W*phiFirstPeak m ell*(S^2-S^4)) := by
  have h (a : ScalarIndex) : dt a m ell*W*D a=W*phiFirstPeak m ell*(d a*D a) := by
    rw [theta_gradient_peaks]
    calc
      _=phiFirstPeak m ell*(d a*W)*D a := by noncomm_ring
      _=phiFirstPeak m ell*(W*d a)*D a := by rw [(real_d scalarWeight scalarWeight_smooth a).symm.eq]
      _=(phiFirstPeak m ell*W)*(d a*D a) := by noncomm_ring
      _=_ := by rw [(first_commute inverse_W m ell).eq]
  simp_rw [h]
  rw [←Finset.mul_sum,mixed_direction_square,mul_smul_comm]

private theorem inverse_radius_commute : Commute S r := by
  change S*r=r*S
  rw [radius_inverse]
  exact inverse_radius
private theorem radius_power (n : ℕ) : r*S^(n+1)=S^n := by
  rw [pow_succ',←mul_assoc,radius_inverse,one_mul]
private theorem radius_hessian (m ell : ℕ) :
    thetaHessian m ell*r=(1/4:ℂ) •
      (phiSecondPeak m ell*(S^3-S^5)-
        phiFirstPeak m ell*((58:ℂ) • S^2+(3:ℂ) • S^4)) := by
  unfold thetaHessian
  simp only [smul_mul_assoc,sub_mul,add_mul,mul_assoc]
  have hp (n : ℕ) : S^(n+1)*r=S^n := by
    rw [(inverse_radius_commute.pow_left (n+1)).eq,radius_power]
  rw [hp 3,hp 5,hp 2,hp 4]


private theorem theta_adjoint (a:ScalarIndex) (m ell:ℕ) :
    bracket (Pa a) (phiThetaAction m ell)=(-Complex.I) • dt a m ell := by
  rw [phiThetaAction,bracket_sub,adjoint_geometric_successor,adjoint_geometric_successor]
  simp only [dt,phiFirstPeak,sub_mul,smul_mul_assoc,smul_sub,smul_smul]
  module
private theorem theta_native (a:ScalarIndex) (m ell:ℕ) :
    bracket (P a) (phiThetaAction m ell)=(-Complex.I) • dt a m ell := by
  have transfer (A B:End) (h:bracket A S=bracket B S) (n:ℕ) : bracket A (Q^n)=bracket B (Q^n) := by
    induction n with
    | zero => simp [bracket]
    | succ n ih =>
      have hQ : bracket A Q=bracket B Q := by
        unfold bracket at h ⊢
        change A*(1-S)-(1-S)*A=B*(1-S)-(1-S)*B
        linear_combination (norm:=noncomm_ring) -h
      rw [pow_succ,bracket_product,bracket_product,ih,hQ]
  have hS : bracket (P a) S=bracket (Pa a) S := (native_inverse a).1.trans (native_inverse a).2.symm
  have he : bracket (P a) (phiThetaAction m ell)=bracket (Pa a) (phiThetaAction m ell) := by
    rw [phiThetaAction,bracket_sub,bracket_sub,transfer _ _ hS,transfer _ _ hS]
  exact he.trans (theta_adjoint a m ell)
private theorem theta_native_source (m ell:ℕ) : bracket diagonalAction (phiThetaAction m ell)=
    (-Complex.I/2:ℂ) • ∑a:ScalarIndex,(Pa a*W*dt a m ell+dt a m ell*W*P a) := by
  have hn : Commute (diagonalAction-scalarKinetic) S := by
    have h := original_phi_radius_non_scalar_commute.2.2.2
    change (diagonalAction-scalarKinetic)*S=S*(diagonalAction-scalarKinetic)
    have hi := congrArg (fun A:End=>S*A*S) h.eq
    simp only [mul_assoc,radius_inverse,mul_one] at hi
    simpa only [←mul_assoc,inverse_radius,one_mul] using hi.symm
  have hnθ := theta_commute hn.symm m ell
  have he : bracket diagonalAction (phiThetaAction m ell)=bracket scalarKinetic (phiThetaAction m ell) := by
    unfold bracket
    linear_combination (norm:=noncomm_ring) hnθ.eq.symm
  have hrow(a:ScalarIndex) : bracket (Pa a*(W*P a)) (phiThetaAction m ell)=
    (-Complex.I) • (Pa a*W*dt a m ell+dt a m ell*W*P a) := by
    have hw := (theta_commute inverse_W m ell).eq
    have hb : bracket (Pa a*(W*P a)) (phiThetaAction m ell)=
      Pa a*W*bracket (P a) (phiThetaAction m ell)+bracket (Pa a) (phiThetaAction m ell)*W*P a := by
      unfold bracket
      linear_combination (norm:=noncomm_ring) -Pa a*hw*P a
    rw [hb,theta_native,theta_adjoint]
    simp only [mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc]
  rw [he]
  unfold scalarKinetic sandwich
  simp only [←Module.End.mul_eq_comp,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,
    Finset.mul_sum,←Finset.sum_sub_distrib,←smul_sub]
  have h := Finset.sum_congr (s₁:=Finset.univ) rfl (fun a _=>hrow a)
  simp only [bracket] at h
  rw [h,←Finset.smul_sum,smul_smul]
  congr 1
  ring

private def nativeRows (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) (a:ScalarIndex) : QuantumTest :=
  dt a m ell (bracket r (resolventCore F z hz) (coreEquiv.symm g))-
    phiThetaAction m ell (D a (resolventCore F z hz (coreEquiv.symm g)))
private theorem native_row_return (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) (a:ScalarIndex) :
    nativeRows m ell F z hz g a=phiNativeVector a m ell F z hz g := by
  have hb (n:ℕ) : (n+1:ℂ) • (S*Q^n)=S*((n+1:ℂ) • Q^n) := by rw [mul_smul_comm]
  have hc := Commute.refl S
  have hQ := (Commute.one_right S).sub_right hc
  have hf : Commute S (phiFirstPeak m ell) := ((hQ.pow_right ell).smul_right _).sub_right ((hQ.pow_right m).smul_right _)
  have hT := theta_commute (inverse_D a) m ell
  have hR : coreEquiv.symm (phiRadiusSource g)=r (coreEquiv.symm g) := coreEquiv.symm_apply_apply _
  unfold nativeRows phiNativeVector
  change (phiFirstPeak m ell*(D a*S^2)) (r (resolventCore F z hz (coreEquiv.symm g))-
    resolventCore F z hz (r (coreEquiv.symm g)))-phiThetaAction m ell (D a _)=
    D a (((ell+1:ℂ) • (S*Q^ell)-(m+1:ℂ) • (S*Q^m)-phiThetaAction m ell) _-
      S (((ell+1:ℂ) • (S*Q^ell)-(m+1:ℂ) • (S*Q^m)) (resolventCore F z hz (coreEquiv.symm (phiRadiusSource g)))))
  rw [hR]
  have hB : (ell+1:ℂ) • (S*Q^ell)-(m+1:ℂ) • (S*Q^m)=phiFirstPeak m ell*S := by
    rw [hb,hb,←mul_sub,←hf.eq]
    rfl
  rw [hB]
  have hD : Commute (phiFirstPeak m ell) (D a) := first_commute (inverse_D a) m ell
  have hS2 : S^2*r=S := by rw [pow_two,mul_assoc,inverse_radius,mul_one]
  have h1 : (phiFirstPeak m ell*(D a*S^2))*r=D a*(phiFirstPeak m ell*S) := by
    calc _=(phiFirstPeak m ell*D a)*(S^2*r) := by noncomm_ring
         _=_ := by rw [hD.eq,hS2];noncomm_ring
  have h2 : phiFirstPeak m ell*(D a*S^2)=D a*S*(phiFirstPeak m ell*S) := by
    calc _=(phiFirstPeak m ell*D a)*S^2 := by noncomm_ring
         _=D a*phiFirstPeak m ell*S^2 := by rw [hD.eq]
         _=D a*(phiFirstPeak m ell*S)*S := by rw [pow_two];noncomm_ring
         _=D a*(S*phiFirstPeak m ell)*S := by rw [hf.eq.symm]
         _=_ := by noncomm_ring
  have hO : (phiFirstPeak m ell*(D a*S^2))*bracket r (resolventCore F z hz)-
      phiThetaAction m ell*D a*resolventCore F z hz=
    D a*((phiFirstPeak m ell*S-phiThetaAction m ell)*resolventCore F z hz-
      S*(phiFirstPeak m ell*S)*resolventCore F z hz*r) := by
    unfold bracket
    linear_combination (norm:=noncomm_ring) h1*resolventCore F z hz-h2*resolventCore F z hz*r-hT.eq*resolventCore F z hz
  have he := LinearMap.congr_fun hO (coreEquiv.symm g)
  simpa only [bracket,Module.End.mul_apply,LinearMap.sub_apply,map_sub] using he

private def radialZero (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : QuantumTest :=
  (-Complex.I/2:ℂ) • (∑a:ScalarIndex,thetaZero a m ell (bracket r (resolventCore F z hz) (coreEquiv.symm g)))+
    (Complex.I/2:ℂ) • phiThetaAction m ell ((∑a:ScalarIndex,radiusZeroCore a) (resolventCore F z hz (coreEquiv.symm g)))-
      ∑a:ScalarIndex,dt a m ell (W (D a (resolventCore F z hz (coreEquiv.symm g))))
private def phiNativeSource (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : QuantumTest :=
  bracket diagonalAction (phiThetaAction m ell) (bracket r (resolventCore F z hz) (coreEquiv.symm g))+
    phiThetaAction m ell (phiRadiusCurrent (resolventCore F z hz (coreEquiv.symm g)))
/-- The zero-order carrier is an explicit pair of bounded radial Hessians on two original fixed sources. -/
def zeroVector (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  bandHessian m ell (resolventCore F z hz (coreEquiv.symm g))-
    thetaHessian m ell (resolventCore F z hz (r (coreEquiv.symm g)))

theorem actual_phi_radius_zero_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    radialZero m ell F z hz g=(-(sourceTime 0:ℂ)/2) • (inverseVolumeAction (zeroVector m ell F z hz g)) := by
  let q := resolventCore F z hz (coreEquiv.symm g)
  let t := resolventCore F z hz (r (coreEquiv.symm g))
  have h0 := LinearMap.congr_fun (original_phi_theta_hessian_source m ell) (r q-t)
  have hr := LinearMap.congr_fun radius_hessian_source q
  have hc := LinearMap.congr_fun (theta_cross_sum m ell) q
  simp only [LinearMap.sum_apply,Module.End.mul_apply,LinearMap.smul_apply] at h0 hr hc
  have hH := LinearMap.congr_fun (radius_hessian m ell) q
  have hW := theta_commute inverse_U m ell
  have hw (f : QuantumTest) : W f=(-(sourceTime 0:ℂ)) • inverseVolumeAction f :=
    LinearMap.congr_fun weight_inverse f
  have hi : Complex.I*Complex.I= -1 := Complex.I_mul_I
  unfold radialZero zeroVector
  change (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,thetaZero a m ell (r q-t))+
      (Complex.I/2:ℂ) • phiThetaAction m ell ((∑ a : ScalarIndex,radiusZeroCore a) q)-
        (∑ a : ScalarIndex,dt a m ell (W (D a q)))=
    (-(sourceTime 0:ℂ)/2) • inverseVolumeAction (bandHessian m ell q-thetaHessian m ell t)
  rw [h0,LinearMap.sum_apply,hr,hc,hw,hw]
  have hθ := LinearMap.congr_fun hW.eq (((60:ℂ) • S+S^3) q)
  change phiThetaAction m ell (inverseVolumeAction _)=inverseVolumeAction (phiThetaAction m ell _) at hθ
  simp only [map_smul,smul_smul,map_sub,map_add,bandHessian,LinearMap.smul_apply,LinearMap.add_apply,
    LinearMap.sub_apply,Module.End.mul_apply,mul_div_assoc] at hH hθ ⊢
  rw [hθ,hH]
  simp only [map_smul,map_sub,map_add]
  match_scalars
  all_goals ring_nf
  all_goals simp only [pow_two,hi]
  all_goals ring

private theorem theta_radius_row (T D K W P Pa : End) (ht : Commute T W)
    (hP : bracket Pa T=(-Complex.I) • D) :
    T*((Complex.I/2:ℂ) • (Pa*W*K+K*W*P))=
      Complex.I • (Pa*W*T*K)+
        (Complex.I/2:ℂ) • (T*(K*W*P-Pa*W*K))-D*W*K := by
  have hp : T*Pa=Pa*T+Complex.I • D := by
    unfold bracket at hP
    linear_combination (norm := module) -hP
  have hrew : T*(Pa*W*K)=(Pa*W*T*K)+Complex.I • (D*W*K) := by
    calc
      _=(T*Pa)*W*K := by noncomm_ring
      _=(Pa*T+Complex.I • D)*W*K := by rw [hp]
      _=Pa*(T*W)*K+Complex.I • (D*W*K) := by simp only [add_mul,smul_mul_assoc,mul_assoc]
      _=_ := by rw [ht.eq];noncomm_ring
  have hc : (Complex.I/2)*Complex.I= -(1/2:ℂ) := by
    calc _=(1/2:ℂ)*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  simp only [mul_smul_comm,mul_add,mul_sub,hrew,smul_add,smul_sub,smul_smul,hc]
  module

/-- The original radius forcing has only the full native divergence and its contracted radial zero-order word. -/
private theorem actual_phi_native_forcing (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    phiNativeSource m ell F z hz g=phiNativeDivergence m ell F z hz g+radialZero m ell F z hz g := by
  let q := resolventCore F z hz (coreEquiv.symm g)
  let v := bracket r (resolventCore F z hz) (coreEquiv.symm g)
  have hrow (a : ScalarIndex) :
      (-Complex.I/2:ℂ) • ((Pa a*W*dt a m ell+dt a m ell*W*P a) v)+
        phiThetaAction m ell (((Complex.I/2:ℂ) • (Pa a*W*D a+D a*W*P a)) q)=
      (-Complex.I) • (Pa a (W (dt a m ell v-phiThetaAction m ell (D a q))))+
        (-Complex.I/2:ℂ) • (thetaZero a m ell v)+
        (Complex.I/2:ℂ) • phiThetaAction m ell (radiusZeroCore a q)-dt a m ell (W (D a q)) := by
    have hr := LinearMap.congr_fun (theta_radius_row (phiThetaAction m ell) (dt a m ell) (D a) W (P a) (Pa a)
      (theta_commute inverse_W m ell) (theta_adjoint a m ell)) q
    have hs : (-Complex.I/2:ℂ) • (Pa a*W*dt a m ell+dt a m ell*W*P a)=
        (-Complex.I) • (Pa a*W*dt a m ell)+(-Complex.I/2:ℂ) • thetaZero a m ell := by
      unfold thetaZero
      module
    have hv := LinearMap.congr_fun hs v
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_smul] at hr hv ⊢
    unfold radiusZeroCore at *
    simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,map_add] at *
    linear_combination (norm := module) hv+hr
  have h := congrArg (fun f : ScalarIndex → QuantumTest => ∑ a,f a) (funext hrow)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.smul_sum,←map_sum] at h
  unfold phiNativeSource phiNativeDivergence radialZero
  simp_rw [←native_row_return m ell F z hz g]
  rw [theta_native_source]
  unfold phiRadiusCurrent
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul]
  change (-Complex.I/2:ℂ) • (∑a:ScalarIndex,(Pa a*W*dt a m ell+dt a m ell*W*P a) v)+
      (Complex.I/2:ℂ) • phiThetaAction m ell (∑a:ScalarIndex,(Pa a*W*D a+D a*W*P a) q)=
    (-Complex.I) • (∑a:ScalarIndex,Pa a (W (dt a m ell v-phiThetaAction m ell (D a q))))+
      (((-Complex.I/2:ℂ) • (∑a:ScalarIndex,thetaZero a m ell v)+
        (Complex.I/2:ℂ) • phiThetaAction m ell (∑a:ScalarIndex,radiusZeroCore a q))-
          ∑a:ScalarIndex,dt a m ell (W (D a q)))
  simpa only [LinearMap.smul_apply,←Finset.smul_sum,map_smul,add_sub_assoc,add_assoc] using h


def phiCoherentDefect (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : QuantumTest :=
  phiThetaAction m ell ((r*defectAction F*resolventCore F z hz-defectAction F*resolventCore F z hz*r) (coreEquiv.symm g))

/-- The actual full source now consumes the paid native70 vector and its explicit bounded radial zero word. -/
theorem actual_phi_response_forcing (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    phiResponseSource m ell F z hz g=phiNativeDivergence m ell F z hz g+
      (-(sourceTime 0:ℂ)/2) • inverseVolumeAction (zeroVector m ell F z hz g)+
        phiCoherentDefect m ell F z hz g := by
  change phiNativeSource m ell F z hz g+phiCoherentDefect m ell F z hz g=_
  rw [actual_phi_native_forcing,actual_phi_radius_zero_source]


private theorem one_le_phi (z:SourceCoordinateSlice) : 1 ≤ phiRadius z := by
  have hp := (phi_pos z).le
  have hs : phiRadius z^2=1+‖scalarField z‖^2/4 := Real.sq_sqrt (by positivity)
  nlinarith only [hp,hs,sq_nonneg ‖scalarField z‖]
private theorem phi_reciprocal_smooth : ContDiff ℝ ∞ phiReciprocal :=
  SourceClockRadiusResponseAffine.affine_radius_smooth.inv (fun z=>(phi_pos z).ne')
private def phiThetaProfile (m ell:ℕ) (z:SourceCoordinateSlice) : ℝ :=
  (1-phiReciprocal z)^(m+1)-(1-phiReciprocal z)^(ell+1)
private theorem phi_theta_profile_smooth (m ell:ℕ) : ContDiff ℝ ∞ (phiThetaProfile m ell) :=
  ((contDiff_const.sub phi_reciprocal_smooth).pow _).sub ((contDiff_const.sub phi_reciprocal_smooth).pow _)
private def phiDamping (m ell:ℕ) (z:SourceCoordinateSlice) : ℝ := phiReciprocal z*phiThetaProfile m ell z
private theorem geometric_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    s*(1-s)^n ≤ 1/(n+1 : ℝ) := by
  have hterm := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(n+1-j)*((n+1).choose j : ℝ))
    (fun j _ => by positivity) (show 1 ∈ Finset.range (n+1+1) by simp)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at hterm
  simp only [pow_one,Nat.add_sub_cancel,Nat.choose_one_right,Nat.cast_add,Nat.cast_one] at hterm
  apply (le_div_iff₀ (show 0 < (n+1 : ℝ) by positivity)).mpr
  exact hterm

/-- The original inverse-radius window supplies a cutoff-order bound, uniform in its upper endpoint. -/
private theorem phi_window_bound (m ell : ℕ) (hle : m ≤ ell) (z : SourceCoordinateSlice) :
    |phiReciprocal z*phiThetaProfile m ell z| ≤ 1/(m+2 : ℝ) := by
  have hs : 0 ≤ phiReciprocal z := (inv_pos.mpr (phi_pos z)).le
  have hs1 : phiReciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have hq : 0 ≤ 1-phiReciprocal z := sub_nonneg.mpr hs1
  have hq1 : 1-phiReciprocal z ≤ 1 := by linarith
  have he := pow_le_pow_of_le_one hq hq1 (Nat.add_le_add_right hle 1)
  have ht : 0 ≤ phiThetaProfile m ell z := sub_nonneg.mpr he
  rw [abs_of_nonneg (mul_nonneg hs ht)]
  have hp := geometric_peak (phiReciprocal z) hs hs1 (m+1)
  have hmul : phiReciprocal z*phiThetaProfile m ell z ≤ phiReciprocal z*(1-phiReciprocal z)^(m+1) := by
    unfold phiThetaProfile
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (pow_nonneg hq _)) hs
  have hd : ((m+1 : ℕ) : ℝ)+1=(m+2 : ℝ) := by push_cast;ring
  rw [hd] at hp
  exact hmul.trans hp

private theorem cubic_geometric_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n+1:ℝ)*(n+2:ℝ)*s^3*(1-s)^n ≤ 6/(n+3:ℝ) := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hterm := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(n+3-j)*((n+3).choose j:ℝ))
    (fun j _ => by positivity) (show 3∈Finset.range (n+3+1) by simp)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at hterm
  rw [show n+3-3=n by omega] at hterm
  have hc := congrArg (fun j : ℕ => (j:ℝ)) (Nat.add_one_mul_choose_eq (n+2) 2)
  push_cast at hc
  rw [Nat.cast_choose_two] at hc
  push_cast at hc
  have hc' : ((n+3).choose 3:ℝ)=(n+3:ℝ)*(n+2:ℝ)*(n+1:ℝ)/6 := by
    convert (show (((n+2)+1).choose (2+1):ℝ)=(n+3:ℝ)*(n+2:ℝ)*(n+1:ℝ)/6 from ?_) using 1
    nlinarith only [hc]
  rw [hc'] at hterm
  apply (le_div_iff₀ (by positivity : 0 < (n+3:ℝ))).mpr
  nlinarith only [hterm]

private theorem second_peak_bound (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n:ℝ)*(n+1:ℝ)*s^3*(1-s)^(n-1) ≤ 6/(n+2:ℝ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    convert cubic_geometric_peak s hs hs1 n using 1 <;> ring

private def firstCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((ell+1:ℝ)*(1-phiReciprocal z)^ell-(m+1:ℝ)*(1-phiReciprocal z)^m)*phiReciprocal z^2
private def secondCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((m:ℝ)*(m+1:ℝ)*(1-phiReciprocal z)^(m-1)-
    (ell:ℝ)*(ell+1:ℝ)*(1-phiReciprocal z)^(ell-1))*phiReciprocal z^3

private theorem first_smooth (m ell : ℕ) : ContDiff ℝ ∞ (firstCoefficient m ell) :=
  (((contDiff_const.mul ((contDiff_const.sub phi_reciprocal_smooth).pow ell)).sub
    (contDiff_const.mul ((contDiff_const.sub phi_reciprocal_smooth).pow m))).mul (phi_reciprocal_smooth.pow 2))
private theorem second_smooth (m ell : ℕ) : ContDiff ℝ ∞ (secondCoefficient m ell) :=
  (((contDiff_const.mul ((contDiff_const.sub phi_reciprocal_smooth).pow (m-1))).sub
    (contDiff_const.mul ((contDiff_const.sub phi_reciprocal_smooth).pow (ell-1)))).mul (phi_reciprocal_smooth.pow 3))

private theorem first_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |firstCoefficient m ell z| ≤ 4/(m+2:ℝ) := by
  have hs : 0 ≤ phiReciprocal z := (inv_pos.mpr (phi_pos z)).le
  have hs1 : phiReciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have hq : 0 ≤ 1-phiReciprocal z := sub_nonneg.mpr hs1
  have h₁ := SourceNativeCutoffContact.squared_geometric_peak (phiReciprocal z) hs hs1 ell
  have h₂ := SourceNativeCutoffContact.squared_geometric_peak (phiReciprocal z) hs hs1 m
  have hd : 2/(ell+2:ℝ) ≤ 2/(m+2:ℝ) := by gcongr
  have he : firstCoefficient m ell z=
      (ell+1:ℝ)*phiReciprocal z^2*(1-phiReciprocal z)^ell-
      (m+1:ℝ)*phiReciprocal z^2*(1-phiReciprocal z)^m := by unfold firstCoefficient;ring
  rw [he]
  calc
    _ ≤ |(ell+1:ℝ)*phiReciprocal z^2*(1-phiReciprocal z)^ell|+
        |(m+1:ℝ)*phiReciprocal z^2*(1-phiReciprocal z)^m| := abs_sub _ _
    _ ≤ 2/(ell+2:ℝ)+2/(m+2:ℝ) := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      exact add_le_add h₁ h₂
    _ ≤ 4/(m+2:ℝ) := (add_le_add hd (le_refl _)).trans_eq (by ring)

private theorem second_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |secondCoefficient m ell z| ≤ 12/(m+2:ℝ) := by
  have hs : 0 ≤ phiReciprocal z := (inv_pos.mpr (phi_pos z)).le
  have hs1 : phiReciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have hq : 0 ≤ 1-phiReciprocal z := sub_nonneg.mpr hs1
  have h₁ := second_peak_bound (phiReciprocal z) hs hs1 m
  have h₂ := second_peak_bound (phiReciprocal z) hs hs1 ell
  have hd : 6/(ell+2:ℝ) ≤ 6/(m+2:ℝ) := by gcongr
  have he : secondCoefficient m ell z=
      (m:ℝ)*(m+1:ℝ)*phiReciprocal z^3*(1-phiReciprocal z)^(m-1)-
      (ell:ℝ)*(ell+1:ℝ)*phiReciprocal z^3*(1-phiReciprocal z)^(ell-1) := by unfold secondCoefficient;ring
  rw [he]
  calc
    _ ≤ |(m:ℝ)*(m+1:ℝ)*phiReciprocal z^3*(1-phiReciprocal z)^(m-1)|+
        |(ell:ℝ)*(ell+1:ℝ)*phiReciprocal z^3*(1-phiReciprocal z)^(ell-1)| := abs_sub _ _
    _ ≤ 6/(m+2:ℝ)+6/(ell+2:ℝ) := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      exact add_le_add h₁ h₂
    _ ≤ 12/(m+2:ℝ) := (add_le_add (le_refl _) hd).trans_eq (by ring)

private def realFiber (c : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem real_fiber_smooth (c : SourceCoordinateSlice → ℝ) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (realFiber c) := (Complex.ofRealCLM.contDiff.comp hc).smul contDiff_const
private theorem real_fiber_weight (c : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (realFiber c z) := (Commute.one_right (GaussFockWeights.weight w)).smul_right _
private theorem real_fiber_bound (c : SourceCoordinateSlice → ℝ) (C : ℝ) (hb : ∀ z,|c z| ≤ C)
    (z : SourceCoordinateSlice) (f : FockFiber) : ‖realFiber c z f‖ ≤ C*‖f‖ := by
  change ‖(c z:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _)

private def thetaCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ := (1/4)*
  (secondCoefficient m ell z*(phiReciprocal z-phiReciprocal z^3)-
    firstCoefficient m ell z*(58*phiReciprocal z+3*phiReciprocal z^3))
private def bandCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ := (1/4)*
  (secondCoefficient m ell z*(1-phiReciprocal z^2)-
    firstCoefficient m ell z*(60+phiReciprocal z^2)+phiDamping m ell z*(60+phiReciprocal z^2))

private theorem theta_smooth (m ell : ℕ) : ContDiff ℝ ∞ (thetaCoefficient m ell) :=
  contDiff_const.mul (((second_smooth m ell).mul (phi_reciprocal_smooth.sub (phi_reciprocal_smooth.pow 3))).sub
    ((first_smooth m ell).mul ((contDiff_const.mul phi_reciprocal_smooth).add
      (contDiff_const.mul (phi_reciprocal_smooth.pow 3)))))
private theorem band_smooth (m ell : ℕ) : ContDiff ℝ ∞ (bandCoefficient m ell) :=
  contDiff_const.mul ((((second_smooth m ell).mul (contDiff_const.sub (phi_reciprocal_smooth.pow 2))).sub
    ((first_smooth m ell).mul (contDiff_const.add (phi_reciprocal_smooth.pow 2)))).add
      ((phi_reciprocal_smooth.mul (phi_theta_profile_smooth m ell)).mul
        (contDiff_const.add (phi_reciprocal_smooth.pow 2))))

private theorem theta_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |thetaCoefficient m ell z| ≤ 64/(m+2:ℝ) := by
  have hs : 0 ≤ phiReciprocal z := (inv_pos.mpr (phi_pos z)).le
  have hs1 : phiReciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have h3 : phiReciprocal z^3 ≤ 1 := pow_le_one₀ hs hs1
  have hd : |phiReciprocal z-phiReciprocal z^3| ≤ 1 := abs_le.mpr ⟨by nlinarith [pow_nonneg hs 3],by nlinarith [pow_nonneg hs 3]⟩
  have hp : |58*phiReciprocal z+3*phiReciprocal z^3| ≤ 61 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith only [hs1,h3]
  have ha : |secondCoefficient m ell z*(phiReciprocal z-phiReciprocal z^3)| ≤ 12/(m+2:ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul (second_bound m ell hml z) hd (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hb : |firstCoefficient m ell z*(58*phiReciprocal z+3*phiReciprocal z^3)| ≤ 4/(m+2:ℝ)*61 := by
    rw [abs_mul]
    exact mul_le_mul (first_bound m ell hml z) hp (abs_nonneg _) (by positivity)
  unfold thetaCoefficient
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
  exact (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ha hb)) (by norm_num : (0:ℝ) ≤ 1/4)).trans_eq (by ring)

private theorem band_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |bandCoefficient m ell z| ≤ 80/(m+2:ℝ) := by
  have hs : 0 ≤ phiReciprocal z := (inv_pos.mpr (phi_pos z)).le
  have hs1 : phiReciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have h2 : phiReciprocal z^2 ≤ 1 := pow_le_one₀ hs hs1
  have hd : |1-phiReciprocal z^2| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg (phiReciprocal z)],by nlinarith [sq_nonneg (phiReciprocal z)]⟩
  have hp : |60+phiReciprocal z^2| ≤ 61 := by rw [abs_of_nonneg (by positivity)];linarith only [h2]
  have ha : |secondCoefficient m ell z*(1-phiReciprocal z^2)| ≤ 12/(m+2:ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul (second_bound m ell hml z) hd (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hb : |firstCoefficient m ell z*(60+phiReciprocal z^2)| ≤ 4/(m+2:ℝ)*61 := by
    rw [abs_mul]
    exact mul_le_mul (first_bound m ell hml z) hp (abs_nonneg _) (by positivity)
  have hc : |phiDamping m ell z*(60+phiReciprocal z^2)| ≤ 1/(m+2:ℝ)*61 := by
    rw [abs_mul]
    exact mul_le_mul (phi_window_bound m ell hml z) hp (abs_nonneg _) (by positivity)
  unfold bandCoefficient
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
  apply (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add ha hb)) hc)) (by norm_num : (0:ℝ) ≤ 1/4)).trans
  convert mul_le_mul_of_nonneg_right (by norm_num : (317/4:ℝ) ≤ 80)
    (by positivity : (0:ℝ) ≤ 1/(m+2:ℝ)) using 1 <;> ring

def thetaBounded (m ell : ℕ) (hml : m ≤ ell) : Op :=
  GaussBoundedMultiplier.extension (realFiber (thetaCoefficient m ell))
    (fun _ => (real_fiber_smooth _ (theta_smooth m ell)).contDiffAt)
    (fun z => real_fiber_weight _ z) (64/(m+2:ℝ)) (by positivity)
    (fun z => real_fiber_bound _ _ (theta_bound m ell hml) z)
def bandBounded (m ell : ℕ) (hml : m ≤ ell) : Op :=
  GaussBoundedMultiplier.extension (realFiber (bandCoefficient m ell))
    (fun _ => (real_fiber_smooth _ (band_smooth m ell)).contDiffAt)
    (fun z => real_fiber_weight _ z) (80/(m+2:ℝ)) (by positivity)
    (fun z => real_fiber_bound _ _ (band_bound m ell hml) z)

theorem original_phi_hessian_norm (m ell : ℕ) (hml : m ≤ ell) :
    ‖bandBounded m ell hml‖ ≤ 80/(m+2:ℝ) ∧ ‖thetaBounded m ell hml‖ ≤ 64/(m+2:ℝ) :=
  ⟨GaussBoundedMultiplier.extension_norm _ _ _ _ _ _,GaussBoundedMultiplier.extension_norm _ _ _ _ _ _⟩

private theorem geometric_point (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (((1-S)^n) f) z=((1-phiReciprocal z:ℝ):ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((1-S)^n) f) z-(phiReciprocal z:ℂ) • ((((1-S)^n) f) z)=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module


private theorem first_peak_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    phiFirstPeak m ell f z=
      (((ell+1:ℝ)*(1-phiReciprocal z)^ell-(m+1:ℝ)*(1-phiReciprocal z)^m):ℂ) • f z := by
  simp only [phiFirstPeak,LinearMap.sub_apply,LinearMap.smul_apply]
  change (ell+1:ℂ) • (((1-S)^ell) f) z-(m+1:ℂ) • (((1-S)^m) f) z=_
  rw [geometric_point,geometric_point]
  push_cast
  module

private theorem second_peak_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    phiSecondPeak m ell f z=(((m:ℝ)*(m+1:ℝ)*(1-phiReciprocal z)^(m-1)-
      (ell:ℝ)*(ell+1:ℝ)*(1-phiReciprocal z)^(ell-1)):ℂ) • f z := by
  simp only [phiSecondPeak,LinearMap.sub_apply,LinearMap.smul_apply]
  change ((m:ℂ)*(m+1:ℂ)) • ((((1-S)^(m-1)) f) z)-
    ((ell:ℂ)*(ell+1:ℂ)) • ((((1-S)^(ell-1)) f) z)=_
  rw [geometric_point,geometric_point]
  push_cast
  module

private theorem add_point (f g : QuantumTest) (z : SourceCoordinateSlice) : (f+g) z=f z+g z := rfl
private theorem sub_point (f g : QuantumTest) (z : SourceCoordinateSlice) : (f-g) z=f z-g z := rfl
private theorem smul_point (c : ℂ) (f : QuantumTest) (z : SourceCoordinateSlice) : (c • f) z=c • f z := rfl
private theorem inverse_point (f : QuantumTest) (z : SourceCoordinateSlice) :
    S f z=(phiReciprocal z:ℂ) • f z := rfl

private theorem theta_hessian_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    thetaHessian m ell f z=(thetaCoefficient m ell z:ℂ) • f z := by
  unfold thetaHessian
  simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,Module.End.mul_apply,
    add_point,sub_point,smul_point,first_peak_point,second_peak_point,inverse_power_apply]
  unfold thetaCoefficient firstCoefficient secondCoefficient
  push_cast
  module

private theorem band_hessian_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    bandHessian m ell f z=(bandCoefficient m ell z:ℂ) • f z := by
  have ht (q:QuantumTest) : phiThetaAction m ell q z=(phiThetaProfile m ell z:ℂ) • q z := by
    change ((Q^(m+1)) q) z-((Q^(ell+1)) q) z=_
    rw [geometric_point,geometric_point]
    unfold phiThetaProfile
    push_cast
    module
  unfold bandHessian
  change (1/4:ℂ) • ((phiSecondPeak m ell ((S^3-S^5) f)) z-
    (phiFirstPeak m ell (((60:ℂ) • S^2+S^4) f)) z+
    (phiThetaAction m ell (((60:ℂ) • S+S^3) f)) z)=_
  rw [second_peak_point,first_peak_point,ht]
  simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,
    add_point,sub_point,smul_point,inverse_power_apply,inverse_point]
  unfold bandCoefficient firstCoefficient secondCoefficient phiDamping
  push_cast
  module

/-- Both small Hessians are the actual source multipliers, on the original core. -/
theorem original_phi_hessian_bounded_core (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    bandBounded m ell hml (embed f)=embed (bandHessian m ell f) ∧
      thetaBounded m ell hml (embed f)=embed (thetaHessian m ell f) := by
  constructor
  · rw [bandBounded,GaussBoundedMultiplier.extension_core]
    congr 1
    apply DFunLike.ext
    intro z
    exact (band_hessian_point m ell f z).symm
  · rw [thetaBounded,GaussBoundedMultiplier.extension_core]
    congr 1
    apply DFunLike.ext
    intro z
    exact (theta_hessian_point m ell f z).symm


end LowEnergy.SourceClockPhiRadiusResponseHessian
