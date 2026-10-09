import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaQ8RadiusBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeHessian
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceRadiusHalfKinetic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockRadiusSourceGeometry
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaOperator GaussYukawaCoefficient GaussRadialMomentum
open GaussLiveMomentum GaussQuantumMultiplier SourcePhysicalKineticSquare SourceClockReflectedForm
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceLocalizedInverseFormPayment SourceClockYukawaRadialNativeDivergence SourceClockYukawaRadialNativeHessian
open SourceScalarDoubleCurrent
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Pa (a : ScalarIndex) : End := GaussMomentumAdjoint.adjoint (scalarDirection a)
attribute [local irreducible] scalarKinetic diagonalAction

private theorem inverse_radius_end : inverseAction*radiusAction=(1:End) := by
  apply LinearMap.ext
  exact inverse_radius_action

private theorem radius_inverse_end : radiusAction*inverseAction=(1:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change radius z • ((reciprocal z:ℂ)*f z word)=f z word
  rw [Complex.real_smul]
  have hr : (radius z:ℂ)≠0 := by exact_mod_cast (radius_pos z).ne'
  simp only [reciprocal,Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ hr,one_mul]

private theorem real_multiply (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val) (f : QuantumTest) :
    (multiply a smooth f : SourceCoordinateSlice → FockFiber)=(fun z => a z • f z) := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem native_multiplier (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (zeroDerivative : ∀ z : physicalChart, ∀ v : Ambient, fderiv ℝ a z.val (direction v z.val)=0)
    (v : Ambient) : Commute (covariantMomentum v) (multiply a smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hd : directional v (multiply a smooth f) z=a z • directional v f z := by
      rw [directional_apply,real_multiply,
        fderiv_fun_smul ((smooth ⟨z,hz⟩).differentiableAt (by simp))
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change a z • fderiv ℝ f z (direction v z)+fderiv ℝ a z (direction v z) • f z=_
      rw [zeroDerivative ⟨z,hz⟩ v,zero_smul,add_zero]
      rfl
    change (-Complex.I) • (directional v (multiply a smooth f) z+
      connection v z ((a z : ℂ) • f z))=
      (a z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))
    rw [hd,map_smul]
    have hr (p : FockFiber) : a z • p=(a z : ℂ) • p := by
      apply PiLp.ext;intro word;exact Complex.real_smul
    rw [hr,←smul_add,smul_comm]
  · have hl : covariantMomentum v (multiply a smooth f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((covariantMomentum v (multiply a smooth f)).tsupport_subset h))
    have hr : multiply a smooth (covariantMomentum v f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((multiply a smooth (covariantMomentum v f)).tsupport_subset h))
    exact hl.trans hr.symm

private theorem root_native (v : Ambient) : Commute (covariantMomentum v) inverseRootAction :=
  native_multiplier inverseRootVolume inverse_root_volume_smooth inverse_root_native_derivative v

private theorem weight_pair (p q : QuantumTest) :
    sourcePair p (multiply scalarWeight scalarWeight_smooth q)=
      (-(sourceTime 0 : ℂ))*sourcePair (inverseRootAction p) (inverseRootAction q) := by
  have he : multiply scalarWeight scalarWeight_smooth q=(-(sourceTime 0 : ℂ)) • inverseVolumeAction q := by
    apply DFunLike.ext
    intro z
    change (scalarWeight z : ℂ) • q z=(-(sourceTime 0 : ℂ)) • ((reciprocalVolume z : ℂ) • q z)
    rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
    congr 1
  rw [he,←inverse_root_square]
  have hp : sourcePair p (inverseRootAction (inverseRootAction q))=
    sourcePair (inverseRootAction p) (inverseRootAction q) := multiply_pair _ _ _ _
  simpa only [sourcePair,map_smul,inner_smul_right] using congrArg (fun c : ℂ => -(sourceTime 0 : ℂ)*c) hp

private theorem inverse_commutator {R : Type*} [Ring R] (P S r C : R)
    (hs : S*r=1) (hr : r*S=1) (hc : bracket P S=C) : bracket P r= -(r*C*r) := by
  have h1 : r*P*S*r=r*P := by
    calc _=r*P*(S*r) := by noncomm_ring
         _=_ := by rw [hs,mul_one]
  have h2 : r*S*P*r=P*r := by rw [hr,one_mul]
  calc
    _= -(r*P*S*r-r*S*P*r) := by rw [h1,h2];unfold bracket;abel
    _= -(r*bracket P S*r) := by unfold bracket;noncomm_ring
    _=_ := by rw [hc]

private theorem real_radius (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) radiusAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (c z:ℂ)*(radius z • f z word)=radius z • ((c z:ℂ)*f z word)
  simp only [Complex.real_smul]
  ring

private theorem radius_contact (a : ScalarIndex) :
    -(radiusAction*commutatorAction (scalarDirection a)*radiusAction)=Complex.I • directionAction a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change -(radius z • (((-Complex.I)*(radialDerivative (scalarDirection a) z:ℂ))*(radius z • f z word)))=
    Complex.I*((directionWeight a z:ℂ)*f z word)
  simp only [Complex.real_smul,radialDerivative,directionWeight,scalarDirection]
  push_cast
  field_simp [(radius_pos z).ne']

private theorem native_radius (a : ScalarIndex) : bracket (P a) radiusAction=Complex.I • directionAction a := by
  have h : bracket (P a) inverseAction=commutatorAction (scalarDirection a) := by
    apply LinearMap.ext
    intro f
    change P a (inverseAction f)-inverseAction (P a f)=_
    rw [core_commutator,add_sub_cancel_left]
  exact (inverse_commutator _ _ _ _ inverse_radius_end radius_inverse_end h).trans (radius_contact a)

private theorem adjoint_radius (a : ScalarIndex) : bracket (Pa a) radiusAction=Complex.I • directionAction a := by
  have h : bracket (Pa a) inverseAction=commutatorAction (scalarDirection a) := by
    apply LinearMap.ext
    intro f
    change Pa a (inverseAction f)-inverseAction (Pa a f)=_
    rw [GaussRadialMomentumDomain.adjoint_core_commutator,add_sub_cancel_left]
  exact (inverse_commutator _ _ _ _ inverse_radius_end radius_inverse_end h).trans (radius_contact a)

/-- All seventy original native columns and their actual density transposes remain present. -/
def radiusCurrent : End := (Complex.I/2:ℂ) • ∑ a : ScalarIndex,
  (Pa a*W*directionAction a+directionAction a*W*P a)

theorem original_radius_scalar_current : bracket scalarKinetic radiusAction=radiusCurrent := by
  have hs (a : ScalarIndex) : bracket (Pa a*(W*P a)) radiusAction=
      Complex.I • (Pa a*W*directionAction a+directionAction a*W*P a) := by
    have hw := (real_radius scalarWeight scalarWeight_smooth).eq
    have he : bracket (Pa a*(W*P a)) radiusAction=
        Pa a*W*bracket (P a) radiusAction+bracket (Pa a) radiusAction*W*P a := by
      unfold bracket
      linear_combination (norm := noncomm_ring) Pa a*hw*P a
    rw [he,native_radius,adjoint_radius]
    simp only [mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc]
  unfold scalarKinetic sandwich radiusCurrent
  simp only [←Module.End.mul_eq_comp,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,
    Finset.mul_sum,←Finset.sum_sub_distrib,←smul_sub]
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => hs a)
  simp only [bracket] at h
  rw [h,←Finset.smul_sum,smul_smul]
  congr 1
  ring

private theorem commute_inverse {R : Type*} [Ring R] (A S r : R)
    (hs : S*r=1) (hr : r*S=1) (h : Commute A S) : Commute A r := by
  have hb : bracket A S=0 := sub_eq_zero.mpr h.eq
  have hc := inverse_commutator A S r 0 hs hr hb
  change A*r=r*A
  simpa only [bracket,mul_zero,zero_mul,neg_zero,sub_eq_zero] using hc

theorem original_radius_nonscalar_commute : Commute (diagonalAction-scalarKinetic) radiusAction := by
  have h : Commute (diagonalAction-scalarKinetic) inverseAction := by
    change (diagonalAction-scalarKinetic)*inverseAction=inverseAction*(diagonalAction-scalarKinetic)
    have hd := GaussRadialHamiltonian.diagonal_commutator
    have hs := GaussRadialHamiltonian.scalar_commutator
    linear_combination (norm := noncomm_ring) hd-hs
  exact commute_inverse _ _ _ inverse_radius_end radius_inverse_end h

theorem original_radius_hamiltonian_current : bracket diagonalAction radiusAction=radiusCurrent := by
  have h := original_radius_nonscalar_commute.eq
  have hs := original_radius_scalar_current
  unfold bracket at h hs ⊢
  linear_combination (norm := noncomm_ring) h+hs

private theorem direction_root (a : ScalarIndex) : Commute (directionAction a) inverseRootAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (directionWeight a z:ℂ) (inverseRootVolume z:ℂ) (f z)

private theorem current_pair (p q : QuantumTest) : sourcePair p (radiusCurrent q)=
    (-Complex.I*(sourceTime 0:ℂ)/2)*∑ a : ScalarIndex,
      (sourcePair (P a (inverseRootAction p)) (directionAction a (inverseRootAction q))+
        sourcePair (directionAction a (inverseRootAction p)) (P a (inverseRootAction q))) := by
  have hP (a : ScalarIndex) (f : QuantumTest) :
      inverseRootAction (P a f)=P a (inverseRootAction f) :=
    (LinearMap.congr_fun (root_native (scalarDirection a)).eq f).symm
  have hd (a : ScalarIndex) (f : QuantumTest) :
      inverseRootAction (directionAction a f)=directionAction a (inverseRootAction f) :=
    (LinearMap.congr_fun (direction_root a).eq f).symm
  have hs (a : ScalarIndex) : sourcePair p ((Pa a*W*directionAction a+directionAction a*W*P a) q)=
      (-(sourceTime 0:ℂ))*(sourcePair (P a (inverseRootAction p)) (directionAction a (inverseRootAction q))+
        sourcePair (directionAction a (inverseRootAction p)) (P a (inverseRootAction q))) := by
    change sourcePair p (Pa a (W (directionAction a q))+directionAction a (W (P a q)))=_
    simp only [sourcePair,map_add,inner_add_right]
    change sourcePair p (Pa a (W (directionAction a q)))+sourcePair p (directionAction a (W (P a q)))=_
    have hdp : sourcePair p (directionAction a (W (P a q)))=sourcePair (directionAction a p) (W (P a q)) :=
      GaussNativeForm.multiply_pair _ _ p _
    rw [GaussNativeForm.adjoint_pair,hdp,weight_pair,weight_pair,hP,hd,hd,hP]
    simp only [sourcePair]
    ring
  simp only [radiusCurrent,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  change (Complex.I/2:ℂ)*(∑ a : ScalarIndex,sourcePair p ((Pa a*W*directionAction a+directionAction a*W*P a) q))=_
  simp_rw [hs]
  rw [←Finset.mul_sum]
  simp only [sourcePair]
  ring

private theorem gradient_energy (f : QuantumTest) :
    (∑ a : ScalarIndex,‖embed (directionAction a f)‖^2) ≤ (1/4:ℝ)*‖embed f‖^2 := by
  have h := original_direction_energy (embed f)
  simp only [original_direction_core] at h
  nlinarith only [h,sq_nonneg ‖inverseRadius (embed f)‖]

private theorem young (x y δ : ℝ) (hδ : 0<δ) : x*y ≤ δ*x^2+y^2/(4*δ) := by
  have h := sq_nonneg (2*δ*x-y)
  have he : δ*x^2+y^2/(4*δ)=(4*δ^2*x^2+y^2)/(4*δ) := by
    field_simp
  rw [he]
  apply (le_div_iff₀ (by positivity : 0<4*δ)).mpr
  nlinarith only [h]

private theorem column_pair_price (p q : QuantumTest) (δ : ℝ) (hδ : 0<δ) :
    (∑ a : ScalarIndex,‖sourcePair (P a p) (directionAction a q)‖) ≤
      δ*scalarForm p+‖embed q‖^2/(16*δ) := by
  have h (a : ScalarIndex) := (norm_inner_le_norm (𝕜 := ℂ) (embed (P a p))
    (embed (directionAction a q))).trans (young _ _ δ hδ)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => h a)
  change (∑ a : ScalarIndex,‖sourcePair (P a p) (directionAction a q)‖) ≤ _ at hs
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div] at hs
  have hg := div_le_div_of_nonneg_right (gradient_energy q) (by positivity : 0≤4*δ)
  apply hs.trans
  change δ*scalarForm p+(∑ a : ScalarIndex,‖embed (directionAction a q)‖^2)/(4*δ) ≤ _
  exact add_le_add le_rfl (hg.trans_eq (by ring))

/-- One finite source gradient Gram pays both native legs; there is no factor seventy or assumed moving native bound. -/
theorem original_radius_current_price (p q : QuantumTest) (δ : ℝ) (hδ : 0<δ) :
    ‖sourcePair p (radiusCurrent q)‖ ≤ (|sourceTime 0|/2)*
      (δ*(scalarForm (inverseRootAction p)+scalarForm (inverseRootAction q))+
        (‖embed (inverseRootAction p)‖^2+‖embed (inverseRootAction q)‖^2)/(16*δ)) := by
  have h1 := column_pair_price (inverseRootAction p) (inverseRootAction q) δ hδ
  have h2 := column_pair_price (inverseRootAction q) (inverseRootAction p) δ hδ
  have he (a : ScalarIndex) : ‖sourcePair (directionAction a (inverseRootAction p)) (P a (inverseRootAction q))‖=
      ‖sourcePair (P a (inverseRootAction q)) (directionAction a (inverseRootAction p))‖ := by
    exact norm_inner_symm _ _
  have hn : ‖-Complex.I*(sourceTime 0:ℂ)/2‖=|sourceTime 0|/2 := by
    simp only [norm_div,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
      one_mul]
    norm_num
  rw [current_pair,norm_mul,hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ a : ScalarIndex,‖sourcePair (P a (inverseRootAction p)) (directionAction a (inverseRootAction q))+
      sourcePair (directionAction a (inverseRootAction p)) (P a (inverseRootAction q))‖ := norm_sum_le _ _
    _ ≤ (∑ a : ScalarIndex,‖sourcePair (P a (inverseRootAction p)) (directionAction a (inverseRootAction q))‖)+
      ∑ a : ScalarIndex,‖sourcePair (P a (inverseRootAction q)) (directionAction a (inverseRootAction p))‖ := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      exact (norm_add_le _ _).trans_eq (by rw [he])
    _ ≤ _ := (add_le_add h1 h2).trans_eq (by ring)

/-- The real native coefficient keeps the entire independent adjoint and density response. -/
def radiusZeroCore (a : ScalarIndex) : End := directionAction a*W*P a-Pa a*W*directionAction a

private theorem radius_column (a : ScalarIndex) : radiusAction^2*inverseCoefficientCore a=directionAction a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change radius z • (radius z • ((directionWeight a z:ℂ)*((reciprocal z:ℂ)*((reciprocal z:ℂ)*f z word))))=
    (directionWeight a z:ℂ)*f z word
  simp only [Complex.real_smul,reciprocal,Complex.ofReal_inv]
  have hr : (radius z:ℂ)≠0 := by exact_mod_cast (radius_pos z).ne'
  field_simp

private theorem radius_cross (a : ScalarIndex) : radiusAction*directionAction a*W*inverseCoefficientCore a=
    W*inverseAction*(directionAction a*directionAction a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change radius z • ((directionWeight a z:ℂ)*((scalarWeight z:ℂ)*
      ((directionWeight a z:ℂ)*((reciprocal z:ℂ)*((reciprocal z:ℂ)*f z word)))))=
    (scalarWeight z:ℂ)*((reciprocal z:ℂ)*((directionWeight a z:ℂ)*((directionWeight a z:ℂ)*f z word)))
  simp only [Complex.real_smul,reciprocal,Complex.ofReal_inv]
  have hr : (radius z:ℂ)≠0 := by exact_mod_cast (radius_pos z).ne'
  field_simp

private theorem native_radius_square (a : ScalarIndex) :
    bracket (Pa a) (radiusAction^2)=(2*Complex.I:ℂ) • (radiusAction*directionAction a) := by
  have hc : Commute (directionAction a) radiusAction := by unfold directionAction;exact real_radius _ _
  have he : bracket (Pa a) (radiusAction^2)=bracket (Pa a) radiusAction*radiusAction+
      radiusAction*bracket (Pa a) radiusAction := by unfold bracket;noncomm_ring
  rw [he,adjoint_radius]
  simp only [smul_mul_assoc,mul_smul_comm]
  rw [hc.eq]
  module

private theorem radius_zero_return (a : ScalarIndex) : radiusZeroCore a=
    radiusAction^2*inverseZeroCore a-(2*Complex.I:ℂ) •
      (radiusAction*directionAction a*W*inverseCoefficientCore a) := by
  have hW := ((real_radius scalarWeight scalarWeight_smooth).pow_right 2).eq
  have he : radiusZeroCore a=radiusAction^2*inverseDivergenceCoefficient a-
      bracket (Pa a) (radiusAction^2)*W*inverseCoefficientCore a := by
    unfold radiusZeroCore inverseDivergenceCoefficient
    rw [←radius_column a]
    unfold bracket
    linear_combination (norm := noncomm_ring) -Pa a*hW*inverseCoefficientCore a
  rw [he,original_inverse_native_divergence,native_radius_square]
  simp only [smul_mul_assoc,mul_assoc]

private theorem direction_square_end : (∑ a : ScalarIndex,directionAction a*directionAction a)=
    (1/4:ℂ) • ((1:End)-inverseAction^2) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,
    Module.End.one_apply,pow_two,sum_apply]
  change (∑ a : ScalarIndex,(directionWeight a z:ℂ) • ((directionWeight a z:ℂ) • f z))=
    (1/4:ℂ) • (f z-(reciprocal z:ℂ) • ((reciprocal z:ℂ) • f z))
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [original_direction_square]
  have he : (((1-(reciprocal z)^2)/4:ℝ):ℂ)=(1/4:ℂ)-(1/4:ℂ)*(reciprocal z:ℂ)^2 := by push_cast;ring
  rw [he]
  module

private theorem weight_inverse : W=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  simp only [scalarWeight,reciprocalVolume,smul_smul,div_eq_mul_inv,Complex.ofReal_mul,
    Complex.ofReal_neg,Complex.ofReal_inv]

private theorem radius_inverse_square : radiusAction^2*inverseAction^2=(1:End) := by
  simp only [pow_two]
  calc _=radiusAction*(radiusAction*inverseAction)*inverseAction := by noncomm_ring
       _=_ := by rw [radius_inverse_end,mul_one,radius_inverse_end]

private theorem radius_inverse_power (n : ℕ) : radiusAction^2*inverseAction^(n+2)=inverseAction^n := by
  rw [show n+2=2+n by omega,pow_add,←mul_assoc,radius_inverse_square,one_mul]

/-- The inherited true scalar61 transpose contracts the complete radius Hessian into 60S+S³. -/
theorem original_radius_hessian_source : (∑ a : ScalarIndex,radiusZeroCore a)=
    (Complex.I*(sourceTime 0:ℂ)/4) •
      (inverseVolumeAction*((60:ℂ) • inverseAction+inverseAction^3)) := by
  have hu : Commute inverseVolumeAction radiusAction := by unfold inverseVolumeAction;exact real_radius _ _
  have hp : radiusAction^2*(inverseVolumeAction*((58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5))=
      inverseVolumeAction*((58:ℂ) • inverseAction+(3:ℂ) • inverseAction^3) := by
    rw [←mul_assoc,(hu.pow_right 2).symm.eq,mul_assoc,mul_add]
    simp only [mul_smul_comm]
    have h3 : radiusAction^2*inverseAction^3=inverseAction := by simpa using radius_inverse_power 1
    have h5 : radiusAction^2*inverseAction^5=inverseAction^3 := by simpa using radius_inverse_power 3
    rw [h3,h5]
  simp_rw [radius_zero_return,radius_cross]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.smul_sum,←Finset.mul_sum,
    original_inverse_hessian_source,direction_square_end,weight_inverse]
  simp only [mul_smul_comm,smul_mul_assoc,smul_smul]
  rw [hp]
  have hs : inverseAction*((1:End)-inverseAction^2)=inverseAction-inverseAction^3 := by
    rw [mul_sub,mul_one,←pow_succ']
  have hs' : inverseVolumeAction*inverseAction*((1:End)-inverseAction^2)=
      inverseVolumeAction*(inverseAction-inverseAction^3) := by rw [mul_assoc,hs]
  rw [hs']
  simp only [mul_sub,mul_add,mul_smul_comm,smul_add,smul_sub,smul_smul]
  module

end LowEnergy.SourceClockRadiusSourceGeometry
