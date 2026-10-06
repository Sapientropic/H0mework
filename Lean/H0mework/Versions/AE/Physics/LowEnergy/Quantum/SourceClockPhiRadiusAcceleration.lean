import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiSecondBulk
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusSourceCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarInverseRetardedBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeHamiltonianForceReduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusAcceleration
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussNativePotential GaussNativeMatter
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceHamiltonianVolume
open SourceScalarRadialContact SourceScalarFlatJoint SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarPairedTransport
open SourceScalarPositiveBulkWard SourceClockPhiRadiusSourceCurrent SourceScalarDoubleCurrent
open SourceGaugeRadialCurrent SourceGaugeRadialPair
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev P (a : ScalarIndex) := covariantMomentum (scalarDirection a)
private abbrev Pa (a : ScalarIndex) := GaussMomentumAdjoint.adjoint (scalarDirection a)
private abbrev W : End := multiply scalarWeight scalarWeight_smooth

def phiSquare : End := phiRadiusAction^2
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
private theorem gauge_pair (f g : QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
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

private theorem direction_radius (a : ScalarIndex) :
    phiDirectionAction (scalarBasis a)*phiRadiusAction=(-1/4:ℂ) • phiColumn a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (phiDirectionWeight (scalarBasis a) z:ℂ) • ((phiRadius z:ℂ) • f z)=
    (-1/4:ℂ) • ((inner ℝ (scalarField z) (scalarBasis a):ℂ) • f z)
  simp only [smul_smul]
  congr 1
  unfold phiDirectionWeight
  have hp : 0<phiRadius z := Real.sqrt_pos.2 (by positivity)
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hp.ne']

private theorem real_radius (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) phiRadiusAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) (phiRadius z:ℂ) (f z)

private theorem native_square (a : ScalarIndex) :
    bracket (P a) phiSquare=(-Complex.I/2:ℂ) • phiColumn a ∧
    bracket (Pa a) phiSquare=(-Complex.I/2:ℂ) • phiColumn a := by
  have step (A : End) (h : bracket A phiRadiusAction=Complex.I • phiDirectionAction (scalarBasis a)) :
      bracket A phiSquare=(-Complex.I/2:ℂ) • phiColumn a := by
    have he : bracket A phiSquare=bracket A phiRadiusAction*phiRadiusAction+
        phiRadiusAction*bracket A phiRadiusAction := by unfold bracket phiSquare;noncomm_ring
    have hd : Commute (phiDirectionAction (scalarBasis a)) phiRadiusAction := real_radius _ _
    rw [he,h,smul_mul_assoc,mul_smul_comm,←hd.eq,direction_radius]
    simp only [smul_smul,←add_smul]
    congr 1
    ring
  exact ⟨step _ (original_phi_radius_native_jet (scalarDirection a)).1,
    step _ (original_phi_radius_native_jet (scalarDirection a)).2⟩

private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hu : inverseVolumeAction*volumeAction=(1:End) :=
    (real_volume _ _).eq.trans (LinearMap.ext volume_inverse)
  have hv : volumeAction*inverseVolumeAction=(1:End) := LinearMap.ext volume_inverse
  change A*inverseVolumeAction=inverseVolumeAction*A
  have h1 := congrArg (fun T : End => inverseVolumeAction*T*inverseVolumeAction) h.eq
  simp only [mul_assoc,hv,mul_one] at h1
  simpa only [←mul_assoc,hu,one_mul] using h1.symm

private theorem weight_inverse : W=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

/-- The literal full-field radius square closes on the source affine generator. -/
theorem original_phi_square_current :
    bracket diagonalAction phiSquare=(sourceTime 0/2:ℂ) • (inverseVolumeAction*Phi) := by
  have hs (a : ScalarIndex) : bracket (Pa a*(W*P a)) phiSquare=
      (-Complex.I/2:ℂ) • (Pa a*W*phiColumn a+phiColumn a*W*P a) := by
    have hw : Commute W phiSquare := (real_radius _ _).pow_right 2
    have he : bracket (Pa a*(W*P a)) phiSquare=
        Pa a*W*bracket (P a) phiSquare+bracket (Pa a) phiSquare*W*P a := by
      unfold bracket
      linear_combination (norm:=noncomm_ring) Pa a*hw.eq*P a
    rw [he,(native_square a).1,(native_square a).2]
    simp only [mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc]
  have hk : bracket scalarKinetic phiSquare=(-Complex.I/4:ℂ) •
      ∑ a : ScalarIndex,(Pa a*W*phiColumn a+phiColumn a*W*P a) := by
    unfold scalarKinetic sandwich
    simp only [←Module.End.mul_eq_comp,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,
      Finset.mul_sum,←Finset.sum_sub_distrib,←smul_sub]
    have h := Finset.sum_congr (s₁:=Finset.univ) rfl (fun a _=>hs a)
    simp only [bracket] at h
    rw [h,←Finset.smul_sum,smul_smul]
    congr 1
    ring
  have hr : (∑ a : ScalarIndex,(Pa a*W*phiColumn a+phiColumn a*W*P a))=
      (-(sourceTime 0:ℂ)) • (inverseVolumeAction*(phiAdjoint+phiMomentum)) := by
    rw [weight_inverse]
    simp only [mul_smul_comm,smul_mul_assoc,←smul_add,←Finset.smul_sum]
    congr 1
    have hPa (a : ScalarIndex) := (inverse_commute _ (native_adjoint_volume (scalarDirection a))).eq
    have hCol (a : ScalarIndex) : Commute (phiColumn a) inverseVolumeAction := by
      unfold phiColumn inverseVolumeAction
      apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
      exact smul_comm (inner ℝ (scalarField z) (scalarBasis a):ℂ) (reciprocalVolume z:ℂ) (f z)
    have ht (a : ScalarIndex) :
        Pa a*inverseVolumeAction*phiColumn a+phiColumn a*inverseVolumeAction*P a=
        inverseVolumeAction*(Pa a*phiColumn a+phiColumn a*P a) := by
      rw [hPa a,(hCol a).eq]
      noncomm_ring
    simp only [ht,←Finset.mul_sum,Finset.sum_add_distrib,phiAdjoint,phiMomentum]
  have hn : bracket diagonalAction phiSquare=bracket scalarKinetic phiSquare := by
    have h := (original_phi_radius_non_scalar_commute.2.2.2.pow_right 2).eq
    change (diagonalAction-scalarKinetic)*phiSquare=phiSquare*(diagonalAction-scalarKinetic) at h
    unfold bracket
    linear_combination (norm:=noncomm_ring) h
  have hphi : phiAdjoint+phiMomentum=(-2*Complex.I:ℂ) • Phi := by
    rw [phi_adjoint_contraction,phi_native_contraction]
    change _=(-2*Complex.I:ℂ) • (phiEulerAction+(61/2:ℂ) • 1)
    module
  rw [hn,hk,hr,hphi,mul_smul_comm,smul_smul,smul_smul]
  have hI : (-Complex.I/4:ℂ)*(-(sourceTime 0:ℂ))*(-2*Complex.I)=(sourceTime 0/2:ℂ) := by
    calc _= -((Complex.I*Complex.I)*(sourceTime 0:ℂ))/2 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hI]

private theorem hamiltonian_phi_source :
    deltaPhi diagonalAction=(-2:ℂ) • scalarKinetic+(2:ℂ) • centeredAction-
      (2:ℂ) • vacuumLinearAction+(2:ℂ) • scalarSpatialAction := by
  have h := original_scalar_gauge_current
  rw [SourceInverseHamiltonianForceReduction.original_hamiltonian_gauge_source] at h
  linear_combination (norm:=module) h

/-- The source coframe current is kept with its two genuine inverse-volume factors. -/
def clockAcceleration : End := (3*Complex.I*(sourceTime 0:ℂ)^2/8) •
  (inverseVolumeAction*SourceCoframeVolumeCurrent.dilation*inverseVolumeAction*Phi)
def scalarAcceleration : End := (sourceTime 0:ℂ) •
  (inverseVolumeAction*(-scalarKinetic+centeredAction-vacuumLinearAction))
def stableSpatialAcceleration : End := (sourceTime 0:ℂ) • (inverseVolumeAction*scalarSpatialAction)

theorem original_phi_square_acceleration :
    -bracket diagonalAction (bracket diagonalAction phiSquare)=
      scalarAcceleration+stableSpatialAcceleration-clockAcceleration := by
  rw [original_phi_square_current]
  have h : bracket diagonalAction (inverseVolumeAction*Phi)=
      bracket diagonalAction inverseVolumeAction*Phi+inverseVolumeAction*bracket diagonalAction Phi := by
    unfold bracket
    noncomm_ring
  have hu : bracket diagonalAction inverseVolumeAction=
      (3*Complex.I*(sourceTime 0:ℂ)/4) •
        (inverseVolumeAction*SourceCoframeVolumeCurrent.dilation*inverseVolumeAction) :=
    SourceScalarInverseRetardedBudget.original_inverse_current
  have hp : bracket diagonalAction Phi= -deltaPhi diagonalAction := by
    rw [←SourceScalarAffineScaleTransport.generator_commutator]
    unfold bracket
    abel
  have hs : bracket diagonalAction ((sourceTime 0/2:ℂ) • (inverseVolumeAction*Phi))=
      (sourceTime 0/2:ℂ) • bracket diagonalAction (inverseVolumeAction*Phi) := by
    unfold bracket
    simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
  rw [hs,h,hu,hp,hamiltonian_phi_source]
  unfold scalarAcceleration stableSpatialAcceleration clockAcceleration
  simp only [smul_mul_assoc,mul_smul_comm,mul_add,mul_sub,mul_neg,smul_add,smul_sub,smul_neg,smul_smul]
  module

/-- All three double-current defect terms are from this exact compression. -/
def accelerationDefect (F : Index) : End :=
  bracket diagonalAction (bracket (defectAction F) phiSquare)+
    bracket (defectAction F) (bracket diagonalAction phiSquare)-
    bracket (defectAction F) (bracket (defectAction F) phiSquare)

theorem actual_phi_square_acceleration (F : Index) :
    -bracket (compressionCore F) (bracket (compressionCore F) phiSquare)=
      scalarAcceleration+stableSpatialAcceleration-clockAcceleration+accelerationDefect F := by
  rw [←original_phi_square_acceleration]
  unfold accelerationDefect defectAction bracket
  noncomm_ring

private theorem metric_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → E) :
    (∑ i : Fin 3,∑ j : Fin 3,(A*A.transpose) i j*inner ℝ (b i) (b j))=
      ∑ k : Fin 3,‖∑ i : Fin 3,A i k • b i‖^2 := by
  simp only [←real_inner_self_eq_norm_sq,Matrix.mul_apply,Matrix.transpose_apply]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  simp only [Fin.sum_univ_three]
  ring

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem scalar_multiplier_sign (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sign : ℝ)
    (hs : ∀ z : physicalChart,0 ≤ sign*c z.val) (f : QuantumTest) :
    0 ≤ sign*(sourcePair f (multiply c hc f)).re := by
  rw [sourcePair_integral]
  have hr : (∫ z, densityPair f (multiply c hc f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫ z, (densityPair f (multiply c hc f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only using! (integral_re (densityPair_integrable f (multiply c hc f))).symm
  rw [hr,←MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_nonneg
  intro z
  change 0 ≤ sign*(densityPair f (multiply c hc f) z).re
  have he : densityPair f (multiply c hc f) z=(c z : ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  by_cases hz : z∈physicalChart
  · have hp : 0 ≤ (densityPair f f z).re := by
      change 0 ≤ (inner ℂ (GaussFockWeights.weight (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z)).re
      have hw := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
        (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
      have hp := (sq_nonneg ‖GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z) (f z)‖).trans_eq hw.symm
      simpa only using! hp
    simpa only [mul_assoc] using mul_nonneg (hs ⟨z,hz⟩) hp
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,mul_zero]
    exact le_refl _

private theorem spatial_pair_nonpositive (f : QuantumTest) :
    (sourcePair f (scalarSpatialAction f)).re ≤ 0 := by
  have h : 0 ≤ (-1:ℝ)*(sourcePair f (scalarSpatialAction f)).re := by
    unfold scalarSpatialAction
    apply scalar_multiplier_sign
    intro z
    change 0 ≤ (-1:ℝ)*(-(sourceTime 0*volume z.val/2 *
      ∑ i : Fin 3,∑ j : Fin 3,inverseSpatial z.val i j*
        inner ℝ (scalarGradient z.val i) (scalarGradient z.val j)))
    rw [inverseSpatial,metric_square]
    have hs : 0 ≤ (∑ k : Fin 3,‖∑ i : Fin 3,triadInverse z.val.1 i k • scalarGradient z.val i‖^2) :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hc := mul_nonneg (div_nonneg (mul_nonneg lapse_pos.le (volume_pos z).le) (show 0 ≤ (2:ℝ) by norm_num)) hs
    linarith
  linarith

/-- The complete signed spatial potential stabilizes the radial acceleration. -/
theorem original_spatial_acceleration_nonpositive (f : QuantumTest) :
    (sourcePair f (stableSpatialAcceleration f)).re ≤ 0 := by
  have hp : sourcePair f ((inverseVolumeAction*scalarSpatialAction) f)=
      sourcePair (inverseRootAction f) (scalarSpatialAction (inverseRootAction f)) := by
    change sourcePair f (inverseVolumeAction (scalarSpatialAction f))=_
    rw [←inverse_root_square]
    have hroot (p q : QuantumTest) : sourcePair p (inverseRootAction q)=sourcePair (inverseRootAction p) q :=
      multiply_pair inverseRootVolume inverse_root_volume_smooth p q
    rw [hroot]
    have hcomm : Commute inverseRootAction scalarSpatialAction :=
      SourcePhysicalHamiltonianSquare.inverse_root_real _ _
    have hc := LinearMap.congr_fun hcomm.eq f
    change inverseRootAction (scalarSpatialAction f)=scalarSpatialAction (inverseRootAction f) at hc
    rw [hc]
  have hn := spatial_pair_nonpositive (inverseRootAction f)
  unfold stableSpatialAcceleration
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]
  change ((sourceTime 0:ℂ)*sourcePair f ((inverseVolumeAction*scalarSpatialAction) f)).re ≤ 0
  rw [hp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonpos_of_nonneg_of_nonpos lapse_pos.le hn

/-- Same F retains the whole double defect while the source spatial term pays its own sign. -/
theorem actual_phi_response_acceleration_upper (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    let f := SourceClockRadiusAffineCutoff.phiResponseCore m ell F z hz g
    (sourcePair f ((-bracket (compressionCore F) (bracket (compressionCore F) phiSquare)) f)).re ≤
      (sourcePair f ((scalarAcceleration-clockAcceleration+accelerationDefect F) f)).re := by
  dsimp only
  rw [actual_phi_square_acceleration]
  have hs := original_spatial_acceleration_nonpositive
    (SourceClockRadiusAffineCutoff.phiResponseCore m ell F z hz g)
  simp only [LinearMap.add_apply,LinearMap.sub_apply,sourcePair,map_add,map_sub,inner_add_right,
    inner_sub_right,Complex.add_re,Complex.sub_re] at hs ⊢
  linarith

end LowEnergy.SourceClockPhiRadiusAcceleration
