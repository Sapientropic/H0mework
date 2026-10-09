import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiSecondBulk
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeEnergy
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockReflectedForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiSecondPressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussNativePotential
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourcePhysicalHamiltonianSquare
open SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarPairedTransport SourceClockRadiusAffineCutoff
open SourceClockPhiSecondBulk SourceScalarInverseNativeEnergy SourceClockReflectedForm
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

/-- The inverse-volume weight is part of the original source pairing. -/
def pressure (f : QuantumTest) : ℝ :=
  (sourcePair (inverseRootAction f) (secondBulk (inverseRootAction f))).re

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

private theorem scalar_root_form (f : QuantumTest) :
    (sourcePair (inverseRootAction f) (scalarKinetic (inverseRootAction f))).re=
      -(sourceTime 0/2)*scalarForm (inverseVolumeAction f) := by
  have hrow (a : ScalarIndex) :
      sourcePair (inverseRootAction f)
        (sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth (inverseRootAction f))=
      (-(sourceTime 0 : ℂ))*sourcePair
        (covariantMomentum (scalarDirection a) (inverseVolumeAction f))
        (covariantMomentum (scalarDirection a) (inverseVolumeAction f)) := by
    change sourcePair (inverseRootAction f) (GaussMomentumAdjoint.adjoint (scalarDirection a)
      (multiply scalarWeight scalarWeight_smooth (covariantMomentum (scalarDirection a) (inverseRootAction f))))=_
    rw [adjoint_pair,weight_pair]
    have hc := LinearMap.congr_fun (root_native (scalarDirection a)).eq (inverseRootAction f)
    change covariantMomentum (scalarDirection a) (inverseRootAction (inverseRootAction f))=
      inverseRootAction (covariantMomentum (scalarDirection a) (inverseRootAction f)) at hc
    rw [inverse_root_square] at hc
    rw [←hc]
  have h : sourcePair (inverseRootAction f) (scalarKinetic (inverseRootAction f))=
      (1/2 : ℂ)*∑ a : ScalarIndex,(-(sourceTime 0 : ℂ))*sourcePair
        (covariantMomentum (scalarDirection a) (inverseVolumeAction f))
        (covariantMomentum (scalarDirection a) (inverseVolumeAction f)) := by
    simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,
      map_smul,map_sum,inner_smul_right,inner_sum]
    exact congrArg (fun x : ℂ => (1/2 : ℂ)*x) (Finset.sum_congr rfl (fun a _ => hrow a))
  rw [h]
  have hs (q : QuantumTest) : sourcePair q q=(‖embed q‖^2 : ℂ) :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed q)
  simp only [hs,←Finset.mul_sum,←Complex.ofReal_pow,←Complex.ofReal_sum,
    Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_im,
    neg_zero,mul_zero,sub_zero]
  norm_num
  unfold scalarForm
  ring

/-- The two-jet source pays all seventy U-weighted rows and the true unweighted shifted field. -/
theorem original_second_pressure_energy (f : QuantumTest) :
    pressure f=sourceTime 0*scalarForm (inverseVolumeAction f)+
      6*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re+
      2*sourceTime 0*shiftedMoment f+
      12*(sourcePair (inverseRootAction f) (magneticAction (inverseRootAction f))).re := by
  unfold pressure
  rw [original_second_bulk_source]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right]
  change (((-2 : ℂ)*sourcePair (inverseRootAction f) (scalarKinetic (inverseRootAction f))+
    (6 : ℂ)*sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f)))+
    (2 : ℂ)*sourcePair (inverseRootAction f) (shiftedAction (inverseRootAction f))+
    (12 : ℂ)*sourcePair (inverseRootAction f) (magneticAction (inverseRootAction f))).re=_
  norm_num only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,sub_zero]
  rw [scalar_root_form,original_inverse_shifted_form]
  unfold sourcePair
  ring

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- The native slot and field moment share one whole signed source price. -/
theorem original_second_pressure_payment (f : QuantumTest) :
    sourceTime 0*scalarForm (inverseVolumeAction f)+2*sourceTime 0*shiftedMoment f ≤ pressure f := by
  rw [original_second_pressure_energy]
  have hG := original_gauge_kinetic_nonnegative (inverseRootAction f)
  have hB := original_magnetic_nonnegative (inverseRootAction f)
  linarith

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
private def pairRead (f g : QuantumTest) : End →ₗ[ℂ] PairMatrix where
  toFun M A B := sourcePair (A f) (M (B g))
  map_add' M N := by ext A B;simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Pi.add_apply]
  map_smul' c M := by ext A B;simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]

private theorem pair_read_delta (G : End) (hG : ∀ f g,sourcePair f (G g)= -sourcePair (G f) g)
    (f g : QuantumTest) (M : End) : pairRead f g (G*M-M*G)=pairDelta G (pairRead f g M) := by
  ext A B
  change sourcePair (A f) (G (M (B g))-M (G (B g)))=
    -sourcePair (G (A f)) (M (B g))-sourcePair (A f) (M (G (B g)))
  simp only [sourcePair,map_sub,inner_sub_right] at hG ⊢
  rw [hG]

private theorem pair_phi (f g : QuantumTest) (A : End) :
    pairRead f g (deltaPhi A)=pairDelta Phi (pairRead f g A) := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator]
  exact pair_read_delta Phi phi_pair f g A
private theorem pair_gauge (f g : QuantumTest) (A : End) :
    pairRead f g (deltaGauge A)=pairDelta Gauge (pairRead f g A) := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  exact pair_read_delta Gauge gauge_pair f g A

/-- Both derivative legs remain in one polarized second-order word. -/
def secondPair (P : PairMatrix) : PairMatrix :=
  (pairDelta Phi P-pairDelta Gauge P)-
    pairDelta Gauge (pairDelta Phi P-pairDelta Gauge P)

private theorem second_pair_source (f g : QuantumTest) (A : End) :
    pairRead f g (secondJet A)=secondPair (pairRead f g A) := by
  change pairRead f g ((deltaPhi A-deltaGauge A)-deltaGauge (deltaPhi A-deltaGauge A))=_
  simp only [map_sub,pair_phi,pair_gauge,secondPair]

/-- The actual compression and its full defect enter the same polarized source price. -/
theorem original_pressure_pair_source (F : Index) (f : QuantumTest) :
    pressure f=(secondPair (fun A B => sourcePair (A (inverseRootAction f))
        (compressionCore F (B (inverseRootAction f)))) 1 1+
      secondPair (fun A B => sourcePair (A (inverseRootAction f))
        (defectAction F (B (inverseRootAction f)))) 1 1+
      (1/2 : ℂ)*sourcePair (inverseRootAction f) (vacuumConstantAction (inverseRootAction f))).re := by
  have hc := congrArg (fun P : PairMatrix => P 1 1)
    (second_pair_source (inverseRootAction f) (inverseRootAction f) (compressionCore F))
  have hd := congrArg (fun P : PairMatrix => P 1 1)
    (second_pair_source (inverseRootAction f) (inverseRootAction f) (defectAction F))
  dsimp only [pairRead,LinearMap.coe_mk,AddHom.coe_mk,Module.End.one_apply] at hc hd
  unfold pressure
  rw [←actual_second_compression_source F]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right] at hc hd ⊢
  rw [hc,hd]

def responsePressure (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  let p := inverseRootAction (phiResponseCore m ell F z hz g)
  (sourcePair p ((secondJet (compressionCore F)+secondJet (defectAction F)+
    (1/2 : ℂ) • vacuumConstantAction) p)).re

/-- No moving graph or derivative bound is supplied to the exact response consumer. -/
theorem actual_phi_response_pressure (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    let v := phiResponseCore m ell F z hz g
    sourceTime 0*scalarForm (inverseVolumeAction v)+2*sourceTime 0*shiftedMoment v ≤
      responsePressure m ell F z hz g := by
  dsimp only [responsePressure]
  rw [actual_second_compression_source]
  exact original_second_pressure_payment _

end LowEnergy.SourceClockPhiSecondPressure
