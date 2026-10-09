import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeWeightedForcing
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeHardy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceInverseOscillator
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy GaussDiagonalHistory GaussRadialMomentum GaussYukawaCoefficient GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarFlatJoint SourceScalarNativeComparison SourcePhysicalKineticSquare
open SourceScalarInverseNativeEnergy SourceScalarVirialBulk SourceHamiltonianVolume
open scoped ContDiff InnerProductSpace BigOperators
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

def shiftedSlice (z : SourceCoordinateSlice) : scalarSlice := z.2.1+(1/2 : ℝ) • vacuumSlice
def position (i : SliceIndex) (z : SourceCoordinateSlice) : ℝ := inner ℝ (shiftedSlice z) (scalarFrame i)
private theorem position_smooth (i : SliceIndex) : ContDiff ℝ ∞ (position i) := by
  change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice =>
    inner ℝ ((z.2.1 : Scalar)+(1/2 : ℝ) • vacuum) (scalarFrame i : Scalar))
  exact (scalarCoordinate.contDiff.add contDiff_const).inner ℝ contDiff_const

def Q (i : SliceIndex) : End := multiply (position i) (fun _ => (position_smooth i).contDiffAt)
def P (i : SliceIndex) : End := inverseVolumeAction*flatMomentum (scalarFrame i)

private theorem position_derivative (i : SliceIndex) (z : SourceCoordinateSlice) :
    fderiv ℝ (position i) z (scalarAxis (scalarFrame i))=1 := by
  have he : position i=(fun w => SourceInverseVolumeHardy.coordinate i w+
      (1/2 : ℝ)*inner ℝ vacuum (scalarFrame i : Scalar)) := by
    funext w
    change inner ℝ ((w.2.1 : Scalar)+(1/2 : ℝ) • vacuum) (scalarFrame i : Scalar)=
      inner ℝ (w.2.1 : Scalar) (scalarFrame i : Scalar)+(1/2 : ℝ)*inner ℝ vacuum (scalarFrame i : Scalar)
    rw [inner_add_left,real_inner_smul_left]
  rw [he,fderiv_add_const]
  change fderiv ℝ (SourceInverseVolumeHardy.coordinate i) z (scalarAxis (scalarFrame i))=1
  change fderiv ℝ (fun w => inner ℝ (scalarCoordinate w) (scalarFrame i : Scalar)) z _=1
  rw [fderiv_inner_apply ℝ (scalarCoordinate.differentiableAt) (differentiableAt_const (scalarFrame i : Scalar)),
    ContinuousLinearMap.fderiv,(hasFDerivAt_const (scalarFrame i : Scalar) z).fderiv,
    zero_apply,inner_zero_right,zero_add]
  change inner ℝ (scalarFrame i : Scalar) (scalarFrame i : Scalar)=1
  rw [real_inner_self_eq_norm_sq]
  change ‖scalarFrame i‖^2=1
  rw [scalarFrame.orthonormal.norm_eq_one i,one_pow]

private theorem scalar_product_derivative (a : SourceCoordinateSlice → ℝ)
    (ha : ContDiff ℝ ∞ a) (f : QuantumTest) (v z : SourceCoordinateSlice) :
    fderiv ℝ (fun w => (a w : ℂ) • f w) z v=
      (a z : ℂ) • fderiv ℝ f z v+(fderiv ℝ a z v : ℂ) • f z := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z ((ha.differentiable (by simp) z).hasFDerivAt)
  have hf := (f.contDiff.differentiable (by simp) z).hasFDerivAt
  have h := hc.smul hf
  change HasFDerivAt (fun w => (a w : ℂ) • f w) _ z at h
  rw [h.fderiv]
  rfl


private theorem flat_position_commutator (i : SliceIndex) (f : QuantumTest) :
    flatMomentum (scalarFrame i) (Q i f)-Q i (flatMomentum (scalarFrame i) f)=(-Complex.I) • f := by
  apply DFunLike.ext
  intro z
  change (-Complex.I) • GaussCoframeCore.derivative (scalarAxis (scalarFrame i)) (Q i f) z-
    (position i z : ℂ) • ((-Complex.I) • GaussCoframeCore.derivative (scalarAxis (scalarFrame i)) f z)=_
  rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply]
  have he : (Q i f : SourceCoordinateSlice → FockFiber)=fun w => (position i w : ℂ) • f w := rfl
  rw [he,scalar_product_derivative _ (position_smooth i),position_derivative]
  simp only [Complex.ofReal_one,one_smul,smul_add,
    smul_comm (-Complex.I) (position i z : ℂ),add_sub_cancel_left]
  rfl

private theorem VQ (i : SliceIndex) (f : QuantumTest) : inverseVolumeAction (Q i f)=Q i (inverseVolumeAction f) := by
  apply DFunLike.ext
  intro z
  exact smul_comm (reciprocalVolume z : ℂ) (position i z : ℂ) (f z)
private theorem VP (i : SliceIndex) (f : QuantumTest) :
    flatMomentum (scalarFrame i) (inverseVolumeAction f)=P i f := by
  have h := LinearMap.congr_fun (original_native_inverse_commute ((scalarFrame i : Scalar),0)).eq f
  rw [actual_flat_momentum] at h
  exact h

/-- The source canonical commutator keeps its actual inverse-volume factor. -/
theorem original_weighted_ccr (i : SliceIndex) (f : QuantumTest) :
    P i (Q i f)-Q i (P i f)=(-Complex.I) • inverseVolumeAction f := by
  have h := congrArg inverseVolumeAction (flat_position_commutator i f)
  simpa only [map_sub,map_smul,VQ,P,Module.End.mul_apply] using h

private theorem P_pair (i : SliceIndex) (f g : QuantumTest) : sourcePair f (P i g)=sourcePair (P i f) g := by
  change sourcePair f (inverseVolumeAction (flatMomentum (scalarFrame i) g))=_
  have hv : sourcePair f (inverseVolumeAction (flatMomentum (scalarFrame i) g))=
    sourcePair (inverseVolumeAction f) (flatMomentum (scalarFrame i) g) := multiply_pair _ _ _ _
  rw [hv,flat_momentum_pair,VP]
private theorem Q_pair (i : SliceIndex) (f g : QuantumTest) : sourcePair f (Q i g)=sourcePair (Q i f) g :=
  multiply_pair _ _ _ _

private theorem square_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (α : ℝ) (u v : E) (c : ℂ)
    (h : inner ℂ u v-inner ℂ v u= -Complex.I*c) :
    ‖u‖^2=‖u-(Complex.I*(α : ℂ)) • v‖^2+α*c.re-α^2*‖v‖^2 := by
  have hi := congrArg Complex.im h
  have hswap : (inner ℂ v u).im= -(inner ℂ u v).im := inner_im_symm (𝕜 := ℂ) v u
  simp only [Complex.sub_im,Complex.mul_im,Complex.neg_im,
    Complex.I_re,Complex.I_im,zero_mul,neg_mul,one_mul,zero_add,hswap] at hi
  have he : c.re= -2*(inner ℂ u v).im := by linarith
  rw [norm_sub_sq (𝕜 := ℂ),inner_smul_right,norm_smul,mul_pow,norm_mul,mul_pow,
    Complex.norm_I,one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs,he]
  change ‖u‖^2=‖u‖^2-2*(Complex.I*(α : ℂ)*inner ℂ u v).re+
    α^2*‖v‖^2+α*(-2*(inner ℂ u v).im)-α^2*‖v‖^2
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add]
  ring


def completed (i : SliceIndex) : End := P i-(Complex.I*(Real.sqrt 2 : ℂ)) • Q i
def oscillatorEnergy (f : QuantumTest) : ℝ := ∑ i : SliceIndex,‖embed (completed i f)‖^2

private theorem row_square (i : SliceIndex) (f : QuantumTest) :
    ‖embed (P i f)‖^2+2*‖embed (Q i f)‖^2=
      ‖embed (completed i f)‖^2+Real.sqrt 2*(sourcePair f (inverseVolumeAction f)).re := by
  have h0 := congrArg (sourcePair f) (original_weighted_ccr i f)
  have hp := P_pair i f (Q i f)
  have hq := Q_pair i f (P i f)
  simp only [sourcePair] at hp hq
  have h : inner ℂ (embed (P i f)) (embed (Q i f))-inner ℂ (embed (Q i f)) (embed (P i f))=
      -Complex.I*sourcePair f (inverseVolumeAction f) := by
    simpa only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right,hp,hq] using h0
  have hs := square_shift (Real.sqrt 2) (embed (P i f)) (embed (Q i f))
    (sourcePair f (inverseVolumeAction f)) h
  have hs2 : Real.sqrt 2^2=2 := Real.sq_sqrt (by norm_num)
  simp only [hs2] at hs
  simp only [completed,LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul]
  linarith only [hs]

private theorem coordinate_square (z : SourceCoordinateSlice) :
    (∑ i : SliceIndex,position i z^2)=‖scalarField z-(1/2 : ℝ) • vacuum‖^2 := by
  rw [show (∑ i : SliceIndex,position i z^2)=‖shiftedSlice z‖^2 from scalarFrame.sum_sq_inner_left _]
  congr 1
  change ‖((shiftedSlice z : scalarSlice) : Scalar)‖=‖scalarField z-(1/2 : ℝ) • vacuum‖
  congr 1
  change (z.2.1 : Scalar)+(1/2 : ℝ) • vacuum=vacuum+(z.2.1 : Scalar)-(1/2 : ℝ) • vacuum
  module

private theorem positions_action (f : QuantumTest) :
    (∑ i : SliceIndex,Q i (Q i f))=∑ a : ScalarIndex,shiftedColumn a (shiftedColumn a f) := by
  apply DFunLike.ext
  intro z
  simp only [sum_apply]
  change (∑ i : SliceIndex,(position i z : ℂ) • ((position i z : ℂ) • f z))=
    ∑ a : ScalarIndex,(shiftedCoordinate a z : ℂ) • ((shiftedCoordinate a z : ℂ) • f z)
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [coordinate_square]
  congr 2
  exact (scalarBasis.sum_sq_inner_left (scalarField z-(1/2 : ℝ) • vacuum)).symm

private theorem position_energy (f : QuantumTest) :
    (∑ i : SliceIndex,‖embed (Q i f)‖^2)=shiftedMoment f := by
  have h := congrArg (fun q => (sourcePair f q).re) (positions_action f)
  have hself (q : QuantumTest) : (sourcePair q q).re=‖embed q‖^2 := by
    change RCLike.re (inner ℂ (embed q) (embed q))=_
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hQ (i : SliceIndex) : (sourcePair f (Q i (Q i f))).re=‖embed (Q i f)‖^2 :=
    congrArg Complex.re (Q_pair i f (Q i f)) |>.trans (hself _)
  have ha (a : ScalarIndex) : (sourcePair f (shiftedColumn a (shiftedColumn a f))).re=‖embed (shiftedColumn a f)‖^2 :=
    congrArg Complex.re (multiply_pair _ _ _ _) |>.trans (hself _)
  simp only [sourcePair,map_sum,inner_sum,Complex.re_sum] at h
  change (∑ i : SliceIndex,(sourcePair f (Q i (Q i f))).re)=
    ∑ a : ScalarIndex,(sourcePair f (shiftedColumn a (shiftedColumn a f))).re at h
  simpa only [hQ,ha,shiftedMoment] using h

private theorem momentum_energy (f : QuantumTest) :
    inverseNativeEnergy f=(∑ i : SliceIndex,‖embed (P i f)‖^2)+orthogonalEnergy (inverseVolumeAction f) := by
  rw [←original_inverse_native_return,actual_scalar_energy_split,actual_flat_kinetic_square]
  simp only [VP]

/-- All seventy native rows complete the same source form into oscillator squares and its generated volume floor. -/
theorem original_inverse_oscillator (f : QuantumTest) :
    inverseForm f=4*sourceTime 0*oscillatorEnergy f+
      4*sourceTime 0*orthogonalEnergy (inverseVolumeAction f)+
      36*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re+
      244*Real.sqrt 2*sourceTime 0*(sourcePair f (inverseVolumeAction f)).re := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset SliceIndex)) rfl (fun i _ => row_square i f)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    actual_scalar_frame_dimension,nsmul_eq_mul,position_energy] at h
  rw [original_inverse_energy,momentum_energy]
  unfold oscillatorEnergy
  norm_num only [Nat.cast_ofNat] at h
  linear_combination (4*sourceTime 0)*h

/-- The source Ward form pays the inverse-volume expectation without a bounded-volume premise. -/
theorem original_inverse_volume_floor (f : QuantumTest) :
    244*Real.sqrt 2*sourceTime 0*(sourcePair f (inverseVolumeAction f)).re ≤ inverseForm f := by
  rw [original_inverse_oscillator]
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hE : 0≤oscillatorEnergy f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hO : 0≤orthogonalEnergy (inverseVolumeAction f) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hG := original_gauge_kinetic_nonnegative (inverseRootAction f)
  nlinarith [mul_nonneg hn.le hE,mul_nonneg hn.le hO]

end LowEnergy.SourceInverseOscillator
