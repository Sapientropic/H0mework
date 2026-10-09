import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarNoetherCommon
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeOscillator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussLiveMomentum GaussNativeEnergy GaussNativePotential GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarFlatJoint SourceScalarNativeComparison SourceScalarInverseNativeEnergy
open SourceScalarVirialBulk SourceCoframeVolume SourceClockPhiNormalizedScalarBudget SourcePhysicalKineticSquare
open scoped ContDiff InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U := inverseVolumeAction
private abbrev P := SourceInverseOscillator.P
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

private def shiftCoefficient (i : SliceIndex) : ℝ := (11/6:ℝ)*inner ℝ vacuum (scalarFrame i : Scalar)
private def Q (i : SliceIndex) : End := SourceInverseOscillator.Q i+(shiftCoefficient i:ℂ) • (1:End)
private def position (i : SliceIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (scalarField z+(4/3:ℝ) • vacuum) (scalarFrame i : Scalar)
private theorem Q_apply (i : SliceIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    Q i f z=(position i z:ℂ) • f z := by
  change (SourceInverseOscillator.position i z:ℂ) • f z+(shiftCoefficient i:ℂ) • f z=_
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
  change inner ℝ ((z.2.1:Scalar)+(1/2:ℝ) • vacuum) (scalarFrame i:Scalar)+
    (11/6:ℝ)*inner ℝ vacuum (scalarFrame i:Scalar)=
    inner ℝ (vacuum+(z.2.1:Scalar)+(4/3:ℝ) • vacuum) (scalarFrame i:Scalar)
  simp only [inner_add_left,real_inner_smul_left]
  ring

private theorem weighted_ccr (i : SliceIndex) (f : QuantumTest) :
    P i (Q i f)-Q i (P i f)=(-Complex.I) • U f := by
  have h:=SourceInverseOscillator.original_weighted_ccr i f
  simpa only [Q,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    map_add,map_smul,add_sub_add_right_eq_sub] using h
private theorem UP (i : SliceIndex) (f : QuantumTest) :
    flatMomentum (scalarFrame i) (U f)=P i f := by
  have h:=LinearMap.congr_fun (original_native_inverse_commute ((scalarFrame i:Scalar),0)).eq f
  rw [actual_flat_momentum] at h
  exact h
private theorem P_pair (i : SliceIndex) (f g : QuantumTest) : sourcePair f (P i g)=sourcePair (P i f) g := by
  change sourcePair f (U (flatMomentum (scalarFrame i) g))=_
  have hu:sourcePair f (U (flatMomentum (scalarFrame i) g))=
    sourcePair (U f) (flatMomentum (scalarFrame i) g):=multiply_pair _ _ _ _
  rw [hu,flat_momentum_pair,UP]
private theorem Q_pair (i : SliceIndex) (f g : QuantumTest) : sourcePair f (Q i g)=sourcePair (Q i f) g := by
  have h:sourcePair f (SourceInverseOscillator.Q i g)=
    sourcePair (SourceInverseOscillator.Q i f) g:=multiply_pair _ _ _ _
  simp only [Q,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    sourcePair,map_add,map_smul,inner_add_right,inner_add_left,inner_smul_right,inner_smul_left,
    Complex.conj_ofReal] at h ⊢
  rw [h]

/-- Actual shifted scalar annihilation rows, with the original inverse-volume momentum. -/
def scalarPaymentCompleted (i : SliceIndex) : End := P i-Complex.I • Q i
def scalarPaymentCompletedEnergy (w : QuantumTest) : ℝ := ∑i:SliceIndex,‖embed (scalarPaymentCompleted i w)‖^2
private theorem row_square (i : SliceIndex) (w : QuantumTest) :
    ‖embed (P i w)‖^2+‖embed (Q i w)‖^2=
      ‖embed (scalarPaymentCompleted i w)‖^2+(sourcePair w (U w)).re := by
  have h0:=congrArg (sourcePair w) (weighted_ccr i w)
  have hp:=P_pair i w (Q i w)
  have hq:=Q_pair i w (P i w)
  simp only [sourcePair] at hp hq
  have h:inner ℂ (embed (P i w)) (embed (Q i w))-inner ℂ (embed (Q i w)) (embed (P i w))=
      -Complex.I*sourcePair w (U w):=by
    simpa only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right,hp,hq] using h0
  have hi:=congrArg Complex.im h
  have hswap:(inner ℂ (embed (Q i w)) (embed (P i w))).im=
      -(inner ℂ (embed (P i w)) (embed (Q i w))).im:=inner_im_symm (𝕜:=ℂ) _ _
  simp only [Complex.sub_im,Complex.mul_im,Complex.neg_im,Complex.I_re,Complex.I_im,
    zero_mul,neg_mul,one_mul,zero_add,hswap] at hi
  simp only [scalarPaymentCompleted,LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul,
    norm_sub_sq (𝕜:=ℂ),inner_smul_right,norm_smul,Complex.norm_I,one_mul,
    RCLike.re_eq_complex_re,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub]
  linarith only [hi]

private def fullPosition (a : ScalarIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (scalarField z+(4/3:ℝ) • vacuum) (scalarBasis a)
private theorem full_position_smooth (a : ScalarIndex) : ContDiff ℝ ∞ (fullPosition a) :=
  (scalarField_smooth.add contDiff_const).inner ℝ contDiff_const
private def fullColumn (a : ScalarIndex) : End := multiply (fullPosition a)
  (fun _ => (full_position_smooth a).contDiffAt)
private theorem coordinate_square (z : SourceCoordinateSlice) :
    (∑i:SliceIndex,position i z^2)=‖scalarField z+(4/3:ℝ) • vacuum‖^2 := by
  let q:scalarSlice:=z.2.1+(7/3:ℝ) • vacuumSlice
  have he:scalarField z+(4/3:ℝ) • vacuum=(q:Scalar):=by
    change vacuum+(z.2.1:Scalar)+(4/3:ℝ) • vacuum=(z.2.1:Scalar)+(7/3:ℝ) • vacuum
    module
  simp only [position,he]
  exact scalarFrame.sum_sq_inner_left q
private theorem positions_action (w : QuantumTest) :
    (∑i:SliceIndex,Q i (Q i w))=∑a:ScalarIndex,fullColumn a (fullColumn a w) := by
  apply DFunLike.ext
  intro z
  simp only [sum_apply,Q_apply]
  change (∑i:SliceIndex,(position i z:ℂ) • ((position i z:ℂ) • w z))=
    ∑a:ScalarIndex,(fullPosition a z:ℂ) • ((fullPosition a z:ℂ) • w z)
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [coordinate_square]
  congr 2
  exact (scalarBasis.sum_sq_inner_left (scalarField z+(4/3:ℝ) • vacuum)).symm
private theorem position_energy (w : QuantumTest) :
    (∑i:SliceIndex,‖embed (Q i w)‖^2)=scalarPaymentSquare w := by
  have h:=congrArg (fun q=>(sourcePair w q).re) (positions_action w)
  have hself(q:QuantumTest):(sourcePair q q).re=‖embed q‖^2:=by
    change RCLike.re (inner ℂ (embed q) (embed q))=_
    exact inner_self_eq_norm_sq (𝕜:=ℂ) _
  have hQ(i:SliceIndex):(sourcePair w (Q i (Q i w))).re=‖embed (Q i w)‖^2:=
    congrArg Complex.re (Q_pair i w (Q i w)) |>.trans (hself _)
  have ha(a:ScalarIndex):(sourcePair w (fullColumn a (fullColumn a w))).re=‖embed (fullColumn a w)‖^2:=
    congrArg Complex.re (multiply_pair _ _ _ _) |>.trans (hself _)
  simp only [sourcePair,map_sum,inner_sum,Complex.re_sum] at h
  change (∑i:SliceIndex,(sourcePair w (Q i (Q i w))).re)=
    ∑a:ScalarIndex,(sourcePair w (fullColumn a (fullColumn a w))).re at h
  simp only [hQ,ha] at h
  unfold scalarPaymentSquare
  convert! h using 2
private theorem momentum_energy (w : QuantumTest) :
    inverseNativeEnergy w=(∑i:SliceIndex,‖embed (P i w)‖^2)+orthogonalEnergy (U w) := by
  rw [←original_inverse_native_return,actual_scalar_energy_split,actual_flat_kinetic_square]
  simp only [UP]

/-- The same affine scalar61 source pays 61 times the actual U mass; all 70 native rows remain. -/
theorem actual_scalar_payment_uncertainty_identity (w : QuantumTest) :
    inverseNativeEnergy w+scalarPaymentSquare w=
      61*(sourcePair w (U w)).re+scalarPaymentCompletedEnergy w+orthogonalEnergy (U w) := by
  have h:=Finset.sum_congr (s₁:=(Finset.univ:Finset SliceIndex)) rfl (fun i _=>row_square i w)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    actual_scalar_frame_dimension,nsmul_eq_mul,position_energy] at h
  rw [momentum_energy]
  unfold scalarPaymentCompletedEnergy
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]
theorem actual_scalar_payment_uncertainty (w : QuantumTest) :
    61*(sourcePair w (U w)).re ≤ inverseNativeEnergy w+scalarPaymentSquare w := by
  rw [actual_scalar_payment_uncertainty_identity]
  have hE:0 ≤ scalarPaymentCompletedEnergy w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hO:0 ≤ orthogonalEnergy (U w):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  linarith

/-- Original negative scalar squares produce the full 183 U-mass payment and retain real debits. -/
theorem actual_scalar_payment_mass_debit (w : QuantumTest) :
    183*sourceTime 0*(sourcePair w (U w)).re+10*sourceTime 0*inverseNativeEnergy w+
      3*sourceTime 0*scalarPaymentSquare w ≤
      13*sourceTime 0*inverseNativeEnergy w+6*sourceTime 0*scalarPaymentSquare w := by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have h:=mul_le_mul_of_nonneg_left (actual_scalar_payment_uncertainty w) (mul_nonneg (by norm_num:0≤(3:ℝ)) hn.le)
  nlinarith only [h]
end LowEnergy.FirstCurrentJointBudget
