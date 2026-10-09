import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeRGaussianSource
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarNativeComparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential GaussYukawaCoefficient
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceHamiltonianVolume
open SourceScalarInverseNativeEnergy SourceScalarNativeComparison SourceScalarVirialBulk SourceScalarEssentialBudget
open SourceClockPhiNormalizedScalarBudget SourceClockPhiRadiusNormalizedFluxBudget
open FirstCurrentPayerNext NativePointReturn MeasureTheory Filter
open scoped InnerProductSpace ContDiff
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U := inverseVolumeAction
attribute [local irreducible] sourcePair embed scalarKinetic diagonalAction normalizedState normalizedForcing
private theorem n_pos : 0 < n := by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem U_pair (f g : QuantumTest) : sourcePair f (U g)=sourcePair (U f) g := multiply_pair _ _ _ _
private theorem inverse_volume (f : QuantumTest) : U (volumeAction f)=f := by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)=f z
    rw [smul_smul]
    simp only [reciprocalVolume,Complex.ofReal_inv,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (volume_pos ⟨z,hz⟩).ne'),one_smul]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem scalar_U (f : QuantumTest) : scalarKinetic (U f)=U (scalarKinetic f) := by
  have h:=LinearMap.congr_fun scalar_kinetic_volume.eq (U f)
  change scalarKinetic (volumeAction (U f))=volumeAction (scalarKinetic (U f)) at h
  rw [volume_inverse] at h
  have hi:=congrArg U h
  rw [inverse_volume] at hi
  exact hi.symm
private theorem inverse_scalar_form (f : QuantumTest) :
    (sourcePair f (U (scalarKinetic f))).re= -(n/2)*inverseNativeEnergy f := by
  have h:=actual_native_scalar_form (U f)
  rw [scalar_U,volume_inverse,original_inverse_native_return] at h
  rw [U_pair]
  exact h

def scalarNativeBlock : End :=
  (-14:ℂ) • (U*scalarKinetic)+(34:ℂ) • (U*centeredAction)-
    (56:ℂ) • (U*vacuumLinearAction)+(128/5:ℂ) • (U*vacuumConstantAction)
def scalarNativePrice (w : QuantumTest) : ℝ := (sourcePair w (scalarNativeBlock w)).re
private def paymentCoordinate (a : ScalarIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (scalarField z+(4/3:ℝ) • vacuum) (scalarBasis a)
private theorem payment_smooth (a : ScalarIndex) : ContDiff ℝ ∞ (paymentCoordinate a) :=
  (scalarField_smooth.add contDiff_const).inner ℝ contDiff_const
private def paymentColumn (a : ScalarIndex) : End := multiply (paymentCoordinate a)
  (fun _ => (payment_smooth a).contDiffAt)
def scalarPaymentSquare (w : QuantumTest) : ℝ := ∑a:ScalarIndex,‖embed (paymentColumn a w)‖^2
private def potentialBlock : End :=
  (34:ℂ) • (U*centeredAction)-(56:ℂ) • (U*vacuumLinearAction)+
    (128/5:ℂ) • (U*vacuumConstantAction)
private theorem potential_completion : potentialBlock=
    (40*(n:ℂ)) • (∑a:ScalarIndex,shiftedColumn a*shiftedColumn a)+
    (((394/15:ℝ)*n*‖vacuum‖^2:ℝ):ℂ) • (1:End)-
    (6*(n:ℂ)) • (∑a:ScalarIndex,paymentColumn a*paymentColumn a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hs : (∑a:ScalarIndex,(shiftedCoordinate a z)^2)=‖scalarField z-(1/2:ℝ) • vacuum‖^2 :=
      scalarBasis.sum_sq_inner_left _
    have hp : (∑a:ScalarIndex,(paymentCoordinate a z)^2)=‖scalarField z+(4/3:ℝ) • vacuum‖^2 :=
      scalarBasis.sum_sq_inner_left _
    have hform : 34*‖scalarField z‖^2-56*inner ℝ vacuum (scalarField z)+(128/5:ℝ)*‖vacuum‖^2=
        40*(∑a:ScalarIndex,(shiftedCoordinate a z)^2)+(394/15:ℝ)*‖vacuum‖^2-
        6*(∑a:ScalarIndex,(paymentCoordinate a z)^2) := by
      rw [hs,hp,norm_sub_sq_real,norm_add_sq_real]
      simp only [norm_smul,Real.norm_eq_abs,real_inner_smul_right]
      norm_num
      rw [real_inner_comm (scalarField z) vacuum]
      ring
    have hv : volume z≠0 := (volume_pos ⟨z,hz⟩).ne'
    change ((34:ℂ) • U (centeredAction f)-(56:ℂ) • U (vacuumLinearAction f)+
      (128/5:ℂ) • U (vacuumConstantAction f)) z=_
    simp only [sub_apply,add_apply,smul_apply,LinearMap.sub_apply,LinearMap.add_apply,
      LinearMap.smul_apply,Module.End.one_apply,LinearMap.sum_apply,Module.End.mul_apply,sum_apply]
    change (34:ℂ) • ((reciprocalVolume z:ℂ) • (((n*volume z*‖scalarField z‖^2:ℝ):ℂ) • f z))-
      (56:ℂ) • ((reciprocalVolume z:ℂ) • (((n*volume z*inner ℝ vacuum (scalarField z):ℝ):ℂ) • f z))+
      (128/5:ℂ) • ((reciprocalVolume z:ℂ) • (((n*volume z*‖vacuum‖^2:ℝ):ℂ) • f z))=
      (40*(n:ℂ)) • (∑a:ScalarIndex,(shiftedCoordinate a z:ℂ) • ((shiftedCoordinate a z:ℂ) • f z))+
      (((394/15:ℝ)*n*‖vacuum‖^2:ℝ):ℂ) • f z-
      (6*(n:ℂ)) • (∑a:ScalarIndex,(paymentCoordinate a z:ℂ) • ((paymentCoordinate a z:ℂ) • f z))
    simp only [smul_smul,←pow_two,←Finset.sum_smul,←Complex.ofReal_pow,←Complex.ofReal_sum,
      ←add_smul,←sub_smul]
    apply congrArg (fun c:ℂ=>c • f z)
    push_cast
    unfold reciprocalVolume
    push_cast
    have hvC:(volume z:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv
    have hc:=congrArg (fun r:ℝ=>(r:ℂ)) hform
    push_cast at hc
    field_simp [hvC]
    linear_combination (norm:=ring) 75*(n:ℂ)*hc
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- The scalar native current and its literal vacuum field are paid by the original scalar Noether
energy with explicit unused momentum and completed-square debits. -/
theorem actual_scalar_native_joint_square (w : QuantumTest) :
    scalarNativePrice w=5*scalarEnergy w+(394/15:ℝ)*n*‖vacuum‖^2*‖embed w‖^2-
      13*n*inverseNativeEnergy w-6*n*scalarPaymentSquare w := by
  have hs(a:ScalarIndex):sourcePair w ((shiftedColumn a*shiftedColumn a) w)=
      sourcePair (shiftedColumn a w) (shiftedColumn a w):=multiply_pair _ _ _ _
  have hp(a:ScalarIndex):sourcePair w ((paymentColumn a*paymentColumn a) w)=
      sourcePair (paymentColumn a w) (paymentColumn a w):=multiply_pair _ _ _ _
  have hself(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
    simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  have hsum(q:ScalarIndex→QuantumTest):sourcePair w (∑a,q a)=∑a,sourcePair w (q a):=by
    simp only [sourcePair,map_sum,inner_sum]
  have hsplit:scalarNativeBlock=(-14:ℂ) • (U*scalarKinetic)+potentialBlock:=by
    unfold scalarNativeBlock potentialBlock
    module
  unfold scalarNativePrice
  rw [hsplit,potential_completion]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    LinearMap.sum_apply,pair_add_r,pair_sub_r,pair_smul_r,hsum,hs,hp]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.neg_re,Complex.neg_im,
    mul_zero,zero_mul,sub_zero,add_zero,neg_zero,Complex.re_sum,hself]
  simp only [Module.End.mul_apply]
  rw [inverse_scalar_form]
  unfold scalarEnergy scalarPaymentSquare shiftedMoment
  ring
end LowEnergy.FirstCurrentJointBudget
