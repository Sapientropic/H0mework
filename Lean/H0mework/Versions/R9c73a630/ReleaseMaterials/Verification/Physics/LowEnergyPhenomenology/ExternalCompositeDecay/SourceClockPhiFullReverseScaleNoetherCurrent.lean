import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFullReverseScale
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceScalarVolumePressure
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussMatterCore
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceHamiltonianVolume SourceDilationRemainder
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarShiftedBulk SourceScalarEssentialBudget
open SourceScalarOscillatorAbsorption SourceScalarSpatialCurrent SourceScalarVolumePressure
open SourceNativeMatterCovarianceCancellation SourceUnmixedPotentialCancellation SourceMixedCurrentCancellation
open FirstCurrentDilationPrimitive SourceClockPhiOriginalGaussianH0KineticPrimitives
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev V:End:=volumeAction
private abbrev K:End:=scalarKinetic
private abbrev L:End:=localAction
private abbrev O:End:=offsetAction
private abbrev B:End:=scalarBulkComplete
private abbrev Z:End:=reverseNativeClock
attribute [local irreducible] sourcePair embed diagonalAction scalarKinetic gaugeKinetic GaussMatterCore.matterAction
  scalarBulkComplete scalarBulk nativeDilationWord reverseScaleForce
private theorem end_sum_commute {R:Type*}[Ring R]{ι:Type*}[Fintype ι](A:ι→R)(B:R)
    (h:∀i,Commute (A i) B):Commute (∑i,A i) B:=by
  change (∑i,A i)*B=B*(∑i,A i)
  rw [Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _=>(h i).eq)
private theorem end_smul_commute {R:Type*}[Ring R][Module ℂ R][IsScalarTower ℂ R R][SMulCommClass ℂ R R]
    (c:ℂ)(A B:R)(h:Commute A B):Commute (c • A) B:=by
  change (c • A)*B=B*(c • A)
  rw [smul_mul_assoc,mul_smul_comm,h.eq]
private theorem end_mul_commute {R:Type*}[Ring R](A C E:R)(hA:Commute A E)(hC:Commute C E):
    Commute (A*C) E:=hA.mul_left hC
private theorem end_add_commute {R:Type*}[Ring R](A C E:R)(hA:Commute A E)(hC:Commute C E):
    Commute (A+C) E:=hA.add_left hC
private theorem real_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem matter_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute matterAction (multiply c hc) := by
  unfold matterAction
  apply end_sum_commute (R:=End)
  intro i
  apply end_sum_commute (R:=End)
  intro b
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (GaussQuantumMultiplier.quantized (localMatrix i b z)) (c z : ℂ) (f z)


private theorem O_pair(f g:QuantumTest):sourcePair f (O g)=sourcePair (O f) g:=multiply_pair _ _ _ _
private theorem gauge_O:Commute gaugeKinetic O:=by
  have hp(i:Fin 3)(a:LieIndex):Commute (covariantMomentum (gaugeDirection i a)) O:=by
    apply sub_eq_zero.mp
    simpa only [gaugeDirection,inner_zero_left,Complex.ofReal_zero,mul_zero,zero_smul] using
      original_offset_momentum (gaugeDirection i a)
  have ha(i:Fin 3)(a:LieIndex):Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)) O:=by
    apply LinearMap.ext;intro g
    apply GaussCoreLabel.pair_separates;intro f
    change sourcePair f (GaussMomentumAdjoint.adjoint (gaugeDirection i a) (O g))=
      sourcePair f (O (GaussMomentumAdjoint.adjoint (gaugeDirection i a) g))
    have he:(covariantMomentum (gaugeDirection i a)) (O f)=O ((covariantMomentum (gaugeDirection i a)) f):=
      LinearMap.congr_fun (hp i a).eq f
    rw [adjoint_pair,O_pair,←he,←adjoint_pair,←O_pair]
  unfold gaugeKinetic
  apply end_smul_commute (R:=End)
  apply end_sum_commute (R:=End);intro a
  apply end_sum_commute (R:=End);intro i
  apply end_sum_commute (R:=End);intro j
  change Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
    (multiply (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) O
  exact end_mul_commute (R:=End) _ _ _ (ha i a) (end_mul_commute (R:=End) _ _ _ (real_commute _ _ _ _) (hp j a))
private theorem bulk_commute(T:End)(hU:Commute T U)(hK:Commute T K)(hL:Commute T L)(hO:Commute T O):
    Commute T B:=by
  unfold B scalarBulkComplete scalarBulk
  have h1:Commute (U*K) T:=end_mul_commute (R:=End) _ _ _ hU.symm hK.symm
  have h2:Commute (U*L) T:=end_mul_commute (R:=End) _ _ _ hU.symm hL.symm
  exact (end_add_commute (R:=End) _ _ _ (end_add_commute (R:=End) _ _ _
    (end_smul_commute (R:=End) (-8) _ _ h1) (end_smul_commute (R:=End) 8 _ _ h2))
    (end_smul_commute (R:=End) 8 _ _ hO.symm)).symm
private theorem gauge_B:Commute gaugeKinetic B:=
  bulk_commute _ gauge_kinetic_primitives.1.symm original_scalar_gauge_commute.symm original_gauge_local_commute gauge_O
private theorem matter_B:Commute GaussMatterCore.matterAction B:=by
  apply bulk_commute
  · exact matter_real _ _
  · exact original_scalar_matter_commute.symm
  · exact matter_real _ _
  · exact matter_real _ _
private theorem magnetic_B:Commute magneticAction B:=by
  apply bulk_commute
  · exact real_commute _ _ _ _
  · exact original_scalar_magnetic_commute.symm
  · exact real_commute _ _ _ _
  · exact real_commute _ _ _ _
private theorem V_B:Commute V B:=by
  apply bulk_commute
  · exact real_commute _ _ _ _
  · exact scalar_kinetic_volume.symm
  · exact real_commute _ _ _ _
  · exact real_commute _ _ _ _
private theorem U_K:Commute U K:=scalar_kinetic_primitives.1
private theorem U_L:Commute U L:=real_commute _ _ _ _
private theorem U_O:Commute U O:=real_commute _ _ _ _
private theorem L_O:Commute L O:=real_commute _ _ _ _
private theorem VU:V*U=(1:End):=LinearMap.ext volume_inverse
private theorem badd(A C E:End):bracket A (C+E)=bracket A C+bracket A E:=by unfold bracket;noncomm_ring
private theorem bsmul(A C:End)(c:ℂ):bracket A (c • C)=c • bracket A C:=by
  unfold bracket;simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bprod(A C E:End):bracket A (C*E)=bracket A C*E+C*bracket A E:=by unfold bracket;noncomm_ring
private theorem prodbr(A C E:End):bracket (A*C) E=A*bracket C E+bracket A E*C:=by unfold bracket;noncomm_ring
private theorem K_B:bracket K B=(8:ℂ) • (U*bracket K L)+(8:ℂ) • bracket K O:=by
  have hU:bracket K U=0:=sub_eq_zero.mpr U_K.eq.symm
  have hK:bracket K K=0:=sub_self _
  unfold B scalarBulkComplete scalarBulk
  rw [badd,badd,bsmul,bsmul,bsmul,bprod,bprod,hU,hK]
  simp only [mul_zero,zero_mul,add_zero,zero_add,smul_zero]
private theorem L_B:bracket L B=(8:ℂ) • (U*bracket K L):=by
  have hU:bracket L U=0:=sub_eq_zero.mpr U_L.eq.symm
  have hL:bracket L L=0:=sub_self _
  have hO:bracket L O=0:=sub_eq_zero.mpr L_O.eq
  have hK:bracket L K= -bracket K L:=by unfold bracket;noncomm_ring
  unfold B scalarBulkComplete scalarBulk
  rw [badd,badd,bsmul,bsmul,bsmul,bprod,bprod,hU,hL,hO,hK]
  simp only [mul_zero,zero_mul,add_zero,zero_add,smul_zero,mul_neg,smul_neg,neg_smul,neg_neg]
private theorem O_B:bracket O B=(8:ℂ) • (U*bracket K O):=by
  have hU:bracket O U=0:=sub_eq_zero.mpr U_O.eq.symm
  have hL:bracket O L=0:=sub_eq_zero.mpr L_O.eq.symm
  have hO:bracket O O=0:=sub_self _
  have hK:bracket O K= -bracket K O:=by unfold bracket;noncomm_ring
  unfold B scalarBulkComplete scalarBulk
  rw [badd,badd,bsmul,bsmul,bsmul,bprod,bprod,hU,hL,hO,hK]
  simp only [mul_zero,zero_mul,add_zero,zero_add,smul_zero,mul_neg,smul_neg,neg_smul,neg_neg]
private theorem VO_B:bracket (V*O) B=(8:ℂ) • bracket K O:=by
  rw [prodbr,O_B,show bracket V B=0 from sub_eq_zero.mpr V_B.eq]
  simp only [mul_smul_comm,zero_mul,add_zero,←mul_assoc,VU,one_mul]
private theorem scalar_current_return:SourceScalarOscillatorAbsorption.scalarCurrent=(16:ℂ) • (U*bracket K L):=by
  unfold SourceScalarOscillatorAbsorption.scalarCurrent scalarHamiltonian
  change bracket (K+L) scalarBulk=_
  have hk:bracket K scalarBulk=(8:ℂ) • (U*bracket K L):=by
    have h:=K_B
    unfold B scalarBulkComplete at h
    rw [badd,bsmul] at h
    exact add_right_cancel h
  have hl:bracket L scalarBulk=(8:ℂ) • (U*bracket K L):=by
    have h:=L_B
    unfold B scalarBulkComplete at h
    rw [badd,bsmul,show bracket L O=0 from sub_eq_zero.mpr L_O.eq,smul_zero,add_zero] at h
    exact h
  have he:bracket (K+L) scalarBulk=bracket K scalarBulk+bracket L scalarBulk:=by unfold bracket;noncomm_ring
  rw [he,hk,hl]
  module
private theorem center_offset:centeredAction-vacuumLinearAction=L+V*O-(1/4:ℂ) • vacuumConstantAction:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  have he:sourceTime 0*volume z*‖scalarField z‖^2-sourceTime 0*volume z*inner ℝ vacuum (scalarField z)=
      localPotential z+volume z*offsetCoefficient z-(1/4:ℝ)*(sourceTime 0*volume z*‖vacuum‖^2):=by
    unfold localPotential offsetCoefficient GaussCoframeForm.volumePotential scalarField
    rw [norm_add_sq_real,inner_add_right,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
      real_inner_comm vacuum (z.2.1:Scalar)]
    ring
  change (((sourceTime 0*volume z*‖scalarField z‖^2:ℝ):ℂ) • f z)-
      (((sourceTime 0*volume z*inner ℝ vacuum (scalarField z):ℝ):ℂ) • f z)=
    ((localPotential z:ℂ) • f z)+(volume z:ℂ) • ((offsetCoefficient z:ℂ) • f z)-
      (1/4:ℂ) • (((sourceTime 0*volume z*‖vacuum‖^2:ℝ):ℂ) • f z)
  rw [←sub_smul,←Complex.ofReal_sub,he]
  simp only [Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat,add_smul,sub_smul,mul_smul]
private theorem vacuum_B:Commute vacuumConstantAction B:=by
  have hv:vacuumConstantAction=((sourceTime 0*‖vacuum‖^2:ℝ):ℂ) • V:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    change (((sourceTime 0*volume z*‖vacuum‖^2:ℝ):ℂ) • f z)=
      (((sourceTime 0*‖vacuum‖^2:ℝ):ℂ) • ((volume z:ℂ) • f z))
    rw [smul_smul,←Complex.ofReal_mul]
    congr 1;congr 1;ring
  rw [hv]
  exact V_B.smul_left _
private theorem spatial_split:spatialAction=scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (spatialPotential z:ℂ) • f z=
    ((-(sourceTime 0*volume z/2*∑i:Fin 3,∑j:Fin 3,inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j)):ℝ):ℂ) • f z+
    (magneticPotential z:ℂ) • f z
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
private theorem spatial_B:bracket spatialAction B=(8:ℂ) • (U*scalarSpatialDivergence):=by
  have hS:Commute scalarSpatialAction U:=real_commute _ _ _ _
  have hL:Commute scalarSpatialAction L:=real_commute _ _ _ _
  have hO:Commute scalarSpatialAction O:=real_commute _ _ _ _
  have hK:bracket scalarSpatialAction K= -scalarSpatialDivergence:=by
    have h:=original_scalar_spatial_current
    unfold bracket
    linear_combination (norm:=module) -h
  have hb:bracket scalarSpatialAction B=(8:ℂ) • (U*scalarSpatialDivergence):=by
    unfold B scalarBulkComplete scalarBulk
    rw [badd,badd,bsmul,bsmul,bsmul,bprod,bprod,
      show bracket scalarSpatialAction U=0 from sub_eq_zero.mpr hS.eq,
      show bracket scalarSpatialAction L=0 from sub_eq_zero.mpr hL.eq,
      show bracket scalarSpatialAction O=0 from sub_eq_zero.mpr hO.eq,hK]
    simp only [zero_mul,mul_zero,add_zero,zero_add,smul_zero,mul_neg,smul_neg,neg_smul,neg_neg]
  have he:bracket spatialAction B=bracket scalarSpatialAction B+bracket magneticAction B:=by
    rw [spatial_split];unfold bracket;noncomm_ring
  rw [he,hb,show bracket magneticAction B=0 from sub_eq_zero.mpr magnetic_B.eq,add_zero]

/-- The full balanced scale force meets the original scalar Noether form through only its native oscillator and literal scalar-spatial force. All coframe, electric, matter, magnetic and vacuum-offset current words cancel at the source. -/
theorem actual_reverse_force_scalar_current:
    bracket reverseScaleForce B=(-18:ℂ) • SourceScalarOscillatorAbsorption.scalarCurrent-
      (192:ℂ) • (U*scalarSpatialDivergence):=by
  have hf:reverseScaleForce=(-6:ℂ) • K-(18:ℂ) • gaugeKinetic-(15:ℂ) • GaussMatterCore.matterAction-
      (30:ℂ) • L+(6:ℂ) • (V*O)-(3/2:ℂ) • vacuumConstantAction-
      (12:ℂ) • magneticAction-(24:ℂ) • spatialAction:=by
    rw [actual_reverse_scale_departments]
    have he:=congrArg (fun T:End=>(6:ℂ) • T) center_offset
    linear_combination (norm:=module) he
  have hc:=scalar_current_return
  rw [hf]
  have hd(A C:End):bracket (A-C) B=bracket A B-bracket C B:=by unfold bracket;noncomm_ring
  have ha(A C:End):bracket (A+C) B=bracket A B+bracket C B:=by unfold bracket;noncomm_ring
  have hs(c:ℂ)(A:End):bracket (c • A) B=c • bracket A B:=by unfold bracket;simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
  simp only [hd,ha,hs,K_B,L_B,VO_B,spatial_B,
    show bracket gaugeKinetic B=0 from sub_eq_zero.mpr gauge_B.eq,
    show bracket GaussMatterCore.matterAction B=0 from sub_eq_zero.mpr matter_B.eq,
    show bracket magneticAction B=0 from sub_eq_zero.mpr magnetic_B.eq,
    show bracket vacuumConstantAction B=0 from sub_eq_zero.mpr vacuum_B.eq,hc,smul_zero,sub_zero]
  module

/-- The mixed Noether transport carries a native force current; the full scalar/geometric H0 current remains on its proper side. -/
theorem actual_reverse_joint_noether_current:
    bracket diagonalAction (bracket Z B)=
      bracket Z (bracket diagonalAction B)-(18:ℂ) • bracket diagonalAction B+
        (18:ℂ) • SourceScalarOscillatorAbsorption.scalarCurrent+(192:ℂ) • (U*scalarSpatialDivergence):=by
  have h:bracket diagonalAction (bracket Z B)=
      bracket Z (bracket diagonalAction B)-bracket (bracket Z diagonalAction) B:=by unfold bracket;noncomm_ring
  rw [h,actual_reverse_full_hamiltonian_scale]
  have he:bracket ((18:ℂ) • diagonalAction+reverseScaleForce) B=
      (18:ℂ) • bracket diagonalAction B+bracket reverseScaleForce B:=by
    unfold bracket;simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_sub];module
  rw [he,actual_reverse_force_scalar_current]
  module
end LowEnergy.ReverseNativeClock
