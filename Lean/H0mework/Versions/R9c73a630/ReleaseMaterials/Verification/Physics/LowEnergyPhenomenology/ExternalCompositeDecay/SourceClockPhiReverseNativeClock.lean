import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0RealPrimitives
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0KineticPrimitives
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPrimitiveCurrentCancellation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarGaugeScale SourceGaugeRadialCurrent SourceGaugeRadialPair
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceHamiltonianScaleJet SourceKineticScale
open SourceClockPhiCombinedScalePressure SourceClockPhiOriginalGaussianH0KineticPrimitives
open SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarInverseNativeEnergy FirstCurrentJointBudget
open SourceScalarPositiveBulkWard SourceHamiltonianVolume SourceInverseNoetherEnergy
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev Dc:End:=dilation
private abbrev B:End:=scalarBulkComplete
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction scalarKinetic scalarBulkComplete

/-- This is a fixed combination of the original scalar/gauge and coframe source generators. -/
def reverseNativeClock:End:=(3:ℂ) • D-(9*Complex.I:ℂ) • Dc
private abbrev Z:End:=reverseNativeClock
private def phiScale (r:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  (z.1,r • (vacuumSlice+z.2.1)-vacuumSlice,z.2.2)
private theorem phi_scale_one(z:SourceCoordinateSlice):phiScale 1 z=z:=by simp [phiScale]
private theorem phi_scale_derivative(z:SourceCoordinateSlice):
    HasDerivAt (fun r=>phiScale r z) (phiEuler z) 1:=by
  have hs:HasDerivAt (fun r:ℝ=>r • (vacuumSlice+z.2.1)-vacuumSlice) (vacuumSlice+z.2.1) 1:=by
    simpa only [id_eq,one_smul] using
      (((hasDerivAt_id (1:ℝ)).smul_const (vacuumSlice+z.2.1)).sub_const vacuumSlice)
  have hc:HasDerivAt (fun _:ℝ=>z.1) (0:Coframe) 1:=hasDerivAt_const _ _
  have hg:HasDerivAt (fun _:ℝ=>z.2.2) (0:coordinateSlice) 1:=hasDerivAt_const _ _
  exact hc.prodMk (hs.prodMk hg)
private theorem homogeneous_multiplier(E:End)(e:SourceCoordinateSlice→SourceCoordinateSlice)
    (flow:ℝ→SourceCoordinateSlice→SourceCoordinateSlice)
    (hE:∀f z,E f z=fderiv ℝ f z (e z))
    (hg:∀z,HasDerivAt (fun r=>flow r z) (e z) 1)(h1:∀z,flow 1 z=z)
    (A:End)(B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)(p:ℕ)
    (law:∀f z,A f z=B z (f z))(hp:∀r z,B (flow r z)=((r^p:ℝ):ℂ) • B z):
    E*A-A*E=(p:ℂ) • A:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hf:=(f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (hg z) (h1 z).symm
  have hA:=((A f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (hg z) (h1 z).symm
  have hb:=(B z).restrictScalars ℝ |>.hasFDerivAt |>.comp_hasDerivAt 1 hf
  have hr:HasDerivAt (fun r:ℝ=>((r^p:ℝ):ℂ)) (p:ℂ) 1:=by
    have h:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 ((hasDerivAt_id (1:ℝ)).pow p)
    simpa only [Function.comp_def,id_eq,one_pow,mul_one,Complex.ofRealCLM_apply,
      Complex.ofReal_natCast] using! h
  have hh:=hr.smul hb
  have hx:(fun r=>A f (flow r z))=(fun r:ℝ=>((r^p:ℝ):ℂ) • B z (f (flow r z))):=by
    funext r
    rw [law,hp]
    rfl
  change HasDerivAt (fun r=>A f (flow r z)) _ 1 at hA
  rw [hx] at hA
  have hu:=hA.unique hh
  simp only [Function.comp_def,one_pow,Complex.ofReal_one,one_smul,h1,
    ContinuousLinearMap.coe_restrictScalars'] at hu
  change E (A f) z-A (E f) z=(p:ℂ) • A f z
  rw [hE,law,hE,law,hu]
  exact add_sub_cancel_left _ _
private theorem phi_real_degree(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(p:ℕ)
    (hp:∀r z,b (phiScale r z)=r^p*b z):
    deltaPhi (multiply b hb)=(p:ℂ) • multiply b hb:=by
  apply homogeneous_multiplier phiEulerAction phiEuler phiScale phi_euler_apply
    phi_scale_derivative phi_scale_one (multiply b hb)
    (fun z=>(b z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) p (fun _ _=>rfl)
  intro r z
  rw [hp,Complex.ofReal_mul,smul_smul]
private theorem gauge_real_degree(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(p:ℕ)
    (hp:∀r z,b (gaugeScale r z)=r^p*b z):
    deltaGauge (multiply b hb)=(p:ℂ) • multiply b hb:=by
  apply homogeneous_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply
    (fun z=>gauge_scale_derivative z 1) gauge_scale_one (multiply b hb)
    (fun z=>(b z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) p (fun _ _=>rfl)
  intro r z
  rw [hp,Complex.ofReal_mul,smul_smul]

private theorem scale_real_degree(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(k:ℤ)
    (hk:∀r z,r≠0→b (SourceCoframeVolume.scale r z)=r^k*b z):
    scaleDerivative (multiply b hb)=(k:ℂ) • multiply b hb:=by
  have he(z:physicalChart):fderiv ℝ b z.val (SourceCoframeVolume.euler z.val)=
      (k:ℝ)*b z.val:=
    SourceKineticScale.euler_of_scale b k z (hb z) (fun r hr=>hk r z.val hr)
  have h:=SourceDilationMultiplier.homogeneous_multiplier b hb (k:ℝ) he
  change (3*Complex.I/2:ℂ) •
    (SourceCoframeVolumeCurrent.dilation*multiply b hb-
      multiply b hb*SourceCoframeVolumeCurrent.dilation)=_
  rw [h,smul_smul]
  congr 1
  push_cast
  calc
    (3*Complex.I/2)*((-2*Complex.I/3)*(k:ℂ))=
        -(Complex.I*Complex.I)*(k:ℂ):=by ring
    _=_:=by rw [Complex.I_mul_I];ring


private theorem combined_delta(T:End):bracket D T=deltaPhi T-deltaGauge T:=by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator T
  have hg:=SourceGaugeScaleTransport.generator_commutator T
  unfold D combinedGenerator bracket
  linear_combination (norm:=noncomm_ring) hp-hg
private theorem real_current(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(k:ℕ)
    (hp:∀r z,b (phiScale r z)=r^k*b z)
    (hg:∀r z,b (gaugeScale r z)=b z)
    (hc:∀r z,r≠0→b (SourceCoframeVolume.scale r z)=b z):
    bracket Z (multiply b hb)=(3*(k:ℂ)) • multiply b hb:=by
  have hD:bracket D (multiply b hb)=(k:ℂ) • multiply b hb:=by
    rw [combined_delta,phi_real_degree b hb k hp,gauge_real_degree b hb 0 (by simpa using hg),Nat.cast_zero,zero_smul,sub_zero]
  have hC:bracket Dc (multiply b hb)=0:=by
    have h:=scale_real_degree b hb 0 (by simpa using hc)
    norm_num only [Int.cast_zero,zero_smul] at h
    change (3*Complex.I/2:ℂ) • bracket Dc (multiply b hb)=0 at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  unfold Z reverseNativeClock bracket at *
  linear_combination (norm:=(noncomm_ring;module)) (3:ℂ) • hD-(9*Complex.I:ℂ) • hC
private theorem D_U:Commute D U:=by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator U
  have hg:=SourceGaugeScaleTransport.generator_commutator U
  rw [SourceScalarInverseBulk.inverse_phi] at hp
  rw [SourceScalarInverseBulk.inverse_gauge] at hg
  change (SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)*U=
    U*(SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)
  linear_combination (norm:=noncomm_ring) hp-hg
private theorem Dc_U:bracket Dc U=(2*Complex.I:ℂ) • U:=by
  have h:=congrArg (fun A:End=>(-2*Complex.I/3:ℂ) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3:ℂ) • ((3*Complex.I/2:ℂ) • bracket Dc U)=
    (-2*Complex.I/3:ℂ) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have he:(-2*Complex.I/3:ℂ)*(3*Complex.I/2)=1:=by
    calc _= -(Complex.I*Complex.I):=by ring
         _= _:=by rw [Complex.I_mul_I];ring
  rw [he,one_smul] at h
  convert h using 1;congr 1;ring
private theorem bracket_Z(T:End):bracket Z T=(3:ℂ) • bracket D T-(9*Complex.I:ℂ) • bracket Dc T:=by
  unfold Z reverseNativeClock bracket
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_sub]
  module
private theorem Z_U:bracket Z U=(18:ℂ) • U:=by
  have hd:bracket D U=0:=sub_eq_zero.mpr D_U.eq
  rw [bracket_Z,hd,Dc_U,smul_zero,zero_sub,smul_smul]
  have hi:(9*Complex.I)*(2*Complex.I)=(-18:ℂ):=by
    calc _=18*(Complex.I*Complex.I):=by ring
         _= _:=by rw [Complex.I_mul_I];ring
  rw [hi,neg_smul,neg_neg]
private theorem Z_scalar:bracket Z scalarKinetic=(12:ℂ) • scalarKinetic:=by
  have hd:bracket D scalarKinetic=(-2:ℂ) • scalarKinetic:=scalar_kinetic_primitives.2.2.1
  have hc:bracket Dc scalarKinetic=(2*Complex.I) • scalarKinetic:=SourceDilationKinetic.scalar_kinetic_current
  rw [bracket_Z,hd,hc,smul_smul,smul_smul,←sub_smul]
  congr 1
  calc _= -6-18*(Complex.I*Complex.I):=by ring
       _= _:=by rw [Complex.I_mul_I];ring
private theorem Z_inverse_scalar:bracket Z (U*scalarKinetic)=(30:ℂ) • (U*scalarKinetic):=by
  have h:bracket Z (U*scalarKinetic)=bracket Z U*scalarKinetic+U*bracket Z scalarKinetic:=by
    unfold bracket;noncomm_ring
  rw [h,Z_U,Z_scalar]
  simp only [smul_mul_assoc,mul_smul_comm]
  module
private def centerValue(z:SourceCoordinateSlice):ℝ:=n*‖scalarField z‖^2
private def linearValue(z:SourceCoordinateSlice):ℝ:=n*inner ℝ vacuum (scalarField z)
private theorem center_smooth(z:physicalChart):ContDiffAt ℝ ∞ centerValue z.val:=
  contDiffAt_const.mul (scalarField_smooth.norm_sq ℝ).contDiffAt
private theorem linear_smooth(z:physicalChart):ContDiffAt ℝ ∞ linearValue z.val:=
  contDiffAt_const.mul (contDiff_const.inner ℝ scalarField_smooth).contDiffAt
private theorem phi_field(r:ℝ)(z:SourceCoordinateSlice):scalarField (phiScale r z)=r • scalarField z:=by
  change vacuum+(r • (vacuum+(z.2.1:Scalar))-vacuum)=r • (vacuum+(z.2.1:Scalar))
  abel
private theorem local_inverse(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hv:∀z:physicalChart,ContDiffAt ℝ ∞ (fun z=>volume z*c z) z.val):
    U*multiply (fun z=>volume z*c z) hv=multiply c hc:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • (((volume z*c z:ℝ):ℂ) • f z)=(c z:ℂ) • f z
    rw [smul_smul,←Complex.ofReal_mul]
    have hv0:volume z≠0:=(volume_pos ⟨z,hz⟩).ne'
    unfold reciprocalVolume
    rw [inv_mul_cancel_left₀ hv0]
  · have hzero(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm
private theorem center_local:U*centeredAction=multiply centerValue center_smooth:=by
  convert local_inverse centerValue center_smooth (fun z=>volume_smooth.contDiffAt.mul (center_smooth z)) using 2
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (((n*volume z*‖scalarField z‖^2:ℝ):ℂ) • f z)=(((volume z*centerValue z:ℝ):ℂ) • f z)
  congr 1;unfold centerValue;push_cast;ring
private theorem linear_local:U*vacuumLinearAction=multiply linearValue linear_smooth:=by
  convert local_inverse linearValue linear_smooth (fun z=>volume_smooth.contDiffAt.mul (linear_smooth z)) using 2
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (((n*volume z*inner ℝ vacuum (scalarField z):ℝ):ℂ) • f z)=(((volume z*linearValue z:ℝ):ℂ) • f z)
  congr 1;unfold linearValue;push_cast;ring
private theorem constant_local:U*vacuumConstantAction=((n*‖vacuum‖^2:ℝ):ℂ) • (1:End):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • (((n*volume z*‖vacuum‖^2:ℝ):ℂ) • f z)=(((n*‖vacuum‖^2:ℝ):ℂ) • f z)
    rw [smul_smul,←Complex.ofReal_mul]
    congr 1;congr 1
    unfold reciprocalVolume
    field_simp [(volume_pos ⟨z,hz⟩).ne']
  · have hzero(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm
private theorem Z_center:bracket Z (U*centeredAction)=(6:ℂ) • (U*centeredAction):=by
  rw [center_local]
  have hp:∀r z,centerValue (phiScale r z)=r^2*centerValue z:=by
    intro r z;unfold centerValue;rw [phi_field,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs];ring
  simpa only [Nat.cast_ofNat,show (3:ℂ)*2=6 from by norm_num] using
    real_current centerValue center_smooth 2 hp (fun _ _=>rfl) (fun _ _ _=>rfl)
private theorem Z_linear:bracket Z (U*vacuumLinearAction)=(3:ℂ) • (U*vacuumLinearAction):=by
  rw [linear_local]
  have hp:∀r z,linearValue (phiScale r z)=r^1*linearValue z:=by
    intro r z;unfold linearValue;rw [phi_field,real_inner_smul_right,pow_one];ring
  simpa only [Nat.cast_one,mul_one] using
    real_current linearValue linear_smooth 1 hp (fun _ _=>rfl) (fun _ _ _=>rfl)
private theorem Z_constant:bracket Z (U*vacuumConstantAction)=0:=by
  rw [constant_local]
  unfold bracket
  simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,sub_self]
private theorem scalar_bulk_atoms:B=(-8:ℂ) • (U*scalarKinetic)+(8:ℂ) • (U*centeredAction)-
    (8:ℂ) • (U*vacuumLinearAction)+(2:ℂ) • (U*vacuumConstantAction):=by
  have h:=original_bulk_complete_split
  rw [bulkAction,positiveBulk,original_filtered_bulk] at h
  simp only [mul_add,mul_sub,mul_smul_comm] at h
  linear_combination (norm:=module) -h

/-- One actual balanced source current acts positively on both scalar kinetic and scalar potential directions. All original vacuum terms are retained. -/
theorem actual_reverse_clock_scalar_current:
    bracket Z B=(-240:ℂ) • (U*scalarKinetic)+(48:ℂ) • (U*centeredAction)-(24:ℂ) • (U*vacuumLinearAction):=by
  rw [scalar_bulk_atoms]
  have hk:=Z_inverse_scalar
  have hc:=Z_center
  have hl:=Z_linear
  have hv:=Z_constant
  unfold bracket at *
  linear_combination (norm:=(noncomm_ring;module)) (-8:ℂ) • hk+(8:ℂ) • hc-(8:ℂ) • hl+(2:ℂ) • hv
end LowEnergy.ReverseNativeClock
