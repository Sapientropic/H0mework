import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedPrimitiveCurrentSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarBalancedPrimitive
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarGaugeScale SourceCoframeVolume SourceDilationRemainder
open SourcePhysicalKineticSquare SourceClockPhiRadiusSourceCurrent SourceClockPhiRadiusAcceleration
open SourceClockPhiOriginalGaussianH0RealPrimitives SourceClockPhiOriginalGaussianH0KineticPrimitives
open FirstCurrentClockPrimitive ReverseBalancedForcePayer
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
private abbrev P:End:=positivePrimitive
private abbrev A:End:=gaugeBalancedNativeForce
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic matterAction positivePrimitive
  gaugeBalancedNativeForce sourcePair embed SourceScalarAffineScaleTransport.generator deltaPhi sourceTime
private theorem phi_scale_one(z:SourceCoordinateSlice):phiScale 1 z=z:=by simp [phiScale]
private theorem phi_scale_derivative(z:SourceCoordinateSlice):
    HasDerivAt (fun r=>phiScale r z) (phiEuler z) 1:=by
  have hs:HasDerivAt (fun r:ℝ=>r • (vacuumSlice+z.2.1)-vacuumSlice) (vacuumSlice+z.2.1) 1:=by
    simpa only [one_smul,id_eq] using
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
  unfold deltaPhi
  apply homogeneous_multiplier phiEulerAction phiEuler phiScale phi_euler_apply
    phi_scale_derivative phi_scale_one (multiply b hb)
    (fun z=>(b z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) p (fun _ _=>rfl)
  intro r z
  rw [hp,Complex.ofReal_mul,smul_smul]

private theorem phi_field(r:ℝ)(z:SourceCoordinateSlice):scalarField (phiScale r z)=r • scalarField z:=by
  change vacuum+(r • (vacuum+(z.2.1:Scalar))-vacuum)=r • (vacuum+(z.2.1:Scalar))
  abel
private theorem center_phi:deltaPhi centeredAction=(2:ℂ) • centeredAction:=by
  apply phi_real_degree _ _ 2
  intro r z
  change sourceTime 0*volume z*‖scalarField (phiScale r z)‖^2=r^2*(sourceTime 0*volume z*‖scalarField z‖^2)
  rw [phi_field,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
private theorem vac_phi:deltaPhi vacuumLinearAction=vacuumLinearAction:=by
  have h:=phi_real_degree (fun z=>sourceTime 0*volume z*inner ℝ vacuum (scalarField z))
    (fun z=>(contDiffAt_const.mul volume_smooth.contDiffAt).mul
      (contDiff_const.inner ℝ scalarField_smooth).contDiffAt) 1 (by
    intro r z
    change sourceTime 0*volume z*inner ℝ vacuum (scalarField (phiScale r z))=r^1*(sourceTime 0*volume z*inner ℝ vacuum (scalarField z))
    rw [phi_field,real_inner_smul_right,pow_one]
    ring)
  simpa only [Nat.cast_one,one_smul] using! h
private theorem invariant_real(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(he:∀r z,c (phiScale r z)=c z):
    deltaPhi (multiply c hc)=0:=by
  exact phi_invariant_local _ (fun z=>(c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _=>rfl) (fun r z=>by rw [he])
private theorem local_phi:deltaPhi localAction=(2:ℂ) • centeredAction-(2:ℂ) • vacuumLinearAction:=by
  let VP:End:=multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
  have hs:localAction=centeredAction-(2:ℂ) • vacuumLinearAction+vacuumConstantAction+VP:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    have hsub:scalarField z-vacuum=(z.2.1:Scalar):=by unfold scalarField;abel
    have hn:=norm_sub_sq_real (scalarField z) vacuum
    rw [hsub] at hn
    have hn' : ‖(z.2.1:Scalar)‖^2=‖scalarField z‖^2-2*inner ℝ vacuum (scalarField z)+‖vacuum‖^2:=by
      calc _= _:=hn
           _= _:=by rw [real_inner_comm]
    have hc:localPotential z=(sourceTime 0*volume z*‖scalarField z‖^2)-2*(sourceTime 0*volume z*inner ℝ vacuum (scalarField z))+(sourceTime 0*volume z*‖vacuum‖^2)+GaussCoframeForm.volumePotential z:=by
      unfold localPotential
      rw [real_inner_self_eq_norm_sq,hn']
      ring
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
      localAction,centeredAction,vacuumLinearAction,vacuumConstantAction,VP,multiply_apply,
      add_apply,sub_apply,smul_apply]
    rw [hc]
    push_cast
    simp only [add_smul,sub_smul,mul_smul]
    simp only [←mul_smul,←Complex.ofReal_mul,←Complex.ofReal_pow,←mul_assoc]
    rfl
  have hv:deltaPhi vacuumConstantAction=0:=invariant_real _ _ (fun _ _=>rfl)
  have hp:deltaPhi VP=0:=invariant_real _ _ (fun _ _=>rfl)
  rw [hs]
  simp only [map_add,map_sub,map_smul,center_phi,vac_phi,hv,hp,add_zero]

/-- The compensated force's scalar derivative is generated department by department, including the vacuum-linear and signed spatial terms. -/
theorem actual_balanced_force_scalar_derivative:
    bracket Phi A=(12:ℂ) • scalarKinetic-(60:ℂ) • centeredAction+
      (66:ℂ) • vacuumLinearAction-(84:ℂ) • scalarSpatialAction:=by
  have h:=SourceScalarAffineScaleTransport.generator_commutator A
  change bracket Phi A=deltaPhi A at h
  rw [h,show A=gaugeBalancedNativeForce from rfl,actual_balanced_native_departments]
  simp only [map_sub,map_add,map_smul,original_scalar_kinetic_phi,original_matter_phi,
    center_phi,vac_phi,original_magnetic_phi,local_phi,original_signed_spatial_phi,smul_zero,sub_zero,
    smul_smul,smul_sub]
  module
private theorem real_commute(c d:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)
private theorem end_sum_commute {R:Type*}[Ring R]{ι:Type*}[Fintype ι](T:ι→R)(B:R)
    (h:∀i,Commute (T i) B):Commute (∑i,T i) B:=by
  change (∑i,T i)*B=B*(∑i,T i)
  rw [Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _=>(h i).eq)
private theorem matter_inverse:Commute matterAction U:=by
  unfold matterAction
  apply end_sum_commute (R:=End);intro i
  apply end_sum_commute (R:=End);intro b
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact map_smul (GaussQuantumMultiplier.quantized (localMatrix i b z)) (reciprocalVolume z:ℂ) (f z)

/-- The complete compensated force is native and local, so the actual inverse volume commutes with it. -/
theorem actual_balanced_force_inverse:Commute A U:=by
  have hk:Commute scalarKinetic U:=scalar_kinetic_primitives.1.symm
  have hc:Commute centeredAction U:=real_commute _ _ _ _
  have hv:Commute vacuumLinearAction U:=real_commute _ _ _ _
  have hm:Commute magneticAction U:=real_commute _ _ _ _
  have hl:Commute localAction U:=real_commute _ _ _ _
  have hs:Commute scalarSpatialAction U:=real_commute _ _ _ _
  have hM:=matter_inverse
  change A*U=U*A
  rw [show A=gaugeBalancedNativeForce from rfl,actual_balanced_native_departments]
  linear_combination (norm:=noncomm_ring) (-6:ℂ) • hk.eq-(24:ℂ) • hM.eq+
    (6:ℂ) • hc.eq-(6:ℂ) • hv.eq-(72:ℂ) • hm.eq-(36:ℂ) • hl.eq-(42:ℂ) • hs.eq

/-- The actual force acceleration retains every scalar kinetic, center, vacuum and spatial coefficient. -/
def balancedPrimitiveAcceleration:End:=
  (-72:ℂ) • (U*scalarKinetic)+(360:ℂ) • (U*centeredAction)-
    (396:ℂ) • (U*vacuumLinearAction)+(504:ℂ) • (U*scalarSpatialAction)

theorem actual_balanced_primitive_acceleration:
    -bracket A (bracket A P)=balancedPrimitiveAcceleration:=by
  rw [actual_balanced_primitive_current]
  have hp:=actual_balanced_force_scalar_derivative
  have hu:=actual_balanced_force_inverse.eq
  unfold balancedPrimitiveAcceleration bracket at hp ⊢
  linear_combination (norm:=(noncomm_ring;module))
    (6:ℂ) • (hu*Phi-U*hp)
end LowEnergy.ScalarBalancedPrimitive
