import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNormalizedScalarBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiSecondPressure
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeSignedCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockAbelNativeContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCombinedScalePressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceGaugeRadialCurrent SourceGaugeRadialPair
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarVirialBulk SourceScalarGaugeScale
open SourcePhysicalKineticSquare SourcePhysicalHamiltonianSquare SourceScalarInverseNativeEnergy
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiNormalizedScalarBudget
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceHamiltonianVolume
open SourceClockReflectedForm SourceClockSourceTail
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U : End := inverseVolumeAction
private abbrev a : End := inverseRootAction
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev Gauge : End := SourceGaugeScaleTransport.generator
private abbrev H0 : End := diagonalAction
private abbrev n : ℝ := sourceTime 0
attribute [local irreducible] diagonalAction compressionCore defectAction resolventCore sourcePair embed

def combinedGenerator : End := Phi-Gauge
def combinedConjugate : End := a*combinedGenerator

def combinedPressureOperator : End :=
  bracket combinedConjugate (bracket combinedConjugate H0)+
    (2:ℂ) • (U*bracket combinedGenerator H0)+U*GaussMatterCore.matterAction+
    (9/8:ℂ) • (U*vacuumConstantAction)
def combinedPressure (f:QuantumTest) : ℝ := (sourcePair f (combinedPressureOperator f)).re

def shiftedColumn38 (i:ScalarIndex) : End := shiftedColumn i+
  ((inner ℝ vacuum (scalarBasis i)/8:ℝ):ℂ) • (1:End)
def shiftedMoment38 (f:QuantumTest) : ℝ := ∑i:ScalarIndex,‖embed (shiftedColumn38 i f)‖^2

private theorem lapse_pos : 0<n := by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem bracket_product (A B C:End) : bracket A (B*C)=bracket A B*C+B*bracket A C := by
  unfold bracket;noncomm_ring
private theorem product_bracket (A B C:End) : bracket (A*B) C=A*bracket B C+bracket A C*B := by
  unfold bracket;noncomm_ring
private theorem bracket_add (A B C:End) : bracket A (B+C)=bracket A B+bracket A C := by
  unfold bracket;noncomm_ring
private theorem bracket_smul (A B:End)(c:ℂ) : bracket A (c • B)=c • bracket A B := by
  unfold bracket;simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem combined_delta (A:End):bracket combinedGenerator A=deltaPhi A-deltaGauge A := by
  unfold combinedGenerator bracket
  rw [sub_mul,mul_sub]
  have hp:=SourceScalarAffineScaleTransport.generator_commutator A
  have hg:=SourceGaugeScaleTransport.generator_commutator A
  linear_combination (norm:=module) hp-hg
private theorem first_source : bracket combinedGenerator H0=
    (-2:ℂ) • scalarKinetic+(2:ℂ) • gaugeKinetic+(2:ℂ) • centeredAction-
      (2:ℂ) • vacuumLinearAction-(4:ℂ) • magneticAction-GaussMatterCore.matterAction := by
  rw [combined_delta]
  exact original_scalar_gauge_current

private theorem coframe_double_product (A D H:End)
    (ha:Commute A D)(hb:Commute A (bracket D H)):
    bracket (A*D) (bracket (A*D) H)=
      A*A*bracket D (bracket D H)+bracket A (bracket A H)*D*D := by
  have hda:bracket D A=0 := sub_eq_zero.mpr ha.eq.symm
  have had:bracket A D=0 := sub_eq_zero.mpr ha.eq
  have hab:bracket A (bracket D H)=0 := sub_eq_zero.mpr hb.eq
  have hdc:bracket D (bracket A H)=0 := by
    have hj:bracket D (bracket A H)=bracket A (bracket D H)+bracket (bracket D A) H := by
      unfold bracket;noncomm_ring
    rw [hj,hab,hda]
    simp [bracket]
  rw [product_bracket A D H,bracket_add,bracket_product,bracket_product]
  rw [product_bracket A D A,product_bracket A D (bracket D H),
    product_bracket A D (bracket A H),product_bracket A D D]
  simp only [hda,had,hab,hdc,zero_mul,mul_zero,add_zero,zero_add]
  have hz:bracket A A=0 := sub_self _
  have hzD:bracket D D=0 := sub_self _
  rw [hz,hzD]
  simp only [mul_zero,zero_mul,add_zero,zero_add,mul_assoc]


private def phiScale (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (z.1,r • (vacuumSlice+z.2.1)-vacuumSlice,z.2.2)
private theorem phi_scale_one (z : SourceCoordinateSlice) : phiScale 1 z=z := by
  simp [phiScale]
private theorem phi_scale_derivative (z : SourceCoordinateSlice) :
    HasDerivAt (fun r => phiScale r z) (phiEuler z) 1 := by
  simpa only [phiScale,phiEuler,id_eq,one_smul] using!
    (hasDerivAt_const (1 : ℝ) z.1).prodMk
      ((((hasDerivAt_id (1 : ℝ)).smul_const (vacuumSlice+z.2.1)).sub_const vacuumSlice).prodMk
        (hasDerivAt_const (1 : ℝ) z.2.2))


private theorem homogeneous_multiplier (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (flow : ℝ → SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z))
    (hg : ∀ z,HasDerivAt (fun r => flow r z) (e z) 1) (h1 : ∀ z,flow 1 z=z)
    (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber) (p : ℕ)
    (law : ∀ f z,A f z=B z (f z)) (hp : ∀ r z,B (flow r z)=((r^p : ℝ) : ℂ) • B z) :
    E*A-A*E=(p : ℂ) • A := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (hg z) (h1 z).symm
  have hA := ((A f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (hg z) (h1 z).symm
  have hb := (B z).restrictScalars ℝ |>.hasFDerivAt |>.comp_hasDerivAt 1 hf
  have hr : HasDerivAt (fun r : ℝ => ((r^p : ℝ) : ℂ)) (p : ℂ) 1 := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).pow p)
    simpa only [Function.comp_def,id_eq,one_pow,mul_one,Complex.ofRealCLM_apply,Complex.ofReal_natCast] using! h
  have hh := hr.smul hb
  have hx : (fun r => A f (flow r z))=(fun r : ℝ => ((r^p : ℝ) : ℂ) • B z (f (flow r z))) := by
    funext r
    rw [law,hp]
    rfl
  change HasDerivAt (fun r => A f (flow r z)) _ 1 at hA
  rw [hx] at hA
  have hu := hA.unique hh
  simp only [Function.comp_def,one_pow,Complex.ofReal_one,one_smul,h1,
    ContinuousLinearMap.coe_restrictScalars'] at hu
  change E (A f) z-A (E f) z=(p : ℂ) • A f z
  rw [hE,law,hE,law,hu]
  exact add_sub_cancel_left _ _


private theorem phi_degree (A:End)(c:SourceCoordinateSlice→ℝ)(p:ℕ)
    (law:∀f z,A f z=(c z:ℂ) • f z)(hc:∀t z,c (phiScale t z)=t^p*c z):
    deltaPhi A=(p:ℂ) • A := by
  apply homogeneous_multiplier phiEulerAction phiEuler phiScale phi_euler_apply
    phi_scale_derivative phi_scale_one A
    (fun z=>(c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) p law
  intro t z
  rw [hc,Complex.ofReal_mul,smul_smul]
private theorem gauge_degree (A:End)(c:SourceCoordinateSlice→ℝ)(p:ℕ)
    (law:∀f z,A f z=(c z:ℂ) • f z)(hc:∀t z,c (gaugeScale t z)=t^p*c z):
    deltaGauge A=(p:ℂ) • A := by
  apply homogeneous_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply
    (fun z=>gauge_scale_derivative z 1) gauge_scale_one A
    (fun z=>(c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) p law
  intro t z
  rw [hc,Complex.ofReal_mul,smul_smul]
private theorem phi_field (t:ℝ)(z:SourceCoordinateSlice):scalarField (phiScale t z)=t • scalarField z := by
  change vacuum+(t • (vacuum+(z.2.1:Scalar))-vacuum)=t • (vacuum+(z.2.1:Scalar))
  abel
private theorem centered_phi : deltaPhi centeredAction=(2:ℂ) • centeredAction := by
  apply phi_degree centeredAction (fun z=>n*volume z*‖scalarField z‖^2) 2 (fun _ _=>rfl)
  intro t z
  change n*volume z*‖scalarField (phiScale t z)‖^2=t^2*(n*volume z*‖scalarField z‖^2)
  rw [phi_field,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
private theorem vacuum_phi : deltaPhi vacuumLinearAction=vacuumLinearAction := by
  have h:=phi_degree vacuumLinearAction (fun z=>n*volume z*inner ℝ vacuum (scalarField z)) 1
    (fun _ _=>rfl) (by
      intro t z
      change n*volume z*inner ℝ vacuum (scalarField (phiScale t z))=t^1*(n*volume z*inner ℝ vacuum (scalarField z))
      rw [phi_field,real_inner_smul_right,pow_one]
      ring)
  simpa only [Nat.cast_one,one_smul] using h
private theorem centered_gauge : deltaGauge centeredAction=0 := by
  have h:=gauge_degree centeredAction (fun z=>n*volume z*‖scalarField z‖^2) 0
    (fun _ _=>rfl) (by intro t z;simp only [pow_zero,one_mul];rfl)
  simpa only [Nat.cast_zero,zero_smul] using h
private theorem vacuum_gauge : deltaGauge vacuumLinearAction=0 := by
  have h:=gauge_degree vacuumLinearAction (fun z=>n*volume z*inner ℝ vacuum (scalarField z)) 0
    (fun _ _=>rfl) (by intro t z;simp only [pow_zero,one_mul];rfl)
  simpa only [Nat.cast_zero,zero_smul] using h
private theorem root_phi : deltaPhi a=0 := by
  have h:=phi_degree a inverseRootVolume 0 (fun _ _=>rfl)
    (by intro t z;simp only [pow_zero,one_mul];rfl)
  simpa only [Nat.cast_zero,zero_smul] using h
private theorem root_gauge : deltaGauge a=0 := by
  have h:=gauge_degree a inverseRootVolume 0 (fun _ _=>rfl)
    (by intro t z;simp only [pow_zero,one_mul];rfl)
  simpa only [Nat.cast_zero,zero_smul] using h
private theorem root_combined : Commute a combinedGenerator := by
  have h:=combined_delta a
  rw [root_phi,root_gauge,sub_zero] at h
  exact (sub_eq_zero.mp h).symm
private theorem second_source : bracket combinedGenerator (bracket combinedGenerator H0)+
    (2:ℂ) • bracket combinedGenerator H0=
      (8:ℂ) • gaugeKinetic+(8:ℂ) • centeredAction-(6:ℂ) • vacuumLinearAction+
        (8:ℂ) • magneticAction-GaussMatterCore.matterAction := by
  simp only [first_source]
  simp only [combined_delta,map_add,map_sub,map_smul,
    original_scalar_kinetic_phi,original_scalar_kinetic_gauge,original_gauge_kinetic_phi,
    original_gauge_kinetic_gauge,centered_phi,centered_gauge,vacuum_phi,vacuum_gauge,
    original_magnetic_phi,original_magnetic_gauge,original_matter_phi,original_matter_gauge]
  module


private theorem pair_add_l (f g h:QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (f g h:QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l (f g h:QuantumTest) : sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r (f g h:QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l (c:ℂ)(f g:QuantumTest) : sourcePair (c • f) g=(starRingEnd ℂ c)*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_r (c:ℂ)(f g:QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sum_r {ι:Type*}[Fintype ι] (f:QuantumTest)(v:ι → QuantumTest) :
    sourcePair f (∑i,v i)=∑i,sourcePair f (v i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem self_pair (f:QuantumTest) : sourcePair f f=(‖embed f‖^2:ℂ) := by
  simpa only [sourcePair,Complex.ofReal_pow] using!
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed f)
private theorem flow_pair_generator (flow:ℝ → End)(G:End)
    (hzero:∀f,flow 0 f=f)
    (hpair:∀t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv:∀f,HasDerivAt (fun t:ℝ=>embed (flow t f)) (embed (G f)) 0)
    (f g:QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t:ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=fun _=>inner ℂ (embed f) (embed g) :=
    funext (fun t=>hpair t f g)
  rw [he] at h
  have heq:=h.unique (hasDerivAt_const (0:ℝ) (inner ℂ (embed f) (embed g)))
  exact eq_neg_of_add_eq_zero_left heq
private theorem phi_pair (f g:QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem gauge_pair (f g:QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
private theorem combined_pair (f g:QuantumTest) :
    sourcePair f (combinedGenerator g)= -sourcePair (combinedGenerator f) g := by
  simp only [combinedGenerator,LinearMap.sub_apply,pair_sub_l,pair_sub_r,phi_pair,gauge_pair]
  ring
private theorem root_square : a*a=U := by
  apply LinearMap.ext;intro f
  exact inverse_root_square f
private theorem weight_combined : Commute U combinedGenerator := by
  rw [←root_square]
  exact root_combined.mul_left root_combined
private theorem weight_pair (f g:QuantumTest) : sourcePair f (U g)=sourcePair (U f) g :=
  multiply_pair _ _ f g
private theorem root_pair (f g:QuantumTest) : sourcePair f (a g)=sourcePair (a f) g :=
  multiply_pair _ _ f g
private theorem weighted_combined_square (f:QuantumTest) :
    sourcePair f ((U*U*combinedGenerator*combinedGenerator) f)=
      -(‖embed (U (combinedGenerator f))‖^2:ℂ) := by
  have hc:=LinearMap.congr_fun weight_combined.eq (combinedGenerator f)
  change U (combinedGenerator (combinedGenerator f))=combinedGenerator (U (combinedGenerator f)) at hc
  change sourcePair f (U (U (combinedGenerator (combinedGenerator f))))=_
  rw [weight_pair,hc,combined_pair]
  have hd:=LinearMap.congr_fun weight_combined.eq f
  change U (combinedGenerator f)=combinedGenerator (U f) at hd
  rw [←hd,self_pair]
private theorem root_form (B:End)(hc:Commute a B)(f:QuantumTest) :
    sourcePair f ((U*B) f)=sourcePair (a f) (B (a f)) := by
  rw [←root_square]
  change sourcePair f (a (a (B f)))=_
  rw [root_pair]
  exact congrArg (sourcePair (a f)) (LinearMap.congr_fun hc.eq f)
private theorem shifted38_point (i:ScalarIndex)(f:QuantumTest)(x:SourceCoordinateSlice) :
    shiftedColumn38 i f x=(inner ℝ (scalarField x-(3/8:ℝ) • vacuum) (scalarBasis i):ℂ) • f x := by
  change (shiftedCoordinate i x:ℂ) • f x+((inner ℝ vacuum (scalarBasis i)/8:ℝ):ℂ) • f x=_
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
  unfold shiftedCoordinate
  simp only [inner_sub_left,real_inner_smul_left]
  ring
private theorem shifted38_pair (i:ScalarIndex)(f g:QuantumTest) :
    sourcePair f (shiftedColumn38 i g)=sourcePair (shiftedColumn38 i f) g := by
  have hs:sourcePair f (shiftedColumn i g)=sourcePair (shiftedColumn i f) g := multiply_pair _ _ _ _
  simp only [shiftedColumn38,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,hs,Complex.conj_ofReal]
private theorem potential_completion :
    U*((8:ℂ) • centeredAction-(6:ℂ) • vacuumLinearAction+(9/8:ℂ) • vacuumConstantAction)=
      (8*(n:ℂ)) • ∑i:ScalarIndex,shiftedColumn38 i*shiftedColumn38 i := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  have hs:(∑i:ScalarIndex,(inner ℝ (scalarField x-(3/8:ℝ) • vacuum) (scalarBasis i))^2)=
      ‖scalarField x-(3/8:ℝ) • vacuum‖^2 := scalarBasis.sum_sq_inner_left _
  have hp:8*‖scalarField x‖^2-6*inner ℝ vacuum (scalarField x)+(9/8:ℝ)*‖vacuum‖^2=
      8*‖scalarField x-(3/8:ℝ) • vacuum‖^2 := by
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
      real_inner_comm vacuum (scalarField x)]
    norm_num
    ring
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply]
  change (reciprocalVolume x:ℂ) • ((8:ℂ) • ((n*volume x*‖scalarField x‖^2:ℝ):ℂ) • f x-
    (6:ℂ) • ((n*volume x*inner ℝ vacuum (scalarField x):ℝ):ℂ) • f x+
    (9/8:ℂ) • ((n*volume x*‖vacuum‖^2:ℝ):ℂ) • f x)=
      (8*(n:ℂ)) • ((∑i:ScalarIndex,shiftedColumn38 i (shiftedColumn38 i f)) x)
  rw [sum_apply]
  simp only [shifted38_point,smul_smul,←pow_two,←Finset.sum_smul,←Complex.ofReal_pow,
    ←Complex.ofReal_sum,hs]
  by_cases hx:x ∈ physicalChart
  · have hc:reciprocalVolume x*(8*(n*volume x*‖scalarField x‖^2)-
        6*(n*volume x*inner ℝ vacuum (scalarField x))+(9/8:ℝ)*(n*volume x*‖vacuum‖^2))=
        8*n*‖scalarField x-(3/8:ℝ) • vacuum‖^2 := by
      unfold reciprocalVolume
      have hv:volume x≠0:=(volume_pos ⟨x,hx⟩).ne'
      field_simp [hv]
      linear_combination (norm:=ring) (8*n)*hp
    simp only [←add_smul,←sub_smul,smul_smul]
    simpa only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_div,
      Complex.ofReal_ofNat] using congrArg (fun c:ℝ=>(c:ℂ) • f x) hc
  · rw [image_eq_zero_of_notMem_tsupport (fun h=>hx (f.tsupport_subset h))]
    simp only [smul_zero,sub_self,zero_add]
private theorem shifted38_square_pair (f:QuantumTest) :
    sourcePair f ((∑i:ScalarIndex,shiftedColumn38 i*shiftedColumn38 i) f)=
      (shiftedMoment38 f:ℂ) := by
  simp only [LinearMap.sum_apply,Module.End.mul_apply,pair_sum_r,shifted38_pair,self_pair,
    ←Complex.ofReal_pow,←Complex.ofReal_sum,shiftedMoment38]

private theorem pair_sum_l {ι:Type*}[Fintype ι] (v:ι → QuantumTest)(f:QuantumTest) :
    sourcePair (∑i,v i) f=∑i,sourcePair (v i) f := by
  simp only [sourcePair,map_sum,sum_inner]
private theorem pair_star (f g:QuantumTest) :
    starRingEnd ℂ (sourcePair f g)=sourcePair g f := by
  unfold sourcePair
  exact inner_conj_symm _ _
private theorem paired_bracket {D A:End}
    (hD:∀f g,sourcePair f (D g)= -sourcePair (D f) g)
    (hA:GaussCoframeForm.Paired A A) : GaussCoframeForm.Paired (bracket D A) (bracket D A) := by
  intro f g
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_l,pair_sub_r]
  rw [hD,hA,hA,hD]
  ring
private theorem bracket_commute {D A B:End}(hD:Commute D B)(hA:Commute A B) :
    Commute (bracket D A) B :=
  (hD.mul_left hA).sub_left (hA.mul_left hD)
private theorem bracket_apply (D A:End)(f:QuantumTest) :
    D (A f)=bracket D A f+A (D f) := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
  module
private theorem paired_move_weight {A:End}(hA:GaussCoframeForm.Paired A A)(hU:Commute U A)
    (f g:QuantumTest) : sourcePair f (U (A g))=sourcePair (A f) (U g) := by
  have he:=LinearMap.congr_fun hU.eq g
  change U (A g)=A (U g) at he
  rw [he,hA]

private theorem matrix_phase_source {ι:Type*}[Fintype ι] (W:ι → End)(X:ι → QuantumTest)
    (hW:∀i,GaussCoframeForm.Paired (W i) (W i))
    (hU:∀i,Commute U (W i)) :
    (∑i,∑j,sourcePair (X i)
      (((1/2:ℂ) • (U*(bracket combinedGenerator (W i*W j)*combinedGenerator+
        combinedGenerator*bracket combinedGenerator (W i*W j)))) (X j)))=
      sourcePair (∑i,bracket combinedGenerator (W i) (X i))
        (U (combinedGenerator (∑i,W i (X i))))-
      sourcePair (U (combinedGenerator (∑i,W i (X i))))
        (∑i,bracket combinedGenerator (W i) (X i))-
      (1/2:ℂ)*(sourcePair (∑i,W i (X i))
          (U (∑i,bracket combinedGenerator (bracket combinedGenerator (W i)) (X i)))-
        sourcePair (U (∑i,bracket combinedGenerator (bracket combinedGenerator (W i)) (X i)))
          (∑i,W i (X i))) := by
  let B:ι → End:=fun i=>bracket combinedGenerator (W i)
  let C:ι → End:=fun i=>bracket combinedGenerator (B i)
  have hB(i):GaussCoframeForm.Paired (B i) (B i):=paired_bracket combined_pair (hW i)
  have hUB(i):Commute U (B i):=(bracket_commute weight_combined.symm (hU i).symm).symm
  have hrow(i j):sourcePair (X i)
      (((1/2:ℂ) • (U*(bracket combinedGenerator (W i*W j)*combinedGenerator+
        combinedGenerator*bracket combinedGenerator (W i*W j)))) (X j))=
      (1/2:ℂ)*(sourcePair (B i (X i)) (U (W j (combinedGenerator (X j))))+
        sourcePair (W i (X i)) (U (B j (combinedGenerator (X j))))-
        sourcePair (B i (combinedGenerator (X i))) (U (W j (X j)))-
        sourcePair (W i (combinedGenerator (X i))) (U (B j (X j)))) := by
    rw [bracket_product]
    simp only [LinearMap.smul_apply,Module.End.mul_apply,LinearMap.add_apply,pair_smul_r,
      pair_add_r,map_add]
    have hd(f g:QuantumTest):sourcePair f (U (combinedGenerator g))=
        -sourcePair (combinedGenerator f) (U g) := by
      have he:=LinearMap.congr_fun weight_combined.eq g
      change U (combinedGenerator g)=combinedGenerator (U g) at he
      rw [he,combined_pair]
    rw [hd,hd]
    rw [paired_move_weight (hB i) (hUB i),paired_move_weight (hW i) (hU i),
      paired_move_weight (hB i) (hUB i),paired_move_weight (hW i) (hU i)]
    ring
  have hv: (∑i,W i (combinedGenerator (X i)))=
      combinedGenerator (∑i,W i (X i))-(∑i,B i (X i)) := by
    simp only [map_sum,bracket_apply combinedGenerator]
    dsimp only [B]
    rw [Finset.sum_add_distrib]
    abel
  have hb: (∑i,B i (combinedGenerator (X i)))=
      combinedGenerator (∑i,B i (X i))-(∑i,C i (X i)) := by
    simp only [map_sum,bracket_apply combinedGenerator]
    dsimp only [C]
    rw [Finset.sum_add_distrib]
    abel
  simp_rw [hrow]
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [←pair_sum_r,←pair_sum_l,←map_sum]
  rw [hv,hb]
  simp only [map_sub,pair_sub_l,pair_sub_r]
  have ht(f g:QuantumTest):sourcePair f (U (combinedGenerator g))=
      -sourcePair (U (combinedGenerator f)) g := by
    rw [weight_pair,combined_pair]
    have he:=LinearMap.congr_fun weight_combined.eq f
    change U (combinedGenerator f)=combinedGenerator (U f) at he
    rw [←he]
  simp only [ht,weight_pair]
  dsimp only [B,C]
  ring

private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev T (m ell:ℕ):End:=phiThetaAction m ell

def phaseRow(m ell:ℕ)(i:Fin 2):End:=![T m ell,-(S*T m ell)] i
def phaseSeed(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):Fin 2 → QuantumTest:=
  ![resolventCore F z hz (coreEquiv.symm g),resolventCore F z hz (r (coreEquiv.symm g))]
def phaseFirst(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  ∑i,bracket Phi (phaseRow m ell i) (phaseSeed F z hz g i)
def phaseSecond(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  ∑i,bracket Phi (bracket Phi (phaseRow m ell i)) (phaseSeed F z hz g i)
def phaseContact(m ell:ℕ)(i j:Fin 2):End:=
  (1/2:ℂ) • (U*(bracket Phi (phaseRow m ell i*phaseRow m ell j)*combinedGenerator+
    combinedGenerator*bracket Phi (phaseRow m ell i*phaseRow m ell j)))
def combinedPhase(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  -2*z.im*(∑i,∑j,sourcePair (phaseSeed F z hz g i)
    (phaseContact m ell i j (phaseSeed F z hz g j))).im

private theorem real_commute (c d:SourceCoordinateSlice → ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : r*S=(1:End):=(real_commute _ _ _ _).eq.symm.trans inverse_radius
private theorem theta_commute {A:End}(hA:Commute A S)(m ell:ℕ):Commute A (T m ell):=
  (((Commute.one_right A).sub_right hA).pow_right (m+1)).sub_right
    (((Commute.one_right A).sub_right hA).pow_right (ell+1))
private theorem pair_product {A B:End}(hA:GaussCoframeForm.Paired A A)
    (hB:GaussCoframeForm.Paired B B)(hc:Commute A B):GaussCoframeForm.Paired (A*B) (A*B) := by
  intro f g
  change sourcePair f (A (B g))=sourcePair (A (B f)) g
  rw [hA,hB]
  exact congrArg (fun h=>sourcePair h g) (LinearMap.congr_fun hc.eq f).symm
private theorem pair_power {A:End}(hA:GaussCoframeForm.Paired A A)(k:ℕ):
    GaussCoframeForm.Paired (A^k) (A^k) := by
  induction k with
  | zero => intro f g;rfl
  | succ k ih => rw [pow_succ];exact pair_product ih hA ((Commute.refl A).pow_left k)
private theorem pair_sub {A B:End}(hA:GaussCoframeForm.Paired A A)(hB:GaussCoframeForm.Paired B B):
    GaussCoframeForm.Paired (A-B) (A-B) := by
  intro f g
  simp only [LinearMap.sub_apply,pair_sub_l,pair_sub_r]
  rw [hA,hB]
private theorem theta_pair(m ell:ℕ):GaussCoframeForm.Paired (T m ell) (T m ell) := by
  have h1:GaussCoframeForm.Paired (1:End) 1:=by intro f g;rfl
  exact pair_sub (pair_power (pair_sub h1 (multiply_pair _ _)) (m+1))
    (pair_power (pair_sub h1 (multiply_pair _ _)) (ell+1))
private theorem row_pair(m ell:ℕ)(i:Fin 2):GaussCoframeForm.Paired (phaseRow m ell i) (phaseRow m ell i) := by
  fin_cases i
  · exact theta_pair m ell
  · intro f g
    change sourcePair f (-(S*(T m ell)) g)=sourcePair (-(S*(T m ell)) f) g
    have hp:sourcePair f ((S*T m ell) g)=sourcePair ((S*T m ell) f) g:=
      pair_product (show GaussCoframeForm.Paired S S from multiply_pair _ _) (theta_pair m ell)
        (theta_commute (Commute.refl S) m ell) f g
    simpa only [sourcePair,map_neg,inner_neg_left,inner_neg_right] using congrArg Neg.neg hp
private theorem row_weight(m ell:ℕ)(i:Fin 2):Commute U (phaseRow m ell i) := by
  have hs:Commute U S:=real_commute _ _ _ _
  fin_cases i
  · exact theta_commute hs m ell
  · exact (hs.mul_right (theta_commute hs m ell)).neg_right
private theorem phi_inverse : bracket Phi S=S^3-S := by
  have hr:bracket Phi r=r-S := by
    have h:=original_phi_euler_radius
    change bracket phiEulerAction r=r-S at h
    unfold bracket at h
    change (phiEulerAction+(61/2:ℂ) • (1:End))*r-r*(phiEulerAction+(61/2:ℂ) • (1:End))=_
    linear_combination (norm:=noncomm_ring) h
  have hi:bracket Phi S= -(S*bracket Phi r*S) := by
    have h1:S*Phi*r*S=S*Phi := by rw [mul_assoc (S*Phi),radius_inverse,mul_one]
    have h2:S*r*Phi*S=Phi*S := by rw [inverse_radius,one_mul]
    calc
      _= -(S*Phi*r*S-S*r*Phi*S) := by rw [h1,h2];unfold bracket;abel
      _=_ := by unfold bracket;noncomm_ring
  rw [hi,hr]
  calc
    _= -((S*r)*S)+S^3 := by noncomm_ring
    _=_ := by rw [inverse_radius,one_mul];abel
private theorem gauge_inverse : Commute Gauge S := by
  have h:=gauge_degree S phiReciprocal 0 (fun _ _=>rfl)
    (by intro t z;simp only [pow_zero,one_mul];rfl)
  have hg:=SourceGaugeScaleTransport.generator_commutator S
  rw [h] at hg
  simp only [Nat.cast_zero,zero_smul] at hg
  exact sub_eq_zero.mp hg
private def GaugeRegular(A:End):Prop:=Commute Gauge A ∧ Commute Gauge (bracket Phi A)
private theorem regular_one : GaugeRegular (1:End) := by
  refine ⟨Commute.one_right _,?_⟩
  have hz:bracket Phi (1:End)=0:=by simp [bracket]
  rw [hz]
  exact Commute.zero_right _
private theorem regular_inverse : GaugeRegular S := by
  refine ⟨gauge_inverse,?_⟩
  rw [phi_inverse]
  exact (gauge_inverse.pow_right 3).sub_right gauge_inverse
private theorem regular_sub {A B:End}(hA:GaugeRegular A)(hB:GaugeRegular B):GaugeRegular (A-B) := by
  refine ⟨hA.1.sub_right hB.1,?_⟩
  have he:bracket Phi (A-B)=bracket Phi A-bracket Phi B:=by unfold bracket;noncomm_ring
  rw [he]
  exact hA.2.sub_right hB.2
private theorem regular_mul {A B:End}(hA:GaugeRegular A)(hB:GaugeRegular B):GaugeRegular (A*B) := by
  refine ⟨hA.1.mul_right hB.1,?_⟩
  rw [bracket_product]
  exact (hA.2.mul_right hB.1).add_right (hA.1.mul_right hB.2)
private theorem regular_power {A:End}(hA:GaugeRegular A)(k:ℕ):GaugeRegular (A^k) := by
  induction k with
  | zero => simpa only [pow_zero] using regular_one
  | succ k ih => rw [pow_succ];exact regular_mul ih hA
private theorem regular_theta(m ell:ℕ):GaugeRegular (T m ell):=
  regular_sub (regular_power (regular_sub regular_one regular_inverse) (m+1))
    (regular_power (regular_sub regular_one regular_inverse) (ell+1))
private theorem regular_row(m ell:ℕ)(i:Fin 2):GaugeRegular (phaseRow m ell i) := by
  fin_cases i
  · exact regular_theta m ell
  · have h:=regular_mul regular_inverse (regular_theta m ell)
    refine ⟨h.1.neg_right,?_⟩
    have he:bracket Phi (-(S*T m ell))= -bracket Phi (S*T m ell):=by unfold bracket;noncomm_ring
    change Commute Gauge (bracket Phi (-(S*T m ell)))
    rw [he]
    exact h.2.neg_right
private theorem combined_regular {A:End}(hA:Commute Gauge A):bracket combinedGenerator A=bracket Phi A := by
  unfold combinedGenerator bracket
  linear_combination (norm:=noncomm_ring) -hA.eq
private theorem rows_sum(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (∑i,phaseRow m ell i (phaseSeed F z hz g i))=normalizedState m ell F z hz g := by
  simp only [Fin.sum_univ_two,phaseRow,phaseSeed,Matrix.cons_val_zero,Matrix.cons_val_one,
    LinearMap.neg_apply]
  rfl
private theorem phase_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    combinedPhase m ell F z hz g=
      -4*z.im*(sourcePair (phaseFirst m ell F z hz g)
        (U (combinedGenerator (normalizedState m ell F z hz g)))).im+
      2*z.im*(sourcePair (normalizedState m ell F z hz g) (U (phaseSecond m ell F z hz g))).im := by
  have h:=matrix_phase_source (phaseRow m ell) (phaseSeed F z hz g) (row_pair m ell) (row_weight m ell)
  have h1(i):bracket combinedGenerator (phaseRow m ell i)=bracket Phi (phaseRow m ell i):=
    combined_regular (regular_row m ell i).1
  have h2(i):bracket combinedGenerator (bracket Phi (phaseRow m ell i))=
      bracket Phi (bracket Phi (phaseRow m ell i)):=combined_regular (regular_row m ell i).2
  have hN(i j):bracket combinedGenerator (phaseRow m ell i*phaseRow m ell j)=
      bracket Phi (phaseRow m ell i*phaseRow m ell j):=
    combined_regular ((regular_row m ell i).1.mul_right (regular_row m ell j).1)
  simp_rw [hN,h1,h2] at h
  rw [rows_sum] at h
  change (∑i,∑j,sourcePair (phaseSeed F z hz g i) (phaseContact m ell i j (phaseSeed F z hz g j)))=
    sourcePair (phaseFirst m ell F z hz g) (U (combinedGenerator (normalizedState m ell F z hz g)))-
      sourcePair (U (combinedGenerator (normalizedState m ell F z hz g))) (phaseFirst m ell F z hz g)-
      (1/2:ℂ)*(sourcePair (normalizedState m ell F z hz g) (U (phaseSecond m ell F z hz g))-
        sourcePair (U (phaseSecond m ell F z hz g)) (normalizedState m ell F z hz g)) at h
  unfold combinedPhase
  rw [h,←pair_star (phaseFirst m ell F z hz g),←pair_star (normalizedState m ell F z hz g)]
  norm_num only [Complex.sub_im,Complex.mul_im,map_div₀,map_ofNat,map_one,Complex.conj_im,
    Complex.div_re,Complex.div_im,Complex.normSq_apply,Complex.re_ofNat,Complex.im_ofNat,
    Complex.one_re,Complex.one_im,zero_mul,mul_zero,zero_add,add_zero,sub_zero]
  ring

private theorem phi_inverse_core(f:QuantumTest):phiInverseBounded (embed f)=embed (S f):=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem phi_inverse_norm:‖phiInverseBounded‖ ≤ 1:=GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem normalized_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=S (phiResponseCore m ell F z hz g) := by
  have hc(f:QuantumTest):S (T m ell f)=T m ell (S f):=
    LinearMap.congr_fun (theta_commute (Commute.refl S) m ell).eq f
  have hi(f:QuantumTest):S (r f)=f:=LinearMap.congr_fun inverse_radius f
  change T m ell (resolventCore F z hz (coreEquiv.symm g))-
    S (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))=
    S (T m ell (r (resolventCore F z hz (coreEquiv.symm g))-
      resolventCore F z hz (r (coreEquiv.symm g))))
  simp only [map_sub,hc,hi]
private theorem normalized_weight_norm(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    ‖embed (U (normalizedState m ell F z hz g))‖ ≤ ‖embed (U (phiResponseCore m ell F z hz g))‖ := by
  rw [normalized_return]
  have hc:Commute U S:=real_commute _ _ _ _
  have he:=LinearMap.congr_fun hc.eq (phiResponseCore m ell F z hz g)
  change U (S (phiResponseCore m ell F z hz g))=S (U (phiResponseCore m ell F z hz g)) at he
  rw [he,←phi_inverse_core]
  exact (phiInverseBounded.le_opNorm _).trans ((mul_le_mul_of_nonneg_right phi_inverse_norm
    (norm_nonneg _)).trans_eq (one_mul _))
private theorem normalized_weight_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    25*n^2/4*‖embed (U (normalizedState m ell F z hz g))‖^2 ≤ phiPositivePrice m ell F z hz g := by
  let v:=phiResponseCore m ell F z hz g
  have hf:=SourceClockSourceTail.original_inverse_coframe_floor (U v)
  have hp:=actual_phi_positive_slots m ell F z hz g
  have hc:=mul_le_mul_of_nonneg_left hf (show 0 ≤ n^2/4 by positivity)
  have hs:0 ≤ scalarForm (U v):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hs':0 ≤ n^2/2*scalarForm (U v):=mul_nonneg (by positivity) hs
  have hv:0 ≤ 6*n^2*‖embed v‖^2:=by positivity
  change n^2/4*coframeGram (U v)+n^2/2*scalarForm (U v)+6*n^2*‖embed v‖^2 ≤
    phiPositivePrice m ell F z hz g at hp
  have hnorm:=normalized_weight_norm m ell F z hz g
  have hnormsq:=sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hnorm
  have hscaled:=mul_le_mul_of_nonneg_left hnormsq (show 0 ≤ 25*n^2/4 by positivity)
  nlinarith only [hp,hc,hs',hv,hscaled]
private theorem young(x y t:ℝ)(ht:0<t):x*y ≤ t*x^2+y^2/(4*t) := by
  have he:(4*t)*(y^2/(4*t))=y^2:=by field_simp
  nlinarith only [sq_nonneg (2*t*x-y),he,ht]



open SourceDilationMultiplier SourceDilationAlgebra

private theorem root_euler (z : physicalChart) :
    fderiv ℝ inverseRootVolume z.val (euler z.val) = (-3/2 : ℝ)*inverseRootVolume z.val := by
  have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hs := hv.sqrt (volume_pos z).ne'
  have hd := (hasDerivAt_inv (Real.sqrt_pos.mpr (volume_pos z)).ne').comp_hasFDerivAt z.val hs
  change fderiv ℝ ((fun r : ℝ => r⁻¹) ∘ (fun w => Real.sqrt (volume w))) z.val _ = _
  rw [hd.fderiv]
  have he : fderiv ℝ volume z.val (euler z.val)=3*volume z.val := by
    rw [volume_derivative]
    change z.val.1 0*z.val.1 2*z.val.1 5 +
      z.val.1 0*z.val.1 2*z.val.1 5 +
      z.val.1 0*z.val.1 2*z.val.1 5 = 3*volume z.val
    simp only [volume]
    ring
  simp only [smul_apply,smul_eq_mul,he]
  unfold inverseRootVolume
  have hpos : Real.sqrt (volume z.val) ≠ 0 := (Real.sqrt_pos.mpr (volume_pos z)).ne'
  have hsquare : Real.sqrt (volume z.val)^2=volume z.val := Real.sq_sqrt (volume_pos z).le
  field_simp [hpos]
  nlinarith [hsquare]

private theorem root_dilation : bracket SourceCoframeVolumeCurrent.dilation a = Complex.I • a := by
  have h := SourceDilationMultiplier.homogeneous_multiplier inverseRootVolume inverse_root_volume_smooth (-3/2) root_euler
  change bracket SourceCoframeVolumeCurrent.dilation a = _ at h ⊢
  convert h using 1
  · congr 1
    push_cast
    ring

private theorem real_multiply (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) :
    (multiply c smooth f : SourceCoordinateSlice → FockFiber)=(fun z => c z • f z) := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem native_multiplier (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (zeroDerivative : ∀ z : physicalChart, ∀ v : Ambient, fderiv ℝ c z.val (direction v z.val)=0)
    (v : Ambient) : Commute (covariantMomentum v) (multiply c smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hd : directional v (multiply c smooth f) z=c z • directional v f z := by
      rw [directional_apply,real_multiply,
        fderiv_fun_smul ((smooth ⟨z,hz⟩).differentiableAt (by simp))
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change c z • fderiv ℝ f z (direction v z)+fderiv ℝ c z (direction v z) • f z=_
      rw [zeroDerivative ⟨z,hz⟩ v,zero_smul,add_zero]
      rfl
    change (-Complex.I) • (directional v (multiply c smooth f) z+
      connection v z ((c z : ℂ) • f z))=
      (c z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))
    rw [hd,map_smul]
    have hr (p : FockFiber) : c z • p=(c z : ℂ) • p := by
      apply PiLp.ext;intro word;exact Complex.real_smul
    rw [hr,←smul_add,smul_comm]
  · have hl : covariantMomentum v (multiply c smooth f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((covariantMomentum v (multiply c smooth f)).tsupport_subset h))
    have hr : multiply c smooth (covariantMomentum v f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((multiply c smooth (covariantMomentum v f)).tsupport_subset h))
    exact hl.trans hr.symm

private theorem root_native (v : Ambient) : Commute (covariantMomentum v) a :=
  native_multiplier inverseRootVolume inverse_root_volume_smooth inverse_root_native_derivative v

private theorem root_adjoint (v : Ambient) : Commute (GaussMomentumAdjoint.adjoint v) a := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have hc := LinearMap.congr_fun (root_native v).eq f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (a g))=
    sourcePair f (a (GaussMomentumAdjoint.adjoint v g))
  calc
    _ = sourcePair (covariantMomentum v f) (a g) := adjoint_pair _ _ _
    _ = sourcePair (a (covariantMomentum v f)) g := multiply_pair _ _ _ _
    _ = sourcePair (covariantMomentum v (a f)) g := congrArg (fun x => sourcePair x g) hc.symm
    _ = sourcePair (a f) (GaussMomentumAdjoint.adjoint v g) := (adjoint_pair _ _ _).symm
    _ = _ := (multiply_pair _ _ _ _).symm

private theorem scalar_root : Commute a scalarKinetic := by
  have hterm (i : ScalarIndex) :
      Commute a (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth) := by
    change Commute a (GaussMomentumAdjoint.adjoint (scalarDirection i) *
      (multiply scalarWeight scalarWeight_smooth * covariantMomentum (scalarDirection i)))
    have hw : Commute a (multiply scalarWeight scalarWeight_smooth) := by
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      exact smul_comm (inverseRootVolume z : ℂ) (scalarWeight z : ℂ) (f z)
    exact (root_adjoint _).symm.mul_right (hw.mul_right (root_native _).symm)
  change Commute a ((1/2 : ℂ) • ∑ i : ScalarIndex,
    sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth)
  exact (Commute.sum_right _ _ _ (fun i _ => hterm i)).smul_right _

private theorem root_gradient_smooth (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => fderiv ℝ inverseRootVolume x (GaussCoframeCore.coframeDirection i)) z.val :=
  ((inverse_root_volume_smooth z).fderiv_right (by simp)).clm_apply contDiffAt_const

private def rootGradientAction (i : Fin 6) : End :=
  multiply (fun x => fderiv ℝ inverseRootVolume x (GaussCoframeCore.coframeDirection i))
    (root_gradient_smooth i)

private theorem coframe_root_momentum (i : Fin 6) :
    GaussCoframeCore.momentum i*a-a*GaussCoframeCore.momentum i =
      (-Complex.I) • rootGradientAction i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (a f) z-
      (inverseRootVolume z : ℂ) • ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z)=_
    dsimp only [a, inverseRootAction]
    rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,
      real_multiply inverseRootVolume inverse_root_volume_smooth,
      fderiv_fun_smul ((inverse_root_volume_smooth ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
    change (-Complex.I) • (inverseRootVolume z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
      fderiv ℝ inverseRootVolume z (GaussCoframeCore.coframeDirection i) • f z)-
      (inverseRootVolume z : ℂ) • ((-Complex.I) • fderiv ℝ f z (GaussCoframeCore.coframeDirection i))=
        (-Complex.I) • ((fderiv ℝ inverseRootVolume z (GaussCoframeCore.coframeDirection i) : ℂ) • f z)
    apply PiLp.ext
    intro word
    simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,Complex.real_smul]
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem coframe_root_adjoint (i : Fin 6) :
    GaussCoframeCore.adjoint i*a-a*GaussCoframeCore.adjoint i =
      (-Complex.I) • rootGradientAction i := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have h := congrArg (fun A : End => sourcePair (A f) g) (coframe_root_momentum i)
  change sourcePair (GaussCoframeCore.momentum i (a f)-a (GaussCoframeCore.momentum i f)) g=
    sourcePair ((-Complex.I) • rootGradientAction i f) g at h
  simp only [pair_sub_l,pair_smul_l,map_neg,Complex.conj_I,neg_neg] at h
  change sourcePair (GaussCoframeCore.momentum i (a f)) g-
    sourcePair (a (GaussCoframeCore.momentum i f)) g=Complex.I*sourcePair (rootGradientAction i f) g at h
  change sourcePair f (GaussCoframeCore.adjoint i (a g)-a (GaussCoframeCore.adjoint i g))=
    sourcePair f ((-Complex.I) • rootGradientAction i g)
  simp only [pair_sub_r,pair_smul_r]
  dsimp only [a, inverseRootAction] at h ⊢
  rw [GaussCoframeKinetic.adjoint_pair,multiply_pair,multiply_pair,GaussCoframeKinetic.adjoint_pair]
  have hg : sourcePair f (rootGradientAction i g)=sourcePair (rootGradientAction i f) g := multiply_pair _ _ _ _
  rw [hg]
  linear_combination -h

private theorem root_multiply_commute (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute a (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (inverseRootVolume z : ℂ) (c z : ℂ) (f z)

private theorem root_gradient_commute (i : Fin 6) : Commute a (rootGradientAction i) :=
  root_multiply_commute _ _

private theorem root_coefficient_commute (i j : Fin 6) : Commute a (coefficientAction i j) :=
  root_multiply_commute _ _

private theorem root_coordinate_derivative (z : physicalChart) (i : Fin 6) :
    fderiv ℝ inverseRootVolume z.val (GaussCoframeCore.coframeDirection i) =
      (-1/2 : ℝ)*inverseRootVolume z.val*reciprocalVolume z.val*volumeGradient z.val i := by
  have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hs := hv.sqrt (volume_pos z).ne'
  have hd := (hasDerivAt_inv (Real.sqrt_pos.mpr (volume_pos z)).ne').comp_hasFDerivAt z.val hs
  change fderiv ℝ ((fun r : ℝ => r⁻¹) ∘ (fun w => Real.sqrt (volume w))) z.val _ = _
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul,volume_coordinate_derivative]
  unfold inverseRootVolume reciprocalVolume
  have hpos : Real.sqrt (volume z.val) ≠ 0 := (Real.sqrt_pos.mpr (volume_pos z)).ne'
  have hsquare : Real.sqrt (volume z.val)^2=volume z.val := Real.sq_sqrt (volume_pos z).le
  rw [←hsquare]
  simp only [Real.sqrt_sq_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (volume_pos z))]
  field_simp [hpos]

private theorem root_gradient_zero (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) :
    rootGradientAction i=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have h := root_coordinate_derivative ⟨z,hz⟩ i
    change fderiv ℝ inverseRootVolume z (GaussCoframeCore.coframeDirection i) = _ at h
    change (fderiv ℝ inverseRootVolume z (GaussCoframeCore.coframeDirection i) : ℂ) • f z = 0
    rw [h]
    rcases hi with rfl|rfl|rfl <;> simp [volumeGradient]
  · exact image_eq_zero_of_notMem_tsupport (fun h => hz ((rootGradientAction i f).tsupport_subset h))

private theorem coframe_root_momentum_zero (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) :
    Commute (GaussCoframeCore.momentum i) a := by
  have h := coframe_root_momentum i
  rw [root_gradient_zero i hi,smul_zero] at h
  exact sub_eq_zero.mp h

private theorem coframe_root_adjoint_zero (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) :
    Commute (GaussCoframeCore.adjoint i) a := by
  have h := coframe_root_adjoint i
  rw [root_gradient_zero i hi,smul_zero] at h
  exact sub_eq_zero.mp h




private theorem root_bracket_commute (X Y : End) (h : Commute X Y) : bracket X Y=0 := by
  unfold bracket
  rw [h.eq,sub_self]

private theorem root_adjoint_bracket (i : Fin 6) :
    bracket a (GaussCoframeCore.adjoint i)=Complex.I • rootGradientAction i := by
  have h := coframe_root_adjoint i
  change GaussCoframeCore.adjoint i*a-a*GaussCoframeCore.adjoint i=
    (-Complex.I) • rootGradientAction i at h
  unfold bracket
  calc
    _ = -(GaussCoframeCore.adjoint i*a-a*GaussCoframeCore.adjoint i) := by abel
    _ = -((-Complex.I) • rootGradientAction i) := congrArg Neg.neg h
    _ = Complex.I • rootGradientAction i := by module

private theorem root_momentum_bracket (i : Fin 6) :
    bracket a (GaussCoframeCore.momentum i)=Complex.I • rootGradientAction i := by
  have h := coframe_root_momentum i
  change GaussCoframeCore.momentum i*a-a*GaussCoframeCore.momentum i=
    (-Complex.I) • rootGradientAction i at h
  unfold bracket
  calc
    _ = -(GaussCoframeCore.momentum i*a-a*GaussCoframeCore.momentum i) := by abel
    _ = -((-Complex.I) • rootGradientAction i) := congrArg Neg.neg h
    _ = Complex.I • rootGradientAction i := by module

private theorem double_sandwich (P C Q G J : End)
    (hP : bracket a P=Complex.I • G)
    (hQ : bracket a Q=Complex.I • J)
    (hC : Commute a C) (hG : Commute a G) (hJ : Commute a J) :
    bracket a (bracket a (P*(C*Q)))=(-2 : ℂ) • (G*C*J) := by
  have hzC : bracket a C=0 := root_bracket_commute _ _ hC
  have hzG : bracket a G=0 := root_bracket_commute _ _ hG
  have hzJ : bracket a J=0 := root_bracket_commute _ _ hJ
  simp only [bracket_product,bracket_add,bracket_smul,hP,hQ,hzC,hzG,hzJ,
    zero_mul,mul_zero,add_zero,zero_add,smul_zero]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [Complex.I_mul_I]
  module

private theorem root_double_term (i j : Fin 6) :
    bracket a (bracket a (GaussCoframeKinetic.term i j))=
      (-2 : ℂ) • (rootGradientAction i*coefficientAction i j*rootGradientAction j) := by
  change bracket a (bracket a (GaussCoframeCore.adjoint i *
    (coefficientAction i j * GaussCoframeCore.momentum j))) = _
  simpa only [mul_assoc] using double_sandwich _ _ _ _ _
    (root_adjoint_bracket i) (root_momentum_bracket j)
    (root_coefficient_commute i j) (root_gradient_commute i) (root_gradient_commute j)

private theorem volume_gradient_euler (z : SourceCoordinateSlice) :
    (∑ i : Fin 6, volumeGradient z i*z.1 i)=3*volume z := by
  simp [volumeGradient,volume,Fin.sum_univ_succ]
  ring

private theorem pointwise_root_contact (z : physicalChart) :
    (∑ i : Fin 6,∑ j : Fin 6,
      GaussCoframeKinetic.coefficient i j z.val *
        fderiv ℝ inverseRootVolume z.val (GaussCoframeCore.coframeDirection i) *
        fderiv ℝ inverseRootVolume z.val (GaussCoframeCore.coframeDirection j)) =
      (3*sourceTime 0/16)*reciprocalVolume z.val^2 := by
  simp_rw [root_coordinate_derivative z]
  have hi (i : Fin 6) :
      (∑ j : Fin 6, GaussCoframeKinetic.coefficient i j z.val *
        ((-1/2 : ℝ)*inverseRootVolume z.val*reciprocalVolume z.val*volumeGradient z.val i) *
        ((-1/2 : ℝ)*inverseRootVolume z.val*reciprocalVolume z.val*volumeGradient z.val j)) =
      ((1/4 : ℝ)*inverseRootVolume z.val^2*reciprocalVolume z.val^2)*
        volumeGradient z.val i *
        (∑ j : Fin 6, GaussCoframeKinetic.coefficient i j z.val*volumeGradient z.val j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hi,coefficient_volume z]
  have he : (∑ i : Fin 6,
      ((1/4 : ℝ)*inverseRootVolume z.val^2*reciprocalVolume z.val^2)*
        volumeGradient z.val i*((sourceTime 0/4)*z.val.1 i)) =
      ((3*sourceTime 0/16 : ℝ)*inverseRootVolume z.val^2*
        reciprocalVolume z.val^2)*volume z.val := by
    rw [show (∑ i : Fin 6,
        ((1/4 : ℝ)*inverseRootVolume z.val^2*reciprocalVolume z.val^2)*
          volumeGradient z.val i*((sourceTime 0/4)*z.val.1 i)) =
        ((sourceTime 0/16 : ℝ)*inverseRootVolume z.val^2*reciprocalVolume z.val^2)*
          (∑ i : Fin 6,volumeGradient z.val i*z.val.1 i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [volume_gradient_euler]
    ring
  rw [he]
  have hr : inverseRootVolume z.val^2=reciprocalVolume z.val := by
    unfold inverseRootVolume reciprocalVolume
    rw [inv_pow,Real.sq_sqrt (volume_pos z).le]
  rw [hr]
  unfold reciprocalVolume
  field_simp [(volume_pos z).ne']

private theorem root_contact_density :
    (∑ i : Fin 6,∑ j : Fin 6,
      rootGradientAction i*coefficientAction i j*rootGradientAction j)=
      (3*(n : ℂ)/16) • (U*U) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sum_apply,smul_apply,rootGradientAction,coefficientAction,U,inverseVolumeAction,multiply_apply,
    WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
  change (∑ i : Fin 6,∑ j : Fin 6,
      (fderiv ℝ inverseRootVolume z (GaussCoframeCore.coframeDirection i) : ℂ)*
        ((GaussCoframeKinetic.coefficient i j z : ℂ)*
          ((fderiv ℝ inverseRootVolume z (GaussCoframeCore.coframeDirection j) : ℂ)*f z word))) =
      (3*(n : ℂ)/16)*((reciprocalVolume z : ℂ)*((reciprocalVolume z : ℂ)*f z word))
  by_cases hz : z ∈ physicalChart
  · have hr := pointwise_root_contact ⟨z,hz⟩
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hr
    push_cast at hc
    calc
      _ = ((∑ i : Fin 6,∑ j : Fin 6,
        (GaussCoframeKinetic.coefficient i j z : ℂ)*
          (fderiv ℝ inverseRootVolume z (GaussCoframeCore.coframeDirection i) : ℂ)*
          (fderiv ℝ inverseRootVolume z (GaussCoframeCore.coframeDirection j) : ℂ)))*f z word := by
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = _ := by rw [hc]; ring
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp [hf]

private theorem bracket_sum {ι : Type*} [Fintype ι] (X : End) (F : ι → End) :
    bracket X (∑ i,F i)=∑ i,bracket X (F i) := by
  unfold bracket
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]

private theorem root_double_kinetic :
    bracket a (bracket a GaussCoframeKinetic.kinetic)=
      (-3*(n : ℂ)/8) • (U*U) := by
  change bracket a (bracket a (∑ i : Fin 6,∑ j : Fin 6,
    GaussCoframeKinetic.term i j)) = _
  simp only [bracket_sum,root_double_term,←Finset.smul_sum]
  rw [root_contact_density,smul_smul]
  congr 1
  ring

private theorem quantum_root
    (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart,
      ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val) :
    Commute a (GaussQuantumMultiplier.action A smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (inverseRootVolume z : ℂ) • GaussQuantumMultiplier.quantized (A z) (f z)=
    GaussQuantumMultiplier.quantized (A z) ((inverseRootVolume z : ℂ) • f z)
  exact (map_smul _ _ _).symm

private theorem current_root (j : Fin 7) : Commute a (GaussCoframeSpin.current j) :=
  quantum_root _ _

private theorem mixed_root (i : Fin 6) (j : Fin 7)
    (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi : i=1 ∨ i=3 ∨ i=4) :
    Commute a (GaussCoframeForm.mixed i j c hc) := by
  change Commute a ((1/2 : ℂ) •
    (GaussCoframeSpin.current j*(multiply c hc*GaussCoframeCore.momentum i)+
      GaussCoframeCore.adjoint i*(multiply c hc*GaussCoframeSpin.current j)))
  exact (((current_root j).mul_right
    ((root_multiply_commute c hc).mul_right (coframe_root_momentum_zero i hi).symm)).add_right
    ((coframe_root_adjoint_zero i hi).symm.mul_right
      ((root_multiply_commute c hc).mul_right (current_root j)))).smul_right _

private theorem current_action_root : Commute a GaussCoframeForm.currentAction := by
  unfold GaussCoframeForm.currentAction
  exact (((mixed_root 1 5 _ _ (Or.inl rfl)).add_right
    (mixed_root 3 3 _ _ (Or.inr (Or.inl rfl)))).add_right
    (mixed_root 3 4 _ _ (Or.inr (Or.inl rfl)))).add_right
    (mixed_root 4 3 _ _ (Or.inr (Or.inr rfl)))

private theorem spin_square_root (j : Fin 7) :
    Commute a (GaussCoframeForm.spinSquare j) := by
  change Commute a ((GaussCoframeForm.spinWeight j : ℂ) •
    (GaussCoframeSpin.current j *
      (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth *
        GaussCoframeSpin.current j)))
  exact ((current_root j).mul_right
    ((root_multiply_commute _ _).mul_right (current_root j))).smul_right _

private theorem number_root : Commute a GaussCoframeForm.number := quantum_root _ _

private theorem number_shift_root : Commute a GaussCoframeForm.numberShift := by
  change Commute a ((1/2 : ℂ) •
    (GaussCoframeForm.number*multiply GaussCoframeForm.numberCoefficient
      GaussCoframeForm.numberCoefficient_smooth+
      multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*
        GaussCoframeForm.number))
  exact (((number_root).mul_right (root_multiply_commute _ _)).add_right
    ((root_multiply_commute _ _).mul_right number_root)).smul_right _

private theorem matter_root : Commute a GaussMatterCore.matterAction := by
  unfold GaussMatterCore.matterAction
  exact Commute.sum_right _ _ _ (fun i _ =>
    Commute.sum_right _ _ _ (fun j _ => quantum_root _ _))

private def rest : End := scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential
  GaussNativePotential.potential_smooth+GaussCoframeForm.currentAction+
  (∑ j : Fin 7,GaussCoframeForm.spinSquare j)+GaussCoframeForm.numberShift+
  multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth+
  GaussMatterCore.matterAction

private theorem rest_root : Commute a rest := by
  unfold rest
  exact (((((((scalar_root.add_right inverse_root_electric).add_right
    (root_multiply_commute _ _)).add_right current_action_root).add_right
    (Commute.sum_right _ _ _ (fun j _ => spin_square_root j))).add_right
    number_shift_root).add_right (root_multiply_commute _ _)).add_right matter_root)

private theorem h0_split : H0=GaussCoframeKinetic.kinetic+rest := by
  unfold H0 GaussDiagonalHistory.diagonalAction GaussNativeForm.nativeAction
    GaussCoframeForm.coframeAction rest
  abel

private theorem root_double_contact :
    bracket a (bracket a H0)=(-3*(n : ℂ)/8) • (U*U) := by
  rw [h0_split,bracket_add,bracket_add]
  have hz : bracket a rest=0 := root_bracket_commute _ _ rest_root
  rw [hz]
  simp only [bracket, mul_zero,zero_mul,sub_self,add_zero]
  exact root_double_kinetic


private theorem root_first : Commute a (bracket combinedGenerator H0) := by
  rw [first_source]
  have hc:Commute a centeredAction:=inverse_root_real _ _
  have hv:Commute a vacuumLinearAction:=inverse_root_real _ _
  have hm:Commute a magneticAction:=inverse_root_real _ _
  exact (((((scalar_root.smul_right (-2:ℂ)).add_right (inverse_root_electric.smul_right (2:ℂ))).add_right
    (hc.smul_right (2:ℂ))).sub_right (hv.smul_right (2:ℂ))).sub_right
      (hm.smul_right (4:ℂ))).sub_right inverse_root_matter
private theorem combined_operator_source : combinedPressureOperator=
    (-(3*(n:ℂ)/8)) • (U*U*combinedGenerator*combinedGenerator)+
      (8:ℂ) • (U*gaugeKinetic)+(8:ℂ) • (U*magneticAction)+
        (8*(n:ℂ)) • (∑i:ScalarIndex,shiftedColumn38 i*shiftedColumn38 i) := by
  have hs:=congrArg (fun B:End=>U*B) second_source
  have hv:=potential_completion
  unfold combinedPressureOperator combinedConjugate
  rw [coframe_double_product a combinedGenerator H0 root_combined root_first,
    root_double_contact,root_square]
  simp only [mul_add,mul_sub,mul_smul_comm,smul_mul_assoc] at hs hv ⊢
  linear_combination (norm:=module) hs+hv

/-- One source conjugate generates the U² affine–gauge slot and its full positive fields. -/
theorem original_combined_pressure_source (f:QuantumTest) :
    combinedPressure f=(3*n/8)*‖embed (U (combinedGenerator f))‖^2+
      8*(sourcePair (a f) (gaugeKinetic (a f))).re+
      8*(sourcePair (a f) (magneticAction (a f))).re+8*n*shiftedMoment38 f ∧
    (3*n/8)*‖embed (U (combinedGenerator f))‖^2+8*n*shiftedMoment38 f ≤ combinedPressure f := by
  have he:combinedPressure f=(3*n/8)*‖embed (U (combinedGenerator f))‖^2+
      8*(sourcePair (a f) (gaugeKinetic (a f))).re+
      8*(sourcePair (a f) (magneticAction (a f))).re+8*n*shiftedMoment38 f := by
    unfold combinedPressure
    rw [combined_operator_source]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_r,pair_smul_r,
      weighted_combined_square,shifted38_square_pair]
    rw [root_form gaugeKinetic inverse_root_electric,
      root_form magneticAction (inverse_root_real _ _)]
    norm_num only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
      Complex.div_re,Complex.div_im,Complex.normSq_apply,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,zero_mul,mul_zero,zero_add,add_zero,sub_zero,neg_zero]
    simp only [←Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_im,
      Complex.re_ofNat,Complex.im_ofNat,zero_mul,mul_zero,add_zero]
    ring
  refine ⟨he,?_⟩
  rw [he]
  have hg:=original_gauge_kinetic_nonnegative (a f)
  have hm:=SourceClockPhiSecondBulk.original_magnetic_nonnegative (a f)
  linarith

/-- The complete two-seed contact consumes matching weighted source slots; both profile errors remain. -/
theorem actual_combined_phase_payment(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)
    (η:ℝ)(hη:0<η):
    combinedPhase m ell F z hz g=
      -4*z.im*(sourcePair (phaseFirst m ell F z hz g)
        (U (combinedGenerator (normalizedState m ell F z hz g)))).im+
      2*z.im*(sourcePair (normalizedState m ell F z hz g) (U (phaseSecond m ell F z hz g))).im ∧
    |combinedPhase m ell F z hz g| ≤ η*combinedPressure (normalizedState m ell F z hz g)+
      η*phiPositivePrice m ell F z hz g+
      32*z.im^2/(3*n*η)*‖embed (phaseFirst m ell F z hz g)‖^2+
      4*z.im^2/(25*n^2*η)*‖embed (phaseSecond m ell F z hz g)‖^2 := by
  refine ⟨phase_source m ell F z hz g,?_⟩
  let w:=normalizedState m ell F z hz g
  let b:=phaseFirst m ell F z hz g
  let c:=phaseSecond m ell F z hz g
  have hD:(3*n/8)*‖embed (U (combinedGenerator w))‖^2 ≤ combinedPressure w := by
    have hp:=(original_combined_pressure_source w).2
    have hm:0 ≤ shiftedMoment38 w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    have hn:=lapse_pos
    nlinarith only [hp,mul_nonneg hn.le hm]
  have hU:=normalized_weight_price m ell F z hz g
  have hi1:|(sourcePair b (U (combinedGenerator w))).im| ≤
      ‖embed b‖*‖embed (U (combinedGenerator w))‖ := by
    exact (Complex.abs_im_le_norm _).trans (by unfold sourcePair;exact norm_inner_le_norm _ _)
  have hi2:|(sourcePair w (U c)).im| ≤ ‖embed (U w)‖*‖embed c‖ := by
    rw [weight_pair]
    exact (Complex.abs_im_le_norm _).trans (by unfold sourcePair;exact norm_inner_le_norm _ _)
  have hab:|combinedPhase m ell F z hz g| ≤
      4*|z.im| *‖embed (U (combinedGenerator w))‖*‖embed b‖+
      2*|z.im| *‖embed (U w)‖*‖embed c‖ := by
    rw [phase_source]
    have ht:=abs_add_le (-4*z.im*(sourcePair b (U (combinedGenerator w))).im)
      (2*z.im*(sourcePair w (U c)).im)
    norm_num only [abs_mul,abs_neg] at ht
    have h1:=mul_le_mul_of_nonneg_left hi1 (show 0 ≤ 4*|z.im| by positivity)
    have h2:=mul_le_mul_of_nonneg_left hi2 (show 0 ≤ 2*|z.im| by positivity)
    nlinarith only [ht,h1,h2]
  have hn:=lapse_pos
  have hy1:=young ‖embed (U (combinedGenerator w))‖ (4*|z.im| *‖embed b‖) (η*3*n/8) (by positivity)
  have hy2:=young ‖embed (U w)‖ (2*|z.im| *‖embed c‖) (η*25*n^2/4) (by positivity)
  have he1:(4*|z.im| *‖embed b‖)^2/(4*(η*3*n/8))=
      32*z.im^2/(3*n*η)*‖embed b‖^2 := by
    rw [mul_pow,mul_pow,sq_abs]
    field_simp
    ring
  have he2:(2*|z.im| *‖embed c‖)^2/(4*(η*25*n^2/4))=
      4*z.im^2/(25*n^2*η)*‖embed c‖^2 := by
    rw [mul_pow,mul_pow,sq_abs]
    field_simp
    ring
  rw [he1] at hy1
  rw [he2] at hy2
  have hpD:=mul_le_mul_of_nonneg_left hD hη.le
  have hpU:=mul_le_mul_of_nonneg_left hU hη.le
  change |combinedPhase m ell F z hz g| ≤ η*combinedPressure w+η*phiPositivePrice m ell F z hz g+
    32*z.im^2/(3*n*η)*‖embed b‖^2+4*z.im^2/(25*n^2*η)*‖embed c‖^2
  nlinarith only [hab,hy1,hy2,hpD,hpU]

end LowEnergy.SourceClockPhiCombinedScalePressure
