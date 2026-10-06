import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourcePairedMomentumFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarDoubleCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussYukawaCoefficient GaussRadialDomain
open SourceCoframeVolumeCurrent SourceCoframeVolume SourceCoframeDilation SourceDilationRemainder
open SourceHamiltonianScaleJet SourceKineticTranspose SourceMixedNativeReturn SourceClosedCostNativeProbe
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarPairedTransport SourcePairedRadialFlux SourcePairedMomentumFlux
open scoped ContDiff InnerProductSpace BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

def bracket {R : Type*} [Ring R] (A B : R) : R := A*B-B*A

private theorem scale_product (A B : CoreEnd) :
    scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  change (3*Complex.I/2) • (dilation*(A*B)-(A*B)*dilation)=
    ((3*Complex.I/2) • (dilation*A-A*dilation))*B+A*((3*Complex.I/2) • (dilation*B-B*dilation))
  simp only [smul_mul_assoc,mul_smul_comm,←smul_add]
  congr 1
  noncomm_ring

private theorem scale_bracket (A B : CoreEnd) :
    scaleDerivative (bracket A B)=bracket (scaleDerivative A) B+bracket A (scaleDerivative B) := by
  simp only [bracket,map_sub,scale_product]
  abel

private theorem scale_zero {A : CoreEnd} (h : Commute dilation A) : scaleDerivative A=0 := by
  change (3*Complex.I/2) • (dilation*A-A*dilation)=0
  rw [h.eq,sub_self,smul_zero]

private theorem coordinate_scale (v : Ambient) :
    scaleDerivative (SourceClosedCostNativeProbe.coordinateAction v)=0 := by
  have he (z : physicalChart) : fderiv ℝ (SourceClosedCostNativeProbe.coordinate v) z.val (euler z.val)=
      (0 : ℝ)*SourceClosedCostNativeProbe.coordinate v z.val := by
    simpa only [Int.cast_zero] using! SourceKineticScale.euler_of_scale (SourceClosedCostNativeProbe.coordinate v) 0 z
      (GaussRadialMomentum.scalarCoordinate.contDiff.inner ℝ contDiff_const).contDiffAt
      (fun _ _ => by simp only [zpow_zero,one_mul]; rfl)
  have h := SourceDilationMultiplier.homogeneous_multiplier _
    (fun _ => (GaussRadialMomentum.scalarCoordinate.contDiff.inner ℝ contDiff_const).contDiffAt) 0 he
  change dilation*SourceClosedCostNativeProbe.coordinateAction v-
    SourceClosedCostNativeProbe.coordinateAction v*dilation=_ at h
  simp only [Complex.ofReal_zero,mul_zero,zero_smul] at h
  exact scale_zero (sub_eq_zero.mp h)

private theorem scalar_sum (sharp : Bool) :
    scalarAction sharp=∑ a : ScalarIndex,constantAction sharp (scalarBasis a)*
      SourceClosedCostNativeProbe.coordinateAction (scalarDirection a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.sum_apply,sum_apply]
  change branchMap sharp (z.2.1 : Scalar) (f z)=∑ a : ScalarIndex,
    branchMap sharp (scalarBasis a) ((inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) • f z)
  have he : ∑ a : ScalarIndex,inner ℝ (z.2.1 : Scalar) (scalarBasis a) • scalarBasis a=(z.2.1 : Scalar) := by
    simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using scalarBasis.sum_repr (z.2.1 : Scalar)
  conv_lhs => rw [←he,map_sum,sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul,map_smul]
  rfl

private theorem scalar_scale (sharp : Bool) : scaleDerivative (scalarAction sharp)=0 := by
  rw [scalar_sum]
  simp only [map_sum,scale_product,coordinate_scale,scale_zero (constant_dilation sharp _),
    zero_mul,mul_zero,add_zero,Finset.sum_const_zero]

/-- The insertion retains the full vacuum-plus-scalar coefficient on either genuine branch. -/
def fullInsertion (sharp : Bool) (m ell : ℕ) : CoreEnd := fullAction sharp*thetaAction m ell

theorem full_insertion_scale (sharp : Bool) (m ell : ℕ) :
    scaleDerivative (fullInsertion sharp m ell)=0 := by
  simp only [fullInsertion,scale_product,full_scalar_split,map_add,scalar_scale,
    scale_zero (constant_dilation sharp vacuum),scale_zero (theta_dilation m ell),
    add_zero,zero_mul,mul_zero]

private theorem local_multiplier (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) : Commute localAction (localMultiplier A smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (A z) (localPotential z : ℂ) (f z)).symm

private theorem local_real (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val) : Commute localAction (multiply a ha) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (localPotential z : ℂ) (a z : ℂ) (f z)

private theorem commute_product {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A B) (hB : Commute A C) : Commute A (B*C) := hA.mul_right hB

theorem local_full_insertion (sharp : Bool) (m ell : ℕ) : Commute localAction (fullInsertion sharp m ell) := by
  apply commute_product (R := CoreEnd)
  · cases sharp
    · exact local_multiplier (fun z => sourceMap (GaussNativePotential.scalarField z))
        (fun _ => (sourceMap.contDiff.comp GaussNativePotential.scalarField_smooth).contDiffAt)
    · exact local_multiplier (fun z => GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z))
        (fun _ => (GaussFullHamiltonian.adjointMap.contDiff.comp GaussNativePotential.scalarField_smooth).contDiffAt)
  · have ht : SourceNativeCutoffContact.thetaAction m ell=thetaAction m ell :=
      SourceNativeCutoffContact.theta_action_polynomial m ell
    rw [←ht]
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (localPotential z : ℂ) (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)

def electricSpatial : CoreEnd := gaugeKinetic+spatialAction
def kineticMinus : CoreEnd := kineticAction-gaugeKinetic

private theorem kinetic_minus_scale : scaleDerivative kineticMinus=(-3 : ℂ) • kineticMinus := by
  simp only [kineticMinus,map_sub,scale_kinetic,scale_electric]
  module

private theorem electric_spatial_scale : scaleDerivative electricSpatial=electricSpatial := by
  simp only [electricSpatial,map_add,scale_electric,scale_spatial]

def component : Fin 4 → CoreEnd := ![kineticMinus,GaussMatterCore.matterAction,electricSpatial,localAction]
def weight : Fin 4 → ℂ := ![-3,-1,1,3]

private theorem component_scale (i : Fin 4) : scaleDerivative (component i)=weight i • component i := by
  fin_cases i
  · exact kinetic_minus_scale
  · exact scale_matter
  · change scaleDerivative electricSpatial=(1 : ℂ) • electricSpatial
    simpa only [one_smul] using electric_spatial_scale
  · exact scale_local

private theorem full_components : diagonalAction=∑ i : Fin 4, component i := by
  simp only [Fin.sum_univ_succ,component,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  rw [original_action_split]
  unfold kineticMinus electricSpatial
  abel

private theorem bracket_add_left {R : Type*} [Ring R] (A B C : R) :
    (A+B)*C-C*(A+B)=(A*C-C*A)+(B*C-C*B) := by noncomm_ring

private theorem bracket_eigen (A B : CoreEnd) (a b : ℂ)
    (hA : scaleDerivative A=a • A) (hB : scaleDerivative B=b • B) :
    scaleDerivative (bracket A B)=(a+b) • bracket A B := by
  rw [scale_bracket,hA,hB]
  simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
  module

def cubic : CoreEnd →ₗ[ℂ] CoreEnd :=
  scaleDerivative.comp (scaleDerivative.comp scaleDerivative)+(12 : ℂ) • scaleDerivative.comp scaleDerivative+
    (44 : ℂ) • scaleDerivative+(48 : ℂ) • LinearMap.id

private theorem cubic_eigen (A : CoreEnd) (a : ℂ) (hA : scaleDerivative A=a • A) :
    cubic A=(a^3+12*a^2+44*a+48) • A := by
  simp only [cubic,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.id_apply,hA,map_smul,smul_smul]
  module

private theorem bracket_sum_left {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : ι → R) (X : R) :
    bracket (∑ i, A i) X=∑ i, bracket (A i) X := by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]

private theorem bracket_sum_right {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : R) (X : ι → R) :
    bracket A (∑ i, X i)=∑ i, bracket A (X i) := by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]

private theorem double_expand (X : CoreEnd) :
    bracket diagonalAction (bracket diagonalAction X)=
      ∑ i : Fin 4, ∑ j : Fin 4, bracket (component i) (bracket (component j) X) := by
  rw [full_components]
  simp only [bracket_sum_left,bracket_sum_right]
  exact Finset.sum_comm

/-- Actual source weights generate every surviving double-H block before any finite compression. -/
theorem actual_double_scale_blocks (sharp : Bool) (m ell : ℕ) :
    cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell)))=
      ∑ i : Fin 4, ∑ j : Fin 4,
        ((weight i+weight j)^3+12*(weight i+weight j)^2+44*(weight i+weight j)+48) •
          bracket (component i) (bracket (component j) (fullInsertion sharp m ell)) := by
  rw [double_expand]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply cubic_eigen
  apply bracket_eigen
  · exact component_scale i
  · simpa only [add_zero] using bracket_eigen (component j) (fullInsertion sharp m ell) (weight j) 0
      (component_scale j) (by rw [full_insertion_scale,zero_smul])

private theorem sum_commute {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : R) (B : ι → R)
    (h : ∀ i, Commute A (B i)) : Commute A (∑ i, B i) :=
  Commute.sum_right Finset.univ B A (fun i _ => h i)

private theorem smul_commute {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    [SMulCommClass ℂ R R] (c : ℂ) (A B : R) (h : Commute A B) : Commute A (c • B) := h.smul_right c

private theorem gauge_local (v : Ambient) (hv : v.1=0) : Commute localAction (covariantMomentum v) := by
  have hq : SourceClosedCostNativeProbe.coordinateAction v=0 := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (inner ℝ (z.2.1 : Scalar) v.1 : ℂ) • f z=0
    rw [hv,inner_zero_right,Complex.ofReal_zero,zero_smul]
  have h := local_native_force v
  rw [hq,mul_zero,smul_zero] at h
  change Complex.I • (localAction*covariantMomentum v-covariantMomentum v*localAction)=0 at h
  exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left Complex.I_ne_zero)

private theorem paired_local (A B : CoreEnd) (pair : GaussCoframeForm.Paired B A)
    (h : Commute localAction A) : Commute localAction B := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (localAction (B g))=sourcePair f (B (localAction g))
  have he : localAction (A f)=A (localAction f) := LinearMap.congr_fun h.eq f
  calc
    _=sourcePair (localAction f) (B g) := multiply_pair _ _ _ _
    _=sourcePair (A (localAction f)) g := pair _ _
    _=sourcePair (localAction (A f)) g := congrArg (fun q => sourcePair q g) he.symm
    _=sourcePair (A f) (localAction g) := (multiply_pair _ _ _ _).symm
    _=_ := (pair _ _).symm

private theorem local_gauge_kinetic : Commute localAction gaugeKinetic := by
  unfold gaugeKinetic
  apply smul_commute (R := CoreEnd)
  apply sum_commute (R := CoreEnd)
  intro a
  apply sum_commute (R := CoreEnd)
  intro i
  apply sum_commute (R := CoreEnd)
  intro j
  change Commute localAction (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
    (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))
  apply commute_product (R := CoreEnd)
  · exact paired_local _ _ (GaussNativeForm.adjoint_pair _) (gauge_local _ rfl)
  · apply commute_product (R := CoreEnd)
    · exact local_multiplier _ _
    · exact gauge_local _ rfl

theorem local_electric_spatial : Commute localAction electricSpatial :=
  local_gauge_kinetic.add_right (local_multiplier _
    (fun z => (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (spatial_smooth z)).smul contDiffAt_const))

theorem local_matter : Commute localAction GaussMatterCore.matterAction := by
  unfold GaussMatterCore.matterAction
  apply sum_commute (R := CoreEnd)
  intro i
  apply sum_commute (R := CoreEnd)
  intro b
  exact local_multiplier _ _

private theorem current_elimination {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (K M E L X : R)
    (hX : Commute L X) (hM : Commute L M) (hE : Commute L E) :
    (48 : ℂ) • (bracket K (bracket L X)+bracket L (bracket K X)+
      bracket M (bracket E X)+bracket E (bracket M X))+
    (192 : ℂ) • (bracket M (bracket L X)+bracket L (bracket M X)+bracket E (bracket E X))+
    (480 : ℂ) • (bracket E (bracket L X)+bracket L (bracket E X))+
    (960 : ℂ) • bracket L (bracket L X)=
      (48 : ℂ) • (bracket (bracket L (K+M+E+L)) X+
        bracket M (bracket E X)+bracket E (bracket M X)+(4 : ℂ) • bracket E (bracket E X)) := by
  have hLX : bracket L X=0 := sub_eq_zero.mpr hX.eq
  have hLM : bracket L (bracket M X)=0 := by
    simp only [bracket]
    calc
      _=(L*M-M*L)*X-X*(L*M-M*L)+M*(L*X-X*L)-(L*X-X*L)*M := by noncomm_ring
      _=0 := by rw [hM.eq,hX.eq]; noncomm_ring
  have hLE : bracket L (bracket E X)=0 := by
    simp only [bracket]
    calc
      _=(L*E-E*L)*X-X*(L*E-E*L)+E*(L*X-X*L)-(L*X-X*L)*E := by noncomm_ring
      _=0 := by rw [hE.eq,hX.eq]; noncomm_ring
  have hLK : bracket (bracket L (K+M+E+L)) X=bracket L (bracket K X) := by
    simp only [bracket]
    calc
      _=L*(K*X-X*K)-(K*X-X*K)*L+
        (L*M-M*L)*X-X*(L*M-M*L)+(L*E-E*L)*X-X*(L*E-E*L)+
        (L*X-X*L)*K-K*(L*X-X*L) := by noncomm_ring
      _=_ := by rw [hM.eq,hE.eq,hX.eq]; noncomm_ring
  rw [hLX,hLM,hLE,hLK]
  simp only [bracket,mul_zero,zero_mul,sub_self,add_zero,zero_add,smul_add,smul_smul]
  module

/-- The electric/spatial--matter cross survives at source weight zero and is retained literally. -/
def electricMatterCurrent (X : CoreEnd) : CoreEnd :=
  bracket GaussMatterCore.matterAction (bracket electricSpatial X)+
    bracket electricSpatial (bracket GaussMatterCore.matterAction X)+
      (4 : ℂ) • bracket electricSpatial (bracket electricSpatial X)

theorem actual_double_scale_current (sharp : Bool) (m ell : ℕ) :
    cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell)))=
      (48 : ℂ) • (bracket (bracket localAction diagonalAction) (fullInsertion sharp m ell)+
        electricMatterCurrent (fullInsertion sharp m ell)) := by
  have h := actual_double_scale_blocks sharp m ell
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,component,weight,
    Matrix.cons_val_zero,Matrix.cons_val_succ] at h
  norm_num only [neg_add_cancel,add_neg_cancel,show (-3 : ℂ)+ -3= -6 by norm_num,
    show (-3 : ℂ)+ -1= -4 by norm_num,show (-3 : ℂ)+1= -2 by norm_num,
    show (-1 : ℂ)+ -3= -4 by norm_num,show (-1 : ℂ)+ -1= -2 by norm_num,
    show (-1 : ℂ)+3=2 by norm_num,show (1 : ℂ)+ -3= -2 by norm_num,
    show (1 : ℂ)+1=2 by norm_num,show (1 : ℂ)+3=4 by norm_num,
    show (3 : ℂ)+ -1=2 by norm_num,show (3 : ℂ)+1=4 by norm_num,
    show (3 : ℂ)+3=6 by norm_num] at h
  have hs : diagonalAction=kineticMinus+GaussMatterCore.matterAction+electricSpatial+localAction := by
    rw [original_action_split]
    unfold kineticMinus electricSpatial
    abel
  have he := current_elimination kineticMinus GaussMatterCore.matterAction electricSpatial localAction
    (fullInsertion sharp m ell) (local_full_insertion sharp m ell) local_matter local_electric_spatial
  rw [←hs] at he
  have hc : cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell)))=
      (48 : ℂ) • (bracket kineticMinus (bracket localAction (fullInsertion sharp m ell))+
        bracket localAction (bracket kineticMinus (fullInsertion sharp m ell))+
        bracket GaussMatterCore.matterAction (bracket electricSpatial (fullInsertion sharp m ell))+
        bracket electricSpatial (bracket GaussMatterCore.matterAction (fullInsertion sharp m ell)))+
      (192 : ℂ) • (bracket GaussMatterCore.matterAction (bracket localAction (fullInsertion sharp m ell))+
        bracket localAction (bracket GaussMatterCore.matterAction (fullInsertion sharp m ell))+
        bracket electricSpatial (bracket electricSpatial (fullInsertion sharp m ell)))+
      (480 : ℂ) • (bracket electricSpatial (bracket localAction (fullInsertion sharp m ell))+
        bracket localAction (bracket electricSpatial (fullInsertion sharp m ell)))+
      (960 : ℂ) • bracket localAction (bracket localAction (fullInsertion sharp m ell)) := by
    rw [h]
    module
  exact hc.trans (he.trans (by unfold electricMatterCurrent; module))

def quadPotential (z : SourceCoordinateSlice) : ℝ := ‖(z.2.1 : Scalar)‖^2+3
private theorem quad_smooth : ContDiff ℝ ∞ quadPotential :=
  (GaussRadialMomentum.scalarCoordinate.contDiff.norm_sq ℝ).add contDiff_const

def quadAction : CoreEnd := multiply quadPotential (fun _ => quad_smooth.contDiffAt)
private theorem quad_pair (f g : QuantumTest) : sourcePair f (quadAction g)=sourcePair (quadAction f) g :=
  multiply_pair _ _ f g

private theorem quad_real (f : QuantumTest) :
    (quadAction f : SourceCoordinateSlice → FockFiber)=
      fun z => quadPotential z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem multiplier_commutes
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) :
    Commute (localMultiplier A smooth) (quadAction) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (quadPotential z : ℂ) (f z)

private theorem real_commutes (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c smooth) (quadAction) := multiplier_commutes _ _

private theorem paired_commutes (A B : CoreEnd)
    (pair : GaussCoframeForm.Paired B A) (hc : Commute A (quadAction)) :
    Commute B (quadAction) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (B (quadAction g))=
    sourcePair f (quadAction (B g))
  have he : A (quadAction f)=quadAction (A f) := LinearMap.congr_fun hc.eq f
  calc
    _=sourcePair (A f) (quadAction g) := pair _ _
    _=sourcePair (quadAction (A f)) g := quad_pair _ _
    _=sourcePair (A (quadAction f)) g := congrArg (fun q => sourcePair q g) he.symm
    _=sourcePair (quadAction f) (B g) := (pair _ _).symm
    _=_ := (quad_pair _ _).symm

private theorem quad_coframe_derivative (z : SourceCoordinateSlice) (i : Fin 6) :
    fderiv ℝ (quadPotential) z (GaussCoframeCore.coframeDirection i)=0 := by
  have hd := ((quad_smooth).differentiable (by simp)).differentiableAt (x := z) |>.hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ => z+r • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (GaussCoframeCore.coframeDirection i) |>.const_add z
  have hh := hd.comp_hasDerivAt_of_eq 0 hc (by simp)
  have he : (fun r : ℝ => quadPotential (z+r • GaussCoframeCore.coframeDirection i))=
      (fun _ => quadPotential z) := by
    funext r
    simp [quadPotential,GaussCoframeCore.coframeDirection]
  change HasDerivAt (fun r : ℝ => quadPotential (z+r • GaussCoframeCore.coframeDirection i))
    (fderiv ℝ (quadPotential) z (GaussCoframeCore.coframeDirection i)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)

private theorem coframe_derivative (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (quadAction) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeCore.derivative _ (quadAction f) z=
    quadAction (GaussCoframeCore.derivative _ f) z
  rw [GaussCoframeCore.derivative_apply,quad_real,
    fderiv_fun_smul ((quad_smooth).differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change quadPotential z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
    fderiv ℝ (quadPotential) z (GaussCoframeCore.coframeDirection i) • f z=_
  rw [quad_coframe_derivative,zero_smul,add_zero]
  change _=(quadPotential z : ℂ) • GaussCoframeCore.derivative _ f z
  rw [GaussCoframeCore.derivative_apply]
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem coframe_momentum (i : Fin 6) :
    Commute (GaussCoframeCore.momentum i) (quadAction) :=
  (coframe_derivative i).smul_left (-Complex.I)

private theorem coframe_adjoint (i : Fin 6) :
    Commute (GaussCoframeCore.adjoint i) (quadAction) :=
  paired_commutes _ _ (GaussCoframeKinetic.adjoint_pair i) (coframe_momentum i)

private theorem quantum_commutes (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val) :
    Commute (GaussQuantumMultiplier.action A smooth) (quadAction) := multiplier_commutes _ _

private theorem end_sum_commute {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : ι → R) (B : R)
    (h : ∀ i, Commute (A i) B) : Commute (∑ i, A i) B := by
  change (∑ i, A i)*B=B*(∑ i, A i)
  rw [Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (h i).eq)

private theorem end_smul_commute {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (c : ℂ) (A B : R) (h : Commute A B) : Commute (c • A) B := by
  change (c • A)*B=B*(c • A)
  rw [smul_mul_assoc,mul_smul_comm,h.eq]

private theorem end_mul_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A*B) C := hA.mul_left hB

private theorem end_add_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A+B) C := hA.add_left hB

private theorem coframe_kinetic :
    Commute GaussCoframeKinetic.kinetic (quadAction) := by
  change Commute (∑ i : Fin 6, ∑ j : Fin 6, GaussCoframeKinetic.term i j) (quadAction)
  apply end_sum_commute (R := CoreEnd)
  intro i
  apply end_sum_commute (R := CoreEnd)
  intro j
  change Commute (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j)) (quadAction)
  apply end_mul_commute (R := CoreEnd)
  · exact coframe_adjoint i
  · apply end_mul_commute (R := CoreEnd)
    · exact real_commutes _ _
    · exact coframe_momentum j

private theorem coframe_current (a : Fin 7) :
    Commute (GaussCoframeSpin.current a) (quadAction) := quantum_commutes _ _

private theorem coframe_mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeForm.mixed i a c smooth) (quadAction) := by
  change Commute ((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply c smooth*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply c smooth*GaussCoframeSpin.current a))) (quadAction)
  apply end_smul_commute (R := CoreEnd)
  apply end_add_commute (R := CoreEnd)
  · apply end_mul_commute (R := CoreEnd)
    · exact coframe_current a
    · apply end_mul_commute (R := CoreEnd)
      · exact real_commutes c smooth
      · exact coframe_momentum i
  · apply end_mul_commute (R := CoreEnd)
    · exact coframe_adjoint i
    · apply end_mul_commute (R := CoreEnd)
      · exact real_commutes c smooth
      · exact coframe_current a

private theorem coframe_commutes :
    Commute GaussCoframeForm.coframeAction (quadAction) := by
  unfold GaussCoframeForm.coframeAction GaussCoframeForm.currentAction
    GaussCoframeForm.spinSquare GaussCoframeForm.numberShift
  apply end_add_commute (R := CoreEnd)
  · apply end_add_commute (R := CoreEnd)
    · apply end_add_commute (R := CoreEnd)
      · apply end_add_commute (R := CoreEnd)
        · exact coframe_kinetic
        · apply end_add_commute (R := CoreEnd)
          · apply end_add_commute (R := CoreEnd)
            · apply end_add_commute (R := CoreEnd)
              · exact coframe_mixed _ _ _ _
              · exact coframe_mixed _ _ _ _
            · exact coframe_mixed _ _ _ _
          · exact coframe_mixed _ _ _ _
      · apply end_sum_commute (R := CoreEnd)
        intro a
        apply end_smul_commute (R := CoreEnd)
        change Commute (GaussCoframeSpin.current a*(multiply GaussCoframeForm.inverseVolume
          GaussCoframeForm.inverseVolume_smooth*GaussCoframeSpin.current a)) (quadAction)
        apply end_mul_commute (R := CoreEnd)
        · exact coframe_current a
        · apply end_mul_commute (R := CoreEnd)
          · exact real_commutes _ _
          · exact coframe_current a
    · apply end_smul_commute (R := CoreEnd)
      change Commute (GaussCoframeForm.number*multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
        multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*GaussCoframeForm.number) (quadAction)
      apply end_add_commute (R := CoreEnd)
      · apply end_mul_commute (R := CoreEnd)
        · exact quantum_commutes _ _
        · exact real_commutes _ _
      · apply end_mul_commute (R := CoreEnd)
        · exact real_commutes _ _
        · exact quantum_commutes _ _
  · exact real_commutes _ _

private theorem matter_commutes :
    Commute GaussMatterCore.matterAction (quadAction) := by
  unfold GaussMatterCore.matterAction
  apply end_sum_commute (R := CoreEnd)
  intro i
  apply end_sum_commute (R := CoreEnd)
  intro a
  exact quantum_commutes _ _

private theorem local_factor : localAction=(sourceTime 0 : ℂ) • (volumeAction*quadAction) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (localPotential z : ℂ)*f z word=
    (sourceTime 0 : ℂ)*((volume z : ℂ)*((quadPotential z : ℂ)*f z word))
  unfold localPotential GaussCoframeForm.volumePotential quadPotential
  rw [real_inner_self_eq_norm_sq]
  push_cast
  ring

private theorem coframe_volume :
    bracket GaussCoframeForm.coframeAction volumeAction=
      (-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation := by
  have hm : Commute GaussMatterCore.matterAction volumeAction := by
    unfold GaussMatterCore.matterAction
    apply end_sum_commute (R := CoreEnd)
    intro i
    apply end_sum_commute (R := CoreEnd)
    intro j
    exact SourceCoframeVolumeCurrent.scalar_volume_commutes _ _
  have h := SourceHamiltonianVolume.full_source_volume_current
  change (scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential GaussNativePotential.potential_smooth+
    GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)*volumeAction-
    volumeAction*(scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential GaussNativePotential.potential_smooth+
    GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)=_ at h
  simp only [add_mul,mul_add,SourceHamiltonianVolume.scalar_kinetic_volume.eq,
    SourceHamiltonianVolume.gauge_kinetic_volume.eq,(SourceHamiltonianVolume.real_volume _ _).eq,hm.eq] at h
  change GaussCoframeForm.coframeAction*volumeAction-volumeAction*GaussCoframeForm.coframeAction=_
  convert! h using 1
  abel

private theorem product_commutator {R : Type*} [Ring R] (U Q A : R) (hQ : Commute A Q) :
    bracket (U*Q) A= -bracket A U*Q := by
  change U*Q*A-A*(U*Q)= -(A*U-U*A)*Q
  calc
    _=U*(Q*A)-(A*U)*Q := by noncomm_ring
    _=U*(A*Q)-(A*U)*Q := by rw [←hQ.eq]
    _=_ := by noncomm_ring

private theorem local_coframe_current :
    bracket localAction GaussCoframeForm.coframeAction=
      (3*Complex.I*(sourceTime 0 : ℂ)^2/4) • (dilation*quadAction) := by
  rw [local_factor]
  change ((sourceTime 0 : ℂ) • (volumeAction*quadAction))*GaussCoframeForm.coframeAction-
    GaussCoframeForm.coframeAction*((sourceTime 0 : ℂ) • (volumeAction*quadAction))=_
  rw [smul_mul_assoc,mul_smul_comm,←smul_sub]
  change (sourceTime 0 : ℂ) • bracket (volumeAction*quadAction) GaussCoframeForm.coframeAction=_
  rw [product_commutator _ _ _ coframe_commutes,coframe_volume,←neg_smul,smul_mul_assoc,smul_smul]
  congr 1
  ring

def localMomentumContact (v : Ambient) : CoreEnd :=
  (-2*Complex.I*(sourceTime 0 : ℂ)) • (volumeAction*SourceClosedCostNativeProbe.coordinateAction v)

private theorem force_contact {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    [SMulCommClass ℂ R R] (L P V : R) (c : ℂ) (h : Complex.I • (L*P-P*L)=c • V) :
    P*L=L*P+(Complex.I*c) • V := by
  have he := congrArg (fun A : R => Complex.I • A) h
  rw [smul_smul,Complex.I_mul_I,neg_one_smul,smul_smul] at he
  have hh : P*L-L*P=(Complex.I*c) • V := (by module : P*L-L*P= -(L*P-P*L)).trans he
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

private theorem momentum_local (v : Ambient) (f : QuantumTest) :
    covariantMomentum v (localAction f)=localAction (covariantMomentum v f)+localMomentumContact v f := by
  have h := force_contact localAction (covariantMomentum v)
    (volumeAction*SourceClosedCostNativeProbe.coordinateAction v) (-2*(sourceTime 0 : ℂ)) (local_native_force v)
  have hc : Complex.I*(-2*(sourceTime 0 : ℂ))= -2*Complex.I*(sourceTime 0 : ℂ) := by ring
  rw [hc] at h
  exact LinearMap.congr_fun h f

private theorem local_contact_pair (v : Ambient) (f g : QuantumTest) :
    sourcePair f (localMomentumContact v g)= -sourcePair (localMomentumContact v f) g := by
  have h (a b : QuantumTest) : sourcePair a (volumeAction (SourceClosedCostNativeProbe.coordinateAction v b))=
      sourcePair (volumeAction (SourceClosedCostNativeProbe.coordinateAction v a)) b := by
    have hc : SourceClosedCostNativeProbe.coordinateAction v (volumeAction a)=
        volumeAction (SourceClosedCostNativeProbe.coordinateAction v a) := by
      apply DFunLike.ext
      intro z
      exact smul_comm (SourceClosedCostNativeProbe.coordinate v z : ℂ) (volume z : ℂ) (a z)
    exact (multiply_pair _ _ a _).trans ((multiply_pair _ _ _ b).trans
      (congrArg (fun q : QuantumTest => sourcePair q b) hc))
  simp only [localMomentumContact,LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right,inner_smul_left,
    map_mul,map_neg,map_ofNat,Complex.conj_I,Complex.conj_ofReal]
  change (-2*Complex.I*(sourceTime 0 : ℂ))*sourcePair f
      (volumeAction (SourceClosedCostNativeProbe.coordinateAction v g))=
    -((-2*(-Complex.I)*(sourceTime 0 : ℂ))*sourcePair
      (volumeAction (SourceClosedCostNativeProbe.coordinateAction v f)) g)
  rw [h]
  ring

private theorem adjoint_local (v : Ambient) (g : QuantumTest) :
    GaussMomentumAdjoint.adjoint v (localAction g)=localAction (GaussMomentumAdjoint.adjoint v g)+localMomentumContact v g := by
  apply SourceCoframeVolume.pair_ext
  intro f
  have h1 := GaussNativeForm.adjoint_pair v f (localAction g)
  have h2 := multiply_pair localPotential local_smooth (covariantMomentum v f) g
  have h3 := GaussNativeForm.adjoint_pair v (localAction f) g
  have h4 := multiply_pair localPotential local_smooth f (GaussMomentumAdjoint.adjoint v g)
  have h5 := local_contact_pair v f g
  change sourcePair (covariantMomentum v f) (localAction g)=sourcePair (localAction (covariantMomentum v f)) g at h2
  change sourcePair f (localAction (GaussMomentumAdjoint.adjoint v g))=
    sourcePair (localAction f) (GaussMomentumAdjoint.adjoint v g) at h4
  rw [momentum_local] at h3
  change sourcePair (localAction f) (GaussMomentumAdjoint.adjoint v g)=
    inner ℂ (embed (localAction (covariantMomentum v f)+localMomentumContact v f)) (embed g) at h3
  rw [map_add,inner_add_left] at h3
  change sourcePair f (GaussMomentumAdjoint.adjoint v (localAction g))=
    inner ℂ (embed f) (embed (localAction (GaussMomentumAdjoint.adjoint v g)+localMomentumContact v g))
  rw [map_add,inner_add_right]
  change _=sourcePair f (localAction (GaussMomentumAdjoint.adjoint v g))+sourcePair f (localMomentumContact v g)
  rw [h1,h2,h4,h3,h5]
  unfold sourcePair
  ring

private theorem weight_local_contact (v : Ambient) :
    multiply scalarWeight scalarWeight_smooth*localMomentumContact v=
      (2*Complex.I*(sourceTime 0 : ℂ)^2) • SourceClosedCostNativeProbe.coordinateAction v := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · apply PiLp.ext
    intro word
    change (scalarWeight z : ℂ)*((-2*Complex.I*(sourceTime 0 : ℂ))*
      ((volume z : ℂ)*((SourceClosedCostNativeProbe.coordinate v z : ℂ)*f z word)))=
      (2*Complex.I*(sourceTime 0 : ℂ)^2)*((SourceClosedCostNativeProbe.coordinate v z : ℂ)*f z word)
    unfold scalarWeight
    push_cast
    field_simp [show (volume z : ℂ)≠0 from by exact_mod_cast (volume_pos ⟨z,hz⟩).ne']
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    change (scalarWeight z : ℂ) • ((-2*Complex.I*(sourceTime 0 : ℂ)) •
      ((volume z : ℂ) • ((SourceClosedCostNativeProbe.coordinate v z : ℂ) • f z)))=_
    rw [hf,smul_zero,smul_zero,smul_zero,smul_zero]
    change 0=(2*Complex.I*(sourceTime 0 : ℂ)^2) • ((SourceClosedCostNativeProbe.coordinate v z : ℂ) • f z)
    rw [hf,smul_zero,smul_zero]

private theorem local_contact_weight (v : Ambient) :
    localMomentumContact v*multiply scalarWeight scalarWeight_smooth=
      (2*Complex.I*(sourceTime 0 : ℂ)^2) • SourceClosedCostNativeProbe.coordinateAction v := by
  have h : Commute (localMomentumContact v) (multiply scalarWeight scalarWeight_smooth) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    change (-2*Complex.I*(sourceTime 0 : ℂ))*((volume z : ℂ)*
      ((SourceClosedCostNativeProbe.coordinate v z : ℂ)*((scalarWeight z : ℂ)*f z word)))=
      (scalarWeight z : ℂ)*((-2*Complex.I*(sourceTime 0 : ℂ))*
      ((volume z : ℂ)*((SourceClosedCostNativeProbe.coordinate v z : ℂ)*f z word)))
    ring
  exact h.eq.trans (weight_local_contact v)

private theorem sandwich_contact {R : Type*} [Ring R] (a b w t c : R)
    (ha : a*t=t*a+c) (hb : b*t=t*b+c) (hw : w*t=t*w) :
    (a*w*b)*t=t*(a*w*b)+(a*w*c+c*w*b) := by
  calc
    _=a*w*(b*t) := by noncomm_ring
    _=a*w*(t*b+c) := by rw [hb]
    _=a*(w*t)*b+a*w*c := by noncomm_ring
    _=(a*t)*w*b+a*w*c := by rw [hw]; noncomm_ring
    _=_ := by rw [ha]; noncomm_ring

private theorem contact_collapse {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (A W K Q P : R) (c : ℂ)
    (hW : W*K=c • Q) (hK : K*W=c • Q) :
    A*W*K+K*W*P=c • (A*Q+Q*P) := by
  calc
    _=A*(W*K)+(K*W)*P := by noncomm_ring
    _=A*(c • Q)+(c • Q)*P := by rw [hW,hK]
    _=_ := by rw [mul_smul_comm,smul_mul_assoc,←smul_add]

theorem original_scalar_local_current :
    bracket scalarKinetic localAction=(sourceTime 0 : ℂ)^2 •
      ((2 : ℂ) • SourceScalarRadialContact.scalarEulerAction+(61 : ℂ) • (1 : CoreEnd)) := by
  have hs (a : ScalarIndex) :
      sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth*localAction=
      localAction*sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth+
        (2*Complex.I*(sourceTime 0 : ℂ)^2) •
          (GaussMomentumAdjoint.adjoint (scalarDirection a)*SourceGammaNativeBudget.scalarColumn a+
            SourceGammaNativeBudget.scalarColumn a*covariantMomentum (scalarDirection a)) := by
    have ha : GaussMomentumAdjoint.adjoint (scalarDirection a)*localAction=
        localAction*GaussMomentumAdjoint.adjoint (scalarDirection a)+localMomentumContact (scalarDirection a) :=
      LinearMap.ext (adjoint_local (scalarDirection a))
    have hb : covariantMomentum (scalarDirection a)*localAction=
        localAction*covariantMomentum (scalarDirection a)+localMomentumContact (scalarDirection a) :=
      LinearMap.ext (momentum_local (scalarDirection a))
    have h := sandwich_contact (R := CoreEnd) _ _ (multiply scalarWeight scalarWeight_smooth) _ _ ha hb
      (local_real scalarWeight scalarWeight_smooth).symm.eq
    have he : GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
        localMomentumContact (scalarDirection a)+localMomentumContact (scalarDirection a)*
        multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)=
        (2*Complex.I*(sourceTime 0 : ℂ)^2) •
          (GaussMomentumAdjoint.adjoint (scalarDirection a)*SourceGammaNativeBudget.scalarColumn a+
            SourceGammaNativeBudget.scalarColumn a*covariantMomentum (scalarDirection a)) := by
      simpa only [SourceGammaNativeBudget.scalarColumn] using! contact_collapse (R := CoreEnd) _ _ _ _ _ _
        (weight_local_contact (scalarDirection a)) (local_contact_weight (scalarDirection a))
    exact h.trans (congrArg (fun q : CoreEnd => localAction*sandwich (scalarDirection a) (scalarDirection a)
      scalarWeight scalarWeight_smooth+q) he)
  have hsum : scalarKinetic*localAction=localAction*scalarKinetic+
      (Complex.I*(sourceTime 0 : ℂ)^2) • (SourceScalarRadialContact.radialAdjoint+SourceScalarRadialContact.radialMomentum) := by
    simp only [scalarKinetic,smul_mul_assoc,Finset.sum_mul,hs,Finset.sum_add_distrib,
      ←Finset.mul_sum,mul_smul_comm,smul_add,←Finset.smul_sum,smul_smul,
      SourceScalarRadialContact.radialAdjoint,SourceScalarRadialContact.radialMomentum]
    congr 1
    module
  change scalarKinetic*localAction-localAction*scalarKinetic=_
  rw [hsum,add_sub_cancel_left,SourceScalarRadialContact.scalar_adjoint_contraction,
    SourceScalarRadialContact.scalar_native_contraction,←smul_add,smul_smul]
  have hi : (Complex.I*(sourceTime 0 : ℂ)^2)*(-Complex.I)=(sourceTime 0 : ℂ)^2 := by
    calc _= -(Complex.I*Complex.I)*(sourceTime 0 : ℂ)^2 := by ring
         _=_ := by rw [Complex.I_mul_I]; ring
  rw [hi]
  module

theorem original_local_hamiltonian_current :
    bracket localAction diagonalAction=
      (-(sourceTime 0 : ℂ)^2) •
        ((2 : ℂ) • SourceScalarRadialContact.scalarEulerAction+(61 : ℂ) • (1 : CoreEnd))+
      (3*Complex.I*(sourceTime 0 : ℂ)^2/4) • (dilation*quadAction) := by
  have hp : Commute localAction (multiply GaussNativePotential.potential GaussNativePotential.potential_smooth) :=
    local_multiplier _ (fun z => (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
      (GaussNativePotential.potential_smooth z)).smul contDiffAt_const)
  have hs : bracket localAction scalarKinetic= -bracket scalarKinetic localAction := by
    unfold bracket
    abel
  have he : bracket localAction diagonalAction=
      bracket localAction scalarKinetic+bracket localAction GaussCoframeForm.coframeAction := by
    change localAction*(scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential
      GaussNativePotential.potential_smooth+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)-
      (scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential
      GaussNativePotential.potential_smooth+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)*localAction=_
    simp only [mul_add,add_mul,local_gauge_kinetic.eq,hp.eq,local_matter.eq,bracket]
    abel
  rw [he,hs,original_scalar_local_current,local_coframe_current,neg_smul]

private theorem full_quad (sharp : Bool) (m ell : ℕ) : Commute (fullInsertion sharp m ell) quadAction := by
  apply end_mul_commute (R := CoreEnd)
  · cases sharp
    · exact multiplier_commutes (fun z => sourceMap (GaussNativePotential.scalarField z))
        (fun _ => (sourceMap.contDiff.comp GaussNativePotential.scalarField_smooth).contDiffAt)
    · exact multiplier_commutes (fun z => GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z))
        (fun _ => (GaussFullHamiltonian.adjointMap.contDiff.comp GaussNativePotential.scalarField_smooth).contDiffAt)
  · have ht : SourceNativeCutoffContact.thetaAction m ell=thetaAction m ell :=
      SourceNativeCutoffContact.theta_action_polynomial m ell
    rw [←ht]
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (SourceNativeCutoffContact.theta m ell z : ℂ) (quadPotential z : ℂ) (f z)

private theorem full_dilation (sharp : Bool) (m ell : ℕ) : Commute dilation (fullInsertion sharp m ell) := by
  have h := full_insertion_scale sharp m ell
  change (3*Complex.I/2) • (dilation*fullInsertion sharp m ell-fullInsertion sharp m ell*dilation)=0 at h
  have hi : (3*Complex.I/2 : ℂ)≠0 := div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by norm_num)
  exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left hi)

private theorem affine_bracket {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (E J X : R) (a b c d : ℂ) (hJ : Commute J X) :
    bracket (a • (b • E+c • (1 : R))+d • J) X=(a*b) • bracket E X := by
  simp only [bracket,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,hJ.eq]
  module

/-- The coframe volume current cancels in this nested source commutator; the scalar61 Euler remains. -/
theorem original_local_double_current (sharp : Bool) (m ell : ℕ) :
    bracket (bracket localAction diagonalAction) (fullInsertion sharp m ell)=
      (-2*(sourceTime 0 : ℂ)^2) • bracket (R := CoreEnd) SourceScalarRadialContact.scalarEulerAction (fullInsertion sharp m ell) := by
  rw [original_local_hamiltonian_current]
  have h := affine_bracket (R := CoreEnd) SourceScalarRadialContact.scalarEulerAction (dilation*quadAction)
    (fullInsertion sharp m ell) (-(sourceTime 0 : ℂ)^2) 2 61 (3*Complex.I*(sourceTime 0 : ℂ)^2/4)
    (end_mul_commute _ _ _ (full_dilation sharp m ell) (full_quad sharp m ell).symm)
  exact h.trans (congrArg (fun c : ℂ => c • bracket (R := CoreEnd) SourceScalarRadialContact.scalarEulerAction
    (fullInsertion sharp m ell)) (by ring))

/-- The source double-H jet isolates a radial oscillator current and the complete surviving electric/matter cross. -/
theorem original_double_oscillator_current (sharp : Bool) (m ell : ℕ) :
    cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell)))=
      (-96*(sourceTime 0 : ℂ)^2) • bracket (R := CoreEnd) SourceScalarRadialContact.scalarEulerAction (fullInsertion sharp m ell)+
        (48 : ℂ) • electricMatterCurrent (fullInsertion sharp m ell) := by
  rw [actual_double_scale_current,original_local_double_current,smul_add,smul_smul]
  congr 1
  ring

private def scalarCurve (z : SourceCoordinateSlice) (r : ℝ) : SourceCoordinateSlice :=
  (z.1,r • z.2.1,z.2.2)

private theorem scalar_curve_derivative (z : SourceCoordinateSlice) :
    HasDerivAt (scalarCurve z) (SourceScalarRadialContact.scalarEuler z) 1 := by
  have h := (hasDerivAt_const (1 : ℝ) z.1).prodMk
    (((hasDerivAt_id (1 : ℝ)).smul_const z.2.1).prodMk (hasDerivAt_const (1 : ℝ) z.2.2))
  simpa only [scalarCurve,SourceScalarRadialContact.scalarEuler,id_eq,one_smul] using! h

private theorem full_apply (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fullAction sharp f z=branchMap sharp (vacuum+(z.2.1 : Scalar)) (f z) := by
  cases sharp <;> rfl

/-- Scalar Euler differentiates the full source coefficient to q, preserving its actual vacuum part. -/
theorem original_euler_full_current (sharp : Bool) :
    bracket (R := CoreEnd) SourceScalarRadialContact.scalarEulerAction (fullAction sharp)=scalarAction sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hz : scalarCurve z 1=z := by simp [scalarCurve]
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scalar_curve_derivative z) hz.symm
  have hfull := ((fullAction sharp f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scalar_curve_derivative z) hz.symm
  have ha := ((branchMap sharp vacuum).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 1 hf
  have hb := ((branchMap sharp (z.2.1 : Scalar)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 1 hf
  have hp := ha.add ((hasDerivAt_id (1 : ℝ)).smul hb)
  have he : (fun r : ℝ => fullAction sharp f (scalarCurve z r))=
      (fun r : ℝ => branchMap sharp vacuum (f (scalarCurve z r))+
        r • branchMap sharp (z.2.1 : Scalar) (f (scalarCurve z r))) := by
    funext r
    rw [full_apply]
    change branchMap sharp (vacuum+r • (z.2.1 : Scalar)) (f (scalarCurve z r))=_
    rw [map_add,map_smul,add_apply,smul_apply]
  change HasDerivAt (fun r : ℝ => fullAction sharp f (scalarCurve z r))
    (fderiv ℝ (fullAction sharp f) z (SourceScalarRadialContact.scalarEuler z)) 1 at hfull
  rw [he] at hfull
  have hu := hfull.unique hp
  simp only [Function.comp_def,one_smul,id_eq,hz] at hu
  change SourceScalarRadialContact.scalarEulerAction (fullAction sharp f) z-
    fullAction sharp (SourceScalarRadialContact.scalarEulerAction f) z=scalarAction sharp f z
  rw [SourceScalarRadialContact.scalar_euler_apply,full_apply,
    SourceScalarRadialContact.scalar_euler_apply,hu,map_add,add_apply]
  change branchMap sharp vacuum (fderiv ℝ f z (SourceScalarRadialContact.scalarEuler z))+
      (branchMap sharp (z.2.1 : Scalar) (fderiv ℝ f z (SourceScalarRadialContact.scalarEuler z))+
        branchMap sharp (z.2.1 : Scalar) (f z))-
      (branchMap sharp vacuum (fderiv ℝ f z (SourceScalarRadialContact.scalarEuler z))+
        branchMap sharp (z.2.1 : Scalar) (fderiv ℝ f z (SourceScalarRadialContact.scalarEuler z)))=_
  abel

def cutoffEuler (m ell : ℕ) : CoreEnd := bracket (R := CoreEnd) SourceScalarRadialContact.scalarEulerAction (thetaAction m ell)

private theorem bracket_product {R : Type*} [Ring R] (A B C : R) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by unfold bracket; noncomm_ring

theorem original_radial_insertion (sharp : Bool) (m ell : ℕ) :
    bracket (R := CoreEnd) SourceScalarRadialContact.scalarEulerAction (fullInsertion sharp m ell)=
      scalarAction sharp*thetaAction m ell+fullAction sharp*cutoffEuler m ell := by
  rw [fullInsertion,bracket_product (R := CoreEnd),original_euler_full_current]
  rfl

def scaleDoubleRemainder (sharp : Bool) (m ell : ℕ) : CoreEnd :=
  let J : CoreEnd := bracket (R := CoreEnd) diagonalAction (bracket (R := CoreEnd) diagonalAction (fullInsertion sharp m ell))
  scaleDerivative (scaleDerivative (scaleDerivative J))+
    (12 : ℂ) • scaleDerivative (scaleDerivative J)+(44 : ℂ) • scaleDerivative J

/-- No whole-action positivity is assumed: all scale, electric/matter, cutoff and vacuum forces remain explicit. -/
def oscillatorForce (sharp : Bool) (m ell : ℕ) : CoreEnd :=
  electricMatterCurrent (fullInsertion sharp m ell)-
    (2*(sourceTime 0 : ℂ)^2) • (fullAction sharp*cutoffEuler m ell)+
    (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)-
    (1/48 : ℂ) • scaleDoubleRemainder sharp m ell

private theorem solve_oscillator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : ℂ) (J B C E W R X : V) (hX : X=W+B)
    (h : R+(48 : ℂ) • J=(-96*a) • (B+C)+(48 : ℂ) • E) :
    J+(2*a) • X=E-(2*a) • C+(2*a) • W-(1/48 : ℂ) • R := by
  have hh : (48 : ℂ) • J=(-96*a) • (B+C)+(48 : ℂ) • E-R :=
    eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  have hj := congrArg (fun v : V => (1/48 : ℂ) • v) hh
  rw [smul_smul,show (1/48 : ℂ)*48=1 by norm_num,one_smul] at hj
  rw [hj,hX]
  module

private theorem oscillator_balance (sharp : Bool) (m ell : ℕ) :
    scaleDoubleRemainder sharp m ell+
      (48 : ℂ) • bracket (R := CoreEnd) diagonalAction (bracket (R := CoreEnd) diagonalAction (fullInsertion sharp m ell))=
      (-96*(sourceTime 0 : ℂ)^2) • (scalarAction sharp*thetaAction m ell+fullAction sharp*cutoffEuler m ell)+
      (48 : ℂ) • electricMatterCurrent (fullInsertion sharp m ell) := by
  let J : CoreEnd := bracket (R := CoreEnd) diagonalAction (bracket (R := CoreEnd) diagonalAction (fullInsertion sharp m ell))
  have hc : cubic J=scaleDoubleRemainder sharp m ell+(48 : ℂ) • J := by
    simp only [cubic,scaleDoubleRemainder,J,LinearMap.add_apply,LinearMap.comp_apply,
      LinearMap.smul_apply,LinearMap.id_apply]
  have h0 := original_double_oscillator_current sharp m ell
  rw [original_radial_insertion] at h0
  change scaleDoubleRemainder sharp m ell+(48 : ℂ) • J=_
  rw [←hc]
  simpa only [J] using! h0

/-- The actual full source produces the strictly gapped double-H equation, with every force retained. -/
theorem original_oscillator_equation (sharp : Bool) (m ell : ℕ) :
    bracket (R := CoreEnd) diagonalAction (bracket (R := CoreEnd) diagonalAction (fullInsertion sharp m ell))+
      (2*(sourceTime 0 : ℂ)^2) • fullInsertion sharp m ell=oscillatorForce sharp m ell := by
  let J : CoreEnd := bracket (R := CoreEnd) diagonalAction (bracket (R := CoreEnd) diagonalAction (fullInsertion sharp m ell))
  have hfull : fullInsertion sharp m ell=constantAction sharp vacuum*thetaAction m ell+
      scalarAction sharp*thetaAction m ell := by rw [fullInsertion,full_scalar_split,add_mul]
  simpa only [oscillatorForce] using! solve_oscillator (V := CoreEnd) ((sourceTime 0 : ℂ)^2)
    J
    (scalarAction sharp*thetaAction m ell) (fullAction sharp*cutoffEuler m ell)
    (electricMatterCurrent (fullInsertion sharp m ell))
    (constantAction sharp vacuum*thetaAction m ell) (scaleDoubleRemainder sharp m ell)
    (fullInsertion sharp m ell) hfull (oscillator_balance sharp m ell)

theorem source_oscillator_gap_positive (a b : ℝ) :
    0<(a-b)^2+2*(sourceTime 0)^2 := by
  have hn := sq_pos_of_ne_zero source_time_nonzero
  nlinarith [sq_nonneg (a-b)]


end LowEnergy.SourceScalarDoubleCurrent
