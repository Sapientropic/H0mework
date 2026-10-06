import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGammaNativeBudget
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFixedJetBudget
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarPairedTransport
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussFockPair
open GaussNativeEnergy GaussNativeForm GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussHistoryHilbert
open GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum GaussMomentumAdjoint
open SourceMixedNativeReturn SourceGammaNativeBudget SourceEscapeCurrent SourceMinimalGraphParticular
open SourcePhysicalHamiltonianSquare SourceCoframeVolumeCurrent SourceFixedJetBudget
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped ContDiff InnerProductSpace BigOperators

private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
private abbrev OriginalCore : Type := diagonal.domain

/-- Actual radial primitives normalized at radius one. -/
def radialPrimitive : ℕ → ℝ → ℝ
  | 0,x => 2*(x^2-1)
  | 1,x => 4*(x-1)
  | 2,x => 4*Real.log x
  | n+3,x => (4/(n+1 : ℝ))*(1-(x⁻¹)^(n+1))

private theorem radial_primitive_derivative (j : ℕ) (x : ℝ) (hx : 0<x) :
    HasDerivAt (radialPrimitive j) (4*x*(x⁻¹)^j) x := by
  have hx0 := hx.ne'
  match j with
  | 0 =>
    convert! (((hasDerivAt_id x).pow 2).sub_const 1).const_mul 2 using 1
    simp
    ring
  | 1 =>
    convert! ((hasDerivAt_id x).sub_const 1).const_mul 4 using 1
    simp [hx0]
  | 2 =>
    convert! (Real.hasDerivAt_log hx0).const_mul 4 using 1
    field_simp
  | n+3 =>
    have h := (((hasDerivAt_inv hx0).pow (n+1)).const_sub 1).const_mul (4/(n+1 : ℝ))
    convert! h using 1
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
    rw [pow_succ,pow_succ,pow_succ]
    field_simp

private theorem radial_primitive_smooth (j : ℕ) :
    ContDiff ℝ ∞ (fun z : SourceCoordinateSlice => radialPrimitive j (radius z)) := by
  match j with
  | 0 => exact contDiff_const.mul ((radius_smooth.pow 2).sub contDiff_const)
  | 1 => exact contDiff_const.mul (radius_smooth.sub contDiff_const)
  | 2 => exact contDiff_const.mul (radius_smooth.log (fun z => (radius_pos z).ne'))
  | n+3 => exact contDiff_const.mul (contDiff_const.sub (reciprocal_smooth.pow (n+1)))

private theorem direction_radius (v : Ambient) (z : physicalChart) :
    fderiv ℝ radius z.val (direction v z.val)=
      inner ℝ (z.val.2.1 : Scalar) v.1/(4*radius z.val) := by
  have hs := (((scalarCoordinate.hasFDerivAt (x := z.val)).norm_sq).mul_const (4⁻¹ : ℝ)).const_add 1
  have hd := hs.sqrt (show 1+‖scalarCoordinate z.val‖^2*4⁻¹≠0 by positivity)
  change HasFDerivAt radius _ z.val at hd
  rw [hd.fderiv]
  simp only [smul_apply,two_smul,smul_eq_mul]
  change (1/(2*radius z.val))*(4⁻¹*(inner ℝ (z.val.2.1 : Scalar)
    ((inverseL z.val v).2.1 : Scalar)+inner ℝ (z.val.2.1 : Scalar)
    ((inverseL z.val v).2.1 : Scalar)))=_
  rw [inverse_radial]
  ring

private theorem primitive_direction (j : ℕ) (v : Ambient) (z : physicalChart) :
    fderiv ℝ (fun w => radialPrimitive j (radius w)) z.val (direction v z.val)=
      inner ℝ (z.val.2.1 : Scalar) v.1*(reciprocal z.val)^j := by
  have h := (radial_primitive_derivative j (radius z.val) (radius_pos z.val)).comp_hasFDerivAt z.val
    ((radius_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change fderiv ℝ (radialPrimitive j ∘ radius) z.val (direction v z.val)=_
  rw [h.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rw [direction_radius]
  unfold reciprocal
  field_simp [(radius_pos z.val).ne']

def primitivePower (n : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ)*(-1)^j)*radialPrimitive j (radius z)

def radialPotential (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  primitivePower (m+1) z-primitivePower (ell+1) z

private theorem primitive_power_smooth (n : ℕ) : ContDiff ℝ ∞ (primitivePower n) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (radial_primitive_smooth j)

theorem potential_smooth (m ell : ℕ) : ContDiff ℝ ∞ (radialPotential m ell) :=
  (primitive_power_smooth _).sub (primitive_power_smooth _)

private theorem binomial_scalar (n : ℕ) (u : ℝ) :
    (∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ)*(-1)^j)*u^j)=(1-u)^n := by
  rw [sub_eq_add_neg,add_comm (1 : ℝ),add_pow]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_pow,mul_one]
  have hu : (-u)^j=(-1 : ℝ)^j*u^j := by rw [←mul_pow]; congr 1; ring
  rw [hu]
  ring

private theorem primitive_power_direction (n : ℕ) (v : Ambient) (z : physicalChart) :
    fderiv ℝ (primitivePower n) z.val (direction v z.val)=
      inner ℝ (z.val.2.1 : Scalar) v.1*(1-reciprocal z.val)^n := by
  have hd (j : ℕ) : DifferentiableAt ℝ (fun w =>
      ((n.choose j : ℝ)*(-1)^j)*radialPrimitive j (radius w)) z.val :=
    (contDiff_const.mul (radial_primitive_smooth j)).differentiable (by simp) |>.differentiableAt
  unfold primitivePower
  rw [fderiv_fun_sum (fun j _ => hd j)]
  simp only [sum_apply]
  have hh (j : ℕ) : fderiv ℝ (fun w => ((n.choose j : ℝ)*(-1)^j)*radialPrimitive j (radius w))
      z.val (direction v z.val)=((n.choose j : ℝ)*(-1)^j)*
        (inner ℝ (z.val.2.1 : Scalar) v.1*(reciprocal z.val)^j) := by
    rw [fderiv_const_mul ((radial_primitive_smooth j).differentiable (by simp)).differentiableAt]
    simp only [smul_apply,smul_eq_mul]
    rw [primitive_direction]
  simp_rw [hh]
  rw [←binomial_scalar]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem radial_potential_direction (m ell : ℕ) (v : Ambient) (z : physicalChart) :
    fderiv ℝ (radialPotential m ell) z.val (direction v z.val)=
      inner ℝ (z.val.2.1 : Scalar) v.1*SourceNativeCutoffContact.theta m ell z.val := by
  unfold radialPotential
  rw [fderiv_fun_sub
    ((primitive_power_smooth _).differentiable (by simp)).differentiableAt
    ((primitive_power_smooth _).differentiable (by simp)).differentiableAt]
  simp only [sub_apply,primitive_power_direction,SourceNativeCutoffContact.theta]
  ring

def potentialAction (m ell : ℕ) : CoreEnd :=
  multiply (radialPotential m ell) (fun _ => (potential_smooth m ell).contDiffAt)

def scalarMomentum (sharp : Bool) : CoreEnd :=
  ∑ a : ScalarIndex,constantAction sharp (scalarBasis a)*covariantMomentum (scalarDirection a)

def scalarMomentumAdjoint (sharp : Bool) : CoreEnd :=
  ∑ a : ScalarIndex,GaussMomentumAdjoint.adjoint (scalarDirection a)*constantAction (!sharp) (scalarBasis a)

theorem scalar_momentum_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (scalarMomentum sharp g)=sourcePair (scalarMomentumAdjoint sharp f) g := by
  simp only [scalarMomentum,scalarMomentumAdjoint,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro a _
  change sourcePair f (constantAction sharp (scalarBasis a) (covariantMomentum (scalarDirection a) g))=
    sourcePair (GaussMomentumAdjoint.adjoint (scalarDirection a) (constantAction (!sharp) (scalarBasis a) f)) g
  exact (constant_pair sharp (scalarBasis a) f _).trans (momentum_pair _ _ g)

theorem potential_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (potentialAction m ell g)=sourcePair (potentialAction m ell f) g :=
  multiply_pair _ _ f g

private theorem potential_real (m ell : ℕ) (f : QuantumTest) :
    (potentialAction m ell f : SourceCoordinateSlice → FockFiber)=fun z => radialPotential m ell z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem directional_potential (m ell : ℕ) (v : Ambient) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    directional v (potentialAction m ell f) z=radialPotential m ell z • directional v f z+
      (inner ℝ (z.2.1 : Scalar) v.1*SourceNativeCutoffContact.theta m ell z) • f z := by
  rw [directional_apply,potential_real,
    fderiv_fun_smul ((potential_smooth m ell).differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change radialPotential m ell z • directional v f z+
    fderiv ℝ (radialPotential m ell) z (direction v z) • f z=_
  by_cases hz : z∈physicalChart
  · rw [radial_potential_direction m ell v ⟨z,hz⟩]
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    rw [hf,smul_zero,smul_zero]

theorem momentum_potential (m ell : ℕ) (v : Ambient) (f : QuantumTest) :
    covariantMomentum v (potentialAction m ell f)=potentialAction m ell (covariantMomentum v f)+
      (-Complex.I) • SourceClosedCostNativeProbe.coordinateAction v (SourceMixedNativeReturn.thetaAction m ell f) := by
  apply DFunLike.ext
  intro z
  have hθ : SourceMixedNativeReturn.thetaAction m ell f z=
      (SourceNativeCutoffContact.theta m ell z : ℂ) • f z := by
    change (((1-inverseAction)^(m+1)-(1-inverseAction)^(ell+1)) f) z=_
    rw [←SourceNativeCutoffContact.theta_action_polynomial]
    rfl
  change (-Complex.I) • (directional v (potentialAction m ell f) z+
    connection v z (potentialAction m ell f z))=_
  rw [directional_potential]
  change (-Complex.I) • (radialPotential m ell z • directional v f z+
      (inner ℝ (z.2.1 : Scalar) v.1*SourceNativeCutoffContact.theta m ell z) • f z+
      connection v z ((radialPotential m ell z : ℂ) • f z))=
    (radialPotential m ell z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))+
      (-Complex.I) • ((inner ℝ (z.2.1 : Scalar) v.1 : ℂ) • (SourceMixedNativeReturn.thetaAction m ell f z))
  rw [hθ,map_smul]
  apply PiLp.ext
  intro word
  simp only [PiLp.smul_apply,PiLp.add_apply,Complex.real_smul,Complex.ofReal_mul]
  ring

private theorem constant_potential (sharp : Bool) (v : Scalar) (m ell : ℕ) :
    Commute (constantAction sharp v) (potentialAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (branchMap sharp v) (radialPotential m ell z : ℂ) (f z)

private theorem scalar_sum (sharp : Bool) :
    (∑ a : ScalarIndex,constantAction sharp (scalarBasis a)*
      SourceClosedCostNativeProbe.coordinateAction (scalarDirection a))=scalarAction sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.sum_apply,sum_apply]
  change (∑ a : ScalarIndex,branchMap sharp (scalarBasis a)
    ((inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) • f z))=branchMap sharp (z.2.1 : Scalar) (f z)
  have he : ∑ a : ScalarIndex,(inner ℝ (z.2.1 : Scalar) (scalarBasis a)) • scalarBasis a=(z.2.1 : Scalar) := by
    simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using scalarBasis.sum_repr (z.2.1 : Scalar)
  conv_rhs => rw [←he,map_sum,sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul,map_smul]
  rfl

private theorem end_sum_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] (C P Q : ι → Module.End ℂ V) (b T : Module.End ℂ V)
    (hC : ∀ a, Commute (C a) b)
    (hP : ∀ a, P a*b=b*P a+(-Complex.I) • (Q a*T)) :
    (∑ a, C a*P a)*b-b*(∑ a, C a*P a)=(-Complex.I) • ((∑ a,C a*Q a)*T) := by
  simp only [Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc,hP,mul_add,←mul_assoc,(hC a).eq]
  simp only [mul_smul_comm,←mul_assoc]
  abel

/-- The original scalar coefficient comes from a radial commutator, on both genuine source branches. -/
theorem actual_scalar_commutator (sharp : Bool) (m ell : ℕ) :
    scalarAction sharp*SourceMixedNativeReturn.thetaAction m ell=
      Complex.I • (scalarMomentum sharp*potentialAction m ell-potentialAction m ell*scalarMomentum sharp) := by
  have hp (v : Ambient) : covariantMomentum v*potentialAction m ell=
      potentialAction m ell*covariantMomentum v+(-Complex.I) •
        (SourceClosedCostNativeProbe.coordinateAction v*SourceMixedNativeReturn.thetaAction m ell) :=
    LinearMap.ext (momentum_potential m ell v)
  have he := end_sum_commutator
    (fun a => constantAction sharp (scalarBasis a))
    (fun a => covariantMomentum (scalarDirection a))
    (fun a => SourceClosedCostNativeProbe.coordinateAction (scalarDirection a))
    (potentialAction m ell) (SourceMixedNativeReturn.thetaAction m ell)
    (fun a => constant_potential sharp (scalarBasis a) m ell) (fun a => hp (scalarDirection a))
  have hc : scalarMomentum sharp*potentialAction m ell-potentialAction m ell*scalarMomentum sharp=
      (-Complex.I) • (scalarAction sharp*SourceMixedNativeReturn.thetaAction m ell) :=
    he.trans (congrArg (fun A : CoreEnd => (-Complex.I) • (A*SourceMixedNativeReturn.thetaAction m ell))
      (scalar_sum sharp))
  rw [hc,smul_smul]
  norm_num

theorem actual_scalar_pair (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell g))=
      Complex.I*(sourcePair (scalarMomentumAdjoint sharp f) (potentialAction m ell g)-
        sourcePair (potentialAction m ell f) (scalarMomentum sharp g)) := by
  have h := LinearMap.congr_fun (actual_scalar_commutator sharp m ell) g
  change scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell g)=
    Complex.I • (scalarMomentum sharp (potentialAction m ell g)-potentialAction m ell (scalarMomentum sharp g)) at h
  rw [h]
  change inner ℂ (embed f) (embed (Complex.I • (_-_)))=_
  rw [map_smul,map_sub,inner_smul_right,inner_sub_right]
  change Complex.I*(sourcePair f (scalarMomentum sharp (potentialAction m ell g))-
    sourcePair f (potentialAction m ell (scalarMomentum sharp g)))=_
  exact congrArg (fun a : ℂ => Complex.I*a)
    (congrArg₂ (fun a b : ℂ => a-b) (scalar_momentum_pair sharp f (potentialAction m ell g))
      (potential_pair m ell f (scalarMomentum sharp g)))

private theorem core_embed (g : OriginalCore) : embed (coreEquiv.symm g)=Subtype.val g :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)

def compressionCore (F : Index) : CoreEnd where
  toFun f := coreEquiv.symm ⟨GaussGradedCompression.compression F (embed f),compression_mem_core F _⟩
  map_add' f g := by apply coreEquiv.injective; apply Subtype.ext; simp [map_add]
  map_smul' c f := by apply coreEquiv.injective; apply Subtype.ext; simp [map_smul]

private theorem compression_core (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) :=
  core_embed _

/-- The full core defect, including the actual graded compression and escape carrier. -/
def defectAction (F : Index) : CoreEnd := diagonalAction-compressionCore F

def transportCorrection (F : Index) (A : CoreEnd) (q : QuantumTest) : H :=
  embed ((diagonalAction*A-A*diagonalAction) q)+embed (A (defectAction F q))-
    embed (defectAction F (A q))

theorem actual_source_defect (F : Index) (z : ℂ) (hz : z.im≠0) (g : OriginalCore) :
    embed (defectAction F (coreEquiv.symm (sourceCore F z hz g)))=finiteProjectionDefect F z hz g := by
  rw [defectAction,LinearMap.sub_apply,map_sub,compression_core,core_embed]
  rfl

private theorem correction_compression (F : Index) (A : CoreEnd) (q : QuantumTest) :
    transportCorrection F A q=GaussGradedCompression.compression F (embed (A q))-
      embed (A (compressionCore F q)) := by
  simp only [transportCorrection,defectAction,LinearMap.sub_apply,Module.End.mul_apply,
    map_sub,compression_core]
  abel

private theorem transport_finish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (x h a e : E) (hx : R h=x) (he : e=h-a) : x=R a+R e := by
  rw [he,map_sub,hx]
  abel

/-- Each relative correction is generated by the actual full source commutator and both core defects. -/
theorem actual_relative_transport (F : Index) (A : CoreEnd) (z : ℂ) (hz : z.im≠0) (g : OriginalCore) :
    embed (A (coreEquiv.symm (sourceCore F z hz g)))=
      finiteResolvent F z (embed (A (coreEquiv.symm g)))+
      finiteResolvent F z (transportCorrection F A (coreEquiv.symm (sourceCore F z hz g))) := by
  let q := coreEquiv.symm (sourceCore F z hz g)
  have hs : compressionCore F q=coreEquiv.symm g+z • q := by
    have he := congrArg (fun B : H →L[ℂ] H => B (Subtype.val g))
      (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    change GaussGradedCompression.compression F (finiteResolvent F z (Subtype.val g))-
      z • finiteResolvent F z (Subtype.val g)=Subtype.val g at he
    have hq : embed q=finiteResolvent F z (Subtype.val g) := core_embed _
    have lhs := (compression_core F q).trans (congrArg (GaussGradedCompression.compression F) hq)
    have rhs : embed (coreEquiv.symm g+z • q)=Subtype.val g+z • finiteResolvent F z (Subtype.val g) :=
      (map_add embed _ _).trans (congrArg₂ (fun a b : H => a+b) (core_embed g)
        ((map_smul embed z q).trans (congrArg (fun a : H => z • a) hq)))
    exact embed_injective ((lhs.trans (sub_eq_iff_eq_add.mp he)).trans rhs.symm)
  have ha : embed (A (compressionCore F q))=
      embed (A (coreEquiv.symm g))+z • embed (A q) := by
    have he := congrArg (fun f : QuantumTest => embed (A f)) hs
    have hA := (map_add A (coreEquiv.symm g) (z • q)).trans
      (congrArg (fun f : QuantumTest => A (coreEquiv.symm g)+f) (map_smul A z q))
    have hem := (map_add embed (A (coreEquiv.symm g)) (z • A q)).trans
      (congrArg (fun x : H => embed (A (coreEquiv.symm g))+x) (map_smul embed z (A q)))
    exact he.trans ((congrArg embed hA).trans hem)
  have hc : transportCorrection F A q=
      GaussGradedCompression.compression F (embed (A q))-z • embed (A q)-embed (A (coreEquiv.symm g)) :=
    (correction_compression F A q).trans ((congrArg
      (fun x : H => GaussGradedCompression.compression F (embed (A q))-x) ha).trans (by abel))
  have hl := congrArg (fun B : H →L[ℂ] H => B (embed (A q)))
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F (embed (A q))-z • embed (A q))=embed (A q) at hl
  exact transport_finish (finiteResolvent F z) (embed (A q))
    (GaussGradedCompression.compression F (embed (A q))-z • embed (A q))
    (embed (A (coreEquiv.symm g))) (transportCorrection F A q) hl hc

private theorem star_im_ne (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

/-- These are the six generated relative terms, retained as one signed current. -/
def signedCorrection (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) : ℂ :=
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  let R := finiteResolvent F z
  let Rstar := finiteResolvent F (star z)
  let b := potentialAction m ell
  let L := scalarMomentum sharp
  let Lstar := scalarMomentumAdjoint sharp
  inner ℂ (Rstar (embed (Lstar (coreEquiv.symm k)))) (R (transportCorrection F b q))+
  inner ℂ (Rstar (transportCorrection F Lstar p)) (R (embed (b (coreEquiv.symm g))))+
  inner ℂ (Rstar (transportCorrection F Lstar p)) (R (transportCorrection F b q))-
  inner ℂ (Rstar (embed (b (coreEquiv.symm k)))) (R (transportCorrection F L q))-
  inner ℂ (Rstar (transportCorrection F b p)) (R (embed (L (coreEquiv.symm g))))-
  inner ℂ (Rstar (transportCorrection F b p)) (R (transportCorrection F L q))

def fixedProfiles (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : OriginalCore) : ℂ :=
  inner ℂ (finiteResolvent F (star z) (embed (scalarMomentumAdjoint sharp (coreEquiv.symm k))))
    (finiteResolvent F z (embed (potentialAction m ell (coreEquiv.symm g))))-
  inner ℂ (finiteResolvent F (star z) (embed (potentialAction m ell (coreEquiv.symm k))))
    (finiteResolvent F z (embed (scalarMomentum sharp (coreEquiv.symm g))))

private theorem paired_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b c d e f h j : E) :
    inner ℂ (a+b) (c+d)-inner ℂ (e+f) (h+j)=
      (inner ℂ a c-inner ℂ e h)+
      (inner ℂ a d+inner ℂ b c+inner ℂ b d-inner ℂ e j-inner ℂ f h-inner ℂ f j) := by
  simp only [inner_add_left,inner_add_right]
  ring

/-- Complete actual eight-term return; no correction budget is a premise. -/
theorem actual_scalar_relative_ward (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) :
    sourcePair (coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k))
      (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell (coreEquiv.symm (sourceCore F z hz g))))=
      Complex.I*(fixedProfiles sharp m ell F z g k+signedCorrection sharp m ell F z hz g k) := by
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  have hL := actual_relative_transport F (scalarMomentumAdjoint sharp) (star z) (star_im_ne z hz) k
  have hb := actual_relative_transport F (potentialAction m ell) z hz g
  have hb' := actual_relative_transport F (potentialAction m ell) (star z) (star_im_ne z hz) k
  have hL' := actual_relative_transport F (scalarMomentum sharp) z hz g
  have h := actual_scalar_pair sharp m ell p q
  have he := congrArg₂ (fun a b : ℂ => a-b) (congrArg₂ (inner ℂ) hL hb) (congrArg₂ (inner ℂ) hb' hL')
  have hex := paired_expansion
    (finiteResolvent F (star z) (embed (scalarMomentumAdjoint sharp (coreEquiv.symm k))))
    (finiteResolvent F (star z) (transportCorrection F (scalarMomentumAdjoint sharp) p))
    (finiteResolvent F z (embed (potentialAction m ell (coreEquiv.symm g))))
    (finiteResolvent F z (transportCorrection F (potentialAction m ell) q))
    (finiteResolvent F (star z) (embed (potentialAction m ell (coreEquiv.symm k))))
    (finiteResolvent F (star z) (transportCorrection F (potentialAction m ell) p))
    (finiteResolvent F z (embed (scalarMomentum sharp (coreEquiv.symm g))))
    (finiteResolvent F z (transportCorrection F (scalarMomentum sharp) q))
  exact h.trans (congrArg (fun a : ℂ => Complex.I*a) (he.trans hex))

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) (star_im_ne z hz))
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
    star z • FullYSourceResolventGraphSplice.resolvent C (star z) k=k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f)-
    z • FullYSourceResolventGraphSplice.resolvent C z f=f at hf
  have hs : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
      star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun x => inner ℂ x _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (C (FullYSourceResolventGraphSplice.resolvent C z f)-z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,hs,
        starRingEnd_apply,star_star]
    _ = _ := congrArg (fun x => inner ℂ _ x) hf

/-- The literal Gamma numerator now consumes the full paired relative return. -/
theorem actual_gamma_paired_return (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) :
    sourceGamma sharp m ell F g k z=
      (-96*(sourceTime 0 : ℂ)^2)*(Complex.I*(fixedProfiles sharp m ell F z g k+
        signedCorrection sharp m ell F z hz g k))-
      Complex.I*inner ℂ (Subtype.val k)
        ((sourceRead F g (primitive sharp m ell)*SourceMovingJetFlux.orbitWord F z-
          SourceMovingJetFlux.orbitWord F z*sourceRead F g (primitive sharp m ell)) (Subtype.val g)) := by
  let q := coreEquiv.symm (sourceCore F z hz g)
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  have hp : inner ℂ (Subtype.val k) (finiteResolvent F z
      (embed (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell q))))=
        sourcePair p (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell q)) := by
    have he := resolvent_pair (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz (Subtype.val k)
      (embed (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell q)))
    exact he.trans (congrArg (fun x : H => inner ℂ x
      (embed (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell q)))) (core_embed (sourceCore F (star z) (star_im_ne z hz) k)).symm)
  have h := gamma_source_return sharp m ell F g k z hz
  have hw := hp.trans (actual_scalar_relative_ward sharp m ell F z hz g k)
  exact h.trans (congrArg (fun a : ℂ => (-96*(sourceTime 0 : ℂ)^2)*a-
    Complex.I*inner ℂ (Subtype.val k)
      ((sourceRead F g (primitive sharp m ell)*SourceMovingJetFlux.orbitWord F z-
        SourceMovingJetFlux.orbitWord F z*sourceRead F g (primitive sharp m ell)) (Subtype.val g))) hw)

def r2Profile (F : Index) (z : ℂ) (x y : H) : ℂ :=
  inner ℂ x (finiteResolvent F z (finiteResolvent F z y))

private theorem r2_pair (F : Index) (z : ℂ) (hz : z.im≠0) (x y : H) :
    inner ℂ (finiteResolvent F (star z) x) (finiteResolvent F z y)=r2Profile F z x y :=
  (resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) z hz x _).symm

private theorem r2_continuous (F : Index) (μ : ℝ) (hμ : 0<μ) (x y : H) :
    Continuous (fun w => r2Profile F (line μ w) x y) :=
  continuous_const.inner ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply
    ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const))

private theorem r2_square_bound (F : Index) (μ : ℝ) (hμ : 0<μ) (w : ℝ) (x y : H) :
    ‖r2Profile F (line μ w) x y‖^2  ≤  (‖x‖^2/μ^2)*‖finiteResolvent F (line μ w) y‖^2 := by
  have hn : ‖finiteResolvent F (line μ w)‖ ≤ 1/μ := by
    simpa only [line_im,abs_of_pos hμ] using finite_resolvent_norm F (line μ w)
      (by simpa only [line_im] using hμ.ne')
  have hb := (norm_inner_le_norm (𝕜 := ℂ) x
    (finiteResolvent F (line μ w) (finiteResolvent F (line μ w) y))).trans
    (mul_le_mul_of_nonneg_left (((finiteResolvent F (line μ w)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) (norm_nonneg x))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [r2Profile,mul_pow,one_div,inv_pow,div_eq_mul_inv,mul_assoc,one_pow,one_mul] using! hs

private theorem r2_square_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (x y : H) :
    Integrable (fun w => ‖r2Profile F (line μ w) x y‖^2) := by
  have hi : Integrable (fun w => ‖finiteResolvent F (line μ w) y‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! SourceActualResolventEnergy.actual_square_integrable F μ hμ y
  apply (hi.const_mul (‖x‖^2/μ^2)).mono' ((r2_continuous F μ hμ x y).norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact r2_square_bound F μ hμ w x y

private theorem r2_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (x y : H) :
    (∫ w : ℝ, ‖r2Profile F (line μ w) x y‖^2) ≤ (Real.pi/μ^3)*(‖x‖^2*‖y‖^2) := by
  have hi : Integrable (fun w => ‖finiteResolvent F (line μ w) y‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! SourceActualResolventEnergy.actual_square_integrable F μ hμ y
  have hm := integral_mono (r2_square_integrable F μ hμ x y) (hi.const_mul (‖x‖^2/μ^2))
    (fun w => r2_square_bound F μ hμ w x y)
  have he : (∫ w : ℝ, ‖finiteResolvent F (line μ w) y‖^2)=(Real.pi/μ)*‖y‖^2 := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! SourceActualResolventEnergy.actual_square_integral F μ hμ y
  rw [integral_const_mul,he] at hm
  exact hm.trans_eq (by field_simp)

private theorem fixed_r2_profiles (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) : fixedProfiles sharp m ell F z g k=
      r2Profile F z (embed (scalarMomentumAdjoint sharp (coreEquiv.symm k)))
        (embed (potentialAction m ell (coreEquiv.symm g)))-
      r2Profile F z (embed (potentialAction m ell (coreEquiv.symm k)))
        (embed (scalarMomentum sharp (coreEquiv.symm g))) :=
  congrArg₂ (fun a b : ℂ => a-b) (r2_pair F z hz _ _) (r2_pair F z hz _ _)

private theorem two_square (a b : ℂ) : ‖a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := norm_sub_le a b
  nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a-b),norm_nonneg a,norm_nonneg b]

private theorem fixed_square_integrable (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : OriginalCore) : Integrable (fun w => ‖fixedProfiles sharp m ell F (line μ w) g k‖^2) := by
  let x := embed (scalarMomentumAdjoint sharp (coreEquiv.symm k))
  let y := embed (potentialAction m ell (coreEquiv.symm g))
  let a := embed (potentialAction m ell (coreEquiv.symm k))
  let b := embed (scalarMomentum sharp (coreEquiv.symm g))
  have hi := ((r2_square_integrable F μ hμ x y).add (r2_square_integrable F μ hμ a b)).const_mul 2
  have hc := ((r2_continuous F μ hμ x y).sub (r2_continuous F μ hμ a b)).norm.pow 2
  have hd : Integrable (fun w => ‖r2Profile F (line μ w) x y-r2Profile F (line μ w) a b‖^2) := by
    apply hi.mono' hc.aestronglyMeasurable
    apply Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact two_square _ _
  apply hd.congr
  exact Eventually.of_forall (fun w => congrArg (fun c : ℂ => ‖c‖^2)
    (fixed_r2_profiles sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k).symm)

/-- All-F paired frequency budget, consuming the actual resolvent before any cofinal limit. -/
theorem actual_fixed_profiles_energy (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : OriginalCore) :
    (∫ w : ℝ, ‖fixedProfiles sharp m ell F (line μ w) g k‖^2) ≤ (2*Real.pi/μ^3)*
      (‖embed (scalarMomentumAdjoint sharp (coreEquiv.symm k))‖^2*
          ‖embed (potentialAction m ell (coreEquiv.symm g))‖^2+
       ‖embed (potentialAction m ell (coreEquiv.symm k))‖^2*
          ‖embed (scalarMomentum sharp (coreEquiv.symm g))‖^2) := by
  let x := embed (scalarMomentumAdjoint sharp (coreEquiv.symm k))
  let y := embed (potentialAction m ell (coreEquiv.symm g))
  let a := embed (potentialAction m ell (coreEquiv.symm k))
  let b := embed (scalarMomentum sharp (coreEquiv.symm g))
  have hl := r2_square_integrable F μ hμ x y
  have hr := r2_square_integrable F μ hμ a b
  have hm := integral_mono (fixed_square_integrable sharp m ell F μ hμ g k)
    ((hl.add hr).const_mul 2) (fun w => by
      rw [fixed_r2_profiles sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne')]
      exact two_square _ _)
  rw [integral_const_mul] at hm
  simp only [Pi.add_apply] at hm
  rw [integral_add hl hr] at hm
  exact hm.trans ((mul_le_mul_of_nonneg_left (add_le_add (r2_energy F μ hμ x y)
    (r2_energy F μ hμ a b)) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by dsimp [x,y,a,b]; ring))

private def radialPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1),((n.choose j : ℝ)*(-1)^j)*radialPrimitive j x

private theorem polynomial_derivative (n : ℕ) (x : ℝ) (hx : 0<x) :
    HasDerivAt (radialPolynomial n) (4*x*(1-x⁻¹)^n) x := by
  have h := HasDerivAt.fun_sum (u := Finset.range (n+1)) (fun j _ =>
    (radial_primitive_derivative j x hx).const_mul ((n.choose j : ℝ)*(-1)^j))
  convert! h using 1
  rw [←binomial_scalar,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem polynomial_one (n : ℕ) : radialPolynomial n 1=0 := by
  have hp (j : ℕ) : radialPrimitive j 1=0 := by
    match j with
    | 0 => norm_num [radialPrimitive]
    | 1 => norm_num [radialPrimitive]
    | 2 => norm_num [radialPrimitive]
    | j+3 => simp only [radialPrimitive,inv_one,one_pow,sub_self,mul_zero]
  simp only [radialPolynomial,hp,mul_zero,Finset.sum_const_zero]

private def radialSum (m ell : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico (m+1) (ell+1),(1-x⁻¹)^j

private theorem radial_sum_identity (m ell : ℕ) (hle : m ≤ ell) (x : ℝ) (hx : x≠0) :
    radialSum m ell x=x*((1-x⁻¹)^(m+1)-(1-x⁻¹)^(ell+1)) := by
  have h := geom_sum_Ico_mul_neg (1-x⁻¹) (show m+1 ≤ ell+1 by omega)
  change radialSum m ell x*(1-(1-x⁻¹))=_ at h
  rw [show 1-(1-x⁻¹)=x⁻¹ by ring] at h
  have he := congrArg (fun a : ℝ => a*x) h
  simp only [mul_assoc,inv_mul_cancel₀ hx,mul_one] at he
  exact he.trans (mul_comm _ _)

private theorem radial_sum_nonneg (m ell : ℕ) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ radialSum m ell x := by
  apply Finset.sum_nonneg
  intro j _
  exact pow_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hx)) _

private theorem radial_sum_mono (m ell : ℕ) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    radialSum m ell x ≤ radialSum m ell y := by
  apply Finset.sum_le_sum
  intro j _
  apply pow_le_pow_left₀ (sub_nonneg.mpr (inv_le_one_of_one_le₀ hx))
  exact sub_le_sub_left (inv_anti₀ (by linarith) hxy) _

/-- The antiderivative is controlled by the original relative cutoff, with a fixed polynomial source weight. -/
theorem radial_potential_bound (m ell : ℕ) (hle : m ≤ ell) (z : SourceCoordinateSlice) :
    |radialPotential m ell z| ≤ 4*(radius z)^2*SourceNativeCutoffContact.theta m ell z := by
  let ρ := radius z
  have hρ : 1 ≤ ρ := one_le_radius z
  let f : ℝ → ℝ := fun x => radialPolynomial (m+1) x-radialPolynomial (ell+1) x
  have hd (x : ℝ) (hx : 1 ≤ x) : HasDerivAt f (4*radialSum m ell x) x := by
    have h := (polynomial_derivative (m+1) x (by linarith)).sub
      (polynomial_derivative (ell+1) x (by linarith))
    convert! h using 1
    rw [radial_sum_identity m ell hle x (by linarith)]
    ring
  have hb (x : ℝ) (hx : x∈Set.Ico 1 ρ) : ‖4*radialSum m ell x‖ ≤ 4*radialSum m ell ρ := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) (radial_sum_nonneg m ell x hx.1))]
    exact mul_le_mul_of_nonneg_left (radial_sum_mono m ell hx.1 hx.2.le) (by norm_num)
  have hv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x hx => (hd x hx.1).hasDerivWithinAt) hb ρ (show ρ∈Set.Icc 1 ρ from ⟨hρ,le_rfl⟩)
  have hf : f 1=0 := by simp only [f,polynomial_one,sub_self]
  rw [hf,sub_zero,Real.norm_eq_abs] at hv
  have hsum := radial_sum_nonneg m ell ρ hρ
  have hs := radial_sum_identity m ell hle ρ (by linarith)
  have ht : radialSum m ell ρ=ρ*SourceNativeCutoffContact.theta m ell z := hs
  have hθ : 0 ≤ SourceNativeCutoffContact.theta m ell z := by rw [ht] at hsum; nlinarith
  change |f ρ| ≤ _
  apply hv.trans
  rw [ht]
  change 4*(ρ*SourceNativeCutoffContact.theta m ell z)*(ρ-1) ≤ 4*ρ^2*SourceNativeCutoffContact.theta m ell z
  nlinarith [mul_nonneg (by linarith : 0 ≤ ρ) hθ]

private theorem scalar_multiplier_domination (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart, ContDiffAt ℝ ∞ d z.val)
    (hcd : ∀ z : physicalChart, |c z.val| ≤ |d z.val|) (f : QuantumTest) :
    ‖embed (multiply c hc f)‖ ≤ ‖embed (multiply d hd f)‖ := by
  let a := multiply c hc f
  let b := multiply d hd f
  have hp (z : SourceCoordinateSlice) : (densityPair a a z).re ≤ (densityPair b b z).re := by
    by_cases hz : z∈physicalChart
    · change (inner ℂ (GaussFockWeights.weight (fun N => (GaussDensityCore.density N z : ℂ))
        ((c z : ℂ) • f z)) ((c z : ℂ) • f z)).re ≤
        (inner ℂ (GaussFockWeights.weight (fun N => (GaussDensityCore.density N z : ℂ))
        ((d z : ℂ) • f z)) ((d z : ℂ) • f z)).re
      have hpos (N : ℕ) : 0 ≤ GaussDensityCore.density N z := (GaussDensityCore.density_pos N ⟨z,hz⟩).le
      have ha : (inner ℂ (GaussFockWeights.weight (fun N => (GaussDensityCore.density N z : ℂ))
          ((c z : ℂ) • f z)) ((c z : ℂ) • f z)).re=
          ‖GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z) ((c z : ℂ) • f z)‖^2 :=
        GaussBoundedMultiplier.weighted_square _ hpos _
      have hb : (inner ℂ (GaussFockWeights.weight (fun N => (GaussDensityCore.density N z : ℂ))
          ((d z : ℂ) • f z)) ((d z : ℂ) • f z)).re=
          ‖GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z) ((d z : ℂ) • f z)‖^2 :=
        GaussBoundedMultiplier.weighted_square _ hpos _
      rw [ha,hb,map_smul,map_smul,norm_smul,norm_smul,
        Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
      exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hcd ⟨z,hz⟩) (norm_nonneg _)) 2
    · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
      simp [densityPair,a,b,multiply_apply,hf]
  have hn := integral_mono (densityPair_integrable a a).re (densityPair_integrable b b).re hp
  rw [←GaussBoundedMultiplier.norm_square_integral,←GaussBoundedMultiplier.norm_square_integral] at hn
  nlinarith [norm_nonneg (embed a),norm_nonneg (embed b)]

def radiusSquareAction : CoreEnd :=
  multiply (fun z => 4*(radius z)^2) (fun _ => (contDiff_const.mul (radius_smooth.pow 2)).contDiffAt)

/-- A fixed source absorbs the polynomial weight; no state moment is supplied. -/
theorem actual_potential_tail_domination (m ell : ℕ) (hle : m ≤ ell) (f : QuantumTest) :
    ‖embed (potentialAction m ell f)‖ ≤
      ‖SourceRelativePowerTail.relativeTail m ell (embed (radiusSquareAction f))‖ := by
  let d := fun z => 4*(radius z)^2*SourceNativeCutoffContact.theta m ell z
  have hd : ContDiff ℝ ∞ d :=
    (contDiff_const.mul (radius_smooth.pow 2)).mul (SourceNativeCutoffContact.theta_smooth m ell)
  have hb (z : physicalChart) : |radialPotential m ell z.val| ≤ |d z.val| :=
    (radial_potential_bound m ell hle z.val).trans (le_abs_self _)
  have h := scalar_multiplier_domination (radialPotential m ell) d
    (fun _ => (potential_smooth m ell).contDiffAt) (fun _ => hd.contDiffAt) hb f
  have he : multiply d (fun _ => hd.contDiffAt) f=
      SourceNativeCutoffContact.thetaAction m ell (radiusSquareAction f) := by
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    simp only [multiply_apply,SourceNativeCutoffContact.thetaAction,radiusSquareAction,PiLp.smul_apply]
    change (d z : ℂ)*f z word=(SourceNativeCutoffContact.theta m ell z : ℂ)*((4*(radius z)^2 : ℝ)*f z word)
    dsimp [d]
    push_cast
    ring
  exact h.trans_eq (congrArg (fun q : QuantumTest => ‖embed q‖) he |>.trans
    (congrArg norm (SourceNativeCutoffContact.theta_core m ell (radiusSquareAction f))))

theorem actual_potential_fixed_source_tail (f : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ‖embed (potentialAction m ell f)‖<ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := SourceHardyRetardedTail.original_relative_tail (embed (radiusSquareAction f)) ε hε
  exact ⟨N,fun m hm ell hell => (actual_potential_tail_domination m ell hell f).trans_lt (hN m hm ell hell)⟩
private theorem potential_scaled_tail (f : QuantumTest) (C : ℝ) (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → C*‖embed (potentialAction m ell f)‖^2 ≤ ε := by
  intro ε hε
  have hp : 0<C+1 := by linarith
  obtain ⟨N,hN⟩ := actual_potential_fixed_source_tail f (Real.sqrt (ε/(C+1)))
    (Real.sqrt_pos.mpr (div_pos hε hp))
  refine ⟨N,fun m hm ell hell => ?_⟩
  have ht := hN m hm ell hell
  have hs := Real.sq_sqrt (div_pos hε hp).le
  have hb : ‖embed (potentialAction m ell f)‖^2 ≤ ε/(C+1) := by
    nlinarith [norm_nonneg (embed (potentialAction m ell f)),Real.sqrt_nonneg (ε/(C+1))]
  calc
    _  ≤  (C+1)*‖embed (potentialAction m ell f)‖^2 := by nlinarith [sq_nonneg ‖embed (potentialAction m ell f)‖]
    _  ≤  (C+1)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hb hp.le
    _ = ε := mul_div_cancel₀ ε hp.ne'

/-- The two fixed profiles have the original full-frequency cutoff tail, uniform in F and ell. -/
theorem actual_fixed_profiles_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : OriginalCore) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ, ENNReal.ofReal (‖fixedProfiles sharp m ell F (line μ w) g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hC : 0<2*Real.pi/μ^3 := div_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hμ _)
  have hδ : 0<ε/(2*(2*Real.pi/μ^3)) := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨N₁,h₁⟩ := potential_scaled_tail (coreEquiv.symm g)
    (‖embed (scalarMomentumAdjoint sharp (coreEquiv.symm k))‖^2) (sq_nonneg _) _ hδ
  obtain ⟨N₂,h₂⟩ := potential_scaled_tail (coreEquiv.symm k)
    (‖embed (scalarMomentum sharp (coreEquiv.symm g))‖^2) (sq_nonneg _) _ hδ
  refine ⟨max N₁ N₂,fun m hm ell hell F => ?_⟩
  have hl := h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell
  have hr := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell
  rw [←ofReal_integral_eq_lintegral_ofReal (fixed_square_integrable sharp m ell F μ hμ g k)
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  apply (actual_fixed_profiles_energy sharp m ell F μ hμ g k).trans
  rw [mul_comm (‖embed (potentialAction m ell (coreEquiv.symm k))‖^2)]
  calc
    _  ≤  (2*Real.pi/μ^3)*(ε/(2*(2*Real.pi/μ^3))+ε/(2*(2*Real.pi/μ^3))) := by gcongr
    _ = ε := by field_simp; ring

end LowEnergy.SourceScalarPairedTransport
