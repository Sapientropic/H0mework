import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialJoinedHessian
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open GaussScalarTransport GaussDensityCore SourceNativeMomentumCurvature SourceNativeDensityTrace SourceNativeCoframeCompatibility
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceClockYukawaRadialNativeDivergence SourceClockYukawaRadialNativeHessian SourceClockYukawaRadialMixedCore
open SourceCoframeVolume SourceHamiltonianVolume SourceLocalizedInverseFormPayment SourceCutoffDilationWard
open PositiveScalarWeakBudget PositiveScalarCoefficientDecay SourceYukawaCoefficientCommutator SourceScalarGaugeForce
open scoped ContDiff InnerProductSpace BigOperators Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev Q : End := 1-inverseAction
private abbrev d (a : ScalarIndex) : End := inverseCoefficientCore a
private abbrev M (sharp : Bool) (a : ScalarIndex) : End := constantAction sharp (scalarBasis a)
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Pa (a : ScalarIndex) : End := GaussMomentumAdjoint.adjoint (scalarDirection a)
attribute [local irreducible] fullAction compressionCore defectAction

/-- Both original boundary peaks are retained, including their natural zero cases. -/
def firstPeak (m ell : ℕ) : End := (ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m

def secondPeak (m ell : ℕ) : End := ((m:ℂ)*(m+1:ℂ)) • Q^(m-1)-
  ((ell:ℂ)*(ell+1:ℂ)) • Q^(ell-1)

private theorem d_point (a : ScalarIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    d a f z=(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ) • f z := by
  change directionAction a ((inverseAction^2) f) z=_
  rw [pow_two]
  change (directionWeight a z:ℂ) • ((reciprocal z:ℂ) • ((reciprocal z:ℂ) • f z))=_
  simp only [smul_smul]
  congr 1
  unfold GaussRadialMomentum.radialDerivative directionWeight reciprocal scalarDirection
  push_cast
  field_simp [(show (radius z:ℂ)≠0 by exact_mod_cast (radius_pos z).ne')]

private theorem real_d (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (a : ScalarIndex) : Commute (multiply c hc) (d a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change multiply c hc (d a f) z=d a (multiply c hc f) z
  rw [multiply_apply,d_point,d_point,multiply_apply]
  exact smul_comm _ _ _

private theorem geometric_point (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (Q^n) f z=((1-reciprocal z:ℝ):ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (Q ((Q^n) f)) z=_
    change ((Q^n) f) z-(reciprocal z:ℂ) • ((Q^n) f) z=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module

private theorem first_peak_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    firstPeak m ell f z=
      (((ell+1:ℝ)*(1-reciprocal z)^ell-(m+1:ℝ)*(1-reciprocal z)^m):ℂ) • f z := by
  simp only [firstPeak,LinearMap.sub_apply,LinearMap.smul_apply]
  change (ell+1:ℂ) • ((Q^ell) f) z-(m+1:ℂ) • ((Q^m) f) z=_
  rw [geometric_point,geometric_point]
  push_cast
  module

private theorem contact_peak (a : ScalarIndex) (m ell : ℕ) :
    SourceNativeCutoffContact.contactAction (scalarDirection a) m ell=(-Complex.I) • (firstPeak m ell*d a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative (scalarDirection a) m ell z:ℂ)) • f z=
    (-Complex.I) • (firstPeak m ell (d a f)) z
  rw [first_peak_point,d_point]
  simp only [smul_smul]
  congr 1
  unfold SourceNativeCutoffContact.thetaDerivative
  push_cast
  ring

private theorem coefficient_peaks (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    coefficient sharp a m ell=M sharp a*thetaAction m ell+fullAction sharp*firstPeak m ell*d a := by
  rw [PositiveScalarWeakBudget.coefficient,contact_peak]
  have hi : Complex.I*(-Complex.I)=1 := by rw [mul_neg,Complex.I_mul_I,neg_neg]
  simp only [mul_smul_comm,smul_smul,hi,one_smul,mul_assoc]
  rfl

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) : Commute (multiply c hc) (fullAction sharp) := by
  unfold fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (sourceMap (scalarField z)) (c z:ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z:ℂ) (f z)).symm

private theorem inverse_M (sharp : Bool) (a : ScalarIndex) : Commute inverseAction (M sharp a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (branchMap sharp (scalarBasis a)) (reciprocal z:ℂ) (f z)).symm
private theorem inverse_Y (sharp : Bool) : Commute inverseAction (fullAction sharp) :=
  real_full _ _ sharp
private theorem inverse_W : Commute inverseAction W := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (reciprocal z:ℂ) (scalarWeight z:ℂ) (f z)
private theorem inverse_d (a : ScalarIndex) : Commute inverseAction (d a) := real_d _ _ a

private theorem Q_commute {A : End} (h : Commute inverseAction A) : Commute Q A :=
  (Commute.one_left A).sub_left h
private theorem first_commute {A : End} (h : Commute inverseAction A) (m ell : ℕ) : Commute (firstPeak m ell) A :=
  (((Q_commute h).pow_left ell).smul_left _).sub_left (((Q_commute h).pow_left m).smul_left _)
private theorem second_commute {A : End} (h : Commute inverseAction A) (m ell : ℕ) : Commute (secondPeak m ell) A :=
  (((Q_commute h).pow_left (m-1)).smul_left _).sub_left (((Q_commute h).pow_left (ell-1)).smul_left _)
private theorem theta_commute {A : End} (h : Commute inverseAction A) (m ell : ℕ) : Commute (thetaAction m ell) A :=
  ((Q_commute h).pow_left (m+1)).sub_left ((Q_commute h).pow_left (ell+1))

private theorem bracket_product (A B C : End) : bracket A (B*C)=bracket A B*C+B*bracket A C := by unfold bracket;noncomm_ring
private theorem bracket_smul (A B : End) (c : ℂ) : bracket A (c • B)=c • bracket A B := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bracket_sub (A B C : End) : bracket A (B-C)=bracket A B-bracket A C := by unfold bracket;noncomm_ring

private theorem adjoint_inverse (a : ScalarIndex) : bracket (Pa a) inverseAction=(-Complex.I) • d a := by
  apply LinearMap.ext
  intro f
  change GaussMomentumAdjoint.adjoint (scalarDirection a) (inverseAction f)-inverseAction (GaussMomentumAdjoint.adjoint (scalarDirection a) f)=_
  rw [GaussRadialMomentumDomain.adjoint_core_commutator,add_sub_cancel_left]
  apply DFunLike.ext
  intro z
  change ((-Complex.I)*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)) • f z=
    (-Complex.I) • (d a f z)
  rw [d_point]
  exact mul_smul _ _ _

private theorem adjoint_Q (a : ScalarIndex) : bracket (Pa a) Q=Complex.I • d a := by
  rw [bracket_sub]
  have hz : bracket (Pa a) (1:End)=0 := by simp [bracket]
  rw [hz,adjoint_inverse,zero_sub,neg_smul,neg_neg]

private theorem adjoint_geometric_successor (a : ScalarIndex) (n : ℕ) :
    bracket (Pa a) (Q^(n+1))=((n+1:ℂ)*Complex.I) • (Q^n*d a) := by
  induction n with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul] using adjoint_Q a
  | succ n ih =>
    rw [show n+1+1=(n+1)+1 from rfl,pow_succ,bracket_product,ih,adjoint_Q]
    have hm : (Q^n*d a)*Q=Q^(n+1)*d a := by
      rw [mul_assoc,(Q_commute (inverse_d a)).symm.eq,←mul_assoc,←pow_succ]
    simp only [smul_mul_assoc,mul_smul_comm]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module

private theorem adjoint_geometric (a : ScalarIndex) (n : ℕ) :
    bracket (Pa a) (Q^n)=((n:ℂ)*Complex.I) • (Q^(n-1)*d a) := by
  cases n with
  | zero => simp [bracket]
  | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using adjoint_geometric_successor a n

private theorem adjoint_first_peak (a : ScalarIndex) (m ell : ℕ) :
    bracket (Pa a) (firstPeak m ell)=(-Complex.I) • (secondPeak m ell*d a) := by
  rw [firstPeak,bracket_sub,bracket_smul,bracket_smul,adjoint_geometric,adjoint_geometric]
  simp only [secondPeak,sub_mul,smul_mul_assoc,smul_sub,smul_smul]
  module

private theorem adjoint_theta (a : ScalarIndex) (m ell : ℕ) :
    bracket (Pa a) (thetaAction m ell)=(-Complex.I) • (firstPeak m ell*d a) := by
  apply LinearMap.ext
  intro f
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
  rw [thetaAction,←SourceNativeCutoffContact.theta_action_polynomial,SourceNativeCutoffContact.sharp_core_contact,add_sub_cancel_left]
  exact LinearMap.congr_fun (contact_peak a m ell) f

private def constantFiber (sharp : Bool) (a : ScalarIndex) (z : SourceCoordinateSlice) : FiberEnd :=
  connection (scalarDirection a) z*branchMap sharp (scalarBasis a)-branchMap sharp (scalarBasis a)*connection (scalarDirection a) z
private theorem constant_smooth (sharp : Bool) (a : ScalarIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (constantFiber sharp a) z.val :=
  ((connection_smooth (scalarDirection a) z).mul contDiffAt_const).sub
    (contDiffAt_const.mul (connection_smooth (scalarDirection a) z))

private theorem density_smooth (N : ℕ) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (SourceNativeMomentumCurvature.divergenceCoefficient N v) z.val := by
  apply ContDiffAt.sum
  intro i _
  exact (inverseDensity_smooth N z).mul
    ((((complexDensity_smooth N z).mul (coefficient_smooth v i z)).fderiv_right (by simp)).clm_apply contDiffAt_const)
private theorem correction_smooth (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (nativeDensityCorrection v) z.val := by
  have he : nativeDensityCorrection v=ᶠ[nhds z.val] (fun x => (SourceNativeMomentumCurvature.divergenceCoefficient 0 v x).re) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    have h := congrArg Complex.re (original_density_gamma_return 0 v ⟨x,hx⟩)
    simpa only [Complex.ofReal_re,nativeDensityCorrection,intrinsicDensity] using h.symm
  exact (Complex.reCLM.contDiff.contDiffAt.comp z.val (density_smooth 0 v z)).congr_of_eventuallyEq he

private def densityFiber (sharp : Bool) (a : ScalarIndex) (z : SourceCoordinateSlice) : FiberEnd :=
  constantFiber sharp a z+(nativeDensityCorrection (scalarDirection a) z:ℂ) • branchMap sharp (scalarBasis a)
private theorem density_fiber_smooth (sharp : Bool) (a : ScalarIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (densityFiber sharp a) z.val :=
  (constant_smooth sharp a z).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (correction_smooth (scalarDirection a) z)).smul contDiffAt_const)

private theorem gamma_smooth (sharp : Bool) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => branchMap sharp (gammaGradient x)) z.val := by
  have he : (fun x => branchMap sharp (gammaGradient x))=(fun x => -(∑ a : ScalarIndex,densityFiber sharp a x)) := by
    funext x
    have h := congrArg (fun A : FiberEnd => -A) (original_constant_density_hessian sharp x)
    simpa only [neg_neg,densityFiber,constantFiber] using h.symm
  rw [he]
  exact (ContDiffAt.sum (fun a _ => density_fiber_smooth sharp a z)).neg

/-- The surviving direction is the actual broken gamma-gradient; no boundedness or vanishing is assumed. -/
def gammaAction (sharp : Bool) : End := localMultiplier (fun x => branchMap sharp (gammaGradient x)) (gamma_smooth sharp)

private theorem native_weight (v : Ambient) : Commute (covariantMomentum v) (multiply scalarWeight scalarWeight_smooth) := by
  have hvu : (volumeAction:End)*inverseVolumeAction=1 := by apply LinearMap.ext;intro f;exact volume_inverse f
  have huv : inverseVolumeAction*(volumeAction:End)=1 := by
    have hc : Commute inverseVolumeAction (volumeAction:End) := by
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      exact smul_comm (reciprocalVolume z:ℂ) (volume z:ℂ) (f z)
    rw [hc.eq]
    exact hvu
  have hP := (native_momentum_volume v).eq
  have hu : Commute (covariantMomentum v) inverseVolumeAction := by
    calc
      _=inverseVolumeAction*(volumeAction*covariantMomentum v)*inverseVolumeAction := by rw [←mul_assoc inverseVolumeAction volumeAction,huv,one_mul]
      _=inverseVolumeAction*(covariantMomentum v*volumeAction)*inverseVolumeAction := by rw [hP.symm]
      _=_ := by rw [mul_assoc,mul_assoc,hvu,mul_one]
  have hw : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    change (scalarWeight z:ℂ)*f z word=(-(sourceTime 0:ℂ))*((reciprocalVolume z:ℂ)*f z word)
    unfold scalarWeight reciprocalVolume
    push_cast
    ring
  rw [hw]
  exact hu.smul_right _

private theorem row_algebra (P D W A : End) (hp : Commute P W) (hw : Commute W A) :
    A*W*P-(P-Complex.I • D)*W*A=
      -W*bracket P A+Complex.I • (D*W*A) := by
  have h1 := congrArg (fun B : End => B*P) hw.eq
  have h2 := congrArg (fun B : End => B*A) hp.eq
  simp only [bracket,sub_mul,smul_mul_assoc,mul_sub,neg_mul,mul_assoc] at *
  linear_combination (norm := module) -h1-h2


private theorem constant_directional (sharp : Bool) (a : ScalarIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional (scalarDirection a) (M sharp a f) z=branchMap sharp (scalarBasis a) (directional (scalarDirection a) f z) := by
  have h := ((branchMap sharp (scalarBasis a)).restrictScalars ℝ).hasFDerivAt.comp z
    (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  rw [directional_apply,directional_apply]
  change fderiv ℝ (((branchMap sharp (scalarBasis a)).restrictScalars ℝ) ∘ f) z (direction (scalarDirection a) z)=_
  rw [h.fderiv]
  rfl

private theorem native_constant (sharp : Bool) (a : ScalarIndex) :
    bracket (P a) (M sharp a)=(-Complex.I) • localMultiplier (constantFiber sharp a) (constant_smooth sharp a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional (scalarDirection a) (M sharp a f) z+
    connection (scalarDirection a) z (branchMap sharp (scalarBasis a) (f z)))-
    branchMap sharp (scalarBasis a) ((-Complex.I) •
      (directional (scalarDirection a) f z+connection (scalarDirection a) z (f z)))=
      (-Complex.I) • constantFiber sharp a z (f z)
  rw [constant_directional]
  simp only [constantFiber,sub_apply,mul_apply_eq_comp,map_smul,map_add]
  module

private def constantDivergence (sharp : Bool) (a : ScalarIndex) : End := M sharp a*W*P a-Pa a*W*M sharp a

private theorem constant_divergence_source (sharp : Bool) (a : ScalarIndex) :
    constantDivergence sharp a=Complex.I •
      (W*localMultiplier (densityFiber sharp a) (density_fiber_smooth sharp a)) := by
  have hw : Commute W (M sharp a) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact (map_smul (branchMap sharp (scalarBasis a)) (scalarWeight z:ℂ) (f z)).symm
  rw [constantDivergence,Pa,original_adjoint_divergence,row_algebra _ _ _ _ (native_weight _) hw,native_constant,
    original_native_density_multiplier]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.add_apply,LinearMap.neg_apply,Module.End.mul_apply,LinearMap.smul_apply]
  change -((scalarWeight z:ℂ) • ((-Complex.I) • constantFiber sharp a z (f z)))+
    Complex.I • ((nativeDensityCorrection (scalarDirection a) z:ℂ) • ((scalarWeight z:ℂ) • branchMap sharp (scalarBasis a) (f z)))=
      Complex.I • ((scalarWeight z:ℂ) • densityFiber sharp a z (f z))
  simp only [densityFiber,add_apply,smul_apply,smul_smul]
  module

private theorem constant_density_sum (sharp : Bool) :
    (∑ a : ScalarIndex,constantDivergence sharp a)=(-Complex.I) • (W*gammaAction sharp) := by
  have hg : (∑ a : ScalarIndex,localMultiplier (densityFiber sharp a) (density_fiber_smooth sharp a))=-gammaAction sharp := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    let ev : QuantumTest →ₗ[ℂ] FockFiber :=
      { toFun := fun q => q z
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    change ev ((∑ a : ScalarIndex,localMultiplier (densityFiber sharp a) (density_fiber_smooth sharp a)) f)=_
    simp only [LinearMap.sum_apply,map_sum]
    change (∑ a : ScalarIndex,densityFiber sharp a z (f z))=-(branchMap sharp (gammaGradient z) (f z))
    have h := congrArg (fun A : FiberEnd => A (f z)) (original_constant_density_hessian sharp z)
    simpa only [densityFiber,constantFiber,sum_apply,neg_apply] using h
  simp_rw [constant_divergence_source]
  rw [←Finset.smul_sum,←Finset.mul_sum,hg,mul_neg,smul_neg,neg_smul]

private theorem native_theta (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) (thetaAction m ell)=(-Complex.I) • (firstPeak m ell*d a) := by
  apply LinearMap.ext
  intro f
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
  rw [thetaAction,←SourceNativeCutoffContact.theta_action_polynomial,SourceNativeCutoffContact.native_core_contact,add_sub_cancel_left]
  exact LinearMap.congr_fun (contact_peak a m ell) f

private theorem d_M (sharp : Bool) (a : ScalarIndex) : Commute (d a) (M sharp a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change d a (M sharp a f) z=M sharp a (d a f) z
  rw [d_point]
  change _=branchMap sharp (scalarBasis a) (d a f z)
  rw [d_point,map_smul]
  rfl
private theorem W_M (sharp : Bool) (a : ScalarIndex) : Commute W (M sharp a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (branchMap sharp (scalarBasis a)) (scalarWeight z:ℂ) (f z)).symm
private theorem W_Y (sharp : Bool) : Commute W (fullAction sharp) := real_full _ _ sharp
private theorem W_d (a : ScalarIndex) : Commute W (d a) := real_d _ _ a

private theorem adjoint_full_peak (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    bracket (Pa a) (fullAction sharp*firstPeak m ell)=(-Complex.I) •
      (M sharp a*firstPeak m ell+fullAction sharp*secondPeak m ell*d a) := by
  rw [bracket_product,native_full_adjoint_commutator,adjoint_first_peak]
  simp only [smul_mul_assoc,mul_smul_comm,←smul_add,mul_assoc]
  rfl

private theorem right_row_product (P Pa W A B : End) (hw : Commute B W) :
    (A*B)*W*P-Pa*W*(A*B)=(A*W*P-Pa*W*A)*B-A*W*bracket P B := by
  have h := congrArg (fun C : End => A*C*P) hw.eq
  unfold bracket
  linear_combination (norm := noncomm_ring) h
private theorem left_row_product (P Pa W A B : End) (hw : Commute W A) :
    (A*B)*W*P-Pa*W*(A*B)=A*(B*W*P-Pa*W*B)-bracket Pa A*W*B := by
  have h := congrArg (fun C : End => Pa*C*B) hw.eq
  unfold bracket
  linear_combination (norm := noncomm_ring) -h

private theorem joined_row_source (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    joinedZeroCore sharp a m ell=constantDivergence sharp a*thetaAction m ell+
      (fullAction sharp*firstPeak m ell)*inverseZeroCore a+
      (2*Complex.I) • (W*firstPeak m ell*d a*M sharp a)+
      Complex.I • (W*fullAction sharp*secondPeak m ell*(d a)^2) := by
  have hadd (A B : End) : (A+B)*W*P a-Pa a*W*(A+B)=
      (A*W*P a-Pa a*W*A)+(B*W*P a-Pa a*W*B) := by noncomm_ring
  rw [←original_joined_native_divergence,SourceClockYukawaRadialNativeDivergence.divergenceCoefficient,
    coefficient_peaks,hadd,right_row_product _ _ _ _ _ (theta_commute inverse_W m ell),
    left_row_product _ _ _ _ _ ((W_Y sharp).mul_right (first_commute inverse_W m ell).symm),
    native_theta,adjoint_full_peak]
  change (constantDivergence sharp a*thetaAction m ell-M sharp a*W*((-Complex.I) • (firstPeak m ell*d a)))+
    ((fullAction sharp*firstPeak m ell)*inverseDivergenceCoefficient a-
    ((-Complex.I) • (M sharp a*firstPeak m ell+fullAction sharp*secondPeak m ell*d a))*W*d a)=_
  rw [original_inverse_native_divergence]
  have hm : Commute (W*firstPeak m ell*d a) (M sharp a) :=
    ((W_M sharp a).mul_left (first_commute (inverse_M sharp a) m ell)).mul_left (d_M sharp a)
  have h1 : M sharp a*W*(firstPeak m ell*d a)=W*firstPeak m ell*d a*M sharp a := by
    calc _=M sharp a*(W*firstPeak m ell*d a) := by noncomm_ring
         _=_ := hm.symm.eq
  have h2 : (M sharp a*firstPeak m ell)*W*d a=W*firstPeak m ell*d a*M sharp a := by
    calc
      _=M sharp a*(firstPeak m ell*W)*d a := by noncomm_ring
      _=M sharp a*(W*firstPeak m ell)*d a := by rw [(first_commute inverse_W m ell).eq]
      _=M sharp a*(W*firstPeak m ell*d a) := by noncomm_ring
      _=_ := hm.symm.eq
  have hw : Commute W (fullAction sharp*secondPeak m ell*d a) :=
    ((W_Y sharp).mul_right (second_commute inverse_W m ell).symm).mul_right (W_d a)
  have h3 : (fullAction sharp*secondPeak m ell*d a)*W*d a=W*fullAction sharp*secondPeak m ell*(d a)^2 := by
    rw [hw.symm.eq,pow_two]
    noncomm_ring
  simp only [mul_smul_comm,smul_mul_assoc,add_mul,h1,h2,h3]
  module

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private theorem derivative_matrix_sum (sharp : Bool) :
    (∑ a : ScalarIndex,d a*M sharp a)=-(1/4:ℂ) • (inverseAction^3*scalarAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let ev : QuantumTest →ₗ[ℂ] FockFiber :=
    { toFun := fun q => q z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev ((∑ a : ScalarIndex,d a*M sharp a) f)=_
  simp only [LinearMap.sum_apply,Module.End.mul_apply,map_sum]
  change (∑ a : ScalarIndex,d a (M sharp a f) z)=_
  have he : ∑ a : ScalarIndex,inner ℝ (z.2.1:Scalar) (scalarBasis a) • scalarBasis a=(z.2.1:Scalar) := by
    simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using scalarBasis.sum_repr (z.2.1:Scalar)
  have h (a : ScalarIndex) : d a (M sharp a f) z=
      (-(1/4:ℂ)*(reciprocal z:ℂ)^3) • branchMap sharp
        (inner ℝ (z.2.1:Scalar) (scalarBasis a) • scalarBasis a) (f z) := by
    rw [d_point,map_smul]
    apply PiLp.ext
    intro word
    change (GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)*(branchMap sharp (scalarBasis a) (f z) word)=
      (-(1/4:ℂ)*(reciprocal z:ℂ)^3)*(inner ℝ (z.2.1:Scalar) (scalarBasis a) • branchMap sharp (scalarBasis a) (f z) word)
    simp only [Complex.real_smul]
    unfold GaussRadialMomentum.radialDerivative scalarDirection reciprocal
    push_cast
    simp only [div_eq_mul_inv,inv_pow,mul_inv_rev]
    ring
  simp_rw [h]
  rw [←Finset.smul_sum,←sum_apply,←map_sum,he]
  change _=(-(1/4:ℂ)) • (((inverseAction^3) (scalarAction sharp f)) z)
  rw [inverse_power_apply]
  simp only [smul_smul]
  rfl

private theorem derivative_square_sum : (∑ a : ScalarIndex,(d a)^2)=(1/4:ℂ) • (inverseAction^4-inverseAction^6) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let ev : QuantumTest →ₗ[ℂ] FockFiber :=
    { toFun := fun q => q z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev ((∑ a : ScalarIndex,(d a)^2) f)=_
  have hs (a : ScalarIndex) : ev (((d a)^2) f)=(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)^2 • f z := by
    change d a (d a f) z=_
    rw [d_point,d_point,smul_smul,←pow_two]
  simp only [LinearMap.sum_apply,map_sum,hs,←Finset.sum_smul,←Complex.ofReal_pow,←Complex.ofReal_sum]
  have he : (∑ a : ScalarIndex,(GaussRadialMomentum.radialDerivative (scalarDirection a) z)^2)=
      (reciprocal z^4-reciprocal z^6)/4 := by
    simp only [GaussRadialMomentum.radialDerivative,scalarDirection,neg_div,neg_sq,div_pow,
      ←Finset.sum_div]
    have hx := scalarBasis.sum_sq_inner_left (z.2.1:Scalar)
    rw [hx]
    have hr : radius z^2=1+‖(z.2.1:Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
    unfold reciprocal
    field_simp [(radius_pos z).ne']
    nlinarith only [hr]
  rw [he]
  change (((reciprocal z^4-reciprocal z^6)/4:ℝ):ℂ) • f z=(1/4:ℂ) •
    (((inverseAction^4) f) z-((inverseAction^6) f) z)
  rw [inverse_power_apply,inverse_power_apply]
  push_cast
  module

/-- The two radial peak coefficients act only through the original bounded B and vacuum source. -/
def radialHessianCore (sharp : Bool) (m ell : ℕ) : End :=
  -(1/2:ℂ) • (firstPeak m ell*inverseAction^2*(SourceClockYukawaNormalizedCurrent.normalizedAction sharp-inverseAction*constantAction sharp vacuum))+
    (1/4:ℂ) • ((secondPeak m ell*(inverseAction^3-inverseAction^5)-
      firstPeak m ell*((58:ℂ) • inverseAction^2+(3:ℂ) • inverseAction^4))*SourceClockYukawaNormalizedCurrent.normalizedAction sharp)

/-- All native jets have one finite-fiber radial part and the actual gamma direction. -/
def joinedHessianCore (sharp : Bool) (m ell : ℕ) : End :=
  Complex.I • (W*(radialHessianCore sharp m ell-thetaAction m ell*gammaAction sharp))

private theorem weight_source : W=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (scalarWeight z:ℂ)*f z word=(-(sourceTime 0:ℂ))*((reciprocalVolume z:ℂ)*f z word)
  unfold scalarWeight reciprocalVolume
  push_cast
  ring

private theorem inverse_sum_weighted : (∑ a : ScalarIndex,inverseZeroCore a)=
    (-Complex.I/4:ℂ) • (W*((58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5)) := by
  rw [original_inverse_hessian_source,weight_source]
  simp only [smul_mul_assoc,smul_smul]
  congr 1
  ring

private theorem inverse_gamma (sharp : Bool) : Commute inverseAction (gammaAction sharp) :=
  (GaussRadialHamiltonian.multiplier_commutes _ _).symm

private theorem joined_sum_raw (sharp : Bool) (m ell : ℕ) :
    (∑ a : ScalarIndex,joinedZeroCore sharp a m ell)=
      (-Complex.I) • (W*gammaAction sharp*thetaAction m ell)+
      (fullAction sharp*firstPeak m ell)*((-Complex.I/4:ℂ) •
        (W*((58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5)))+
      (2*Complex.I) • ((W*firstPeak m ell)*(-(1/4:ℂ) • (inverseAction^3*scalarAction sharp)))+
      Complex.I • ((W*fullAction sharp*secondPeak m ell)*((1/4:ℂ) • (inverseAction^4-inverseAction^6))) := by
  calc
    _=∑ a : ScalarIndex,
      (constantDivergence sharp a*thetaAction m ell+(fullAction sharp*firstPeak m ell)*inverseZeroCore a+
        (2*Complex.I) • ((W*firstPeak m ell)*(d a*M sharp a))+
        Complex.I • ((W*fullAction sharp*secondPeak m ell)*((d a)^2))) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [joined_row_source]
      simp only [mul_assoc]
    _=(∑ a : ScalarIndex,constantDivergence sharp a)*thetaAction m ell+
      (fullAction sharp*firstPeak m ell)*(∑ a : ScalarIndex,inverseZeroCore a)+
      (2*Complex.I) • ((W*firstPeak m ell)*(∑ a : ScalarIndex,d a*M sharp a))+
      Complex.I • ((W*fullAction sharp*secondPeak m ell)*(∑ a : ScalarIndex,(d a)^2)) := by
      simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,Finset.smul_sum]
    _=_ := by rw [constant_density_sum,inverse_sum_weighted,derivative_matrix_sum,derivative_square_sum,smul_mul_assoc]

private def rawRadialCore (sharp : Bool) (m ell : ℕ) : End :=
  -(1/2:ℂ) • (firstPeak m ell*inverseAction^3*scalarAction sharp)+
    (1/4:ℂ) • ((secondPeak m ell*(inverseAction^4-inverseAction^6)-
      firstPeak m ell*((58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5))*fullAction sharp)

private theorem scalar_normalized (sharp : Bool) :
    inverseAction^3*scalarAction sharp=inverseAction^2*
      (SourceClockYukawaNormalizedCurrent.normalizedAction sharp-inverseAction*constantAction sharp vacuum) := by
  have h := full_scalar_split sharp
  rw [SourceClockYukawaNormalizedCurrent.normalizedAction,h]
  noncomm_ring

private theorem radial_normalized (sharp : Bool) (m ell : ℕ) : rawRadialCore sharp m ell=radialHessianCore sharp m ell := by
  unfold rawRadialCore radialHessianCore
  rw [mul_assoc _ (inverseAction^3) (scalarAction sharp),scalar_normalized]
  rw [SourceClockYukawaNormalizedCurrent.normalizedAction]
  simp only [mul_sub,mul_add,smul_mul_assoc,mul_smul_comm,sub_mul,add_mul]
  noncomm_ring

private theorem move_source_right (sharp : Bool) (A B : End) (hAW : Commute A W)
    (hYA : Commute (fullAction sharp) A) (hYB : Commute (fullAction sharp) B) :
    (fullAction sharp*A)*(W*B)=W*(A*B)*fullAction sharp := by
  calc
    _=fullAction sharp*(A*W)*B := by noncomm_ring
    _=fullAction sharp*(W*A)*B := by rw [hAW.eq]
    _=(fullAction sharp*W)*(A*B) := by noncomm_ring
    _=(W*fullAction sharp)*(A*B) := by rw [(W_Y sharp).symm.eq]
    _=W*(fullAction sharp*(A*B)) := by noncomm_ring
    _=_ := by rw [(hYA.mul_right hYB).eq];noncomm_ring

/-- The complete seventy-row native/density Hessian loses every differential and connection exterior leg inside the source. -/
theorem original_joined_hessian_source (sharp : Bool) (m ell : ℕ) :
    (∑ a : ScalarIndex,joinedZeroCore sharp a m ell)=joinedHessianCore sharp m ell := by
  have h := joined_sum_raw sharp m ell
  have hm := move_source_right sharp (firstPeak m ell)
    ((58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5)
    (first_commute inverse_W m ell) (first_commute (inverse_Y sharp) m ell).symm
    ((((inverse_Y sharp).pow_left 3).smul_left (58:ℂ)).add_left
      (((inverse_Y sharp).pow_left 5).smul_left (3:ℂ))).symm
  have hg : (W*fullAction sharp*secondPeak m ell)*(inverseAction^4-inverseAction^6)=
      W*(secondPeak m ell*(inverseAction^4-inverseAction^6))*fullAction sharp := by
    have hc : Commute (fullAction sharp) (secondPeak m ell*(inverseAction^4-inverseAction^6)) :=
      (second_commute (inverse_Y sharp) m ell).symm.mul_right
        (((inverse_Y sharp).pow_left 4).sub_left ((inverse_Y sharp).pow_left 6)).symm
    calc _=W*(fullAction sharp*(secondPeak m ell*(inverseAction^4-inverseAction^6))) := by noncomm_ring
         _=_ := by rw [hc.eq];noncomm_ring
  unfold joinedHessianCore
  rw [←radial_normalized]
  change (∑ a : ScalarIndex,joinedZeroCore sharp a m ell)=Complex.I •
    (W*(rawRadialCore sharp m ell-thetaAction m ell*gammaAction sharp))
  simp only [mul_smul_comm,smul_smul] at h
  rw [hm,hg] at h
  have hγ : W*gammaAction sharp*thetaAction m ell=W*thetaAction m ell*gammaAction sharp := by
    rw [mul_assoc,(theta_commute (inverse_gamma sharp) m ell).symm.eq,←mul_assoc]
  rw [hγ] at h
  simp only [rawRadialCore,smul_sub,mul_sub,mul_add,add_mul,sub_mul,mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc] at h ⊢
  linear_combination (norm := module) h

/-- The same moving core receives the closed radial/gamma word while the already-paid inverse Hessian and full X retain their exact source signs. -/
theorem original_joined_zero_order_source (sharp : Bool) (m ell : ℕ) (rS rA q : QuantumTest) :
    sourceZeroOrderWord sharp m ell rS rA q=
      ((bracket GaussMatterCore.matterAction (fullAction sharp)+SourceInverseNeutralSpinCurrent.reducedSpinCurrent sharp)*thetaAction m ell) rS+
      (1/2:ℂ) • (W*(radialHessianCore sharp m ell-thetaAction m ell*gammaAction sharp)) rS+
      ((sourceTime 0:ℂ)/8) • (inverseVolumeAction*((58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5)) rA+
      ∑ a : ScalarIndex,W (d a (coefficient sharp a m ell q)) := by
  have hZ := LinearMap.congr_fun (original_joined_hessian_source sharp m ell) rS
  have hd := LinearMap.congr_fun original_inverse_hessian_source rA
  have hi : (-Complex.I/2)*Complex.I=(1/2:ℂ) := by
    calc _= -(Complex.I*Complex.I)/2 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  have hn : (-Complex.I/2)*(Complex.I*(sourceTime 0:ℂ)/4)=(sourceTime 0:ℂ)/8 := by
    calc _= -(Complex.I*Complex.I)*(sourceTime 0:ℂ)/8 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  simp only [sourceZeroOrderWord,Finset.sum_add_distrib,←LinearMap.sum_apply,hZ,hd,joinedHessianCore,
    LinearMap.smul_apply,smul_add,smul_smul,hi,hn]
  module

end LowEnergy.SourceClockYukawaRadialJoinedHessian
