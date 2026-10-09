import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedCore
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeCoframeCompatibility

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialNativeDivergence
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open GaussScalarTransport GaussDensityCore SourceNativeMomentumCurvature SourceNativeDensityTrace SourceNativeCoframeCompatibility
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceClockYukawaRadialMixedCore SourceClockYukawaRadialJoinedCross PositiveScalarWeakBudget PositiveScalarCoefficientDecay
open SourceCoframeVolume SourceHamiltonianVolume SourceCutoffDilationWard SourceLocalizedInverseFormPayment
open scoped ContDiff InnerProductSpace BigOperators Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
attribute [local irreducible] fullAction compressionCore defectAction

/-- The source Z is evaluated before any moving response is selected. -/
def joinedFiber (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (z : SourceCoordinateSlice) : FiberEnd :=
  (SourceNativeCutoffContact.theta m ell z:ℂ) • branchMap sharp (scalarDirection a).1+
    (SourceNativeCutoffContact.thetaDerivative (scalarDirection a) m ell z:ℂ) • branchMap sharp (scalarField z)

private theorem joined_smooth (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) : ContDiff ℝ ∞ (joinedFiber sharp a m ell) :=
  ((Complex.ofRealCLM.contDiff.comp (SourceNativeCutoffContact.theta_smooth m ell)).smul contDiff_const).add
    ((Complex.ofRealCLM.contDiff.comp (SourceNativeCutoffContact.theta_derivative_smooth (scalarDirection a) m ell)).smul
      ((branchMap sharp).contDiff.comp scalarField_smooth))

private theorem joined_core (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    PositiveScalarWeakBudget.coefficient sharp a m ell=
      localMultiplier (joinedFiber sharp a m ell) (fun _ => (joined_smooth sharp a m ell).contDiffAt) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  rw [original_coefficient_split]
  have hy (q : QuantumTest) : fullAction sharp q z=branchMap sharp (scalarField z) (q z) := by
    unfold fullAction
    cases sharp <;> rfl
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  change (SourceNativeCutoffContact.theta m ell z:ℂ) • branchMap sharp (scalarDirection a).1 (f z)+
    (SourceNativeCutoffContact.thetaDerivative (scalarDirection a) m ell z:ℂ) • fullAction sharp f z=_
  rw [hy]
  rfl

private def inverseFiber (a : ScalarIndex) (z : SourceCoordinateSlice) : FiberEnd :=
  (GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem inverse_smooth (a : ScalarIndex) : ContDiff ℝ ∞ (inverseFiber a) :=
  (Complex.ofRealCLM.contDiff.comp (GaussRadialMomentum.radialDerivative_smooth (scalarDirection a))).smul contDiff_const

def inverseCoefficientCore (a : ScalarIndex) : End := directionAction a*inverseAction^2

private theorem inverse_coefficient_core (a : ScalarIndex) : inverseCoefficientCore a=
    localMultiplier (inverseFiber a) (fun _ => (inverse_smooth a).contDiffAt) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change directionAction a ((inverseAction^2) f) z=(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ) • f z
  rw [pow_two]
  change (directionWeight a z:ℂ) • ((reciprocal z:ℂ) • ((reciprocal z:ℂ) • f z))=_
  simp only [smul_smul]
  congr 1
  unfold GaussRadialMomentum.radialDerivative directionWeight reciprocal scalarDirection
  push_cast
  field_simp [(show (radius z:ℂ)≠0 by exact_mod_cast (radius_pos z).ne')]

/-- Both the inverse-chart derivative and the full Lie connection remain in this native source jet. -/
def covariantFiber (A : SourceCoordinateSlice → FiberEnd) (v : Ambient) (z : SourceCoordinateSlice) : FiberEnd :=
  fderiv ℝ A z (direction v z)+connection v z*A z-A z*connection v z
private theorem covariant_smooth (A : SourceCoordinateSlice → FiberEnd)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (covariantFiber A v) z.val :=
  ((((hA z).fderiv_right (by simp)).clm_apply (direction_smooth v z)).add
    ((connection_smooth v z).mul (hA z))).sub ((hA z).mul (connection_smooth v z))

private theorem density_smooth (N : ℕ) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (divergenceCoefficient N v) z.val := by
  apply ContDiffAt.sum
  intro i _
  exact (inverseDensity_smooth N z).mul
    ((((complexDensity_smooth N z).mul (coefficient_smooth v i z)).fderiv_right (by simp)).clm_apply contDiffAt_const)
private theorem correction_smooth (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (nativeDensityCorrection v) z.val := by
  have he : nativeDensityCorrection v=ᶠ[nhds z.val] (fun x => (divergenceCoefficient 0 v x).re) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    have h := congrArg Complex.re (original_density_gamma_return 0 v ⟨x,hx⟩)
    simpa only [Complex.ofReal_re,nativeDensityCorrection,intrinsicDensity] using h.symm
  exact (Complex.reCLM.contDiff.contDiffAt.comp z.val (density_smooth 0 v z)).congr_of_eventuallyEq he

private def densityCore (v : Ambient) : End := multiply (nativeDensityCorrection v) (correction_smooth v)
private theorem density_return (v : Ambient) : divergenceAction v=densityCore v := by
  rw [original_native_density_multiplier]
  rfl

/-- This actual zero-order coefficient keeps the generated scalar density correction. -/
def zeroFiber (A : SourceCoordinateSlice → FiberEnd) (v : Ambient) (z : SourceCoordinateSlice) : FiberEnd :=
  Complex.I • ((scalarWeight z:ℂ) •
    (covariantFiber A v z+(nativeDensityCorrection v z:ℂ) • A z))
private theorem zero_smooth (A : SourceCoordinateSlice → FiberEnd)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (zeroFiber A v) z.val := by
  unfold zeroFiber
  exact (contDiffAt_const (c := Complex.I)).smul ((Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (scalarWeight_smooth z)).smul
    ((covariant_smooth A hA v z).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (correction_smooth v z)).smul (hA z))))

private theorem native_local (A : SourceCoordinateSlice → FiberEnd)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) (v : Ambient) :
    bracket (covariantMomentum v) (localMultiplier A hA)=(-Complex.I) •
      localMultiplier (covariantFiber A v) (covariant_smooth A hA v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have hB := ((hA ⟨z,hz⟩).differentiableAt (by simp)).hasFDerivAt
    have hr := (ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ).hasFDerivAt.comp z hB
    have hd := (hr.clm_apply (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
    change fderiv ℝ (fun x => A x (f x)) z=_ at hd
    change (-Complex.I) • (fderiv ℝ (fun x => A x (f x)) z (direction v z)+connection v z (A z (f z)))-
      A z ((-Complex.I) • (fderiv ℝ f z (direction v z)+connection v z (f z)))=
      (-Complex.I) • (covariantFiber A v z (f z))
    rw [hd]
    change (-Complex.I) • (A z (fderiv ℝ f z (direction v z))+
      (fderiv ℝ A z (direction v z)) (f z)+connection v z (A z (f z)))-
      A z ((-Complex.I) • (fderiv ℝ f z (direction v z)+connection v z (f z)))=_
    simp only [covariantFiber,add_apply,sub_apply,mul_apply_eq_comp,map_smul,map_add]
    module
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    change (covariantMomentum v (localMultiplier A hA f)-localMultiplier A hA (covariantMomentum v f)) z=
      ((-Complex.I) • localMultiplier (covariantFiber A v) (covariant_smooth A hA v) f) z
    rw [h0,h0]

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

private theorem real_local (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (A : SourceCoordinateSlice → FiberEnd)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) : Commute (multiply c hc) (localMultiplier A hA) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (A z) (c z:ℂ) (f z)).symm

private theorem row_algebra (P D W A : End) (hp : Commute P W) (hw : Commute W A) :
    A*W*P-(P-Complex.I • D)*W*A=
      -W*bracket P A+Complex.I • (D*W*A) := by
  have h1 := congrArg (fun B : End => B*P) hw.eq
  have h2 := congrArg (fun B : End => B*A) hp.eq
  simp only [bracket,sub_mul,smul_mul_assoc,mul_sub,neg_mul,mul_assoc] at *
  linear_combination (norm := module) -h1-h2

private theorem zero_return (A : SourceCoordinateSlice → FiberEnd)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) (v : Ambient) :
    (localMultiplier A hA)*multiply scalarWeight scalarWeight_smooth*covariantMomentum v-
      GaussMomentumAdjoint.adjoint v*multiply scalarWeight scalarWeight_smooth*(localMultiplier A hA)=
      localMultiplier (zeroFiber A v) (zero_smooth A hA v) := by
  rw [original_adjoint_divergence,row_algebra _ _ _ _ (native_weight v) (real_local _ _ A hA),
    native_local,density_return]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.add_apply,LinearMap.neg_apply,Module.End.mul_apply,LinearMap.smul_apply]
  change -((scalarWeight z:ℂ) • ((-Complex.I) • covariantFiber A v z (f z)))+
    Complex.I • ((nativeDensityCorrection v z:ℂ) • ((scalarWeight z:ℂ) • A z (f z)))=
      zeroFiber A v z (f z)
  simp only [zeroFiber,smul_apply,add_apply,smul_smul]
  module

/-- The full native transpose defect of Z is a concrete local coefficient on the original Fock fiber. -/
def divergenceCoefficient (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) : End :=
  PositiveScalarWeakBudget.coefficient sharp a m ell*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)-
    GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*PositiveScalarWeakBudget.coefficient sharp a m ell

def joinedZeroCore (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) : End :=
  localMultiplier (zeroFiber (joinedFiber sharp a m ell) (scalarDirection a))
    (zero_smooth _ (fun _ => (joined_smooth sharp a m ell).contDiffAt) _)

def inverseDivergenceCoefficient (a : ScalarIndex) : End :=
  inverseCoefficientCore a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)-
    GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*inverseCoefficientCore a

def inverseZeroCore (a : ScalarIndex) : End :=
  localMultiplier (zeroFiber (inverseFiber a) (scalarDirection a))
    (zero_smooth _ (fun _ => (inverse_smooth a).contDiffAt) _)

/-- Actual native coefficient differentiation retains inverse-chart, Lie-connection and density fields. -/
theorem original_joined_native_divergence (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    divergenceCoefficient sharp a m ell=joinedZeroCore sharp a m ell := by
  unfold divergenceCoefficient joinedZeroCore
  rw [joined_core]
  exact zero_return _ _ _

/-- The radial derivative uses the same independent transpose and its source density correction. -/
theorem original_inverse_native_divergence (a : ScalarIndex) :
    inverseDivergenceCoefficient a=inverseZeroCore a := by
  unfold inverseDivergenceCoefficient inverseZeroCore
  rw [inverse_coefficient_core]
  exact zero_return _ _ _

private theorem radial_native_form : GaussRadialHamiltonian.radialAction=(-Complex.I/2:ℂ) • ∑ a : ScalarIndex,
    (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*inverseCoefficientCore a+
      inverseCoefficientCore a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) := by
  have h (a : ScalarIndex) : GaussRadialMomentum.commutatorAction (scalarDirection a)=(-Complex.I) • inverseCoefficientCore a := by
    rw [inverse_coefficient_core]
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change ((-Complex.I)*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)) • f z=
      (-Complex.I) • ((GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ) • f z)
    exact mul_smul _ _ _
  simp only [GaussRadialHamiltonian.radialAction,GaussRadialHamiltonian.radialTerm,←Module.End.mul_eq_comp,h,
    mul_smul_comm,smul_mul_assoc,←smul_add,←Finset.smul_sum,smul_smul,mul_assoc]
  congr 1
  ring

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private theorem weight_derivative (a : ScalarIndex) :
    multiply scalarWeight scalarWeight_smooth*inverseCoefficientCore a=((sourceTime 0:ℂ)/4) •
      (inverseVolumeAction*inverseAction^3*SourceClosedCostNativeProbe.coordinateAction (scalarDirection a)) := by
  rw [inverse_coefficient_core]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.smul_apply,Module.End.mul_apply]
  change (scalarWeight z:ℂ) • ((GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ) • f z)=
    ((sourceTime 0:ℂ)/4) • ((inverseVolumeAction ((inverseAction^3)
      (SourceClosedCostNativeProbe.coordinateAction (scalarDirection a) f))) z)
  rw [inverseVolumeAction,multiply_apply,inverse_power_apply,SourceClosedCostNativeProbe.coordinateAction,multiply_apply]
  apply PiLp.ext
  intro word
  change (scalarWeight z:ℂ)*((GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)*f z word)=
    ((sourceTime 0:ℂ)/4)*((reciprocalVolume z:ℂ)*((reciprocal z:ℂ)^3*
      ((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z:ℂ)*f z word)))
  unfold scalarWeight GaussRadialMomentum.radialDerivative reciprocalVolume reciprocal SourceClosedCostNativeProbe.coordinate
  push_cast
  simp only [div_eq_mul_inv,inv_pow,mul_inv_rev]
  ring

private theorem joined_weight_product (sharp : Bool) (m ell : ℕ) :
    joinedCore sharp m ell=-(∑ a : ScalarIndex,multiply scalarWeight scalarWeight_smooth*inverseCoefficientCore a*
      PositiveScalarWeakBudget.coefficient sharp a m ell) := by
  simp only [joinedCore,weight_derivative,smul_mul_assoc,←Finset.smul_sum,mul_assoc,←Finset.mul_sum]
  simp only [neg_div,neg_smul]

/-- All seventy generated coefficients meet the original native transpose in one divergence. -/
def nativeDivergenceWord (sharp : Bool) (m ell : ℕ) (rS rA : QuantumTest) : QuantumTest :=
  (-Complex.I) • ∑ a : ScalarIndex,GaussMomentumAdjoint.adjoint (scalarDirection a)
    (multiply scalarWeight scalarWeight_smooth
      (PositiveScalarWeakBudget.coefficient sharp a m ell rS+inverseCoefficientCore a rA))

/-- One signed local source word joins all seventy density/covariant jets, the full matter/spin current and the actual cross product. -/
def sourceZeroOrderWord (sharp : Bool) (m ell : ℕ) (rS rA q : QuantumTest) : QuantumTest :=
  ((bracket GaussMatterCore.matterAction (fullAction sharp)+SourceInverseNeutralSpinCurrent.reducedSpinCurrent sharp)*thetaAction m ell) rS+
    (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,(joinedZeroCore sharp a m ell rS+inverseZeroCore a rA))+
    ∑ a : ScalarIndex,multiply scalarWeight scalarWeight_smooth
      (inverseCoefficientCore a (PositiveScalarWeakBudget.coefficient sharp a m ell q))

/-- Both native halves assemble before the mixed source curvature is subtracted. -/
private theorem native_mixed_form (sharp : Bool) (m ell : ℕ) (rS rA q : QuantumTest) :
    nativeCutoffCurrent sharp m ell rS+GaussRadialHamiltonian.radialAction rA-joinedCore sharp m ell q=
      nativeDivergenceWord sharp m ell rS rA+
        (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,(joinedZeroCore sharp a m ell rS+inverseZeroCore a rA))+
        ∑ a : ScalarIndex,multiply scalarWeight scalarWeight_smooth
          (inverseCoefficientCore a (PositiveScalarWeakBudget.coefficient sharp a m ell q)) := by
  have hz : (∑ a : ScalarIndex,
      ((PositiveScalarWeakBudget.coefficient sharp a m ell*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) rS-
      (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*PositiveScalarWeakBudget.coefficient sharp a m ell) rS))=
        ∑ a : ScalarIndex,joinedZeroCore sharp a m ell rS := by
    apply Finset.sum_congr rfl
    intro a _
    exact LinearMap.congr_fun (original_joined_native_divergence sharp a m ell) rS
  have hd : (∑ a : ScalarIndex,
      ((inverseCoefficientCore a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) rA-
      (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*inverseCoefficientCore a) rA))=
        ∑ a : ScalarIndex,inverseZeroCore a rA := by
    apply Finset.sum_congr rfl
    intro a _
    exact LinearMap.congr_fun (original_inverse_native_divergence a) rA
  simp only [Module.End.mul_apply,Finset.sum_sub_distrib] at hz hd
  rw [joined_weight_product]
  simp only [nativeCutoffCurrent,radial_native_form,nativeDivergenceWord,
    LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.neg_apply,
    Module.End.mul_apply,map_add,Finset.sum_add_distrib]
  linear_combination (norm := module) (-Complex.I/2:ℂ) • hz+(-Complex.I/2:ℂ) • hd

/-- The complete original forcing returns one native divergence and one whole signed local source word. -/
theorem original_native_mixed_forcing (sharp : Bool) (m ell : ℕ) (rS rA q : QuantumTest) :
    sourceCutoffCurrent sharp m ell rS+GaussRadialHamiltonian.radialAction rA-joinedCore sharp m ell q=
      nativeDivergenceWord sharp m ell rS rA+sourceZeroOrderWord sharp m ell rS rA q := by
  have h := native_mixed_form sharp m ell rS rA q
  simp only [sourceCutoffCurrent,LinearMap.add_apply,sourceZeroOrderWord]
  linear_combination (norm := module) h

/-- The actual compression keeps every original first and mixed defect in the same source forcing. -/
theorem actual_native_mixed_forcing (sharp : Bool) (m ell : ℕ) (F : Index) (rS rA q : QuantumTest) :
    correctedCutoffCore sharp m ell F rS+SourceRadiusResponseDecay.radialCurrent F rA-correctedJoinedCore sharp m ell F q=
      nativeDivergenceWord sharp m ell rS rA+sourceZeroOrderWord sharp m ell rS rA q-
        bracket (defectAction F) (literalIncrementAction sharp m ell) rS-
        bracket (defectAction F) inverseAction rA+
        bracket (bracket (defectAction F) inverseAction) (literalIncrementAction sharp m ell) q := by
  have h := original_native_mixed_forcing sharp m ell rS rA q
  simp only [correctedCutoffCore,SourceRadiusResponseDecay.radialCurrent,correctedJoinedCore,bracket,
    LinearMap.sub_apply] at *
  linear_combination (norm := module) h

end LowEnergy.SourceClockYukawaRadialNativeDivergence
