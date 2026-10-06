import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaHamiltonianCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceYukawaCoefficientCommutator
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaTail
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussRadialHamiltonian
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceRadiusBandGradient
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceRetardedForcingTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaNormalizedCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open GaussLiveMomentum GaussRadialDomain GaussRadialMomentum GaussYukawaCoefficient
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarGaugeForce
open SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent SourceYukawaCoefficientCommutator
open GaussQuantumMultiplier GaussFockWeights
open SourceScalarPairedTransport
open SourceClockYukawaHamiltonianCurrent SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace RealInnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] fullAction diagonalAction scalarKinetic compressionCore defectAction inverseAction

def normalizedAction (sharp : Bool) : End := inverseAction*fullAction sharp

/-- This is the same bounded B/B-adjoint occurring in the original Gamma directional cost. -/
theorem original_normalized_core (sharp : Bool) (f : QuantumTest) :
    SourceClockYukawaTail.sourceB sharp (embed f)=embed (normalizedAction sharp f) := by
  unfold normalizedAction SourceMixedNativeReturn.fullAction SourceClockYukawaTail.sourceB
  cases sharp
  · have h := GaussRadialDomain.original_graph f
    change GaussYukawaOperator.bounded (embed f)=inverseRadius (embed (GaussYukawaOperator.originalAction f)) at h
    rw [inverse_core] at h
    exact h
  · change GaussYukawaOperator.bounded.adjoint (embed f)=_
    rw [FullYSourceCutoffSharp.bounded_sharp_core]
    congr 1
    have hc := LinearMap.congr_fun GaussRadialHamiltonian.adjoint_commutes.eq f
    exact hc

/-- The derivative is the actual covariant scalar jet, including the inverse chart and connection. -/
def nativeJet (sharp : Bool) (v : Ambient) : End :=
  inverseAction*constantAction sharp v.1+
    multiply (radialDerivative v) (fun _ => (radialDerivative_smooth v).contDiffAt)*fullAction sharp

private theorem inverse_native (v : Ambient) :
    bracket (covariantMomentum v) inverseAction=(-Complex.I) •
      multiply (radialDerivative v) (fun _ => (radialDerivative_smooth v).contDiffAt) := by
  apply LinearMap.ext
  intro f
  have h := core_commutator v f
  change covariantMomentum v (inverseAction f)-inverseAction (covariantMomentum v f)=_
  rw [h,add_sub_cancel_left]
  apply DFunLike.ext
  intro z
  change ((-Complex.I)*(radialDerivative v z:ℂ)) • f z=
    (-Complex.I) • ((radialDerivative v z:ℂ) • f z)
  exact mul_smul _ _ _

private theorem inverse_adjoint (v : Ambient) :
    bracket (GaussMomentumAdjoint.adjoint v) inverseAction=(-Complex.I) •
      multiply (radialDerivative v) (fun _ => (radialDerivative_smooth v).contDiffAt) := by
  apply LinearMap.ext
  intro f
  have h := GaussRadialMomentumDomain.adjoint_core_commutator v f
  change GaussMomentumAdjoint.adjoint v (inverseAction f)-inverseAction (GaussMomentumAdjoint.adjoint v f)=_
  rw [h,add_sub_cancel_left]
  apply DFunLike.ext
  intro z
  change ((-Complex.I)*(radialDerivative v z:ℂ)) • f z=
    (-Complex.I) • ((radialDerivative v z:ℂ) • f z)
  exact mul_smul _ _ _

private theorem bracket_product {R : Type*} [Ring R] (A B C : R) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by
  unfold bracket
  noncomm_ring

private theorem native_full (sharp : Bool) (v : Ambient) :
    bracket (covariantMomentum v) (fullAction sharp)=(-Complex.I) • constantAction sharp v.1 := by
  apply LinearMap.ext
  intro f
  change covariantMomentum v (fullAction sharp f)-fullAction sharp (covariantMomentum v f)=_
  rw [original_full_momentum,add_sub_cancel_left]
  rfl

theorem original_normalized_native_jet (sharp : Bool) (v : Ambient) :
    bracket (covariantMomentum v) (normalizedAction sharp)=(-Complex.I) • nativeJet sharp v := by
  rw [normalizedAction,bracket_product,inverse_native,native_full]
  simp only [nativeJet,smul_mul_assoc,mul_smul_comm,smul_add]
  module

private theorem normalized_adjoint (sharp : Bool) (v : Ambient) :
    bracket (GaussMomentumAdjoint.adjoint v) (normalizedAction sharp)=(-Complex.I) • nativeJet sharp v := by
  rw [normalizedAction,bracket_product,inverse_adjoint,native_full_adjoint_commutator]
  simp only [nativeJet,smul_mul_assoc,mul_smul_comm,smul_add]
  module

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (fullAction sharp) := by
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z:ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z:ℂ) (f z)).symm

private theorem real_normalized (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (normalizedAction sharp) :=
  (GaussRadialHamiltonian.real_commutes c hc).mul_right (real_full c hc sharp)

def normalizedScalarCurrent (sharp : Bool) : End := (-Complex.I/2:ℂ) • ∑ a : ScalarIndex,
  (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
      nativeJet sharp (scalarDirection a)+
    nativeJet sharp (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
      covariantMomentum (scalarDirection a))

private theorem sandwich_current {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (P A w X C : R)
    (hP : bracket P X=(-Complex.I) • C) (hA : bracket A X=(-Complex.I) • C)
    (hw : Commute w X) :
    bracket (A*(w*P)) X=(-Complex.I) • (A*w*C+C*w*P) := by
  have he : bracket (A*(w*P)) X=A*w*bracket P X+bracket A X*w*P := by
    unfold bracket
    linear_combination (norm := noncomm_ring) A*hw.eq*P
  rw [he,hP,hA]
  simp only [mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc]

private theorem normalized_scalar_return (sharp : Bool) :
    bracket scalarKinetic (normalizedAction sharp)=normalizedScalarCurrent sharp := by
  have h (a : ScalarIndex) := sandwich_current (covariantMomentum (scalarDirection a))
    (GaussMomentumAdjoint.adjoint (scalarDirection a)) (multiply scalarWeight scalarWeight_smooth)
    (normalizedAction sharp) (nativeJet sharp (scalarDirection a))
    (original_normalized_native_jet sharp _) (normalized_adjoint sharp _)
    (real_normalized _ _ sharp)
  unfold scalarKinetic normalizedScalarCurrent sandwich
  simp only [←Module.End.mul_eq_comp,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,
    ←Finset.sum_sub_distrib,←smul_sub]
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => h a)
  simp only [bracket] at he
  rw [he,←Finset.smul_sum,smul_smul]
  congr 1
  ring

def normalizedCurrent (sharp : Bool) : End := normalizedScalarCurrent sharp+
  inverseAction*(bracket matterAction (fullAction sharp)+reducedSpinCurrent sharp)

private theorem inverse_hamiltonian : bracket diagonalAction inverseAction=GaussRadialHamiltonian.radialAction := by
  unfold bracket
  rw [GaussRadialHamiltonian.diagonal_commutator,add_sub_cancel_left]

private theorem inverse_scalar : bracket scalarKinetic inverseAction=GaussRadialHamiltonian.radialAction := by
  unfold bracket
  rw [GaussRadialHamiltonian.scalar_commutator,add_sub_cancel_left]

/-- Every original sector is retained; the scalar current uses its decaying normalized jet. -/
theorem original_normalized_hamiltonian_current (sharp : Bool) :
    bracket diagonalAction (normalizedAction sharp)=normalizedCurrent sharp := by
  have hs := normalized_scalar_return sharp
  rw [normalizedAction,bracket_product,inverse_scalar,original_scalar_first_current] at hs
  rw [normalizedAction,bracket_product,inverse_hamiltonian,original_hamiltonian_yukawa_current]
  unfold normalizedCurrent originalCurrent
  rw [←hs]
  noncomm_ring

def normalizedCorrectedCurrent (sharp : Bool) (F : Index) : End :=
  normalizedCurrent sharp-bracket (defectAction F) (normalizedAction sharp)

theorem actual_normalized_compression_current (sharp : Bool) (F : Index) :
    bracket (compressionCore F) (normalizedAction sharp)=normalizedCorrectedCurrent sharp F := by
  rw [normalizedCorrectedCurrent,←original_normalized_hamiltonian_current]
  unfold defectAction bracket
  noncomm_ring

def radialSlope (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  ⟪(z.2.1 : Scalar),v.1⟫/(4*radius z)

private theorem slope_smooth (v : Ambient) : ContDiff ℝ ∞ (radialSlope v) :=
  (scalarCoordinate.contDiff.inner ℝ contDiff_const).div (contDiff_const.mul radius_smooth)
    (fun z => mul_ne_zero (by norm_num) (radius_pos z).ne')

private theorem slope_bound (v : Ambient) (z : SourceCoordinateSlice) :
    |radialSlope v z| ≤ ‖v.1‖/2 := by
  have hr := radius_pos z
  have hx : ‖(z.2.1 : Scalar)‖ ≤ 2*radius z := by
    have hs : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
    nlinarith only [hs,hr,norm_nonneg (z.2.1 : Scalar)]
  rw [radialSlope,abs_div,abs_of_pos (by positivity : 0<4*radius z)]
  apply (div_le_iff₀ (by positivity : 0<4*radius z)).mpr
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans_eq (by ring))

def jetScalar (v : Ambient) (z : SourceCoordinateSlice) : Scalar :=
  v.1-radialSlope v z • normalizedScalar z

def jetFiber (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  branchMap sharp (jetScalar v z)

private theorem jet_smooth (sharp : Bool) (v : Ambient) : ContDiff ℝ ∞ (jetFiber sharp v) :=
  (branchMap sharp).contDiff.comp (contDiff_const.sub ((slope_smooth v).smul normalized_scalar_smooth))

private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) :
    (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A g f

private theorem branch_weight (sharp : Bool) (phi : Scalar) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (branchMap sharp phi) := by
  cases sharp
  · change Commute (GaussFockWeights.weight w) (sourceMap phi)
    rw [source_map_return]
    exact GaussQuantumMultiplier.weight_commute w _
  · change Commute (GaussFockWeights.weight w) (sourceMap phi).adjoint
    rw [source_map_return,quantized_adjoint]
    exact GaussQuantumMultiplier.weight_commute w _

private theorem branch_bound (sharp : Bool) (phi : Scalar) :
    ‖branchMap sharp phi‖ ≤ ‖sourceMap‖*‖phi‖ := by
  cases sharp
  · exact sourceMap.le_opNorm phi
  · change ‖(sourceMap phi).adjoint‖ ≤ _
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact sourceMap.le_opNorm phi

def jetPrice (v : Ambient) : ℝ := ‖sourceMap‖*(1+(‖vacuum‖+2)/2)*‖v.1‖

private theorem jet_bound (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) :
    ‖jetFiber sharp v z‖ ≤ jetPrice v := by
  have hs : ‖jetScalar v z‖ ≤ ‖v.1‖+(‖v.1‖/2)*(‖vacuum‖+2) := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact add_le_add (le_refl _) (mul_le_mul (slope_bound v z) (normalized_scalar_bound z)
      (norm_nonneg _) (by positivity))
  exact (branch_bound sharp _).trans
    ((mul_le_mul_of_nonneg_left hs (norm_nonneg sourceMap)).trans_eq (by unfold jetPrice;ring))

def jetAction (sharp : Bool) (v : Ambient) : End :=
  localMultiplier (jetFiber sharp v) (fun _ => (jet_smooth sharp v).contDiffAt)

def boundedJet (sharp : Bool) (v : Ambient) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (jetFiber sharp v) (fun _ => (jet_smooth sharp v).contDiffAt)
    (fun z => branch_weight sharp (jetScalar v z)) (jetPrice v) (by unfold jetPrice;positivity)
    (fun z f => ((jetFiber sharp v z).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (jet_bound sharp v z) (norm_nonneg f)))

private theorem bounded_jet_core (sharp : Bool) (v : Ambient) (f : QuantumTest) :
    boundedJet sharp v (embed f)=embed (jetAction sharp v f) :=
  GaussBoundedMultiplier.extension_core (jetFiber sharp v) (fun _ => (jet_smooth sharp v).contDiffAt)
    (fun z => branch_weight sharp (jetScalar v z)) (jetPrice v) (by unfold jetPrice;positivity)
    (fun z f => ((jetFiber sharp v z).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (jet_bound sharp v z) (norm_nonneg f))) f

private theorem bounded_jet_norm (sharp : Bool) (v : Ambient) : ‖boundedJet sharp v‖ ≤ jetPrice v :=
  GaussBoundedMultiplier.extension_norm (jetFiber sharp v) (fun _ => (jet_smooth sharp v).contDiffAt)
    (fun z => branch_weight sharp (jetScalar v z)) (jetPrice v) (by unfold jetPrice;positivity)
    (fun z f => ((jetFiber sharp v z).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (jet_bound sharp v z) (norm_nonneg f)))

private theorem full_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp <;> rfl

private theorem jet_factor (sharp : Bool) (v : Ambient) : nativeJet sharp v=inverseAction*jetAction sharp v := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold nativeJet inverseAction
  simp only [LinearMap.add_apply,Module.End.mul_apply]
  change (reciprocal z:ℂ) • (branchMap sharp v.1 (f z))+
    (radialDerivative v z:ℂ) • (fullAction sharp f z)=
      (reciprocal z:ℂ) • (branchMap sharp (jetScalar v z) (f z))
  rw [full_at]
  simp only [jetScalar,normalizedScalar,map_sub,map_smul,sub_apply,smul_apply,smul_smul]
  apply PiLp.ext
  intro word
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul]
  unfold reciprocal radialDerivative radialSlope
  push_cast
  have hi : (radius z:ℂ)^2*(radius z:ℂ)⁻¹^3=(radius z:ℂ)⁻¹ := by
    field_simp [(show (radius z:ℂ)≠0 from by exact_mod_cast (radius_pos z).ne')]
  field_simp [(show (radius z:ℂ)≠0 from by exact_mod_cast (radius_pos z).ne')]
  linear_combination -(((branchMap sharp) v.1) (f z)).ofLp word * hi

private theorem theta_band (m ell : ℕ) (hml : m≤ell) (z : SourceCoordinateSlice) :
    SourceNativeCutoffContact.theta m ell z=SourceRadiusBandGradient.coefficient m ell z/radius z := by
  have he : SourceRadiusBandPolynomial.band m ell (1-reciprocal z)=
      ∑ j∈Finset.Ico (m+1) (ell+1),(1-reciprocal z)^j :=
    Finset.sum_Ico_add' (fun j => (1-reciprocal z)^j) m ell 1
  have h := geom_sum_Ico_mul_neg (1-reciprocal z) (show m+1≤ell+1 by omega)
  rw [←he] at h
  simpa only [sub_sub_cancel,SourceNativeCutoffContact.theta,SourceRadiusBandGradient.coefficient,
    reciprocal,div_eq_mul_inv] using h.symm

/-- The original A=rθ band cancels the native normalized jet's inverse radius. -/
theorem original_band_native_jet (sharp : Bool) (v : Ambient) (m ell : ℕ) (hml : m≤ell)
    (f : QuantumTest) :
    SourceRadiusPairedScalarPrice.radiusBand m ell (embed (nativeJet sharp v f))=
      boundedJet sharp v (SourceRelativePowerTail.relativeTail m ell (embed f)) := by
  rw [←SourceRadiusBandGradient.original_band_core,jet_factor]
  rw [SourceMixedNativeReturn.theta_core,bounded_jet_core]
  congr 1
  apply DFunLike.ext
  intro z
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  unfold inverseAction
  change (SourceRadiusBandGradient.coefficient m ell z:ℂ) •
    ((reciprocal z:ℂ) • (jetFiber sharp v z (f z)))=
    jetFiber sharp v z ((SourceNativeCutoffContact.theta m ell z:ℂ) • f z)
  rw [map_smul,theta_band m ell hml z,smul_smul]
  congr 1
  simp only [reciprocal,Complex.ofReal_inv,div_eq_mul_inv,Complex.ofReal_mul]

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (SourceScalarPositiveBulkWard.state F z hz g)=FullYSourceResolventGraphSplice.finiteResolvent F z (g:H) := by
  unfold SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem band_jet_norm (sharp : Bool) (v : Ambient) (m ell : ℕ) (hml : m≤ell)
    (f : QuantumTest) :
    ‖SourceRadiusPairedScalarPrice.radiusBand m ell (embed (nativeJet sharp v f))‖ ≤
      jetPrice v*‖SourceRelativePowerTail.relativeTail m ell (embed f)‖ := by
  rw [original_band_native_jet sharp v m ell hml]
  exact ((boundedJet sharp v).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (bounded_jet_norm sharp v) (norm_nonneg _))

/-- All native scalar columns and both sharp branches spend the same original
theta tail, after the actual A=rθ band cancels the coefficient's radial growth. -/
theorem actual_band_native_jet_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
          ‖SourceRadiusPairedScalarPrice.radiusBand m ell
            (embed (nativeJet sharp (scalarDirection a) (SourceScalarPositiveBulkWard.state F
              (SourceResolventBandLimit.line μ w) (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g)))‖^2)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := 1+∑ a : ScalarIndex,jetPrice (scalarDirection a)^2
  have hC : 0<C := by dsimp only [C];positivity
  obtain ⟨N,hN⟩ := SourceRetardedForcingTail.actual_theta_full_frequency_tail μ hμ g (ε/C) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF sharp
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal
        (‖SourceRelativePowerTail.relativeTail m ell
          (FullYSourceResolventGraphSplice.finiteResolvent F (SourceResolventBandLimit.line μ w) (g:H))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC.le]
      apply ENNReal.ofReal_le_ofReal
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
        (pow_le_pow_left₀ (norm_nonneg _) (band_jet_norm sharp (scalarDirection a) m ell hell
          (SourceScalarPositiveBulkWard.state F (SourceResolventBandLimit.line μ w)
            (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g)) 2))
      simp only [mul_pow,state_embed,←Finset.sum_mul] at hs
      dsimp only [C]
      nlinarith only [hs,sq_nonneg ‖SourceRelativePowerTail.relativeTail m ell
        (FullYSourceResolventGraphSplice.finiteResolvent F (SourceResolventBandLimit.line μ w) (g:H))‖]
    _ = ENNReal.ofReal C*(∫⁻ w : ℝ,ENNReal.ofReal
        (‖SourceRelativePowerTail.relativeTail m ell
          (FullYSourceResolventGraphSplice.finiteResolvent F (SourceResolventBandLimit.line μ w) (g:H))‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/C) := by gcongr
    _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_mul hC.le,mul_div_cancel₀ _ hC.ne']

end LowEnergy.SourceClockYukawaNormalizedCurrent
