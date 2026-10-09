import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNonlinearSourceTube
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationCausalFieldResponse

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNonlinearFieldCurve
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier CanonicalGradedSpatialSource
open GaussCoreHilbert GaussCoreDifferential
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization PreparationVacuumSourceFieldFamily
open PreparationVacuumCausalFieldResponse
open Set Filter
open scoped ContDiff Topology Distributions InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : NormedAlgebra ℝ FiberMap := NormedAlgebra.restrictScalars ℝ ℂ _
abbrev GaussOp := H →L[ℂ] H
local instance : NormedAlgebra ℝ GaussOp := NormedAlgebra.restrictScalars ℝ ℂ _

section Quadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem quadratic_of_second_derivative (f f' f'' : ℝ→E) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (first : ∀ s,|s| ≤ R → HasDerivAt f (f' s) s)
    (second : ∀ s,|s| ≤ R → HasDerivAt f' (f'' s) s)
    (bound : ∀ s,|s| ≤ R → ‖f'' s‖ ≤ M) (r : ℝ) (small : |r| ≤ R) :
    ‖f r-f 0-r • f' 0‖ ≤ M*‖r‖^2 := by
  have difference (s : ℝ) (hs : |s| ≤ R) : ‖f' s-f' 0‖ ≤ M*|s| := by
    have zero : (0:ℝ)∈Icc (-R) R := ⟨by linarith, hR⟩
    have h:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht=>(second t (abs_le.mpr ht)).hasDerivWithinAt)
      (fun t ht=>bound t (abs_le.mpr ht)) (convex_Icc (-R) R) zero (abs_le.mp hs)
    simpa only [sub_zero,Real.norm_eq_abs] using h
  let error:=fun t : ℝ=>f t-f 0-t • f' 0
  have derivative (s : ℝ) (hs : s∈Icc (-|r|) |r|) : HasDerivWithinAt error (f' s-f' 0) (Icc (-|r|) |r|) s := by
    have h:=((first s ((abs_le.mpr hs).trans small)).sub_const (f 0)).sub ((hasDerivAt_id s).smul_const (f' 0))
    apply HasDerivAt.hasDerivWithinAt
    convert! h using 1
    simp only [one_smul]
  have derivativeBound (s : ℝ) (hs : s∈Icc (-|r|) |r|) : ‖f' s-f' 0‖ ≤ M*|r| :=
    (difference s ((abs_le.mpr hs).trans small)).trans (mul_le_mul_of_nonneg_left (abs_le.mpr hs) hM)
  have zero : (0:ℝ)∈Icc (-|r|) |r| := ⟨by linarith [abs_nonneg r],abs_nonneg r⟩
  have h:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le derivative derivativeBound
    (convex_Icc (-|r|) |r|) zero (abs_le.mp (le_refl |r|))
  have errorZero : error 0=0 := by simp only [error,sub_self,zero_smul]
  rw [errorZero,sub_zero,sub_zero] at h
  exact h.trans_eq (by rw [Real.norm_eq_abs];ring)

end Quadratic

theorem scaled_parameter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (F : ℝ→E) (v : E) (hF : HasDerivAt F v 0) (a : ℝ) :
    HasDerivAt (fun r : ℝ=>F (r*a)) ((a:ℂ) • v) 0 := by
  have h : HasDerivAt (fun r : ℝ=>F (r*a)) (a • v) 0 := by
    have generated:=hF.scomp_of_eq 0 ((hasDerivAt_id (0:ℝ)).mul_const a) (by simp only [id_eq,zero_mul])
    simpa only [Function.comp_def,id_eq,one_mul] using generated
  exact h.congr_deriv (RCLike.real_smul_eq_coe_smul (K:=ℂ) a v)

theorem curveFirst_force (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (z : SourceCoordinateSlice)
    (inside : z∈tsupport psi) : curveFirst g psi p (0,z)=forceCoefficient g p psi z := by
  have valid : (0,z)∈curveDomain g psi := fieldRadius_valid g psi 0 z
    (abs_zero.trans_le (fieldRadius_pos g psi).le) inside
  let F:=fun r : ℝ=>quantizer (fourierLinear p (stateHamiltonian (sourceState z+r • fieldDirection g)))
  have native : DifferentiableAt ℝ F 0 :=
    (actual_quantized_forcing g p ⟨z,psi.tsupport_subset inside⟩).differentiableAt
  have scaled:=scaled_parameter F (deriv F 0) native.hasDerivAt (psi z)
  have source : HasDerivAt (fun r : ℝ=>rawCurve g psi p (r,z)) (forceCoefficient g p psi z) 0 := by
    convert! scaled using 1
  exact (rawCurve_parameter_derivative g psi p 0 z valid).unique source

theorem coefficientCurve_outside (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (z : SourceCoordinateSlice) (outside : z∉tsupport psi) : coefficientCurve g psi p r z=0 := by
  have zero:=image_eq_zero_of_notMem_tsupport outside
  simp only [coefficientCurve,rawCurve,statePath,zero,mul_zero,zero_smul,add_zero,sub_self]

theorem coefficientCurve_support (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ) :
    tsupport (coefficientCurve g psi p r)⊆tsupport psi := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra outside
  exact hz (coefficientCurve_outside g psi p r z outside)

theorem coefficientCurve_smooth (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : ContDiff ℝ ∞ (coefficientCurve g psi p r) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases inside : z∈tsupport psi
  · have here : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice=>(r,w)) := contDiff_const.prodMk contDiff_id
    have initial : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice=>((0:ℝ),w)) := contDiff_const.prodMk contDiff_id
    exact ((rawCurve_smooth g psi p (r,z) (fieldRadius_valid g psi r z small inside)).comp z here.contDiffAt).sub
      ((rawCurve_smooth g psi p (0,z) (fieldRadius_valid g psi 0 z (abs_zero.trans_le (fieldRadius_pos g psi).le) inside)).comp z initial.contDiffAt)
  · apply (contDiffAt_const (c:=(0:FiberMap))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport psi).isOpen_compl.mem_nhds inside] with w hw
    exact coefficientCurve_outside g psi p r w hw

theorem coefficientCurve_remainder (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) (z : SourceCoordinateSlice) :
    ‖coefficientCurve g psi p r z-r • forceCoefficient g p psi z‖ ≤ secondBound g psi p*‖r‖^2 := by
  by_cases inside : z∈tsupport psi
  · have h:=quadratic_of_second_derivative (fun t=>rawCurve g psi p (t,z)) (fun t=>curveFirst g psi p (t,z))
      (fun t=>curveSecond g psi p (t,z)) (fieldRadius g psi) (secondBound g psi p)
      (fieldRadius_pos g psi).le (secondBound_nonneg g psi p)
      (fun s hs=>rawCurve_parameter_derivative g psi p s z (fieldRadius_valid g psi s z hs inside))
      (fun s hs=>curveFirst_parameter_derivative g psi p s z (fieldRadius_valid g psi s z hs inside))
      (fun s hs=>secondBound_controls g psi p s z hs inside) r small
    rw [curveFirst_force g psi p z inside] at h
    exact h
  · have scalarZero : (r:ℝ) • (0:FiberMap)=0 := by
      apply ContinuousLinearMap.ext
      intro v
      apply PiLp.ext
      intro word
      change (r:ℂ)*(0:ℂ)=0
      exact mul_zero _
    rw [coefficientCurve_outside g psi p r z inside,forceCoefficient_generated,
      localized_zero g p psi z inside,neg_zero,scalarZero,sub_self,norm_zero]
    exact mul_nonneg (secondBound_nonneg g psi p) (sq_nonneg ‖r‖)

def curveTest (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : 𝓓(physicalChart,FiberMap) where
  toFun:=coefficientCurve g psi p r
  contDiff':=coefficientCurve_smooth g psi p r small
  hasCompactSupport':=psi.hasCompactSupport.of_isClosed_subset isClosed_closure (coefficientCurve_support g psi p r)
  tsupport_subset':=(coefficientCurve_support g psi p r).trans psi.tsupport_subset

def curveBound (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : ℝ :=
  ‖(curveTest g psi p r small:BoundedContinuousFunction SourceCoordinateSlice FiberMap)‖

theorem curveBound_nonneg (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : 0 ≤ curveBound g psi p r small :=
  norm_nonneg (curveTest g psi p r small:BoundedContinuousFunction SourceCoordinateSlice FiberMap)

theorem coefficientCurve_bound (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) (z : SourceCoordinateSlice) (v : FockFiber) :
    ‖coefficientCurve g psi p r z v‖ ≤ curveBound g psi p r small*‖v‖ :=
  ((coefficientCurve g psi p r z).le_opNorm v).trans (mul_le_mul_of_nonneg_right
    ((curveTest g psi p r small:BoundedContinuousFunction SourceCoordinateSlice FiberMap).norm_coe_le_norm z) (norm_nonneg v))

theorem coefficientCurve_weights (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (z : SourceCoordinateSlice) (w : ℕ→ℂ) :
    Commute (GaussFockWeights.weight w) (coefficientCurve g psi p r z) := by
  rw [coefficientCurve_original]
  exact weight_commute w _

def curveCore (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (coefficientCurve g psi p r) (fun _=>(coefficientCurve_smooth g psi p r small).contDiffAt)

def curveGauss (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : GaussOp :=
  GaussBoundedMultiplier.extension (coefficientCurve g psi p r) (fun _=>(coefficientCurve_smooth g psi p r small).contDiffAt)
    (fun z w=>coefficientCurve_weights g psi p r z w) (curveBound g psi p r small) (curveBound_nonneg g psi p r small)
    (fun z=>coefficientCurve_bound g psi p r small z)

theorem curveGauss_core (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) (test : QuantumTest) :
    curveGauss g psi p r small (embed test)=embed (curveCore g psi p r small test) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ test

theorem curveGauss_zero (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (small : |(0:ℝ)| ≤ fieldRadius g psi) : curveGauss g psi p 0 small=0 := by
  apply GaussYukawaGrade.core_ext
  intro test
  rw [curveGauss_core,zero_apply]
  have same : curveCore g psi p 0 small test=0 := by
    apply DFunLike.ext
    intro z
    change (coefficientCurve g psi p 0 z) (test z)=0
    simp only [coefficientCurve,sub_self,zero_apply]
  rw [same,map_zero]

theorem core_operator_bound (A : GaussOp) (C : ℝ) (nonnegative : 0 ≤ C)
    (bound : ∀ test : QuantumTest,‖A (embed test)‖ ≤ C*‖embed test‖) : ‖A‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound A nonnegative
  intro x
  refine GaussBoundedMultiplier.core_dense.induction_on x
    (isClosed_le A.continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro v
  obtain ⟨test,rfl⟩:=coreEquiv.surjective v
  exact bound test

theorem embed_sub_real (a b : QuantumTest) (r : ℝ) : embed (a-r • b)=embed a-r • embed b := by
  exact (embed.restrictScalars ℝ).map_sub a (r • b) |>.trans
    (congrArg (fun w=>embed a-w) ((embed.restrictScalars ℝ).map_smul r b))

theorem commute_real_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : E →L[ℂ] E) (commutes : Commute A B) (r : ℝ) : Commute A (r • B) := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) r B]
  exact commutes.smul_right (r:ℂ)

theorem curveGauss_remainder (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) :
    ‖curveGauss g psi p r small-r • forceGauss g p psi‖ ≤ secondBound g psi p*‖r‖^2 := by
  let error:=fun z=>coefficientCurve g psi p r z-r • forceCoefficient g p psi z
  have smooth : ContDiff ℝ ∞ error :=
    (coefficientCurve_smooth g psi p r small).sub ((force_smooth g p psi).const_smul r)
  have commutes (z : physicalChart) (w : ℕ→ℂ) : Commute (GaussFockWeights.weight w) (error z) :=
    (coefficientCurve_weights g psi p r z w).sub_right
      (commute_real_smul _ _ (force_weights g p psi z w) r)
  have bound (z : physicalChart) (v : FockFiber) : ‖error z v‖ ≤ (secondBound g psi p*‖r‖^2)*‖v‖ :=
    ((error z).le_opNorm v).trans (mul_le_mul_of_nonneg_right (coefficientCurve_remainder g psi p r small z) (norm_nonneg v))
  apply core_operator_bound _ _ (mul_nonneg (secondBound_nonneg g psi p) (sq_nonneg ‖r‖))
  intro test
  have core : localMultiplier error (fun _=>smooth.contDiffAt) test=curveCore g psi p r small test-r • forceCore g p psi test := by
    apply DFunLike.ext
    intro z
    change (error z) (test z)=coefficientCurve g psi p r z (test z)-r • forceCoefficient g p psi z (test z)
    simp only [error,sub_apply,smul_apply]
  have estimate:=GaussBoundedMultiplier.action_bound error (fun _=>smooth.contDiffAt) commutes
    (secondBound g psi p*‖r‖^2) (mul_nonneg (secondBound_nonneg g psi p) (sq_nonneg ‖r‖)) bound test
  rw [core,embed_sub_real] at estimate
  rw [sub_apply,smul_apply,curveGauss_core,forceGauss_core]
  exact estimate

/-- This local curve is the actual matter Hamiltonian increment; no identity
with the complete diagonal/momentum background is imposed by its definition. -/
def matterIncrement (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ) : GaussOp :=
  if small : |r| ≤ fieldRadius g psi then curveGauss g psi p r small else 0

theorem matterIncrement_actual (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : matterIncrement g psi p r=curveGauss g psi p r small :=
  dif_pos small

theorem matterIncrement_zero (g : Field289) (psi : Localizer) (p : PhysicalMomentum) : matterIncrement g psi p 0=0 := by
  rw [matterIncrement_actual g psi p 0 (abs_zero.trans_le (fieldRadius_pos g psi).le),curveGauss_zero]

theorem matterIncrement_remainder (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) :
    ‖matterIncrement g psi p r-r • forceGauss g p psi‖ ≤ secondBound g psi p*‖r‖^2 := by
  rw [matterIncrement_actual g psi p r small]
  exact curveGauss_remainder g psi p r small

theorem matterIncrement_derivative (g : Field289) (psi : Localizer) (p : PhysicalMomentum) :
    HasDerivAt (matterIncrement g psi p) (forceGauss g p psi) 0 := by
  rw [hasDerivAt_iff_tendsto,matterIncrement_zero]
  simp only [sub_zero]
  let M:=secondBound g psi p
  have convergence : Tendsto (fun r : ℝ=>M*‖r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using ((continuous_norm:Continuous (fun r:ℝ=>‖r‖)).tendsto 0).const_mul M
  apply squeeze_zero' (Eventually.of_forall (fun r=>mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg _))) ?_ convergence
  have small : ∀ᶠ r : ℝ in 𝓝 0,|r| ≤ fieldRadius g psi := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (fieldRadius_pos g psi)] with r hr
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr : |r|<fieldRadius g psi).le
  filter_upwards [small] with r hr
  have bound:=mul_le_mul_of_nonneg_left (matterIncrement_remainder g psi p r hr) (inv_nonneg.mpr (norm_nonneg r))
  have scalar : ‖r‖⁻¹*(M*‖r‖^2)=M*‖r‖ := by
    by_cases zero : ‖r‖=0
    · simp only [zero,inv_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · field_simp
  exact bound.trans_eq scalar

end LowEnergy.PreparationVacuumNonlinearFieldCurve
