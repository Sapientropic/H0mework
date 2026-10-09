import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNonlinearOperatorCurve
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationDampedPreparedLaplace

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNonlinearFieldCurve
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier CanonicalGradedSpatialSource
open GaussCoreHilbert GaussCoreDifferential
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization PreparationVacuumSourceFieldFamily
open PreparationVacuumCausalFieldResponse PreparationVacuumFieldPerturbation
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology Distributions InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ FiberMap := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ GaussOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

def rawReader (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint) : FiberMap :=
  (phi x.2:ℂ) • stateFiber f p (statePath g psi x)

theorem rawReader_smooth (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint)
    (valid : x∈curveDomain g psi) : ContDiffAt ℝ ∞ (rawReader f g phi psi p) x :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp x (phi.contDiff.comp contDiff_snd).contDiffAt).smul
    ((stateFiber_smooth f p (statePath g psi x) valid.1 valid.2).comp x (statePath_smooth g psi).contDiffAt)

def readerFirst (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint) : FiberMap :=
  fderiv ℝ (rawReader f g phi psi p) x parameterDirection

def readerSecond (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint) : FiberMap :=
  fderiv ℝ (readerFirst f g phi psi p) x parameterDirection

theorem readerFirst_smooth (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint)
    (valid : x∈curveDomain g psi) : ContDiffAt ℝ ∞ (readerFirst f g phi psi p) x :=
  ((rawReader_smooth f g phi psi p x valid).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem readerSecond_smooth (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint)
    (valid : x∈curveDomain g psi) : ContDiffAt ℝ ∞ (readerSecond f g phi psi p) x :=
  ((readerFirst_smooth f g phi psi p x valid).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem reader_second_bound_exists (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ x∈sourceTube g psi,‖readerSecond f g phi psi p x‖ ≤ M := by
  have continuous : ContinuousOn (readerSecond f g phi psi p) (sourceTube g psi) := fun x hx=>
    (readerSecond_smooth f g phi psi p x (sourceTube_valid g psi hx)).continuousAt.continuousWithinAt
  obtain ⟨C,bound⟩:=(sourceTube_compact g psi).exists_bound_of_continuousOn continuous
  exact ⟨max 0 C,le_max_left _ _,fun x hx=>(bound x hx).trans (le_max_right _ _)⟩

def readerSecondBound (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) : ℝ :=
  (reader_second_bound_exists f g phi psi p).choose

theorem readerSecondBound_nonneg (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) :
    0 ≤ readerSecondBound f g phi psi p := (reader_second_bound_exists f g phi psi p).choose_spec.1

theorem readerSecondBound_controls (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (z : SourceCoordinateSlice) (small : |r| ≤ fieldRadius g psi) (inside : z∈tsupport psi) :
    ‖readerSecond f g phi psi p (r,z)‖ ≤ readerSecondBound f g phi psi p :=
  (reader_second_bound_exists f g phi psi p).choose_spec.2 (r,z) ⟨abs_le.mp small,inside⟩

private theorem fixed_parameter_path (r : ℝ) (z : SourceCoordinateSlice) :
    HasDerivAt (fun t : ℝ=>(t,z)) parameterDirection r :=
  (hasDerivAt_id r).prodMk (hasDerivAt_const r z)

theorem rawReader_parameter_derivative (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (z : SourceCoordinateSlice) (valid : (r,z)∈curveDomain g psi) :
    HasDerivAt (fun t : ℝ=>rawReader f g phi psi p (t,z)) (readerFirst f g phi psi p (r,z)) r := by
  have hf : HasFDerivAt (rawReader f g phi psi p) (fderiv ℝ (rawReader f g phi psi p) (r,z)) (r,z) :=
    ((rawReader_smooth f g phi psi p (r,z) valid).differentiableAt (by simp)).hasFDerivAt
  convert! hf.comp_hasDerivAt r (fixed_parameter_path r z) using 1

theorem readerFirst_parameter_derivative (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (z : SourceCoordinateSlice) (valid : (r,z)∈curveDomain g psi) :
    HasDerivAt (fun t : ℝ=>readerFirst f g phi psi p (t,z)) (readerSecond f g phi psi p (r,z)) r := by
  have hf : HasFDerivAt (readerFirst f g phi psi p) (fderiv ℝ (readerFirst f g phi psi p) (r,z)) (r,z) :=
    ((readerFirst_smooth f g phi psi p (r,z) valid).differentiableAt (by simp)).hasFDerivAt
  convert! hf.comp_hasDerivAt r (fixed_parameter_path r z) using 1

theorem readerFirst_contact (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (z : SourceCoordinateSlice)
    (inside : z∈tsupport psi) :
    readerFirst f g phi psi p (0,z)=contactCoefficient f g p (contactLocalizer phi psi) z := by
  have valid : (0,z)∈curveDomain g psi := fieldRadius_valid g psi 0 z
    (abs_zero.trans_le (fieldRadius_pos g psi).le) inside
  let F:=fun r : ℝ=>stateFiber f p (sourceState z+r • fieldDirection g)
  have native : HasDerivAt F (contactFiber f g p z) 0 :=
    contactFiber_derivative f g p ⟨z,psi.tsupport_subset inside⟩
  have scaled:=(scaled_parameter F (contactFiber f g p z) native (psi z)).const_smul (phi z:ℂ)
  have scalar : (phi z:ℂ) • ((psi z:ℂ) • contactFiber f g p z)=contactCoefficient f g p (contactLocalizer phi psi) z := by
    change (phi z:ℂ) • ((psi z:ℂ) • contactFiber f g p z)=((phi z*psi z:ℝ):ℂ) • contactFiber f g p z
    rw [smul_smul,Complex.ofReal_mul]
  have source : HasDerivAt (fun r : ℝ=>rawReader f g phi psi p (r,z))
      (contactCoefficient f g p (contactLocalizer phi psi) z) 0 := by
    convert! scaled.congr_deriv scalar using 1
  exact (rawReader_parameter_derivative f g phi psi p 0 z valid).unique source

def readerCoefficientCurve (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (z : SourceCoordinateSlice) : FiberMap := rawReader f g phi psi p (r,z)-rawReader f g phi psi p (0,z)

theorem rawReader_zero (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    rawReader f g phi psi p (0,z)=localizedCoefficient f p phi z := by
  simp only [rawReader,statePath,zero_mul,zero_smul,add_zero]
  rfl

theorem readerCoefficientCurve_outside (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (z : SourceCoordinateSlice) (outside : z∉tsupport psi) : readerCoefficientCurve f g phi psi p r z=0 := by
  have zero:=image_eq_zero_of_notMem_tsupport outside
  simp only [readerCoefficientCurve,rawReader,statePath,zero,mul_zero,zero_smul,add_zero,sub_self]

theorem readerCoefficientCurve_support (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ) :
    tsupport (readerCoefficientCurve f g phi psi p r)⊆tsupport psi := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra outside
  exact hz (readerCoefficientCurve_outside f g phi psi p r z outside)

theorem readerCoefficientCurve_smooth (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : ContDiff ℝ ∞ (readerCoefficientCurve f g phi psi p r) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases inside : z∈tsupport psi
  · have here : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice=>(r,w)) := contDiff_const.prodMk contDiff_id
    have initial : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice=>((0:ℝ),w)) := contDiff_const.prodMk contDiff_id
    exact ((rawReader_smooth f g phi psi p (r,z) (fieldRadius_valid g psi r z small inside)).comp z here.contDiffAt).sub
      ((rawReader_smooth f g phi psi p (0,z) (fieldRadius_valid g psi 0 z (abs_zero.trans_le (fieldRadius_pos g psi).le) inside)).comp z initial.contDiffAt)
  · apply (contDiffAt_const (c:=(0:FiberMap))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport psi).isOpen_compl.mem_nhds inside] with w hw
    exact readerCoefficientCurve_outside f g phi psi p r w hw

theorem readerCoefficientCurve_remainder (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) (z : SourceCoordinateSlice) :
    ‖readerCoefficientCurve f g phi psi p r z-r • contactCoefficient f g p (contactLocalizer phi psi) z‖ ≤
      readerSecondBound f g phi psi p*‖r‖^2 := by
  by_cases inside : z∈tsupport psi
  · have h:=quadratic_of_second_derivative (fun t=>rawReader f g phi psi p (t,z)) (fun t=>readerFirst f g phi psi p (t,z))
      (fun t=>readerSecond f g phi psi p (t,z)) (fieldRadius g psi) (readerSecondBound f g phi psi p)
      (fieldRadius_pos g psi).le (readerSecondBound_nonneg f g phi psi p)
      (fun s hs=>rawReader_parameter_derivative f g phi psi p s z (fieldRadius_valid g psi s z hs inside))
      (fun s hs=>readerFirst_parameter_derivative f g phi psi p s z (fieldRadius_valid g psi s z hs inside))
      (fun s hs=>readerSecondBound_controls f g phi psi p s z hs inside) r small
    rw [readerFirst_contact f g phi psi p z inside] at h
    exact h
  · have outside : z∉tsupport (contactLocalizer phi psi) := by
      intro hz
      apply inside
      exact (tsupport_mul_subset_right : tsupport ((phi:SourceCoordinateSlice→ℝ)*(psi:SourceCoordinateSlice→ℝ))⊆tsupport psi) hz
    have scalarZero : (r:ℝ) • (0:FiberMap)=0 := by
      apply ContinuousLinearMap.ext
      intro v
      apply PiLp.ext
      intro word
      change (r:ℂ)*(0:ℂ)=0
      exact mul_zero _
    rw [readerCoefficientCurve_outside f g phi psi p r z inside,contact_zero f g p (contactLocalizer phi psi) z outside,
      scalarZero,sub_self,norm_zero]
    exact mul_nonneg (readerSecondBound_nonneg f g phi psi p) (sq_nonneg ‖r‖)

def readerCurveTest (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : 𝓓(physicalChart,FiberMap) where
  toFun:=readerCoefficientCurve f g phi psi p r
  contDiff':=readerCoefficientCurve_smooth f g phi psi p r small
  hasCompactSupport':=psi.hasCompactSupport.of_isClosed_subset isClosed_closure (readerCoefficientCurve_support f g phi psi p r)
  tsupport_subset':=(readerCoefficientCurve_support f g phi psi p r).trans psi.tsupport_subset

def readerCurveBound (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : ℝ :=
  ‖(readerCurveTest f g phi psi p r small:BoundedContinuousFunction SourceCoordinateSlice FiberMap)‖

theorem readerCurveBound_nonneg (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : 0 ≤ readerCurveBound f g phi psi p r small :=
  norm_nonneg (readerCurveTest f g phi psi p r small:BoundedContinuousFunction SourceCoordinateSlice FiberMap)

theorem readerCoefficientCurve_bound (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) (z : SourceCoordinateSlice) (v : FockFiber) :
    ‖readerCoefficientCurve f g phi psi p r z v‖ ≤ readerCurveBound f g phi psi p r small*‖v‖ :=
  ((readerCoefficientCurve f g phi psi p r z).le_opNorm v).trans (mul_le_mul_of_nonneg_right
    ((readerCurveTest f g phi psi p r small:BoundedContinuousFunction SourceCoordinateSlice FiberMap).norm_coe_le_norm z) (norm_nonneg v))

theorem readerCoefficientCurve_weights (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (z : SourceCoordinateSlice) (w : ℕ→ℂ) :
    Commute (GaussFockWeights.weight w) (readerCoefficientCurve f g phi psi p r z) :=
  ((weight_commute w _).smul_right (phi z:ℂ)).sub_right ((weight_commute w _).smul_right (phi z:ℂ))

def readerCurveCore (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (readerCoefficientCurve f g phi psi p r) (fun _=>(readerCoefficientCurve_smooth f g phi psi p r small).contDiffAt)

def readerCurveGauss (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : GaussOp :=
  GaussBoundedMultiplier.extension (readerCoefficientCurve f g phi psi p r)
    (fun _=>(readerCoefficientCurve_smooth f g phi psi p r small).contDiffAt)
    (fun z w=>readerCoefficientCurve_weights f g phi psi p r z w)
    (readerCurveBound f g phi psi p r small) (readerCurveBound_nonneg f g phi psi p r small)
    (fun z=>readerCoefficientCurve_bound f g phi psi p r small z)

theorem readerCurveGauss_core (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) (test : QuantumTest) :
    readerCurveGauss f g phi psi p r small (embed test)=embed (readerCurveCore f g phi psi p r small test) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ test

theorem readerCurveGauss_zero (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (small : |(0:ℝ)| ≤ fieldRadius g psi) : readerCurveGauss f g phi psi p 0 small=0 := by
  apply GaussYukawaGrade.core_ext
  intro test
  rw [readerCurveGauss_core,zero_apply]
  have same : readerCurveCore f g phi psi p 0 small test=0 := by
    apply DFunLike.ext
    intro z
    change (readerCoefficientCurve f g phi psi p 0 z) (test z)=0
    simp only [readerCoefficientCurve,sub_self,zero_apply]
  rw [same,map_zero]

theorem readerCurveGauss_remainder (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) :
    ‖readerCurveGauss f g phi psi p r small-r • contactGauss f g p (contactLocalizer phi psi)‖ ≤ readerSecondBound f g phi psi p*‖r‖^2 := by
  let error:=fun z=>readerCoefficientCurve f g phi psi p r z-r • contactCoefficient f g p (contactLocalizer phi psi) z
  have smooth : ContDiff ℝ ∞ error :=
    (readerCoefficientCurve_smooth f g phi psi p r small).sub ((contact_smooth f g p (contactLocalizer phi psi)).const_smul r)
  have commutes (z : physicalChart) (w : ℕ→ℂ) : Commute (GaussFockWeights.weight w) (error z) :=
    (readerCoefficientCurve_weights f g phi psi p r z w).sub_right
      (commute_real_smul _ _ (contact_weights f g p (contactLocalizer phi psi) z w) r)
  have bound (z : physicalChart) (v : FockFiber) : ‖error z v‖ ≤ (readerSecondBound f g phi psi p*‖r‖^2)*‖v‖ :=
    ((error z).le_opNorm v).trans (mul_le_mul_of_nonneg_right (readerCoefficientCurve_remainder f g phi psi p r small z) (norm_nonneg v))
  apply core_operator_bound _ _ (mul_nonneg (readerSecondBound_nonneg f g phi psi p) (sq_nonneg ‖r‖))
  intro test
  have core : localMultiplier error (fun _=>smooth.contDiffAt) test=
      readerCurveCore f g phi psi p r small test-r • contactCore f g p (contactLocalizer phi psi) test := by
    apply DFunLike.ext
    intro z
    change (error z) (test z)=readerCoefficientCurve f g phi psi p r z (test z)-
      r • contactCoefficient f g p (contactLocalizer phi psi) z (test z)
    simp only [error,sub_apply,smul_apply]
  have estimate:=GaussBoundedMultiplier.action_bound error (fun _=>smooth.contDiffAt) commutes
    (readerSecondBound f g phi psi p*‖r‖^2) (mul_nonneg (readerSecondBound_nonneg f g phi psi p) (sq_nonneg ‖r‖)) bound test
  rw [core,embed_sub_real] at estimate
  rw [sub_apply,smul_apply,readerCurveGauss_core,contactGauss_core]
  exact estimate

def readerIncrement (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ) : GaussOp :=
  if small : |r| ≤ fieldRadius g psi then readerCurveGauss f g phi psi p r small else 0

theorem readerIncrement_actual (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) : readerIncrement f g phi psi p r=readerCurveGauss f g phi psi p r small := dif_pos small

theorem readerIncrement_zero (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) : readerIncrement f g phi psi p 0=0 := by
  rw [readerIncrement_actual f g phi psi p 0 (abs_zero.trans_le (fieldRadius_pos g psi).le),readerCurveGauss_zero]

theorem readerIncrement_remainder (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) :
    ‖readerIncrement f g phi psi p r-r • contactGauss f g p (contactLocalizer phi psi)‖ ≤ readerSecondBound f g phi psi p*‖r‖^2 := by
  rw [readerIncrement_actual f g phi psi p r small]
  exact readerCurveGauss_remainder f g phi psi p r small

theorem readerIncrement_derivative (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) :
    HasDerivAt (readerIncrement f g phi psi p) (contactGauss f g p (contactLocalizer phi psi)) 0 := by
  rw [hasDerivAt_iff_tendsto,readerIncrement_zero]
  simp only [sub_zero]
  let M:=readerSecondBound f g phi psi p
  have convergence : Tendsto (fun r : ℝ=>M*‖r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using ((continuous_norm:Continuous (fun r:ℝ=>‖r‖)).tendsto 0).const_mul M
  apply squeeze_zero' (Eventually.of_forall (fun r=>mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg _))) ?_ convergence
  have small : ∀ᶠ r : ℝ in 𝓝 0,|r| ≤ fieldRadius g psi := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (fieldRadius_pos g psi)] with r hr
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr : |r|<fieldRadius g psi).le
  filter_upwards [small] with r hr
  have bound:=mul_le_mul_of_nonneg_left (readerIncrement_remainder f g phi psi p r hr) (inv_nonneg.mpr (norm_nonneg r))
  have scalar : ‖r‖⁻¹*(M*‖r‖^2)=M*‖r‖ := by
    by_cases zero : ‖r‖=0
    · simp only [zero,inv_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · field_simp
  exact bound.trans_eq scalar

def actualReaderCurve (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ) : GaussOp :=
  localizedGauss f p phi+readerIncrement f g phi psi p r

theorem actualReaderCurve_zero (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) :
    actualReaderCurve f g phi psi p 0=localizedGauss f p phi := by rw [actualReaderCurve,readerIncrement_zero,add_zero]

theorem actualReaderCurve_derivative (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) :
    HasDerivAt (actualReaderCurve f g phi psi p) (contactGauss f g p (contactLocalizer phi psi)) 0 :=
  (readerIncrement_derivative f g phi psi p).const_add (localizedGauss f p phi)

theorem actualReaderCurve_core (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) (test : QuantumTest) :
    actualReaderCurve f g phi psi p r (embed test)=embed (localizedCore f p phi test+readerCurveCore f g phi psi p r small test) := by
  rw [actualReaderCurve,readerIncrement_actual f g phi psi p r small,add_apply,localizedGauss_core,readerCurveGauss_core,map_add]

theorem actualReaderCurve_coefficient (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r| ≤ fieldRadius g psi) (test : QuantumTest) (z : SourceCoordinateSlice) :
    (localizedCore f p phi test+readerCurveCore f g phi psi p r small test) z=
      (phi z:ℂ) • stateFiber f p (sourceState z+(r*psi z) • fieldDirection g) (test z) := by
  change localizedCoefficient f p phi z (test z)+(rawReader f g phi psi p (r,z)-rawReader f g phi psi p (0,z)) (test z)=_
  rw [rawReader_zero,sub_apply]
  change _=rawReader f g phi psi p (r,z) (test z)
  abel

open GaussComposite GaussComposite.SourceGraph GaussUnitaryHistory

def preparedGaussRead (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) : GaussOp →L[ℝ] ℂ :=
  ((innerSL ℂ (inclusion (completedLeg left lc ls u))).comp
    (inclusion.toContinuousLinearMap.comp (ContinuousLinearMap.apply ℂ H (completedLeg right rc rs v)))).restrictScalars ℝ

theorem preparedGaussRead_eq (A : GaussOp) (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    preparedGaussRead left right lc ls rc rs u v A=SourceGraph.response (reader A) left right lc ls rc rs u v := by
  unfold SourceGraph.response
  rw [reader_inclusion]
  rfl

theorem prepared_matter_derivative (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    HasDerivAt (fun r : ℝ=>SourceGraph.response (reader (matterIncrement g psi p r)) left right lc ls rc rs u v)
      (SourceGraph.response (reader (forceGauss g p psi)) left right lc ls rc rs u v) 0 := by
  have h:=(preparedGaussRead left right lc ls rc rs u v).hasFDerivAt.comp_hasDerivAt 0 (matterIncrement_derivative g psi p)
  simpa only [Function.comp_def,preparedGaussRead_eq] using h

theorem contact_zero_time_reader (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p k ell : PhysicalMomentum) :
    directContact cut f g (contactLocalizer phi psi) p k ell 0=reader (contactGauss f g p (contactLocalizer phi psi)) := by
  apply SourceFamilyOperator.lift_congr sourceFilter
  intro F
  simp only [contactFamily,finiteContact,neg_zero,SourceFiniteUnitary.time_zero,one_mul,mul_one,SourceFamilyOperator.constant]

theorem prepared_reader_derivative (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p k ell : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    HasDerivAt (fun r : ℝ=>SourceGraph.response (reader (actualReaderCurve f g phi psi p r)) left right lc ls rc rs u v)
      (preparedContact cut f g (contactLocalizer phi psi) p k ell 0 left right lc ls rc rs u v) 0 := by
  have h:=(preparedGaussRead left right lc ls rc rs u v).hasFDerivAt.comp_hasDerivAt 0 (actualReaderCurve_derivative f g phi psi p)
  rw [preparedContact,contact_zero_time_reader]
  simpa only [Function.comp_def,preparedGaussRead_eq] using h

theorem generated_core_field_curve (g : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    ∃ psi : Localizer,∀ r (small : |r| ≤ fieldRadius g psi) z,
      curveCore g psi p r small test z=
        quantizer (fourierLinear p (stateHamiltonian (sourceState z+r • fieldDirection g)-stateHamiltonian (sourceState z))) (test z) := by
  obtain ⟨psi,covers,_⟩:=CanonicalGradedLocalCurrent.coreLocalizer_exists test
  refine ⟨psi,?_⟩
  intro r small z
  change coefficientCurve g psi p r z (test z)=_
  rw [coefficientCurve_original]
  by_cases inside : z∈tsupport test
  · rw [covers z inside,mul_one]
  · rw [image_eq_zero_of_notMem_tsupport inside,map_zero,map_zero]

open CanonicalPreparationCore.Completed CanonicalPreparationCreation PreparationVacuumNativeClosure
open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation

theorem original_prepared_field_curves (x : zeroLocalizedSpace actualNativeLocalizer)
    (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p k ell : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) :
    (∃ h : prepared (zeroLocalizedProfile actualNativeLocalizer x)∈GaussRadialDomain.closedY.domain,
      ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared (zeroLocalizedProfile actualNativeLocalizer x),h⟩-
        FullYSourceCutoffVolterra.cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer x))‖ ≤
          (915/916:ℝ)^(n+1)*916*GaussYukawaCoefficient.bound*‖x‖) ∧
    HasDerivAt (fun r : ℝ=>SourceGraph.response (reader (matterIncrement g psi p r)) left right lc ls rc rs
      (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x))
      (SourceGraph.response (reader (forceGauss g p psi)) left right lc ls rc rs
        (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x)) 0 ∧
    HasDerivAt (fun r : ℝ=>SourceGraph.response (reader (actualReaderCurve f g phi psi p r)) left right lc ls rc rs
      (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x))
      (preparedContact cut f g (contactLocalizer phi psi) p k ell 0 left right lc ls rc rs
        (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x)) 0 := by
  obtain ⟨h,_,bound⟩:=PreparationVacuumLocalizedYukawa.original_prepared_Y_domain x
  exact ⟨⟨h,bound⟩,prepared_matter_derivative g psi p left right lc ls rc rs _ _,
    prepared_reader_derivative cut f g phi psi p k ell left right lc ls rc rs _ _⟩

end LowEnergy.PreparationVacuumNonlinearFieldCurve
