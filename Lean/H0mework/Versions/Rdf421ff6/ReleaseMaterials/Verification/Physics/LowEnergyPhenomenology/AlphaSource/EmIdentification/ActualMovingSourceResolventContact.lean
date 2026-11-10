import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceRestResolvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMovingSourceLight
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ActualSourcePreparationBridge ActualSourceLightCircuit
open PreparationVacuumElectromagneticIdentity PreparationVacuumActionFieldLift
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumGaugeSourceInjection
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open CanonicalGradedSpatialSource GaussHistoryHilbert SourceQuantumFockGauge
open MeasureTheory intervalIntegral Complex Filter Set
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance instDecidableEqIndex_actualMovingSourceResolventContact : DecidableEq Quantum.Index:=Classical.decEq _
local instance instDecidableEqMode_actualMovingSourceResolventContact : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance instNormedAddCommGroupLorentzianCoframe_actualMovingSourceResolventContact : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance instSeminormedAddCommGroupLorentzianCoframe_actualMovingSourceResolventContact : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance instNormedSpaceRealLorentzianCoframe_actualMovingSourceResolventContact : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance movingCompleteHS : CompleteSpace HS:=PiLp.completeSpace 2 (fun _ : HSIndex=>ℂ)
local instance movingCompleteOperator : CompleteSpace HSOperator:=ContinuousLinearMap.instCompleteSpace
local instance movingPartialSeminorm : SeminormedAddCommGroup (Field289→L[ℝ]HSOperator):=
  ContinuousLinearMap.toSeminormedAddCommGroup
local instance movingPartialComplete : CompleteSpace (Field289→L[ℝ]HSOperator):=
  ContinuousLinearMap.instCompleteSpace
local instance movingInverseReal : NormedAlgebra ℝ HSOperator:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance movingInverseRational : NormedAlgebra ℚ HSOperator:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] actualMovingSourceSylvester actualMovingSourceSylvesterContact sourceRestHSGenerator

def actualMovingSourceResolvent (block : RestBlock) (pL pR : PhysicalMomentum)
    (u : JointParameter) (spectral : ℂ) : HSOperator :=
  Ring.inverse (spectral • (1 : HSOperator)-actualMovingSourceSylvester block pL pR u)

def actualMovingSourceResolventContact (block : RestBlock) (pL pR : PhysicalMomentum)
    (force : Field289) (z : SourceCoordinateSlice) (spectral : ℂ) : HSOperator :=
  actualMovingSourceResolvent block pL pR (0,z) spectral*
    actualMovingSourceSylvesterContact block pL pR force z*
    actualMovingSourceResolvent block pL pR (0,z) spectral

/-- The actual changing Hamiltonian generates its own two-sided resolvent contact throughout the source Neumann tube. -/
theorem actual_moving_source_resolvent_contact_generated (block : RestBlock) (pL pR : PhysicalMomentum)
    (force : Field289) (z : physicalChart) (spectral : ℂ) (circle : ‖spectral‖=1/4)
    (small : ‖actualMovingSourceSylvester block pL pR (0,z.val)-sourceRestHSGenerator block‖<1/8) :
    HasDerivAt (fun r : ℝ=>actualMovingSourceResolvent block pL pR (r • force,z.val) spectral)
      (actualMovingSourceResolventContact block pL pR force z.val spectral) 0 := by
  have unit:=actual_moving_circle_isUnit block (actualMovingSourceSylvester block pL pR (0,z.val)) spectral circle (small.trans (by norm_num))
  have inverse:=(hasFDerivAt_ringInverse (𝕜:=ℝ) unit.unit)
  have sameInverse : (↑unit.unit⁻¹ : HSOperator)=
      actualMovingSourceResolvent block pL pR (0,z.val) spectral := by
    rw [←Ring.inverse_unit,unit.unit_spec]
    rfl
  have original:=inverse.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0:ℝ) (spectral • (1 : HSOperator))).sub
      (actual_moving_source_sylvester_contact_generated block pL pR force z))
    (by simp only [Pi.sub_apply,zero_smul,unit.unit_spec])
  have value : (-ContinuousLinearMap.mulLeftRight ℝ HSOperator (↑unit.unit⁻¹) (↑unit.unit⁻¹))
      (0-actualMovingSourceSylvesterContact block pL pR force z.val)=
      actualMovingSourceResolventContact block pL pR force z.val spectral := by
    rw [zero_sub,neg_apply,map_neg,neg_neg,ContinuousLinearMap.mulLeftRight_apply,sameInverse]
    unfold actualMovingSourceResolventContact
    simp only [mul_assoc]
  convert! original.congr_deriv value using 1

/-- The original source circle remains invertible for all sufficiently small true field perturbations. -/
theorem actual_moving_source_circle_field_neighborhood (block : RestBlock) (pL pR : PhysicalMomentum)
    (z : physicalChart)
    (small : ‖actualMovingSourceSylvester block pL pR (0,z.val)-sourceRestHSGenerator block‖<1/8) :
    ∃radius : ℝ,0<radius ∧ ∀h : Field289,‖h‖<radius→
      ambientState (h,z.val)∈validStates ∧
      ‖actualMovingSourceSylvester block pL pR (h,z.val)-sourceRestHSGenerator block‖<1/8 ∧
      ∀spectral : ℂ,‖spectral‖=1/4→
        IsUnit (spectral • (1 : HSOperator)-actualMovingSourceSylvester block pL pR (h,z.val)) := by
  have sourceValid : ambientState (0,z.val)∈validStates := by
    rw [ambientState_zero]
    exact sourceState_valid z
  have curve : ContinuousAt (fun h : Field289=>ambientState (h,z.val)) 0 :=
    ambientState_smooth.continuous.continuousAt.comp
      ((continuous_id (X:=Field289)).prodMk (continuous_const (y:=z.val))).continuousAt
  have validNear : ∀ᶠh : Field289 in 𝓝 0,ambientState (h,z.val)∈validStates:=
    curve.preimage_mem_nhds (validStates_open.mem_nhds sourceValid)
  have pair : ContinuousAt (fun h : Field289=>(h,z.val)) 0:=
    ((continuous_id (X:=Field289)).prodMk (continuous_const (y:=z.val))).continuousAt
  have original := (actual_moving_source_sylvester_smooth block pL pR (0,z.val) sourceValid).continuousAt
  have sylvester : ContinuousAt (fun h : Field289=>actualMovingSourceSylvester block pL pR (h,z.val)) 0 :=
    original.comp_of_eq pair rfl
  have budgetNear : ∀ᶠh : Field289 in 𝓝 0,
      ‖actualMovingSourceSylvester block pL pR (h,z.val)-sourceRestHSGenerator block‖<1/8 :=
    (sylvester.sub continuousAt_const).norm.eventually_lt continuousAt_const small
  obtain ⟨radius,positive,paid⟩:=Metric.eventually_nhds_iff.mp (validNear.and budgetNear)
  refine ⟨radius,positive,fun h bound=>?_⟩
  have both:=paid (by simpa only [dist_zero_right] using bound)
  exact ⟨both.1,both.2,fun spectral circle=>actual_moving_circle_isUnit block _ spectral circle (both.2.trans (by norm_num))⟩

def actualMovingSourceRieszLight (block : RestBlock) (pL pR : PhysicalMomentum) (u : JointParameter) : HSOperator :=
  (2*Real.pi*Complex.I : ℂ)⁻¹ •
    ∮spectral in C((0:ℂ),(1/4:ℝ)),actualMovingSourceResolvent block pL pR u spectral

def actualMovingSourceRieszContact (block : RestBlock) (pL pR : PhysicalMomentum)
    (force : Field289) (z : SourceCoordinateSlice) : HSOperator :=
  (2*Real.pi*Complex.I : ℂ)⁻¹ •
    ∮spectral in C((0:ℂ),(1/4:ℝ)),actualMovingSourceResolventContact block pL pR force z spectral

private def actualCircleSample (block : RestBlock) (pL pR : PhysicalMomentum)
    (z : SourceCoordinateSlice) (u : Field289×ℝ) : HSOperator :=
  (circleMap 0 (1/4) u.2*Complex.I) •
    actualMovingSourceResolvent block pL pR (u.1,z) (circleMap 0 (1/4) u.2)

private def actualCirclePartial (block : RestBlock) (pL pR : PhysicalMomentum)
    (z : SourceCoordinateSlice) (u : Field289×ℝ) : Field289→L[ℝ]HSOperator :=
  (fderiv ℝ (actualCircleSample block pL pR z) u).comp (ContinuousLinearMap.inl ℝ Field289 ℝ)

private theorem actual_circle_sample_smooth (block : RestBlock) (pL pR : PhysicalMomentum)
    (z : SourceCoordinateSlice) (u : Field289×ℝ) (valid : ambientState (u.1,z)∈validStates)
    (small : ‖actualMovingSourceSylvester block pL pR (u.1,z)-sourceRestHSGenerator block‖<1/8) :
    ContDiffAt ℝ ∞ (actualCircleSample block pL pR z) u := by
  have angle : ContDiffAt ℝ ∞ (fun w : Field289×ℝ=>circleMap 0 (1/4) w.2) u:=
    (contDiff_circleMap 0 (1/4) (n:=∞)).contDiffAt.comp u contDiffAt_snd
  have inlet : ContDiffAt ℝ ∞ (fun w : Field289×ℝ=>(w.1,z)) u:=
    contDiffAt_fst.prodMk contDiffAt_const
  have field:=(actual_moving_source_sylvester_smooth block pL pR (u.1,z) valid).comp u inlet
  have denominator:=angle.smul (contDiffAt_const (c:=(1 : HSOperator))) |>.sub field
  have unit:=actual_moving_circle_isUnit block _ (circleMap 0 (1/4) u.2) (by simp) (small.trans (by norm_num))
  have inverse : ContDiffAt ℝ ∞ Ring.inverse (circleMap 0 (1/4) u.2 • (1 : HSOperator)-
      actualMovingSourceSylvester block pL pR (u.1,z)) := by
    simpa only [unit.unit_spec] using contDiffAt_ringInverse ℝ unit.unit
  exact (angle.mul contDiffAt_const).smul (inverse.comp u denominator)

private theorem actual_circle_partial_smooth (block : RestBlock) (pL pR : PhysicalMomentum)
    (z : SourceCoordinateSlice) (u : Field289×ℝ) (smooth : ContDiffAt ℝ ∞ (actualCircleSample block pL pR z) u) :
    ContDiffAt ℝ ∞ (actualCirclePartial block pL pR z) u :=
  (smooth.fderiv_right (m:=∞) (by simp)).clm_comp contDiffAt_const

private theorem actual_circle_partial_derivative (block : RestBlock) (pL pR : PhysicalMomentum)
    (z : SourceCoordinateSlice) (h : Field289) (angle : ℝ)
    (smooth : ContDiffAt ℝ ∞ (actualCircleSample block pL pR z) (h,angle)) :
    HasFDerivAt (fun q : Field289=>actualCircleSample block pL pR z (q,angle))
      (actualCirclePartial block pL pR z (h,angle)) h := by
  have original : HasFDerivAt (actualCircleSample block pL pR z)
      (fderiv ℝ (actualCircleSample block pL pR z) (h,angle)) (h,angle):=
    (smooth.differentiableAt (by simp)).hasFDerivAt
  have pair : HasFDerivAt (fun q : Field289=>(q,angle))
      (ContinuousLinearMap.inl ℝ Field289 ℝ) h:=hasFDerivAt_prodMk_left h angle
  exact original.comp h pair

/-- The source-generated resolvent derivative is integrated on the original contour, with a bound generated on its compact parameter tube. -/
theorem actual_moving_source_riesz_contact_generated (block : RestBlock) (pL pR : PhysicalMomentum)
    (force : Field289) (z : physicalChart)
    (small : ‖actualMovingSourceSylvester block pL pR (0,z.val)-sourceRestHSGenerator block‖<1/8) :
    HasDerivAt (fun r : ℝ=>actualMovingSourceRieszLight block pL pR (r • force,z.val))
      (actualMovingSourceRieszContact block pL pR force z.val) 0 := by
  obtain ⟨radius,positive,paid⟩:=actual_moving_source_circle_field_neighborhood block pL pR z small
  let sample:=actualCircleSample block pL pR z.val
  let sliceDerivative:=actualCirclePartial block pL pR z.val
  have smooth (h : Field289) (angle : ℝ) (bound : ‖h‖<radius) : ContDiffAt ℝ ∞ sample (h,angle):=
    actual_circle_sample_smooth block pL pR z.val (h,angle) (paid h bound).1 (paid h bound).2.1
  have dsmooth (h : Field289) (angle : ℝ) (bound : ‖h‖<radius) : ContDiffAt ℝ ∞ sliceDerivative (h,angle):=
    actual_circle_partial_smooth block pL pR z.val (h,angle) (smooth h angle bound)
  have inside {h : Field289} (member : h∈Metric.closedBall 0 (radius/2)) : ‖h‖<radius := by
    rw [Metric.mem_closedBall,dist_zero_right] at member
    linarith
  have continuous : ContinuousOn sliceDerivative (Metric.closedBall (0 : Field289) (radius/2)×ˢIcc (0 : ℝ) (2*Real.pi)) :=
    fun u member=>(dsmooth u.1 u.2 (inside member.1)).continuousAt.continuousWithinAt
  have compact : IsCompact (Metric.closedBall (0 : Field289) (radius/2)×ˢIcc (0 : ℝ) (2*Real.pi)):=
    (isCompact_closedBall (0 : Field289) (radius/2)).prod isCompact_Icc
  obtain ⟨C,allBound⟩:=compact.exists_bound_of_continuousOn (E:=Field289→L[ℝ]HSOperator) continuous
  have slice (h : Field289) (bound : ‖h‖<radius) : Continuous (fun angle : ℝ=>sample (h,angle)) :=
    continuous_iff_continuousAt.mpr fun angle=>(smooth h angle bound).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt
  have dslice : Continuous (fun angle : ℝ=>sliceDerivative (0,angle)) :=
    continuous_iff_continuousAt.mpr fun angle=>(dsmooth 0 angle (by simpa using positive)).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt
  have neighborhood : Metric.ball (0 : Field289) (radius/2)∈𝓝 (0 : Field289):=Metric.ball_mem_nhds _ (half_pos positive)
  have derivative:=hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F:=fun h angle=>sample (h,angle)) (F':=fun h angle=>sliceDerivative (h,angle))
    (μ:=volume) (a:=0) (b:=2*Real.pi) (bound:=fun _ : ℝ=>C) neighborhood
    (by
      filter_upwards [neighborhood] with h member
      exact (slice h (inside (Metric.ball_subset_closedBall member))).aestronglyMeasurable)
    ((slice 0 (by simpa using positive)).intervalIntegrable (μ:=volume) 0 (2*Real.pi))
    dslice.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with angle member
      intro h hmember
      exact allBound (h,angle) ⟨Metric.ball_subset_closedBall hmember,(by simpa only [uIcc_of_le Real.two_pi_pos.le] using uIoc_subset_uIcc member)⟩)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun angle h hmember=>
      actual_circle_partial_derivative block pL pR z.val h angle (smooth h angle (inside (Metric.ball_subset_closedBall hmember)))))
  have generated:=derivative.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have each (angle : ℝ) : sliceDerivative (0,angle) force=
      (circleMap 0 (1/4) angle*Complex.I) •
        actualMovingSourceResolventContact block pL pR force z.val (circleMap 0 (1/4) angle) := by
    have first:=(actual_circle_partial_derivative block pL pR z.val 0 angle (smooth 0 angle (by simpa using positive))).comp_hasDerivAt_of_eq
      0 (fieldRay_derivative force 0) (by simp)
    have second:=(actual_moving_source_resolvent_contact_generated block pL pR force z
      (circleMap 0 (1/4) angle) (by simp) small).const_smul (circleMap 0 (1/4) angle*Complex.I)
    exact first.unique second
  have value : (∫angle in (0 : ℝ)..(2*Real.pi),sliceDerivative (0,angle)) force=
      ∫angle in (0 : ℝ)..(2*Real.pi),(circleMap 0 (1/4) angle*Complex.I) •
        actualMovingSourceResolventContact block pL pR force z.val (circleMap 0 (1/4) angle) := by
    rw [ContinuousLinearMap.intervalIntegral_apply
      (dslice.intervalIntegrable (E:=Field289→L[ℝ]HSOperator) (μ:=volume) 0 (2*Real.pi))]
    apply intervalIntegral.integral_congr
    intro angle _
    exact each angle
  have result:=(generated.congr_deriv value).const_smul (2*Real.pi*Complex.I : ℂ)⁻¹
  convert! result using 1
  all_goals simp only [actualMovingSourceRieszLight,actualMovingSourceRieszContact,circleIntegral,
    deriv_circleMap,Function.comp_def,sample,actualCircleSample]
  funext r
  rfl

/-- The original contour length, original matching clock and both inverse placements pay the source projector contact. -/
theorem actual_moving_source_riesz_contact_price (block : RestBlock) (pL pR : PhysicalMomentum)
    (force : Field289) (z : physicalChart)
    (small : ‖actualMovingSourceSylvester block pL pR (0,z.val)-sourceRestHSGenerator block‖<1/8) :
    ‖actualMovingSourceRieszContact block pL pR force z.val‖≤
      16*‖actualMovingSourceSylvesterContact block pL pR force z.val‖ := by
  unfold actualMovingSourceRieszContact
  have point (spectral : ℂ) (circle : spectral∈Metric.sphere (0 : ℂ) (1/4 : ℝ)) :
      ‖actualMovingSourceResolventContact block pL pR force z.val spectral‖≤
        64*‖actualMovingSourceSylvesterContact block pL pR force z.val‖ := by
    have normCircle : ‖spectral‖=1/4:=by simpa only [Metric.mem_sphere,dist_zero_right] using circle
    have bound:=actual_moving_circle_resolvent_price block
      (actualMovingSourceSylvester block pL pR (0,z.val)) spectral normCircle small
    change ‖actualMovingSourceResolvent block pL pR (0,z.val) spectral*
      actualMovingSourceSylvesterContact block pL pR force z.val*
      actualMovingSourceResolvent block pL pR (0,z.val) spectral‖≤_
    calc
      _≤(‖actualMovingSourceResolvent block pL pR (0,z.val) spectral‖*
        ‖actualMovingSourceSylvesterContact block pL pR force z.val‖)*
        ‖actualMovingSourceResolvent block pL pR (0,z.val) spectral‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤(8*‖actualMovingSourceSylvesterContact block pL pR force z.val‖)*8 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right bound (norm_nonneg _)) bound
          (norm_nonneg _) (by positivity)
      _=_ :=by ring
  have bound:=circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num : (0 : ℝ)≤1/4) point
  exact bound.trans (by ring_nf;exact le_rfl)

end LowEnergy.GaussComposite.ActualMovingSourceLight
