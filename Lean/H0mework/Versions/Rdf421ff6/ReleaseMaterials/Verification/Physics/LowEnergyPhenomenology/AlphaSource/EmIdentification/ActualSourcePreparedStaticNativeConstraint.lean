import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3MovingResponse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalStaticSpatialCouplingReturn.SourceStaticSpatialCoupling

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedStaticNativeConstraint
open CanonicalGradedSpatialSource PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumNativePoleTensor
open PreparationVacuumStaticPoleResponse PreparationVacuumWholeOrigin
open PreparationPhysicalStaticSpatialCouplingReturn PreparationPhysicalNativePhotonFluxReturn
open SourcePropagationNativeActionHessian
open ActualSourcePreparedN3MovingResponse ActualSourcePreparedN3EMConsumer
open ActualSourcePreparedEMEnclosure ActualDressedCorrectedGreen ActualEMAction
open ActualCompositeFieldCurrent PhysicalN3SourceEnergy
open scoped Matrix BigOperators

theorem source_static_spatial_ray (epsilon : ℝ) (n : PhysicalMomentum) :
    sourceStaticSpatialMomentum n (epsilon^2) = frequencyRay epsilon 0 n := by
  ext i
  fin_cases i
  · change (0 : ℂ) = -Complex.I * ((0*epsilon^2 : ℝ) : ℂ)
    simp only [zero_mul, Complex.ofReal_zero, mul_zero]
  · rfl
  · rfl
  · rfl

private theorem frame_active (p : complementRegular) :
    activeProjection * effectiveFrame p = effectiveFrame p := by
  have active_complement : activeProjection * fullComplementProjection = fullComplementProjection := by
    unfold activeProjection fullComplementProjection projectionMatrix
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    cases flag : activeFlag i <;> simp [fullComplementFlag, flag]
  have green : activeProjection * complementGreen p = complementGreen p := by
    calc
      _ = activeProjection * (fullComplementProjection * complementGreen p) := by
        rw [complementGreen_left_support]
      _ = _ := by rw [← mul_assoc, active_complement, complementGreen_left_support]
  unfold effectiveFrame
  simp only [mul_sub, ← mul_assoc, PreparationVacuumStaticPoleResponse.fullKernel_active, green]

/-- The original static kernel generates the five-mode chart regularity in its
own small-scale domain. No determinant or mode-balance target is an input. -/
theorem source_static_normalized_regular (e : scaleDomain) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) :
    IsUnit (normalizedEffective e ⟨0, by norm_num [slopeDomain]⟩ n (unit_direction_bound n unit)).det := by
  apply isUnit_iff_ne_zero.mpr
  intro singular
  let s : slopeDomain := ⟨0, by norm_num [slopeDomain]⟩
  let direction := unit_direction_bound n unit
  obtain ⟨v, _, nonzero, kernel⟩ := source_mode_of_characteristic e s n direction singular
  let field := effectiveFrame (rayPoint e s n direction) *ᵥ modeCoordinates e v
  have inside : activeProjection *ᵥ field = field := by
    simp only [field, Matrix.mulVec_mulVec, frame_active]
  have active_zero : activeKernel (frequencyRay e.val 0 n) *ᵥ field = 0 := by
    have lifted := congrArg (fun w => activeProjection *ᵥ
      (originalReadback (frequencyRay e.val 0 n) *ᵥ w)) kernel
    have hessian := PreparationVacuumMixedEffective.original_active_field (frequencyRay e.val 0 n)
    rw [nativeActionFourierHessian_original] at hessian
    simp only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← mul_assoc] at lifted
    rw [hessian] at lifted
    simp only [nativeMode, s, Matrix.mulVec_mulVec, ← mul_assoc] at lifted
    have cancel : (activeKernel (frequencyRay e.val 0 n)*originalInverse (frequencyRay e.val 0 n))*
        originalChange (frequencyRay e.val 0 n) = activeKernel (frequencyRay e.val 0 n) := by
      rw [mul_assoc, original_inverse_change, mul_one]
    rw [cancel] at lifted
    simpa only [field, s, Matrix.mulVec_mulVec, ← mul_assoc] using lifted
  let kappa : staticDomain := ⟨e.val^2, by exact ⟨pow_pos e.property.1 2, small⟩⟩
  have zero : field = 0 := by
    apply sourceSpatialSourceStaticKernelZero n unit kappa field inside
    simpa only [kappa, source_static_spatial_ray] using active_zero
  apply nonzero
  change originalChange (frequencyRay e.val s.val n) *ᵥ field = 0
  rw [zero, Matrix.mulVec_zero]

theorem source_native_static_original (e : scaleDomain) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) :
    sourceNativeStaticMatrix e.val n =
      sourceGreen (sourceSpatialStaticRegularPoint n unit
        ⟨e.val^2, by exact ⟨pow_pos e.property.1 2, small⟩⟩) := by
  let s : slopeDomain := ⟨0, by norm_num [slopeDomain]⟩
  have regular := source_static_normalized_regular e n unit small
  ext i j
  change nativeResponse e.val 0 n (Pi.single j 1) i = _
  rw [nativeResponse_original e s n (unit_direction_bound n unit) regular]
  have same : dynamicPoint e s n (unit_direction_bound n unit) regular =
      sourceSpatialStaticRegularPoint n unit
        ⟨e.val^2, by exact ⟨pow_pos e.property.1 2, small⟩⟩ := by
    apply Subtype.ext
    exact (source_static_spatial_ray e.val n).symm
  rw [same]
  simp only [sourceField, Matrix.mulVec_single_one, Matrix.col_apply]

/-- The native deficit is the original transported nine-row null-source
projector, retained at the actual static occurrence. -/
theorem source_prepared_native_constraint_actual (e : scaleDomain) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (small : e.val^2 ≤ staticRadius) :
    sourcePreparedNativeConstraint e.val n = sourcePhotonNullSource e.val 0 n := by
  have whole := original_green_equation (sourceSpatialStaticRegularPoint n unit
    ⟨e.val^2, by exact ⟨pow_pos e.property.1 2, small⟩⟩)
  rw [← source_native_static_original e n unit small] at whole
  have projected : originalJacobi (frequencyRay e.val 0 n) * sourceNativeStaticMatrix e.val n =
      1-sourcePhotonNullSource e.val 0 n := by
    simpa only [sourceSpatialStaticRegularPoint, source_static_spatial_ray,
      sourcePhotonNullSource] using whole
  unfold sourcePreparedNativeConstraint
  rw [em_jacobi_source, projected, sub_sub_cancel]

end LowEnergy.GaussComposite.ActualSourcePreparedStaticNativeConstraint


set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3NativeIR
open ActualDressedFullCoulomb ActualEMResponseSplit
open CanonicalGradedSpatialSource PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticPoleResponse
open PreparationPhysicalStaticSpatialCouplingReturn
open ActualSourcePreparedN3MovingResponse ActualSourcePreparedN3EMConsumer
open ActualSourcePreparedStaticNativeConstraint ActualSourcePreparedEMEnclosure
open ActualDressedCorrectedGreen ActualEMAction ActualCompositeFieldCurrent PhysicalN3SourceEnergy
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

/-- The whole native pole read retains the two independent actual charged
currents. Its EM, mixed and residual disposition is a separate physical read. -/
def sourceN3NativeStaticResidue (detector source : DressedEvent) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : ℂ :=
  dotProduct (physicalN3PoleCurrent detector dLeg dPoles)
    (staticResidue (physicalN3PoleCurrent source sLeg sPoles))

private def staticScale (e : scaleDomain) : staticDomain :=
  ⟨min (e.val^2) staticRadius, lt_min (pow_pos e.property.1 2) staticRadius_pos,
    min_le_right _ _⟩

private theorem staticScale_tendsto : Tendsto staticScale scaleApproach staticApproach := by
  apply tendsto_comap_iff.mpr
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have limit := (scaleVal_tendsto.pow 2).min
      (tendsto_const_nhds : Tendsto (fun _ : scaleDomain => staticRadius) scaleApproach (𝓝 staticRadius))
    simpa only [zero_pow (by decide : 2 ≠ 0), min_eq_left staticRadius_pos.le,
      staticScale, Function.comp_def] using limit
  · exact Eventually.of_forall (fun e => (staticScale e).property.1)

theorem source_native_static_small_eventually :
    ∀ᶠ e : scaleDomain in scaleApproach, e.val^2 ≤ staticRadius := by
  have limit : Tendsto (fun e : scaleDomain => e.val^2) scaleApproach (𝓝 (0 : ℝ)) := by
    simpa using scaleVal_tendsto.pow 2
  exact (limit.eventually (gt_mem_nhds staticRadius_pos)).mono (fun _ h => h.le)

/-- The actual N3 native read reaches the original whole-field static residue
along epsilon^2, with generated chart regularity rather than an IR target premise. -/
theorem source_prepared_n3_native_ir (detector source : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    Tendsto (fun e : scaleDomain => -(e.val : ℂ)^4 *
      sourcePreparedN3NativeRead detector source e.val n dLeg sLeg dPoles sPoles)
      scaleApproach (𝓝 (sourceN3NativeStaticResidue detector source dLeg sLeg dPoles sPoles)) := by
  let jD := physicalN3PoleCurrent detector dLeg dPoles
  let jS := physicalN3PoleCurrent source sLeg sPoles
  have field := (sourceSpatialStaticNativeFieldResidue n unit jS).comp staticScale_tendsto
  have read := ((continuous_const : Continuous (fun v : Fin 289 → ℂ => jD)).dotProduct
    continuous_id).continuousAt.tendsto.comp field
  apply Tendsto.congr' ?_ read
  filter_upwards [source_native_static_small_eventually] with e small
  have actual := source_native_static_original e n unit small
  have same : staticScale e =
      (⟨e.val^2, pow_pos e.property.1 2, small⟩ : staticDomain) := by
    apply Subtype.ext
    exact min_eq_left small
  simp only [Function.comp_def, id_eq]
  rw [same]
  change dotProduct jD ((-((e.val^2 : ℝ) : ℂ)^2) •
    sourceSpatialStaticNativeField n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩ jS) = _
  simp only [sourcePreparedN3NativeRead, emCurrentObservation, actual, dotProduct_smul,
    smul_eq_mul, sourceSpatialStaticNativeField, sourceField, jD, jS]
  congr 1
  push_cast
  ring

/-- The corrected response consumes the now generated original null-source
projector in the same small static chart. -/
theorem source_prepared_full_native_null_response (fieldEvent : DressedEvent)
    (e : scaleDomain) (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (small : e.val^2 ≤ staticRadius) (positive : 0 < sigma)
    (regular : correctedDet fieldEvent e.val 0 sigma n ≠ 0) :
    sourcePreparedFullGreenRead fieldEvent e.val sigma n-sourceNativeStaticMatrix e.val n =
      sourcePreparedFullGreenRead fieldEvent e.val sigma n *
        sourcePreparedClockQuantumMatrix fieldEvent e.val sigma n * sourceNativeStaticMatrix e.val n +
      sourcePreparedFullGreenRead fieldEvent e.val sigma n *
        PreparationPhysicalNativePhotonFluxReturn.sourcePhotonNullSource e.val 0 n := by
  have generated := source_prepared_full_native_response fieldEvent e.val sigma n positive regular
  rw [source_prepared_native_constraint_actual e n unit small] at generated
  exact generated

/-- The same native current contraction consumes the original O(kappa)
whole-field price, with its contact/complement read explicitly separated. -/
theorem source_prepared_n3_native_pole_price (detector source : DressedEvent)
    (e : scaleDomain) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (small : e.val^2 ≤ staticRadius) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, small⟩
    let jD := physicalN3PoleCurrent detector dLeg dPoles
    let jS := physicalN3PoleCurrent source sLeg sPoles
    ‖-(e.val : ℂ)^4 * (sourcePreparedN3NativeRead detector source e.val n dLeg sLeg dPoles sPoles -
      dotProduct jD (sourceSpatialStaticRegularField n unit kappa jS)) -
      dotProduct jD (sourceSpatialStaticPoleCoefficient n unit kappa jS)‖ ≤
      (∑ i, ‖jD i‖) * ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa)‖ *
        (2*staticInverseBudget^2*effectiveErrorBudget*kappa.val) *
          ‖sourceSpatialStaticSourceReader n unit kappa jS‖ := by
  let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, small⟩
  let jD := physicalN3PoleCurrent detector dLeg dPoles
  let jS := physicalN3PoleCurrent source sLeg sPoles
  change ‖-(e.val : ℂ)^4 * (sourcePreparedN3NativeRead detector source e.val n dLeg sLeg dPoles sPoles -
      dotProduct jD (sourceSpatialStaticRegularField n unit kappa jS)) -
      dotProduct jD (sourceSpatialStaticPoleCoefficient n unit kappa jS)‖ ≤ _
  have read : sourcePreparedN3NativeRead detector source e.val n dLeg sLeg dPoles sPoles =
      dotProduct jD (sourceSpatialStaticNativeField n unit kappa jS) := by
    simp only [sourcePreparedN3NativeRead, emCurrentObservation,
      source_native_static_original e n unit small, sourceSpatialStaticNativeField,
      sourceField, jD, jS, kappa]
  have scale : -(e.val : ℂ)^4 = -(kappa.val : ℂ)^2 := by
    change -(e.val : ℂ)^4 = -((e.val^2 : ℝ) : ℂ)^2
    push_cast
    ring
  have contraction (a : ℂ) (v w z : Fin 289 → ℂ) :
      a*(dotProduct jD v-dotProduct jD w)-dotProduct jD z =
        ∑ i, jD i*(a*(v i-w i)-z i) := by
    simp only [dotProduct, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [read, scale, contraction]
  exact sourceStaticSpatialContraction_price n unit kappa jS jD

end LowEnergy.GaussComposite.ActualSourcePreparedN3NativeIR
