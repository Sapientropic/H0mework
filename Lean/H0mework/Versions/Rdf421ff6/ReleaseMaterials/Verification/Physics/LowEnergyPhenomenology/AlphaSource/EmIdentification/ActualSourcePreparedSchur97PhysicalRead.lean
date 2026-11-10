import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedInactiveSchurReturn

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97PhysicalRead
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedPhysicalRayNumerator ActualDressedOrderedStatic
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedStaticCorrectedReturn
open ActualSourcePreparedAuxiliaryClockReduction ActualSourcePreparedAuxiliaryActualReturn
open ActualPreparedMatterSupport ActualPreparedMatterClock ActualSourcePreparedMatterClockField
open ActualSourcePreparedMatterClockBalance ActualSourcePreparedMatterClockPrincipal
open ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedInactiveSchurReturn
open scoped Matrix BigOperators
attribute [local irreducible] Matrix.det Matrix.mulVec sourceMatterNativeMatrix
  sourceTemporalCorrectedField sourceMatterClockActualFieldNumerator

private theorem clock_factor_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n)=
      (sigma : ℂ)^3*sourceClockEval eps sigma (sourceFourClockDenominator event n) := by
  have clock : sourceClockEval eps sigma (X : (ℂ[X])[X])=(sigma : ℂ) := by
    simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
      Polynomial.map_X,Polynomial.coe_evalRingHom,Polynomial.eval_X]
  simp only [sourceAuxiliaryClockFactor,map_mul,map_pow,clock]

/-- The remaining regularity obligation is exactly the actual97 quantum
Schur determinant, with all source clearing and native blocks paid. -/
theorem source_schur97_original_regular_iff (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2)
    (damping : 0<sigma) :
    correctedDet event eps 0 sigma n≠0 ↔ (sourceMatterNativeSchur event n eps sigma).det≠0 := by
  let c := sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n)
  have c_nonzero : c≠0 := by
    dsimp [c]
    rw [clock_factor_eval]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr damping.ne'))
      (source_reduced_clock_denominator_nonzero event n eps sigma damping)
  have source_factor : sourceReducedClockDeterminant event n eps sigma=
      c^192*sourceMatterClockActualDeterminant event n eps sigma := by
    rw [source_auxiliary_actual_determinant_factor,source_matter_actual_det_factor,
      ←mul_assoc,←pow_add]
  have matter : sourceReducedClockDeterminant event n eps sigma≠0 ↔
      sourceMatterClockActualDeterminant event n eps sigma≠0 := by
    rw [source_factor]
    exact ⟨fun h => (mul_ne_zero_iff.mp h).2,
      fun h => mul_ne_zero (pow_ne_zero _ c_nonzero) h⟩
  have prepared : sourceReducedClockDeterminant event n eps sigma≠0 ↔
      (sourcePreparedStaticPencil event eps sigma n).det≠0 := by
    unfold sourceReducedClockDeterminant sourceReducedClockMatrix
    rw [source_clock_reduced_pencil_actual event n eps sigma damping,Matrix.det_smul]
    rw [←clock_factor_eval]
    exact ⟨fun h => (mul_ne_zero_iff.mp h).2,
      fun h => mul_ne_zero (pow_ne_zero _ c_nonzero) h⟩
  have original : correctedDet event eps 0 sigma n≠0 ↔
      (sourcePreparedStaticPencil event eps sigma n).det≠0 := by
    unfold correctedDet
    rw [←actual_physical_ray_pencil_clear event eps 0 sigma n damping,
      ←source_prepared_static_pencil_actual event eps sigma n damping,Matrix.det_smul]
    exact ⟨fun h => (mul_ne_zero_iff.mp h).2,
      fun h => mul_ne_zero (pow_ne_zero _ (physical_ray_denominator_nonzero event eps 0 sigma n damping)) h⟩
  have native_nonzero := Matrix.det_ne_zero_of_right_inverse
    (source_inactive_native_physical_inverse eps n unit positive small).2
  have schur : sourceMatterClockActualDeterminant event n eps sigma≠0 ↔
      (sourceMatterNativeSchur event n eps sigma).det≠0 := by
    rw [source_matter_native_schur_determinant event n eps sigma unit positive small]
    exact ⟨fun h => (mul_ne_zero_iff.mp h).2,fun h => mul_ne_zero native_nonzero h⟩
  exact original.trans (prepared.symm.trans (matter.trans schur))

private theorem field_restriction (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ)
    (damping : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0)
    {I : Type*} (f : I → Fin 289) :
    sourceMatterClockActualDeterminant event n eps sigma •
      (sourceTemporalCorrectedField event eps sigma n ∘ f)=
      sourceMatterClockActualFieldNumerator event n eps sigma ∘ f := by
  funext i
  exact congrFun (source_matter_actual_field_clear event n eps sigma damping regular) (f i)

/-- The same original Green field is read from the full quantum97 inverse;
its192 complementary fields retain both source cross blocks. -/
theorem source_schur97_actual_field_return (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2)
    (damping : 0<sigma) (regular : (sourceMatterNativeSchur event n eps sigma).det≠0) :
    (sourceTemporalCorrectedField event eps sigma n ∘ (Subtype.val : NativeActive → Fin 289))=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n) •
        ((sourceMatterNativeSchur event n eps sigma)⁻¹*ᵥ(sourceTemporalEMForce ∘ Subtype.val)) ∧
    (sourceTemporalCorrectedField event eps sigma n ∘ (Subtype.val : NativeInactive → Fin 289))=
      -(nativeInactiveInverse (frequencyRay eps 0 n)*ᵥ
        ((sourceMatterNativeMatrix event n eps sigma).submatrix
          (Subtype.val : NativeInactive → Fin 289) (Subtype.val : NativeActive → Fin 289)*ᵥ
            (sourceTemporalCorrectedField event eps sigma n ∘ Subtype.val))) := by
  have original := (source_schur97_original_regular_iff event n eps sigma unit positive small damping).mpr regular
  have nonzero := source_matter_actual_determinant_nonzero event n eps sigma damping original
  have cofactor := source_matter_native_schur_cofactor_field event n eps sigma unit positive small
  have active_clear := field_restriction event n eps sigma damping original (Subtype.val : NativeActive → Fin 289)
  have inactive_clear := field_restriction event n eps sigma damping original (Subtype.val : NativeInactive → Fin 289)
  have active := cofactor.2
  rw [←active_clear,Matrix.mulVec_smul,map_mul,source_matter_clock_determinant_eval] at active
  have active_equation : sourceMatterNativeSchur event n eps sigma*ᵥ
      (sourceTemporalCorrectedField event eps sigma n ∘ (Subtype.val : NativeActive → Fin 289))=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n) •
        (sourceTemporalEMForce ∘ Subtype.val) := by
    funext i
    have point := congrFun active i
    simp only [Pi.smul_apply,smul_eq_mul] at point ⊢
    apply mul_left_cancel₀ nonzero
    exact point.trans (by ring)
  have inverse := Matrix.nonsing_inv_mul (sourceMatterNativeSchur event n eps sigma)
    (isUnit_iff_ne_zero.mpr regular)
  have solved := congrArg (fun v => (sourceMatterNativeSchur event n eps sigma)⁻¹*ᵥv) active_equation
  rw [Matrix.mulVec_mulVec,inverse,Matrix.one_mulVec,Matrix.mulVec_smul] at solved
  constructor
  · exact solved
  · have inactive := cofactor.1
    rw [←inactive_clear,←active_clear,Matrix.mulVec_smul,Matrix.mulVec_smul,←smul_neg] at inactive
    funext i
    have point := congrFun inactive i
    simp only [Pi.smul_apply,smul_eq_mul] at point ⊢
    exact mul_left_cancel₀ nonzero point

private theorem force_dot_restrict (v : Fin 289 → ℂ) :
    dotProduct sourceTemporalEMForce v=
      dotProduct (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289)) (v ∘ Subtype.val) := by
  unfold dotProduct
  rw [←nativeWholeIndex.sum_comp,Fintype.sum_sum_type]
  have zero : (∑i : NativeInactive,sourceTemporalEMForce i.val*v i.val)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [actual_em_force_inactive_zero i.val i.property,zero_mul]
  change (∑i : NativeActive,sourceTemporalEMForce i.val*v i.val)+
    (∑i : NativeInactive,sourceTemporalEMForce i.val*v i.val)=_
  rw [zero,add_zero]
  rfl

/-- The original temporal EM read consumes that same97
quantum response, with exactly one original source clock multiplier. -/
theorem source_schur97_actual_em_read (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2)
    (damping : 0<sigma) (regular : (sourceMatterNativeSchur event n eps sigma).det≠0) :
    dotProduct sourceTemporalEMForce (sourceTemporalCorrectedField event eps sigma n)=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n)*
        dotProduct (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289))
          ((sourceMatterNativeSchur event n eps sigma)⁻¹*ᵥ(sourceTemporalEMForce ∘ Subtype.val)) := by
  rw [force_dot_restrict,(source_schur97_actual_field_return event n eps sigma unit positive small damping regular).1]
  unfold dotProduct
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The complete finite Noether coefficient directly consumes the actual97
response. Driver, background and lower terms are paid by their source identity. -/
theorem source_schur97_actual_coefficient (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (sigma : ℝ) (unit : spatialSquare n=1)
    (positive : 0<e.val) (small : e.val≤1/2) (damping : 0<sigma)
    (regular : (sourceMatterNativeSchur event n e.val sigma).det≠0) :
    (e.val : ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n=
      noetherPairScale^2*(e.val : ℂ)^4*
        sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n)*
        dotProduct (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289))
          ((sourceMatterNativeSchur event n e.val sigma)⁻¹*ᵥ(sourceTemporalEMForce ∘ Subtype.val)) := by
  have original := (source_schur97_original_regular_iff event n e.val sigma unit positive small damping).mpr regular
  have nonzero := source_matter_actual_determinant_nonzero event n e.val sigma damping original
  have balance := source_matter_clock_balance_principal_eval event n e.val sigma
  rw [←source_matter_actual_field_clear event n e.val sigma damping original,
    dotProduct_smul,smul_eq_mul,unit,Complex.ofReal_one,mul_one] at balance
  have quotient : (3/4 : ℂ)+
      sourceClockEval e.val sigma (sourceMatterClockBalanceNumerator event n)/
        sourceMatterClockActualDeterminant event n e.val sigma=
      2*(lapse:ℂ)*(e.val:ℂ)^4*
        dotProduct sourceTemporalEMForce (sourceTemporalCorrectedField event e.val sigma n) := by
    apply mul_left_cancel₀ nonzero
    calc
      sourceMatterClockActualDeterminant event n e.val sigma*((3/4:ℂ)+
        sourceClockEval e.val sigma (sourceMatterClockBalanceNumerator event n)/
          sourceMatterClockActualDeterminant event n e.val sigma)=
        sourceClockEval e.val sigma (sourceMatterClockBalanceNumerator event n)+
          (3/4:ℂ)*sourceMatterClockActualDeterminant event n e.val sigma := by field_simp [nonzero];ring
      _=sourceMatterClockActualDeterminant event n e.val sigma*
        (2*(lapse:ℂ)*(e.val:ℂ)^4*
          dotProduct sourceTemporalEMForce (sourceTemporalCorrectedField event e.val sigma n)) :=
        balance.trans (by ring)
  rw [source_em_matter_clock_finite_return event e sigma n unit damping original,
    source_matter_clock_determinant_eval,quotient,
    source_schur97_actual_em_read event n e.val sigma unit positive small damping regular]
  have lapse_nonzero : (lapse:ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  field_simp [lapse_nonzero]

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97PhysicalRead
