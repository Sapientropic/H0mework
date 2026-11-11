import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialExpandedDualSourceAction.Recovery
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialExpandedDualSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalKExpandedInverseSourceAction
local instance readerComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance readerPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
 IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "q" => (1/4:ℝ)

private theorem source_even_quarter (source : BurnolQuarterMeanZeroCarrier) :
 sourceDualEvenQuarter source=(1/2:ℂ) • (source+sourceMeanZeroReflection source) := by
 apply Subtype.ext
 change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolAmbientEvenPart
  (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2))))=_
 unfold burnolAmbientEvenPart
 rw [map_smul,map_add,burnolQuarterRestriction_zeroExtension,map_smul,map_add,
  burnolQuarterMeanZeroProjection_coe]
 have reflection : burnolQuarterRestriction (reflectL2
  (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2))) =
  reflectRestricted q (source : BurnolQuarterIntervalL2) := by
  change restrictToInterval q (reflectL2 (burnolRadiusZeroExtension q (source : BurnolQuarterIntervalL2)))=_
  rw [restrictToInterval_reflectL2]
  change reflectRestricted q (burnolQuarterRestriction (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2)))=_
  rw [burnolQuarterRestriction_zeroExtension]
 rw [reflection,burnolQuarterMeanZeroProjection_reflect,burnolQuarterMeanZeroProjection_coe]
 rfl

/-- Even source elimination preserves the original same-endpoint forcing read exactly. -/
theorem source_even_quarter_eta_read (source : BurnolQuarterMeanZeroCarrier) :
 inner ℂ (sourceDualEvenQuarter source) Response.eta=inner ℂ source Response.eta := by
 have reflected : inner ℂ (sourceMeanZeroReflection source) Response.eta=inner ℂ source Response.eta := by
  have actual := (reflectRestricted q).inner_map_map (source : BurnolQuarterIntervalL2)
   (Response.eta : BurnolQuarterIntervalL2)
  rw [Response.eta_reflection] at actual
  exact actual
 rw [source_even_quarter,inner_smul_left,inner_add_left,reflected]
 simp only [starRingEnd_apply,star_div₀,star_one,star_ofNat]
 ring

private theorem source_quarter_dilation_read (value : BurnolL2) (t : ℝ) (source : BurnolQuarterMeanZeroCarrier) :
 inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
  (burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2))) =
 inner ℂ (sourceExpandedQuarterReader t value) source := by
 have unitary := (burnolMultiplicativeDilation t).inner_map_map
  (burnolEvenAmbientProjection value : BurnolL2)
  (burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2)))
 rw [burnolMultiplicativeDilation_neg_eq_symm,(burnolMultiplicativeDilation t).apply_symm_apply] at unitary
 rw [burnolMultiplicativeDilation_neg_eq_symm,←unitary]
 change inner ℂ (burnolMultiplicativeDilation t (burnolEvenAmbientProjection value : BurnolL2))
  (burnolQuarterRestriction.adjoint (source : BurnolQuarterIntervalL2))=_
 rw [ContinuousLinearMap.adjoint_inner_right]
 change inner ℂ (burnolQuarterRestriction (burnolMultiplicativeDilation t
  (burnolEvenAmbientProjection value : BurnolL2))) (source : BurnolQuarterIntervalL2) =
  inner ℂ (burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto
   (burnolQuarterRestriction (burnolMultiplicativeDilation t (burnolEvenAmbientProjection value : BurnolL2)))) source
 exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right source _).symm

/-- Independent fees are generated only after both source profiles and their full-field recovery. -/
theorem source_received_profiles_pay_expanded_fees (value : BurnolL2) (t : ℝ) :
 inner ℂ (burnolAmbientMeanZeroFirstCorrection (sourceDualCompleteField t value)) Response.eta =
  inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
   (burnolMultiplicativeDilation (-t) (Response.wholeU+Response.wholeV)) ∧
 inner ℂ (burnolAmbientMeanZeroSecondCorrection (sourceDualCompleteField t value)) Response.eta =
  inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
   (burnolMultiplicativeDilation (-t) (Response.wholeU-Response.wholeV)) := by
 have recovery := source_own_profiles_recovered value t
 have plus := source_quarter_dilation_read value t (sourcePlusAction Response.eta)
 have minus := source_quarter_dilation_read value t (sourceMinusAction Response.eta)
 have plusField : burnolQuarterZeroExtension (sourcePlusAction Response.eta : BurnolQuarterIntervalL2)=Response.wholeU+Response.wholeV := by
  rw [source_coupled_fields.1]
  simp only [Submodule.coe_add,map_add,Response.wholeU,Response.wholeV]
 have minusField : burnolQuarterZeroExtension (sourceMinusAction Response.eta : BurnolQuarterIntervalL2)=Response.wholeU-Response.wholeV := by
  rw [source_coupled_fields.2]
  simp only [Submodule.coe_sub,map_sub,Response.wholeU,Response.wholeV]
 rw [plusField] at plus
 rw [minusField] at minus
 rw [←ContinuousLinearMap.adjoint_inner_left] at plus minus
 rw [recovery.1,recovery.2]
 constructor
 · change inner ℂ (sourceDualEvenQuarter (sourceDualPlusRaw t value)) Response.eta=_
   rw [source_even_quarter_eta_read]
   exact plus.symm
 · change inner ℂ (sourceDualEvenQuarter (sourceDualMinusRaw t value)) Response.eta=_
   rw [source_even_quarter_eta_read]
   exact minus.symm
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialExpandedDualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
