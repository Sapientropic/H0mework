import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Recovery
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Budget
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
open Complex BurnolPhysicalState OriginalKMaterialExpandedDualSourceAction OriginalRieszSource OriginalKExpandedInverseSourceAction
open scoped InnerProductSpace
local instance priceComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
 IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def sourcePlusTailFee (value : BurnolL2) (t : ℝ) (N : Nat) : ℂ :=
 inner ℂ (plusSourceRemainder N (sourceExpandedQuarterReader t value)) Response.eta

def sourceMinusTailFee (value : BurnolL2) (t : ℝ) (N : Nat) : ℂ :=
 inner ℂ (minusSourceRemainder N (sourceExpandedQuarterReader t value)) Response.eta

/-- Actual source field conservation generates the original two expanded fees from a finite native programme and its full same-source tail. -/
theorem source_original_fees_finite_and_tail (value : BurnolL2) (t : ℝ) (N : Nat) :
 inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
  (burnolMultiplicativeDilation (-t) (Response.wholeU+Response.wholeV))=
 inner ℂ (burnolAmbientMeanZeroFirstCorrection (sourceFiniteDualField t N value)) Response.eta+
 sourcePlusTailFee value t N ∧
 inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
  (burnolMultiplicativeDilation (-t) (Response.wholeU-Response.wholeV))=
 inner ℂ (burnolAmbientMeanZeroSecondCorrection (sourceFiniteDualField t N value)) Response.eta+
 sourceMinusTailFee value t N := by
 have original := source_received_profiles_pay_expanded_fees value t
 have recovered := source_own_profiles_recovered value t
 have raw := source_raw_profiles_complete (sourceExpandedQuarterReader t value) N
 have finite := source_finite_profiles_recovered value t N
 rw [recovered.1,recovered.2] at original
 rw [finite.1,finite.2]
 constructor
 · have fee : inner ℂ (sourceDualPlusRaw t value) Response.eta=
    inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
     (burnolMultiplicativeDilation (-t) (Response.wholeU+Response.wholeV)) :=
    (source_even_quarter_eta_read _).symm.trans original.1
   rw [←fee]
   change inner ℂ (sourcePlusAction.adjoint (sourceExpandedQuarterReader t value)) Response.eta=_
   rw [raw.1,inner_add_left]
   change _=inner ℂ (sourceDualEvenQuarter (plusSourceStock N (sourceExpandedQuarterReader t value))) Response.eta+_
   rw [source_even_quarter_eta_read]
   rfl
 · have fee : inner ℂ (sourceDualMinusRaw t value) Response.eta=
    inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
     (burnolMultiplicativeDilation (-t) (Response.wholeU-Response.wholeV)) :=
    (source_even_quarter_eta_read _).symm.trans original.2
   rw [←fee]
   change inner ℂ (sourceMinusAction.adjoint (sourceExpandedQuarterReader t value)) Response.eta=_
   rw [raw.2,inner_add_left]
   change _=inner ℂ (sourceDualEvenQuarter (minusSourceStock N (sourceExpandedQuarterReader t value))) Response.eta+_
   rw [source_even_quarter_eta_read]
   rfl

/-- The target reader receives only the actual quarter source budget; no source margin is transferred to a physical projection. -/
theorem source_original_tail_budget (value : BurnolL2) (t : ℝ) (N : Nat) :
 ‖sourcePlusTailFee value t N‖≤((1/2:ℝ)^N*(2*‖sourceExpandedQuarterReader t value‖))*‖Response.eta‖ ∧
 ‖sourceMinusTailFee value t N‖≤((1/2:ℝ)^N*(2*‖sourceExpandedQuarterReader t value‖))*‖Response.eta‖ :=
 actual_raw_remainder_eta_fee_bound _ N _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
