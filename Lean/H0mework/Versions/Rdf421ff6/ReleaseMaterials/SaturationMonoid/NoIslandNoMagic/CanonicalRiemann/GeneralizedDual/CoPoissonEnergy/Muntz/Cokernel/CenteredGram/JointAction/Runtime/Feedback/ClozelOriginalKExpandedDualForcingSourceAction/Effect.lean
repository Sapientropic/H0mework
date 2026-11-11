import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedDualForcingSourceAction.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialExpandedDualSourceAction.Reader
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedDualForcingSourceAction
open Complex BurnolPhysicalState OriginalKExpandedInverseSourceAction
open OriginalKMaterialExpandedDualSourceAction
open scoped InnerProductSpace
local instance effectComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- Both forcing fields are the actual input quarter reader of the same source, before even or eta elimination. -/
theorem actual_raw_profiles_generate_forcing (value : BurnolL2) (t : ℝ) :
 sourceDualPlusForcing (sourceDualPlusRaw t value)=sourceExpandedQuarterReader t value ∧
 sourceDualMinusForcing (sourceDualMinusRaw t value)=sourceExpandedQuarterReader t value :=
 source_dual_signed_forcing _

/-- Removing the own even face exposes a complete odd forcing remainder; no input role is replaced by a price. -/
def actualDualOddPlus (t : ℝ) (value : BurnolL2) :=
 sourceDualPlusRaw t value-sourceDualPlus t value

def actualDualOddMinus (t : ℝ) (value : BurnolL2) :=
 sourceDualMinusRaw t value-sourceDualMinus t value

theorem actual_even_profiles_keep_forcing_residual (value : BurnolL2) (t : ℝ) :
 sourceDualPlusForcing (sourceDualPlus t value)+sourceDualPlusForcing (actualDualOddPlus t value)=sourceExpandedQuarterReader t value ∧
 sourceDualMinusForcing (sourceDualMinus t value)+sourceDualMinusForcing (actualDualOddMinus t value)=sourceExpandedQuarterReader t value := by
 have forcing := actual_raw_profiles_generate_forcing value t
 constructor
 · unfold actualDualOddPlus
   rw [map_sub,←add_sub_assoc,add_sub_cancel_left]
   exact forcing.1
 · unfold actualDualOddMinus
   rw [map_sub,←add_sub_assoc,add_sub_cancel_left]
   exact forcing.2

/-- The independent forcing reader consumes the generated equation and keeps the full odd-source charge. -/
theorem actual_forcing_read_keeps_odd_source_fee (value : BurnolL2) (t : ℝ) (test : BurnolQuarterMeanZeroCarrier) :
 inner ℂ (sourceDualPlus t value) (sourceDualPlusForcing.adjoint test)+
 inner ℂ (actualDualOddPlus t value) (sourceDualPlusForcing.adjoint test)=
 inner ℂ (sourceExpandedQuarterReader t value) test ∧
 inner ℂ (sourceDualMinus t value) (sourceDualMinusForcing.adjoint test)+
 inner ℂ (actualDualOddMinus t value) (sourceDualMinusForcing.adjoint test)=
 inner ℂ (sourceExpandedQuarterReader t value) test := by
 have forcing := actual_even_profiles_keep_forcing_residual value t
 constructor
 · rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,←inner_add_left,forcing.1]
 · rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,←inner_add_left,forcing.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedDualForcingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
