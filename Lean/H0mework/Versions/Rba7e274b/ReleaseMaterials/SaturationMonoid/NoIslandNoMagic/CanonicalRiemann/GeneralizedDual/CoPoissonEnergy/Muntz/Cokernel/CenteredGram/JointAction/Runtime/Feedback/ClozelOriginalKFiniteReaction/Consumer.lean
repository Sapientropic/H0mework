import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteReaction.Inventory
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteReaction.Payment
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
open Complex MeasureTheory
open scoped InnerProductSpace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
local instance consumerGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_native_finite_reaction (ordinal : Nat) :
    actualWriteRead observation nontrivial half depth ordinal =
      finiteFields RSource.sourceShift (returnedField observation nontrivial half depth ordinal+
        actualDelta observation nontrivial half depth ordinal)+
      reaction_source (RSource.coordinate observation nontrivial half) RSource.sourceShift := by
  rw [actual_reaction_write_read]
  unfold actualValue actualEffect
  rw [map_add]
  abel

theorem actual_update_keeps_delta (ordinal : Nat) :
    actualWriteRead observation nontrivial half depth ordinal = actualValue observation nontrivial half depth ordinal ↔
      actualDelta observation nontrivial half depth ordinal = 0 := by
  rw [actual_reaction_write_read]
  constructor
  · intro erased
    have effectZero : actualEffect observation nontrivial half depth ordinal = 0 :=
      add_left_cancel (erased.trans (add_zero _).symm)
    have first := congrArg (fun value : Branches => value.1.1) effectZero
    change burnolMultiplicativeDilation RSource.sourceShift (actualDelta observation nontrivial half depth ordinal)=0 at first
    exact (burnolMultiplicativeDilation RSource.sourceShift).injective (first.trans (map_zero _).symm)
  · intro zero
    rw [actualEffect,zero,map_zero,add_zero]

-- This source computation keeps both material updates and the full compact reaction price.
theorem actual_native_complete_price (ordinal : Nat) :
    inner ℂ (RSource.originalK observation nontrivial half) (actualWriteRead observation nontrivial half depth ordinal).1.1+
    inner ℂ (RSource.originalK observation nontrivial half) (actualWriteRead observation nontrivial half depth ordinal).1.2-
    inner ℂ (RSource.originalK observation nontrivial half)
      (reaction_source (RSource.coordinate observation nontrivial half) RSource.sourceShift).1.1-
    inner ℂ (RSource.originalK observation nontrivial half)
      (reaction_source (RSource.coordinate observation nontrivial half) RSource.sourceShift).1.2 =
    F.originalPairedPrice (RSource.coordinate observation nontrivial half) RSource.sourceShift
      (OriginalKCombPhysicalAction.R observation nontrivial half (Prior.actualDelta observation nontrivial half depth ordinal))+
    inner ℂ (RSource.originalK observation nontrivial half) (burnolMultiplicativeDilation RSource.sourceShift
      (actualDelta observation nontrivial half depth ordinal))+
    inner ℂ (RSource.originalK observation nontrivial half) (burnolMultiplicativeDilation (-RSource.sourceShift)
      (actualDelta observation nontrivial half depth ordinal)) := by
  rw [actual_native_finite_reaction]
  simp only [Prod.fst_add,Prod.snd_add,finiteFields,ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
    map_add,inner_add_right]
  simp only [LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
  have source := actual_returned_price observation nontrivial half depth ordinal
  linear_combination source

def actualCochainWord (ordinal : Nat) := SaturationMonoid.SourceOperationCochain.updateWord (material observation nontrivial half depth ordinal).raw
theorem actual_cochain_update (ordinal : Nat) :
    SourceOperationRelations.evaluation (mixedEnvironment (material observation nontrivial half depth ordinal).environment
      (material observation nontrivial half depth ordinal).increment) (actualCochainWord observation nontrivial half depth ordinal) = 0 :=
  SaturationMonoid.SourceOperationCochain.evaluation_updateWord _ _ _

theorem consume_actual_finite_reaction (ordinal : Nat) :
    (type_of% (actual_native_finite_reaction observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_native_complete_price observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_reaction_whole observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_reaction_next observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_action_payment observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_source_word_inventory observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_math_boundary_in_born observation nontrivial half depth ordinal)) :=
  ⟨actual_native_finite_reaction observation nontrivial half depth ordinal,
    actual_native_complete_price observation nontrivial half depth ordinal,
    actual_reaction_whole observation nontrivial half depth ordinal,
    actual_reaction_next observation nontrivial half depth ordinal,
    actual_action_payment observation nontrivial half depth ordinal,
    actual_source_word_inventory observation nontrivial half depth ordinal,
    actual_math_boundary_in_born observation nontrivial half depth ordinal⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
