import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDefectAction.Inventory
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDefectAction.Payment
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
open Complex MeasureTheory
open scoped InnerProductSpace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
local instance consumerGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_native_defect_action (ordinal : Nat) :
    actualWriteRead observation nontrivial half depth ordinal=
      actionFields (RSource.originalK observation nontrivial half+inheritedIncrement observation nontrivial half depth ordinal+
        actualDelta observation nontrivial half depth ordinal) := by
  rw [actual_defect_write_read]
  unfold actualValue actualEffect
  simp only [map_add]

-- The new actual field controls erasure without asserting any defect injectivity.
theorem actual_update_keeps_delta (ordinal : Nat) :
    actualWriteRead observation nontrivial half depth ordinal=actualValue observation nontrivial half depth ordinal ↔
      actualDelta observation nontrivial half depth ordinal=0 := by
  rw [actual_defect_write_read]
  constructor
  · intro erased
    have effectZero : actualEffect observation nontrivial half depth ordinal=0 :=
      add_left_cancel (erased.trans (add_zero _).symm)
    have actual := congrArg (fun value : Branches=>value.1.1) effectZero
    exact actual
  · intro zero
    rw [actualEffect,zero,map_zero,add_zero]

-- The complete physical defect is generated from the original rank forcing and every actual increment.
theorem actual_native_ranked_defect (ordinal : Nat) :
    (actualWriteRead observation nontrivial half depth ordinal).1.2=
      Math.rankedSourceDefect observation nontrivial half+
      Math.D (inheritedIncrement observation nontrivial half depth ordinal+actualDelta observation nontrivial half depth ordinal) := by
  rw [actual_native_defect_action]
  change Math.D (RSource.originalK observation nontrivial half+inheritedIncrement observation nontrivial half depth ordinal+
    actualDelta observation nontrivial half depth ordinal)=_
  rw [add_assoc]
  exact Math.actual_defect_update observation nontrivial half _

theorem actual_native_physical_field (ordinal : Nat) :
    (actualWriteRead observation nontrivial half depth ordinal).1.1=
      RSource.originalK observation nontrivial half+inheritedIncrement observation nontrivial half depth ordinal+
      actualDelta observation nontrivial half depth ordinal := by
  rw [actual_native_defect_action]
  rfl

theorem actual_native_Fourier_defect (ordinal : Nat) :
    (actualWriteRead observation nontrivial half depth ordinal).2.2=
      fourierL2 (Math.rankedSourceDefect observation nontrivial half+
        Math.D (inheritedIncrement observation nontrivial half depth ordinal+actualDelta observation nontrivial half depth ordinal)) := by
  rw [actual_native_defect_action]
  change fourierL2 (Math.D (RSource.originalK observation nontrivial half+inheritedIncrement observation nontrivial half depth ordinal+
    actualDelta observation nontrivial half depth ordinal))=_
  rw [add_assoc,Math.actual_defect_update]

theorem actual_defect_source_consumer (ordinal : Nat) (probe : BurnolL2) :
    inner ℂ probe (actualWriteRead observation nontrivial half depth ordinal).1.2=
      inner ℂ probe (Math.rankedSourceDefect observation nontrivial half)+
      inner ℂ probe (Math.D (inheritedIncrement observation nontrivial half depth ordinal+actualDelta observation nontrivial half depth ordinal)) := by
  rw [actual_native_ranked_defect,inner_add_right]

theorem actual_native_field_price (ordinal : Nat) :
    ‖(actualWriteRead observation nontrivial half depth ordinal).1.1‖^2=
      ‖RSource.originalK observation nontrivial half‖^2+
      2*(inner ℂ (RSource.originalK observation nontrivial half)
        (inheritedIncrement observation nontrivial half depth ordinal+actualDelta observation nontrivial half depth ordinal)).re+
      ‖inheritedIncrement observation nontrivial half depth ordinal+actualDelta observation nontrivial half depth ordinal‖^2 := by
  rw [actual_native_physical_field,add_assoc,norm_add_sq (𝕜 := ℂ)]
  rfl

 theorem actual_native_Fourier_field_price (ordinal : Nat) :
    ‖(actualWriteRead observation nontrivial half depth ordinal).2.1‖^2=
      ‖RSource.originalK observation nontrivial half‖^2+
      2*(inner ℂ (RSource.originalK observation nontrivial half)
        (inheritedIncrement observation nontrivial half depth ordinal+actualDelta observation nontrivial half depth ordinal)).re+
      ‖inheritedIncrement observation nontrivial half depth ordinal+actualDelta observation nontrivial half depth ordinal‖^2 := by
  rw [actual_native_defect_action]
  change ‖fourierL2 (RSource.originalK observation nontrivial half+inheritedIncrement observation nontrivial half depth ordinal+
    actualDelta observation nontrivial half depth ordinal)‖^2=_
  rw [fourierL2.norm_map,add_assoc,norm_add_sq (𝕜 := ℂ)]
  rfl

def actualCochainWord (ordinal : Nat) := SaturationMonoid.SourceOperationCochain.updateWord (material observation nontrivial half depth ordinal).raw

theorem actual_cochain_update (ordinal : Nat) :
    SourceOperationRelations.evaluation (mixedEnvironment (material observation nontrivial half depth ordinal).environment
      (material observation nontrivial half depth ordinal).increment) (actualCochainWord observation nontrivial half depth ordinal)=0 :=
  SaturationMonoid.SourceOperationCochain.evaluation_updateWord _ _ _

theorem consume_actual_defect_source (ordinal : Nat) :
    (type_of% (actual_native_ranked_defect observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_native_physical_field observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_native_Fourier_defect observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_defect_whole observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_defect_next observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_action_payment observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_source_word_inventory observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_math_boundary_in_born observation nontrivial half depth ordinal)) :=
  ⟨actual_native_ranked_defect observation nontrivial half depth ordinal,
    actual_native_physical_field observation nontrivial half depth ordinal,
    actual_native_Fourier_defect observation nontrivial half depth ordinal,
    actual_defect_whole observation nontrivial half depth ordinal,
    actual_defect_next observation nontrivial half depth ordinal,
    actual_action_payment observation nontrivial half depth ordinal,
    actual_source_word_inventory observation nontrivial half depth ordinal,
    actual_math_boundary_in_born observation nontrivial half depth ordinal⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
