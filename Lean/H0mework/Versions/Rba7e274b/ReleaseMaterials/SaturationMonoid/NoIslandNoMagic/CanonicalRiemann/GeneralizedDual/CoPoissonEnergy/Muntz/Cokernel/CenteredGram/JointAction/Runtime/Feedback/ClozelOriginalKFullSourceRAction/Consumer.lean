import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRAction.Physical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRAction.Inventory
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRAction.Payment
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
open Complex MeasureTheory
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_R_keeps_own_effect (ordinal : Nat) :
    actualWriteRead observation nontrivial half depth ordinal=actualValue observation nontrivial half depth ordinal ↔
      Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)=0 := by
  rw [actual_R_write_read]
  constructor
  · intro erased
    have effectZero : actualEffect observation nontrivial half depth ordinal=0 :=
      add_left_cancel (erased.trans (add_zero _).symm)
    exact congrArg (fun value : Prior.Branches=>value.1.1) effectZero
  · intro zero
    have effectZero : actualEffect observation nontrivial half depth ordinal=0 := by
      change ((Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal),
        Flux.D (Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal))),
        (fourierL2 (Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)),
         fourierL2 (Flux.D (Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)))))=0
      simp only [zero,map_zero]
      rfl
    rw [effectZero,add_zero]

theorem actual_R_complete_four_terms (ordinal : Nat) (shift : ℝ) :
    burnolMultiplicativeDilation shift (actualWriteRead observation nontrivial half depth ordinal).1.1=
      OldR.fourTerms observation nontrivial half shift
        (originalField (Prior.actualWriteRead observation nontrivial half depth ordinal))+
      OldR.fourTerms observation nontrivial half shift (actualDelta observation nontrivial half depth ordinal) := by
  rw [OldR.four_terms_eq_action,OldR.four_terms_eq_action,actual_R_write_read]
  change burnolMultiplicativeDilation shift (Op.R observation nontrivial half
    (originalField (Prior.actualWriteRead observation nontrivial half depth ordinal))+
    Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal))=_
  exact map_add _ _ _

theorem actual_R_source_cotest (ordinal : Nat) (probe : BurnolL2) :
    Flux.sourceA observation*inner ℂ probe (actualWriteRead observation nontrivial half depth ordinal).1.1-
      inner ℂ probe (originalField (Prior.actualWriteRead observation nontrivial half depth ordinal))=
      inner ℂ probe (Flux.primitiveSource observation nontrivial half)+
      Flux.sourceA observation*inner ℂ probe (Op.R observation nontrivial half (oldIncrement observation nontrivial half depth ordinal))-
      inner ℂ probe (oldIncrement observation nontrivial half depth ordinal)+
      Flux.sourceA observation*inner ℂ probe (Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)) := by
  have actual:=congrArg (fun value : BurnolL2=>inner ℂ probe value)
    (actual_R_source_equation observation nontrivial half depth ordinal)
  simpa only [inner_sub_right,inner_add_right,inner_smul_right] using actual

/-- This receiver consumes the new source receipt, full action and own whole-next.
Its constructor receives none of the generated target fields or effects. -/
theorem consume_actual_full_source_R (ordinal : Nat) (shift : ℝ) :
    (type_of% (actual_complete_R_source observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_material_source_effect observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_written_source observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_defect_flux observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_source_equation observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_complete_four_terms observation nontrivial half depth ordinal shift)) ∧
    (type_of% (actual_R_whole observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_next observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_action_payment observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_action_payment_entry observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_word_inventory observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_boundary_in_born observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_four_faces observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_full_trace observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_born_inventory observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_R_joint_inventory observation nontrivial half depth ordinal)) :=
  ⟨actual_complete_R_source _ _ _ _ _,actual_material_source_effect _ _ _ _ _,
   actual_R_written_source _ _ _ _ _,actual_R_defect_flux _ _ _ _ _,
   actual_R_source_equation _ _ _ _ _,actual_R_complete_four_terms _ _ _ _ _ shift,
   actual_R_whole _ _ _ _ _,actual_R_next _ _ _ _ _,actual_action_payment _ _ _ _ _,
   actual_action_payment_entry _ _ _ _ _,actual_R_word_inventory _ _ _ _ _,
   actual_R_boundary_in_born _ _ _ _ _,actual_R_four_faces _ _ _ _ _,actual_R_full_trace _ _ _ _ _,
   actual_R_born_inventory _ _ _ _ _,actual_R_joint_inventory _ _ _ _ _⟩

theorem consume_actual_inherited_and_new_R (ordinal : Nat) (shift : ℝ) :
    (type_of% (OriginalKDefectAction.consume_actual_defect_source observation nontrivial half depth ordinal)) ∧
    (type_of% (consume_actual_full_source_R observation nontrivial half depth ordinal shift)) ∧
    (type_of% (actual_input_stage_payment observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_input_stage_payment_entry observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_input_boundary_in_born observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_input_four_faces observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_input_full_trace observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_input_word_inventory observation nontrivial half depth ordinal)) :=
  ⟨OriginalKDefectAction.consume_actual_defect_source _ _ _ _ _,consume_actual_full_source_R _ _ _ _ _ shift,
    actual_input_stage_payment _ _ _ _ _,actual_input_stage_payment_entry _ _ _ _ _,
    actual_input_boundary_in_born _ _ _ _ _,actual_input_four_faces _ _ _ _ _,
    actual_input_full_trace _ _ _ _ _,actual_input_word_inventory _ _ _ _ _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

