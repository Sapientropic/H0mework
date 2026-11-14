import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.ColumnWriteback

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.CP776Independent

open SourceOperationEffects SourceOperationScalarInventoryLift
open SourceOperationInquiry.Context.Installation
  (executedEnvironmentIncrement next_raw_environment_from_executed_increment executed_increment_eq_difference)
open scoped InnerProductSpace

section Actual
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (grade : Nat) (frame : Frame (K := K) grade)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current := current))

set_option cleanup.letToHave false in
private def one_located_actual_request_pays_old_effect_and_its_literal_next
    (index : Index grade frame) :=
  And.intro (next_raw_environment_from_executed_increment frame supplied) <|
  And.intro (executed_increment_eq_difference frame supplied) <|
  And.intro (request_origin grade frame index) <|
  And.intro (actual_column_action_value grade frame supplied index) <|
  And.intro (actual_column_action_components read grade frame supplied index) <|
  And.intro (actual_column_from_action read grade frame supplied index)
    (actual_column_reads_next read grade frame supplied index)

private theorem original_Gram_entry_reads_all_four_ordered_terms (i j : Index grade frame) :
    let left := columnAction read grade frame supplied i
    let right := columnAction read grade frame supplied j
    FG.gram (columns read grade frame supplied) i j =
      inner ℂ left.1 right.1+inner ℂ left.1 right.2+inner ℂ left.2 right.1+inner ℂ left.2 right.2 :=
  congrArg (fun matrix : Matrix (Index grade frame) (Index grade frame) ℂ => matrix i j)
    (actual_gram_from_column_actions read grade frame supplied)

set_option cleanup.letToHave false in
private def the_full_Gram_action_rhs_kernel_and_residual_use_that_request_family
    (i j : Index grade frame) (value : K)
    (coordinates : SourceGeneratedFiniteGram.Coordinates (Index grade frame)) :=
  And.intro (original_Gram_entry_reads_all_four_ordered_terms read grade frame supplied i j) <|
  And.intro (actual_gram_rhs_from_column_actions read grade frame supplied value) <|
  And.intro (column_action_equation read grade frame supplied value) <|
  And.intro (actual_column_action_fibre read grade frame supplied value coordinates)
    (actual_innovation_from_column_actions read grade frame supplied value)

variable (sourceFrame : JointMeasured.Frame (K := K))

set_option cleanup.letToHave false in
private def the_actual_next_joint_pays_the_action_residual_through_the_original_born
    (ordinal : ℕ) :=
  And.intro (Integrated.next_joint_is_actual read sourceFrame ordinal) <|
  And.intro (Integrated.born_fresh_vector read sourceFrame ordinal)
    (Integrated.actual_next_from_column_actions read sourceFrame ordinal)

set_option cleanup.letToHave false in
private def the_same_site_keeps_completed_whole_next_both_inventories_and_request_positions
    (ordinal : ℕ) :=
  let packet := Integrated.site read sourceFrame ordinal
  let nativeFrame := A.epoch packet.2.1.1
  And.intro (Integrated.next_packet_is_actual read sourceFrame ordinal) <|
  And.intro (Integrated.next_inventory_is_actual read sourceFrame ordinal) <|
  And.intro (Integrated.next_pair_inventory_is_actual read sourceFrame ordinal) <|
  And.intro (Integrated.next_stock_from_actual_born read sourceFrame ordinal) <|
  And.intro (Integrated.completed_whole read sourceFrame ordinal) <|
  And.intro (Integrated.completed_next read sourceFrame ordinal)
    (fun index : Index packet.1 nativeFrame => request_origin packet.1 nativeFrame index)
end Actual

private theorem dropping_both_cross_terms_changes_a_concrete_Gram_entry :
    inner ℂ ((1 : ℂ)+1) ((1 : ℂ)+1) =
      inner ℂ (1 : ℂ) (1 : ℂ)+inner ℂ (1 : ℂ) (1 : ℂ)+
        inner ℂ (1 : ℂ) (1 : ℂ)+inner ℂ (1 : ℂ) (1 : ℂ) ∧
    inner ℂ ((1 : ℂ)+1) ((1 : ℂ)+1) ≠ inner ℂ (1 : ℂ) (1 : ℂ)+inner ℂ (1 : ℂ) (1 : ℂ) := by
  have unit : inner ℂ (1 : ℂ) (1 : ℂ) = 1 := by rw [RCLike.inner_apply]; simp
  have four : inner ℂ ((1 : ℂ)+1) ((1 : ℂ)+1) = 4 := by
    simp only [inner_add_left,inner_add_right,unit]
    norm_num
  constructor
  · rw [four,unit]
    norm_num
  · rw [four,unit]
    norm_num

run_cmd do
  IO.println "CP776_CONTROL + one_located_actual_request_pays_old_effect_and_its_literal_next\nCP776_CONTROL + the_full_Gram_action_rhs_kernel_and_residual_use_that_request_family\nCP776_CONTROL + the_actual_next_joint_pays_the_action_residual_through_the_original_born\nCP776_CONTROL + the_same_site_keeps_completed_whole_next_both_inventories_and_request_positions\nCP776_CONTROL - dropping_both_cross_terms_changes_a_concrete_Gram_entry\nCP776_GATE_PASS positive=4 negative=1"

end PaidSourceContentEnvironment.GradedInnovation.CP776Independent
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
