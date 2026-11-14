import SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthConstants.Receipt.Continuation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.BirthConstants

set_option autoImplicit false
set_option linter.defProp false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.BirthRelation.CP782Independent

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation
open SourceGeneratedScalarDifferentialResidual

section Generic
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] familyGroups
variable (factory : SF.Factory W X s) (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
variable (stock : Feed.Inventory (V := L.Value W packet.1) (X := X) (s := s))
variable (installed : packet.2.1.1.inventory = some stock) (origin : Feed.RelationOccurrence stock)

set_option cleanup.letToHave false in
private def each_supported_item_uses_the_original_request_position_and_paid_segment
    (index : SourceReceiptOccurrence.SupportIndex factory packet stock installed origin) :=
  let execution := SourceReceiptOccurrence.atBirth factory packet stock installed origin index
  have typed : Nonempty (Trace execution.decoder execution.request.expression
    (.const (execution.request.expression.eval execution.decoder))) := ⟨execution.paid⟩
  And.intro (SourceReceiptOccurrence.atBirth_request_position factory packet stock installed origin index) <|
  And.intro (SourceReceiptOccurrence.atBirth_segment_position factory packet stock installed origin index) <|
  And.intro execution.installed <|
  And.intro execution.decoder_source (And.intro typed execution.segment.trace_eq)

set_option cleanup.letToHave false in
private def the_same_signed_receipts_generate_the_whole_table_and_both_inventory_legs :=
  And.intro (receipt_table_action factory packet stock installed origin) <|
  And.intro (receipt_inventory_action factory packet stock installed origin)
    (written_from_receipts factory packet stock installed origin)

set_option cleanup.letToHave false in
private def the_actual_affine_write_has_opposite_effects_and_the_complete_inverse_fibre
    (candidate : Formal ℤ (L.Value W (packet.1+1)) packet.2.2.1.LowVar s) :=
  And.intro (written_inventory factory packet stock installed origin)
    (written_inverse_fibre factory packet stock installed origin candidate)
end Generic

private abbrev IntValue := fun _ : Unit => ℤ
private abbrev IntVar := fun _ : Unit => Unit
private abbrev IntegerWord := Formal ℤ IntValue IntVar ()
private def one : Env IntValue IntVar := fun _ _ => 1
private def variableWord : IntegerWord := Finsupp.single (.var ()) 1
private def normalized : IntegerWord :=
  relationMap (R := ℤ) (one+one) (normalizationCertificate (R := ℤ) (one+one) variableWord)

private theorem normalized_is_literal :
    normalized = variableWord - Finsupp.single (.const 2) 1 := by
  rw [normalized, source_reduction]
  simp only [variableWord,valueMap,constantMap,Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single,Expr.eval,Pi.add_apply,one]
  rfl

private theorem the_produced_integer_affine_word_has_zero_sum_but_two_nonzero_legs :
    let update := updateInventory (R := ℤ) (s := ()) one one
    update normalized = (-1,1) ∧
      (update normalized).1 + (update normalized).2 = 0 ∧ canonicalResidual update normalized ≠ 0 ∧
      ∀ candidate : IntegerWord, canonicalResidual update candidate = canonicalResidual update normalized ↔
        evaluation (R := ℤ) one candidate = -1 ∧ effectEvaluator (R := ℤ) one one candidate = 1 := by
  intro update
  have single (expression : Expr IntValue IntVar ()) :
      update (Finsupp.single expression 1) = (expression.eval one, expression.effect one one) := by
    change ((evaluation (R := ℤ) one) (Finsupp.single expression 1),
      (effectEvaluator (R := ℤ) one one) (Finsupp.single expression 1)) = _
    simp only [evaluation,effectEvaluator,Finsupp.linearCombination_single,one_smul]
  have paid : update normalized = (-1,1) := by
    rw [normalized_is_literal, map_sub]
    change update (Finsupp.single (.var ()) 1) - update (Finsupp.single (.const 2) 1) = _
    simp only [single,Expr.eval,Expr.effect,one,Prod.mk_sub_mk]; decide
  refine ⟨paid, ?_, ?_, ?_⟩
  · rw [paid]
    decide
  · exact (canonicalResidual_ne_zero_iff update normalized).mpr (by rw [paid]; decide)
  · intro candidate
    have full : canonicalResidual update candidate = canonicalResidual update normalized ↔
        update candidate = update normalized := by
      simpa only [map_sub,sub_eq_zero] using canonicalResidual_eq_zero_iff update (candidate-normalized)
    rw [paid] at full
    exact full.trans (by
      change (evaluation (R := ℤ) one candidate,effectEvaluator (R := ℤ) one one candidate) =
        (-1,1) ↔ _
      simp only [Prod.mk.injEq])

end ActualCofinalSourceAction.BirthRelation.CP782Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKDirectRCofinalDivision.BirthConstants.CP782Independent

open BurnolPhysicalState
open SourceOperationScalarInventoryLift
open ActualCofinalSourceAction.BirthRelation (actual_written_next actual_written_model_step)

local instance baseGroups : ∀ target, AddCommGroup (PairValue C.Value target) := fun _ => inferInstance

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

set_option cleanup.letToHave false in
private def paidDivisionContinuation
    (factory : ActualCofinalSourceAction.SF.Factory (PairValue C.Value) C.Var ())
    (initial : ActualCofinalSourceAction.A.M.Frame (Value := PairValue C.Value) (Var := C.Var) (sort := ()))
    (cfg : ActualCofinalSourceAction.A.Programme (PhysicalValue := PairValue C.Value) (PhysicalVar := C.Var) (sort := ()))
    (language : cfg.LowVar = C.Var) (index : Nat) :=
  And.intro
    (actual_written_next (W := PairValue C.Value) (X := C.Var) (s := ()) factory initial cfg language index)
    (actual_written_model_step (W := PairValue C.Value) (X := C.Var) (s := ()) factory initial cfg language index)

set_option cleanup.letToHave false in
private def the_original_D_packet_feeds_its_literal_next_and_model_with_whole_and_K :=
  And.intro
    (paidDivisionContinuation (D.factory observation nontrivial half)
      (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) <|
  And.intro (actual_birth_source observation nontrivial half depth ordinal)
    (actual_birth_K observation nontrivial half depth ordinal)

run_cmd do
  IO.println "CP782_CONTROL + each_supported_item_uses_the_original_request_position_and_paid_segment\nCP782_CONTROL + the_same_signed_receipts_generate_the_whole_table_and_both_inventory_legs\nCP782_CONTROL + the_actual_affine_write_has_opposite_effects_and_the_complete_inverse_fibre\nCP782_CONTROL + the_original_D_packet_feeds_its_literal_next_and_model_with_whole_and_K\nCP782_CONTROL - the_produced_integer_affine_word_has_zero_sum_but_two_nonzero_legs\nCP782_GATE_PASS positive=4 negative=1"

end OriginalKDirectRCofinalDivision.BirthConstants.CP782Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
