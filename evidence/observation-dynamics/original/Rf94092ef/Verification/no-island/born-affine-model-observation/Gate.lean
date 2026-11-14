import SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthConstants.Receipt.Observation
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.BirthConstants
import SaturationMonoid.GenericFoundation.Operations.Observed.Coimage

set_option autoImplicit false
set_option linter.defProp false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.BirthRelation.CP783Independent

open SourceOperationEffects SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation
open private model_observes_packet native_birth_inventory from
  SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthConstants.Receipt.Observation

section Generic
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] familyGroups
variable (factory : SF.Factory W X s)
variable (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s)) (language : cfg.LowVar = X)

set_option cleanup.letToHave false in
private def the_stopped_source_and_updated_decoder_are_the_actual_tower_input
    (ordinal : Nat) (word : Tower.Words factory initial cfg language ordinal) :=
  And.intro
    ((Tower.installed_environment factory initial cfg language ordinal).trans
      (ActualCofinalInstalledRaw.materialAtStop_source factory initial cfg language ordinal).1) <|
  And.intro (Post.updated_environment_current factory initial cfg language ordinal)
    (model_observes_packet factory initial cfg language ordinal word)

set_option cleanup.letToHave false in
private def the_original_birth_inventory_keeps_both_signed_channels
    (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
    (stock : Feed.Inventory (V := L.Value W packet.1) (X := X) (s := s))
    (present : packet.2.1.1.inventory = some stock) (origin : Feed.RelationOccurrence stock) :=
  And.intro (native_birth_inventory factory packet stock present origin)
    (written_inventory factory packet stock present origin)

set_option cleanup.letToHave false in
private def the_literal_born_class_exposes_the_affine_pair_and_its_decoder_is_zero (ordinal : Nat) :=
  And.intro
    (actual_written_model_observation factory initial cfg language ordinal) <|
  And.intro (actual_written_next factory initial cfg language ordinal)
    (actual_written_model_step factory initial cfg language ordinal)
end Generic

namespace Hist
export SourceGeneratedActionObservationHistory (projection modelReadout modelReadout_projection model_fibre_iff)
end Hist

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

private def pairObserver : IntegerWord →ₗ[ℤ] ℤ × ℤ :=
  updateInventory (R := ℤ) one one

private def decoderObserver : IntegerWord →ₗ[ℤ] ℤ :=
  evaluation (R := ℤ) (one+one)

private theorem actual_pair : pairObserver normalized = (-1,1) := by
  have single (expression : Expr IntValue IntVar ()) :
      pairObserver (Finsupp.single expression 1) = (expression.eval one, expression.effect one one) := by
    change ((evaluation (R := ℤ) one) (Finsupp.single expression 1),
      (effectEvaluator (R := ℤ) one one) (Finsupp.single expression 1)) = _
    simp only [evaluation,effectEvaluator,Finsupp.linearCombination_single,one_smul]
  rw [normalized_is_literal, map_sub]
  change pairObserver (Finsupp.single (.var ()) 1) - pairObserver (Finsupp.single (.const 2) 1) = _
  simp only [single,Expr.eval,Expr.effect,one,Prod.mk_sub_mk]
  decide

private theorem the_real_history_model_separates_the_affine_word_that_the_decoder_erases :
    let action : IntegerWord →ₗ[ℤ] IntegerWord := LinearMap.id
    Hist.modelReadout action pairObserver (Hist.projection action pairObserver normalized) = (-1,1) ∧
      Hist.projection action pairObserver normalized ≠ 0 ∧
      Hist.projection action decoderObserver normalized = 0 := by
  intro action
  have pairRead := (Hist.modelReadout_projection action pairObserver normalized).trans actual_pair
  have decoded : decoderObserver normalized = 0 := by
    have read := LinearMap.congr_fun (evaluation_update (R := ℤ) (s := ()) one one) normalized
    change decoderObserver normalized = (pairObserver normalized).1 + (pairObserver normalized).2 at read
    rw [actual_pair] at read
    exact read.trans (by decide)
  refine ⟨pairRead, ?_, ?_⟩
  · intro erase
    have empty := (congrArg (Hist.modelReadout action pairObserver) erase).trans (map_zero _)
    exact (by decide : ((-1,1) : ℤ × ℤ) ≠ 0) (pairRead.symm.trans empty)
  · rw [← map_zero (Hist.projection action decoderObserver)]
    apply (Hist.model_fibre_iff action decoderObserver normalized 0).mpr
    intro stage
    change decoderObserver (((1 : Module.End ℤ IntegerWord) ^ stage) normalized) =
      decoderObserver (((1 : Module.End ℤ IntegerWord) ^ stage) 0)
    simp only [one_pow, Module.End.one_apply, map_zero, decoded]

end ActualCofinalSourceAction.BirthRelation.CP783Independent

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKDirectRCofinalDivision.BirthConstants.CP783Independent

open BurnolPhysicalState
open SourceOperationScalarInventoryLift
open ActualCofinalSourceAction.BirthRelation.CP783Independent
local instance baseGroups : ∀ target, AddCommGroup (PairValue C.Value target) := fun _ => inferInstance

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

set_option cleanup.letToHave false in
private def the_original_D_stop_passes_the_observed_word_to_literal_next_and_K :=
  And.intro
    (the_literal_born_class_exposes_the_affine_pair_and_its_decoder_is_zero
      (W := PairValue C.Value) (X := C.Var) (s := ()) (D.factory observation nontrivial half)
      (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+1)) <|
  And.intro (actual_birth_source observation nontrivial half depth ordinal)
    (actual_birth_K observation nontrivial half depth ordinal)

run_cmd do
  IO.println "CP783_CONTROL + the_stopped_source_and_updated_decoder_are_the_actual_tower_input\nCP783_CONTROL + the_original_birth_inventory_keeps_both_signed_channels\nCP783_CONTROL + the_literal_born_class_exposes_the_affine_pair_and_its_decoder_is_zero\nCP783_CONTROL + the_original_D_stop_passes_the_observed_word_to_literal_next_and_K\nCP783_CONTROL - the_real_history_model_separates_the_affine_word_that_the_decoder_erases\nCP783_GATE_PASS positive=4 negative=1"

end OriginalKDirectRCofinalDivision.BirthConstants.CP783Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
