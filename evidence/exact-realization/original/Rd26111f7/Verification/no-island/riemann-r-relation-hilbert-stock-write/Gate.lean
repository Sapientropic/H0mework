import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace RelationHilbertStockCertificate

open BurnolPhysicalState OriginalKCofinalFullBranchFibre
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.OutsideQuarterAction
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
open OriginalKDirectRCofinalOutsideVolterraSource (hPowerPhysicalCorrection)
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource (powerCorrection_ne_zero)
open OriginalKCofinalFullBranchFibre.RootRelation (actual_root_relation_consumer)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open scoped lp

local instance relationGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKCofinalFullBranchFibre.RootRelation.L.Value
      (PairValue OriginalKCofinalFullBranchFibre.RootRelation.C.Value) grade target) :=
  OriginalKCofinalFullBranchFibre.RootRelation.L.groups
    (PairValue OriginalKCofinalFullBranchFibre.RootRelation.C.Value) grade

local notation "R₀" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "BI" => burnolMeanZeroBlockInverse

section Actual

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "historyAt" => Rel.sourceHistory observation nontrivial half depth
local notation "stockAt" => relationInventory observation nontrivial half depth
local notation "factorAt" => Rel.factor observation nontrivial half depth
local notation "classAt" => Rel.sourceClass observation nontrivial half depth

run_cmd IO.eprintln "CP564_CONTROL + original_word_roundtrips_through_the_complete_branch_stock"
set_option cleanup.letToHave false in
theorem original_word_roundtrips_through_the_complete_branch_stock (ordinal : Nat)
    (word : (historyAt ordinal).generatorClosure) :
    let history := historyAt ordinal;
    let source := Src.raw (Rel.sourceRoot observation nontrivial half depth ordinal)
      (Rel.sourceCurrent observation nontrivial half depth ordinal)
      (Rel.sourceReader observation nontrivial half depth ordinal);
    let pair := branchReadback observation nontrivial half
      (Src.collapseValue (Src.packet observation nontrivial half depth ordinal).1
        (evaluation (R := ℤ) source.environment word.val));
    let read := stockAt ordinal (history.completionProjection word);
    read = branchCoordinates c pair ∧ (branchCoordinates c).symm read = pair := by
  let paid := actual_relation_word_inventory observation nontrivial half depth ordinal word
  exact ⟨paid,(congrArg (fun stock : WholeBranchStock => (branchCoordinates c).symm stock) paid).trans
    ((branchCoordinates c).symm_apply_apply _)⟩

run_cmd IO.eprintln "CP564_CONTROL + the_complete_relation_inventory_has_the_original_factor_fibre"
theorem the_complete_relation_inventory_has_the_original_factor_fibre (ordinal : Nat)
    (left right : Rel.SourceCompletion observation nontrivial half depth ordinal) :
    stockAt ordinal left = stockAt ordinal right ↔ factorAt ordinal left = factorAt ordinal right :=
  actual_relation_inventory_fibre observation nontrivial half depth ordinal left right

run_cmd IO.eprintln "CP564_CONTROL + every_old_model_advances_with_its_true_orthogonal_residual"
theorem every_old_model_advances_with_its_true_orthogonal_residual
    (value : SourceModel observation nontrivial half) :
    let old := modelInventory observation nontrivial half value;
    let a := old.1.fst;
    let quarter := nextFourierCenter c (hankel c a) (centeredFourier c a);
    advanceStock c old =
      modelInventory observation nontrivial half
        (H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half) value) ∧
    (advanceStock c old).2 =
      outsideEmbedding (BI quarter) + O (R₀ c (old.1.snd : BurnolL2)) :=
  ⟨model_inventory_action observation nontrivial half value,rfl⟩

run_cmd IO.eprintln "CP564_CONTROL + both_literal_source_classes_keep_the_old_disposition_whole_and_next"
set_option cleanup.letToHave false in
theorem both_literal_source_classes_keep_the_old_disposition_whole_and_next (ordinal : Nat) :
    stockAt ordinal (classAt ordinal) =
      (WithLp.toLp 2 (coefficientsAt observation nontrivial half depth ordinal, 0),
        (D.input observation nontrivial half depth ordinal).2) ∧
    stockAt (ordinal+1) (classAt (ordinal+1)) =
      (WithLp.toLp 2 (coefficientsAt observation nontrivial half depth (ordinal+1), 0),
        (D.input observation nontrivial half depth (ordinal+1)).2) ∧
    advanceStock c (stockAt ordinal (classAt ordinal)) = stockAt (ordinal+1) (classAt (ordinal+1)) ∧
    type_of% (actual_root_relation_consumer observation nontrivial half depth ordinal) ∧
    type_of% (actual_division_action_same_root observation nontrivial half depth ordinal) :=
  ⟨actual_relation_stock observation nontrivial half depth ordinal,
    actual_relation_stock observation nontrivial half depth (ordinal+1),
    actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_root_relation_consumer observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

end Actual

run_cmd IO.eprintln "CP564_CONTROL - the_old_balanced_pair_cannot_lose_its_actual_exterior"
theorem the_old_balanced_pair_cannot_lose_its_actual_exterior (c : BurnolCompletedMellinCoordinate) :
    let v := hPowerPhysicalCorrection c;
    let balanced : SourcePair := (v,-v);
    let emptyPair : SourcePair := (0,0);
    (branchCoordinates c balanced).1 = (branchCoordinates c emptyPair).1 ∧
      (branchCoordinates c balanced).2 ≠ 0 ∧
      branchCoordinates c balanced ≠ branchCoordinates c emptyPair := by
  dsimp only
  have live : -hPowerPhysicalCorrection c ≠ 0 := neg_ne_zero.mpr (powerCorrection_ne_zero c)
  refine ⟨?_,live,fun same => live (congrArg Prod.snd same)⟩
  change wholeCoordinates c (hPowerPhysicalCorrection c + -hPowerPhysicalCorrection c) =
    wholeCoordinates c (0+0)
  rw [add_neg_cancel,zero_add]

end RelationHilbertStockCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
