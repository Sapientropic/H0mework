import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FullStock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.Consumer

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open BurnolPhysicalState OriginalKCofinalFullBranchFibre
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

open private current from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients

namespace Rel
export OriginalKCofinalFullBranchFibre.RootRelation
  (SourceCompletion sourceHistory sourceRoot sourceCurrent sourceReader factor factor_source_word
    sourceClass factor_source_class receivedModel received_model_next)
end Rel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "step" => sourceStep observation nontrivial half
local notation "branches" => sourceBranches observation nontrivial half
local notation "model" => SourceModel observation nontrivial half
local notation "project" => H.projection step branches
local notation "modelNext" => H.modelAction step branches

/-- Read the complete branch stock from the existing source-action coimage. -/
def modelInventory : model →ₗ[ℂ] WholeBranchStock :=
  (branchCoordinates coord).toLinearMap.comp (modelReadback observation nontrivial half)

local notation "readModel" => modelInventory observation nontrivial half

private theorem model_inventory_projection (value : SourcePair) :
    readModel (project value) = branchCoordinates coord value := by
  change branchCoordinates coord
    (modelReadback observation nontrivial half (project value)) = _
  rw [model_readback_source]

private theorem model_source (value : model) : ∃ pair, project pair = value :=
  (SourceGeneratedActionObservationHistory.actionRow step branches).restriction_surjective value

theorem modelInventory_injective : Function.Injective readModel := by
  intro a b read
  obtain ⟨x, hx⟩ := model_source observation nontrivial half a
  obtain ⟨y, hy⟩ := model_source observation nontrivial half b
  rw [← hx, ← hy] at read ⊢
  rw [model_inventory_projection, model_inventory_projection] at read
  rw [(branchCoordinates coord).injective read]

/-- The independently calculated stock update acts on every original model value. -/
theorem model_inventory_action (value : model) :
    advanceStock coord (readModel value) = readModel (modelNext value) := by
  obtain ⟨source, same⟩ := model_source observation nontrivial half value
  rw [← same, H.modelAction_source, model_inventory_projection, model_inventory_projection]
  exact actual_stock_source_step observation nontrivial half source

variable (depth : Nat)

local notation "packetFactor" => Rel.factor observation nontrivial half depth
local notation "classAt" => Rel.sourceClass observation nontrivial half depth

/-- The relation completion feeds the stock through its actual factor and branch recovery. -/
def relationInventory (ordinal : Nat) :
    Rel.SourceCompletion observation nontrivial half depth ordinal →ₗ[ℤ] WholeBranchStock :=
  ((readModel).restrictScalars ℤ).comp (packetFactor ordinal)

local notation "readRelation" => relationInventory observation nontrivial half depth

/-- The full inventory has the exact original relation-factor fibre. -/
theorem actual_relation_inventory_fibre (ordinal : Nat)
    (left right : Rel.SourceCompletion observation nontrivial half depth ordinal) :
    readRelation ordinal left = readRelation ordinal right ↔
      packetFactor ordinal left = packetFactor ordinal right := by
  change readModel (packetFactor ordinal left) = readModel (packetFactor ordinal right) ↔ _
  exact ⟨fun same => modelInventory_injective observation nontrivial half same,
    congrArg (fun value : model => readModel value)⟩

namespace Src
export OriginalKCofinalFullBranchFibre.RootRelation.D (packet)
export OriginalKCofinalFullBranchFibre.RootRelation.CF (collapseValue)
export OriginalKCofinalFullBranchFibre.RootRelation.Own (raw)
end Src

local instance relationGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKCofinalFullBranchFibre.RootRelation.L.Value
      (PairValue OriginalKCofinalFullBranchFibre.RootRelation.C.Value) grade target) :=
  OriginalKCofinalFullBranchFibre.RootRelation.L.groups
    (PairValue OriginalKCofinalFullBranchFibre.RootRelation.C.Value) grade

/-- Every actual word is read through the original sound evaluator before entering the stock. -/
theorem actual_relation_word_inventory (ordinal : Nat)
    (word : (Rel.sourceHistory observation nontrivial half depth ordinal).generatorClosure) :
    let history := Rel.sourceHistory observation nontrivial half depth ordinal;
    let source := Src.raw (Rel.sourceRoot observation nontrivial half depth ordinal)
      (Rel.sourceCurrent observation nontrivial half depth ordinal)
      (Rel.sourceReader observation nontrivial half depth ordinal);
    readRelation ordinal (history.completionProjection word) =
      branchCoordinates coord (branchReadback observation nontrivial half
        (Src.collapseValue (Src.packet observation nontrivial half depth ordinal).1
          (evaluation (R := ℤ) source.environment word.val))) := by
  dsimp only
  change readModel (packetFactor ordinal
    ((Rel.sourceHistory observation nontrivial half depth ordinal).completionProjection word)) = _
  exact (congrArg (fun value : model => readModel value)
    (Rel.factor_source_word observation nontrivial half depth ordinal word)).trans
    (model_inventory_projection observation nontrivial half _)

/-- The selected relation generator retains the literal Division outside slot and original position coefficients. -/
theorem actual_relation_stock (ordinal : Nat) :
    readRelation ordinal (classAt ordinal) =
      (WithLp.toLp 2 (coefficientsAt observation nontrivial half depth ordinal, 0),
        (D.input observation nontrivial half depth ordinal).2) := by
  change readModel (packetFactor ordinal (classAt ordinal)) = _
  rw [Rel.factor_source_class, model_inventory_projection]
  exact branchCoordinates_gap coord _ (current observation nontrivial half depth ordinal) rfl

/-- The same relation occurrence generates the complete stock of the literal next occurrence. -/
theorem actual_relation_stock_next (ordinal : Nat) :
    advanceStock coord (readRelation ordinal (classAt ordinal)) =
      readRelation (ordinal+1) (classAt (ordinal+1)) := by
  change advanceStock coord (readModel (Rel.receivedModel observation nontrivial half depth ordinal)) =
    readModel (Rel.receivedModel observation nontrivial half depth (ordinal+1))
  rw [model_inventory_action, Rel.received_model_next]

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
