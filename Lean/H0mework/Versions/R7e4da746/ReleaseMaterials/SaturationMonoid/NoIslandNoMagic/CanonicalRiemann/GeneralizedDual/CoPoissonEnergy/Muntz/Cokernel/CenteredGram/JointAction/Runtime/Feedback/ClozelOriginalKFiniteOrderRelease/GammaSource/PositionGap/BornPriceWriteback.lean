import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceInnovation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState Finset
open OriginalKCofinalFullBranchFibre (SourceModel sourceStep sourceBranches)
open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot
open scoped BigOperators

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R" => burnolDirectRightResolventCLM c
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "graph" => actualWide observation nontrivial half depth
local notation "model" => HilbertInventory.Rel.receivedModel observation nontrivial half depth
local notation "readModel" => modelInventory observation nontrivial half
local notation "modelNext" => OriginalKCofinalFullBranchFibre.H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
local notation "width" => birthPriceWidth observation nontrivial half depth

private def rebuildBirth (start ordinal : Nat) (read : PriceGram.Coordinates (range (ordinal+1)) × ℂ) :
    Wide × SourceModel observation nontrivial half :=
  ((∑ j : range (ordinal+1), read.1 j • graph (start+j.val)) + read.2 • graph (start+ordinal+1),
    (∑ j : range (ordinal+1), read.1 j • model (start+j.val)) + read.2 • model (start+ordinal+1))

/-- Both complete stocks are decoded by one price inventory, through their original graph and relation carriers. -/
def restoreBirth (start ordinal : Nat) (values : PriceGram.Coordinates (Fin (width start ordinal))) :
    Wide × SourceModel observation nontrivial half :=
  rebuildBirth observation nontrivial half depth start ordinal
    (decodeBornPrices observation nontrivial half depth start ordinal values)

theorem actual_born_price_writeback (start ordinal : Nat)
    (a : PriceGram.Coordinates (range (ordinal+1))) (b : ℂ) :
    let written := R (raw (start+ordinal))
    let values := readPriceWindow observation half (width start ordinal)
      ((∑ j : range (ordinal+1), a j • raw (start+j.val)) + b • written)
    let restored := restoreBirth observation nontrivial half depth start ordinal values
    let expected := rebuildBirth observation nontrivial half depth start ordinal (a,b)
    let successor := rebuildBirth observation nontrivial half depth (start+1) ordinal (a,b)
    restored = expected ∧
      (advanceWide c observation.mathlibZero restored.1, advanceStock c (readModel restored.2)) =
        (successor.1, readModel successor.2) := by
  have action : R (raw (start+ordinal)) = raw (start+ordinal+1) := by
    rw [OriginalKCombFirstFullSourceDynamics.raw_successor,
      OriginalKCombCofinalRAction.original_R_direct]
    rfl
  dsimp only
  rw [action, restoreBirth, actual_born_price_decode]
  refine ⟨rfl,Prod.ext ?_ ?_⟩
  · simp only [rebuildBirth, map_add, map_sum, map_smul, actual_wide_next,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · rw [HilbertInventory.model_inventory_action]
    apply congrArg readModel
    change modelNext ((∑ j : range (ordinal+1), a j • model (start+j.val))+
      b • model (start+ordinal+1)) = _
    simp only [rebuildBirth, map_add, map_sum, map_smul, HilbertInventory.Rel.received_model_next,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
