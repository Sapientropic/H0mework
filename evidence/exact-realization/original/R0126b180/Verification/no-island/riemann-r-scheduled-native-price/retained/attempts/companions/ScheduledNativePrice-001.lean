import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalCalculatedSource.Projection
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState
open scoped InnerProductSpace

open private nextCutoff from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord
open private literal_price_at from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord

namespace Native
export OriginalKCombFirstFullSourceDynamics (factory initial firstCfg raw)
export ActualCofinalRootResidualConsumer (rootedMaterial)
export OriginalKDirectRCofinalCalculatedSource (calculatedTargetRaw calculated_target_raw_successor)
end Native

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => Native.raw observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth

private theorem scheduled_time_pos (start count : Nat) (i : Fin count) : 0 < (schedule start count).val i := by
  induction count with
  | zero => exact Fin.elim0 i
  | succ count prior =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · unfold priceSchedule
      rw [SourceGeneratedFiniteGram.CofinalRecord.schedule_last]
      unfold SourceGeneratedFiniteGram.CofinalRecord.pivotTime nextCutoff
      omega
    · unfold priceSchedule
      rw [SourceGeneratedFiniteGram.CofinalRecord.schedule_prior]
      exact prior j

private def predecessor (start count actor : Nat) (i : Fin count) : Nat :=
  actor+(schedule start count).val i-1

private theorem predecessor_next (start count actor : Nat) (i : Fin count) :
    predecessor observation nontrivial half depth start count actor i+1 =
      actor+(schedule start count).val i := by
  have positive := scheduled_time_pos observation nontrivial half depth start count i
  unfold predecessor
  omega

private def materialAt (ordinal : Nat) :=
  Native.rootedMaterial factory initial cfg rfl (ordinal+1)

/-- A scheduled sample carries the actual rooted material that wrote the sampled field. -/
def scheduledMaterial (start count actor : Nat) (i : Fin count) :
    Σ ordinal : Nat, type_of% (materialAt observation nontrivial half depth ordinal) :=
  let ordinal := predecessor observation nontrivial half depth start count actor i
  ⟨ordinal,materialAt observation nontrivial half depth ordinal⟩

theorem actual_scheduled_material_prior (start count actor : Nat) (i : Fin count) :
    scheduledMaterial observation nontrivial half depth start (count+1) actor i.castSucc =
      scheduledMaterial observation nontrivial half depth start count actor i := by
  have same : predecessor observation nontrivial half depth start (count+1) actor i.castSucc =
      predecessor observation nontrivial half depth start count actor i := by
    simp only [predecessor, priceSchedule, SourceGeneratedFiniteGram.CofinalRecord.schedule_prior]
  exact congrArg (fun ordinal =>
    (⟨ordinal, materialAt observation nontrivial half depth ordinal⟩ :
      Σ k : Nat, type_of% (materialAt observation nontrivial half depth k))) same

def paidPriceSample (start count actor : Nat) (i : Fin count) : ℂ :=
  let material := scheduledMaterial observation nontrivial half depth start count actor i
  let whole := Native.calculatedTargetRaw observation nontrivial half depth material.1
  inner ℂ (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))
    (OriginalKCombCofinalPaAction.Q whole:BurnolL2)

/-- The price is taken from the actual next material's complete four-branch value and original Q. -/
theorem actual_paid_price_sample (start count actor : Nat) (i : Fin count) :
    paidPriceSample observation nontrivial half depth start count actor i =
      recordedPrices observation nontrivial half depth start count (raw actor) i := by
  let ordinal := predecessor observation nontrivial half depth start count actor i
  have written : Native.calculatedTargetRaw observation nontrivial half depth ordinal = raw (ordinal+1) :=
    Native.calculated_target_raw_successor observation nontrivial half depth ordinal
  change inner ℂ (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))
      (OriginalKCombCofinalPaAction.Q (Native.calculatedTargetRaw observation nontrivial half depth ordinal):BurnolL2) =
    nativePriceAt observation half (raw actor) ((schedule start count).val i)
  rw [written]
  have index : ordinal+1=actor+(schedule start count).val i :=
    predecessor_next observation nontrivial half depth start count actor i
  rw [index]
  exact (literal_price_at observation nontrivial half depth actor ((schedule start count).val i)).symm

def paidPriceRecord (start count actor : Nat) : Record.Values count :=
  WithLp.toLp 2 (fun i => paidPriceSample observation nontrivial half depth start count actor i)

theorem actual_paid_price_record (start count actor : Nat) :
    paidPriceRecord observation nontrivial half depth start count actor =
      recordedPrices observation nontrivial half depth start count (raw actor) := by
  ext i
  exact actual_paid_price_sample observation nontrivial half depth start count actor i

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
