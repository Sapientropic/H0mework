import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CandidateRead

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe

open BurnolPhysicalState Finset RootInquiryCompletion SourceNativeInquiryRuntime
open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot
open scoped BigOperators

open private sourcePrices original_tail_separates literal_price_at actual_mixture_price toRange from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback
open private candidateStart candidateEpoch bounded_token_at from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CandidateRead
open private nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape

namespace Fit
export SourceGeneratedFiniteGram.CofinalRecord (columns exists_birth_pivot pivotTime schedule_last)
export SourceGeneratedFiniteGram.Projection (coefficients)
end Fit

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => Native.raw observation nontrivial half depth
local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "source" => sourcePrices observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "cut" => sourceCutoff observation nontrivial half depth
local notation "length" => residualFuel observation nontrivial half depth
local notation "Offsets" => CandidateOffsets observation nontrivial half depth
local notation "time" => candidateTime observation nontrivial half depth
local notation "paid" => paidPriceRecord observation nontrivial half depth
local notation "paidMixture" => paidMixtureRecord observation nontrivial half depth
local notation "newPrice" => candidatePrice observation nontrivial half depth

private theorem paid_as_sample (start count actor : Nat) :
    paid start count (start+actor) = Record.sample (schedule start count).val (source start actor) := by
  ext i
  calc
    _ = (recordedPrices observation nontrivial half depth start count (raw (start+actor))) i :=
      actual_paid_price_sample observation nontrivial half depth start count (start+actor) i
    _ = _ := literal_price_at observation nontrivial half depth (start+actor) ((schedule start count).val i)

/-- The old fit is solved from the paid records of the old actors and the newborn actor. -/
def paidOldFit (start count : Nat) : Record.Values count :=
  Fit.coefficients (fun j : Fin count => paid start count (start+j.val)) (paid start count (start+count))

theorem actual_paid_old_fit (start count : Nat) :
    paidOldFit observation nontrivial half depth start count =
      Sparse.priorFit (source start) (schedule start count).val := by
  have columns : (fun j : Fin count => paid start count (start+j.val)) =
      Fit.columns (source start) (schedule start count).val := by
    funext j
    exact paid_as_sample observation nontrivial half depth start count j.val
  unfold paidOldFit SourceGeneratedFiniteGram.CofinalRecord.priorFit
  rw [columns,paid_as_sample]

def candidateMixture (start count : Nat) (offset : Offsets start count) (a : Record.Values count) (b : ℂ) : ℂ :=
  (∑ j : Fin count, a j*newPrice start count j.castSucc offset)+b*newPrice start count (Fin.last count) offset

theorem actual_candidate_mixture (start count : Nat) (offset : Offsets start count)
    (a : Record.Values count) (b : ℂ) :
    candidateMixture observation nontrivial half depth start count offset a b =
      Record.withBirth (source start) a b (time start count offset) := by
  simp only [candidateMixture,actual_candidate_price,Record.withBirth,Record.replay,Fin.val_castSucc,Fin.val_last]

def paidCandidateResidual (start count : Nat) (offset : Offsets start count) : ℂ :=
  candidateMixture observation nontrivial half depth start count offset
    (-paidOldFit observation nontrivial half depth start count) 1

local notation "residual" => paidCandidateResidual observation nontrivial half depth

theorem actual_paid_candidate_residual (start count : Nat) (offset : Offsets start count) :
    residual start count offset =
      Sparse.birthResidual (source start) (schedule start count).val (time start count offset) := by
  rw [paidCandidateResidual,actual_candidate_mixture,actual_paid_old_fit]
  simp only [Record.withBirth,Record.replay,Sparse.birthResidual,WithLp.ofLp_neg,Pi.neg_apply,
    neg_mul,sum_neg_distrib,one_mul,sub_eq_add_neg,add_comm]

private def paidLive (start count offset : Nat) : Prop :=
  ∃ within : offset < length start count (cut start count)+1,
    residual start count ⟨offset,within⟩ ≠ 0

private theorem exists_paid_pivot (start count : Nat) :
    ∃ offset, paidLive observation nontrivial half depth start count offset := by
  obtain ⟨offset,_,within,live⟩ := actual_fitted_window_live observation nontrivial half depth start count (cut start count)
  refine ⟨offset,Nat.lt_succ_of_le within,?_⟩
  rw [actual_paid_candidate_residual]
  exact live

/-- Select the first live residual by reading the actual paid candidates within the generated bound. -/
def paidPivot (start count : Nat) : Offsets start count := by
  classical
  let existsLive := exists_paid_pivot observation nontrivial half depth start count
  exact ⟨Nat.find existsLive,(Nat.find_spec existsLive).choose⟩

theorem actual_paid_pivot_live (start count : Nat) :
    residual start count (paidPivot observation nontrivial half depth start count) ≠ 0 := by
  classical
  exact (Nat.find_spec (exists_paid_pivot observation nontrivial half depth start count)).choose_spec

local notation "chosen" => paidPivot observation nontrivial half depth

private theorem originalResidualExists (start count : Nat) :
    ∃ offset : Nat, Sparse.birthResidual (source start) (schedule start count).val (cut start count+offset) ≠ 0 :=
  Fit.exists_birth_pivot (source start) (schedule start count).val (cut start count)
    (original_tail_separates observation nontrivial half depth start (cut start count))

private theorem original_latest_time (start count : Nat) :
    (schedule start (count+1)).val (Fin.last count) =
      cut start count+Nat.find (originalResidualExists observation nontrivial half depth start count) := by
  classical
  unfold priceSchedule
  rw [Fit.schedule_last]
  rfl

/-- The least live paid candidate recovers the original first address inside the source bound. -/
theorem actual_paid_pivot_time (start count : Nat) :
    time start count (chosen start count) = (schedule start (count+1)).val (Fin.last count) := by
  classical
  let has := originalResidualExists observation nontrivial half depth start count
  let k := Nat.find has
  have original : (schedule start (count+1)).val (Fin.last count) = cut start count+k :=
    original_latest_time observation nontrivial half depth start count
  have within : k ≤ length start count (cut start count) := by
    have certifiedBound := actual_original_pivot_bound observation nontrivial half depth start count
    rw [original] at certifiedBound
    exact Nat.le_of_add_le_add_left certifiedBound
  let i : Offsets start count := ⟨k,Nat.lt_succ_of_le within⟩
  have iLive : residual start count i ≠ 0 := by
    rw [actual_paid_candidate_residual]
    exact Nat.find_spec has
  have selected_le : (chosen start count).val ≤ k :=
    Nat.find_min' (exists_paid_pivot observation nontrivial half depth start count) ⟨i.isLt,iLive⟩
  have original_le : k ≤ (chosen start count).val := by
    have live := actual_paid_pivot_live observation nontrivial half depth start count
    rw [actual_paid_candidate_residual] at live
    exact Nat.find_min' has live
  change cut start count+(chosen start count).val = _
  rw [original,le_antisymm selected_le original_le]

/-- Selection recovers the full original dependent token of the appended row for each actor. -/
theorem actual_selected_occurrence (start count : Nat) (actor : Fin (count+1)) :
    candidateOccurrence observation nontrivial half depth start count actor (chosen start count) =
      tapeOccurrence observation nontrivial half depth start count actor (Fin.last count) := by
  have same : candidateStart observation nontrivial half depth start count actor (chosen start count) =
      sampleAdmissionTick observation nontrivial half depth start count actor (Fin.last count) := by
    change Tape.index factory initial cfg language
        (start+actor.val+time start count (chosen start count)-1+1) =
      Tape.index factory initial cfg language
        (start+actor.val+(schedule start (count+1)).val (Fin.last count)-1+1)
    rw [actual_paid_pivot_time]
  rw [candidateOccurrence,bounded_token_at,actual_tape_occurrence,same]

private theorem actual_candidate_latest (start count : Nat) (a : Record.Values count) (b : ℂ) :
    candidateMixture observation nontrivial half depth start count (chosen start count) a b =
      (paidMixture start count (count+1) a b) (Fin.last count) := by
  rw [actual_candidate_mixture,actual_paid_pivot_time,actual_paid_mixture_record]
  exact (congrFun (actual_mixture_price observation nontrivial half depth start count a b)
    ((schedule start (count+1)).val (Fin.last count))).symm

/-- The selected actual paid row drives the original sparse inverse and both canonical inventory writes. -/
theorem actual_selected_paid_writeback (start ordinal : Nat) (a : Record.Values (ordinal+1)) (b : ℂ) :
    let count := ordinal+1
    let previous := paidMixture start count count a b
    let latest := candidateMixture observation nontrivial half depth start count (chosen start count) a b
    let decoded := decodeRecordedPrices observation nontrivial half depth start count previous latest
    let rebuilt := rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal decoded.1,decoded.2)
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal a,b)
    (advanceWide c observation.mathlibZero rebuilt.1,
      advanceStock c (modelInventory observation nontrivial half rebuilt.2)) =
      (next.1, modelInventory observation nontrivial half next.2) := by
  dsimp only
  rw [actual_candidate_latest]
  exact actual_paid_price_writeback observation nontrivial half depth start ordinal a b

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
