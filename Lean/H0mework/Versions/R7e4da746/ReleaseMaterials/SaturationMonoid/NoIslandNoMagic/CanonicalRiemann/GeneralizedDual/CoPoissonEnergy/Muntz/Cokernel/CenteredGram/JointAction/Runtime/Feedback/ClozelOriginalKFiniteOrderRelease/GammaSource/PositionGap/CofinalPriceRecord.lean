import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState Finset
open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot
open scoped BigOperators InnerProductSpace

open private literal_columns_independent from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedLiteralRead
open private raw_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierKFeedback
open private rebuildBirth from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback

namespace Record
export SourceGeneratedFiniteGram.CofinalRecord
  (Values Schedule sample schedule schedule_prior schedule_fresh schedule_read_insert withBirth replay decodeInsert)
end Record

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "R" => burnolDirectRightResolventCLM c
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "price" => FixedFourierKFeedback.price observation nontrivial half depth

private def sourcePrices (start j t : Nat) : ℂ := price (start+j+t)

local notation "source" => sourcePrices observation nontrivial half depth

private theorem original_tail_separates (start cutoff : Nat) :
    LinearIndependent ℂ (fun j : Nat => fun t : Nat => source start j (cutoff+t)) := by
  have changed : (fun j : Nat => fun t : Nat => source start j (cutoff+t)) =
      (fun j : Nat => fun t : Nat => price (start+cutoff+j+t)) := by
    funext j t
    unfold sourcePrices
    congr 1
    omega
  rw [changed]
  exact literal_columns_independent observation nontrivial half depth (start+cutoff)

/-- A source-generated schedule for the fixed Fourier–K reader on the original R tail. -/
def priceSchedule (start count : Nat) : Record.Schedule (source start) count :=
  Record.schedule (source start) (original_tail_separates observation nontrivial half depth start) count

local notation "schedule" => priceSchedule observation nontrivial half depth

def nativePriceAt (field : BurnolL2) (time : Nat) : ℂ :=
  inner ℂ (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)) ((R^time) field)

def recordedPrices (start count : Nat) (field : BurnolL2) : Record.Values count :=
  Record.sample (schedule start count).val (nativePriceAt observation half field)

/-- Enlarging the source inventory preserves its exact original query addresses. -/
theorem actual_price_record_prior (start count : Nat) (field : BurnolL2) (i : Fin count) :
    recordedPrices observation nontrivial half depth start (count+1) field i.castSucc =
      recordedPrices observation nontrivial half depth start count field i := by
  change nativePriceAt observation half field ((schedule start (count+1)).val i.castSucc) =
    nativePriceAt observation half field ((schedule start count).val i)
  simp only [priceSchedule, Record.schedule_prior]

theorem actual_price_record_fresh (start count : Nat) (i : Fin count) :
    (schedule start count).val i < (schedule start (count+1)).val (Fin.last count) :=
  Record.schedule_fresh (source start) (original_tail_separates observation nontrivial half depth start) count i

def decodeRecordedPrices (start count : Nat) (previous : Record.Values count) (latest : ℂ) :
    Record.Values count × ℂ :=
  Record.decodeInsert (source start) (schedule start count).val
    ((schedule start (count+1)).val (Fin.last count)) previous latest

private theorem literal_price_at (ordinal time : Nat) :
    nativePriceAt observation half (raw ordinal) time = price (ordinal+time) := by
  unfold nativePriceAt
  rw [← FixedFourierKFeedback.actual_whole_price observation nontrivial half depth, raw_power, raw_power,
    ← mul_apply_eq_comp, ← pow_add]
  rw [show time+(m+(ordinal+2))=m+(ordinal+time+2) by omega]

private theorem actual_mixture_price (start count : Nat) (a : Record.Values count) (b : ℂ) :
    nativePriceAt observation half
      ((∑ j : Fin count, a j • raw (start+j.val)) + b • raw (start+count)) =
      Record.withBirth (source start) a b := by
  funext time
  simp only [nativePriceAt, map_add, map_smul, map_sum, inner_add_right, inner_smul_right, inner_sum,
    Record.withBirth, Record.replay]
  have old := literal_price_at observation nontrivial half depth
  simp only [nativePriceAt] at old
  simp only [old, sourcePrices]

/-- The same recorded field gives both the retained prices and the one new sample. -/
theorem actual_recorded_price_birth (start count : Nat) (a : Record.Values count) (b : ℂ) :
    let field := (∑ j : Fin count, a j • raw (start+j.val)) + b • raw (start+count)
    let previous := recordedPrices observation nontrivial half depth start count field
    let time := (schedule start (count+1)).val (Fin.last count)
    decodeRecordedPrices observation nontrivial half depth start count previous
      (nativePriceAt observation half field time) = (a,b) := by
  dsimp only [recordedPrices, decodeRecordedPrices]
  rw [actual_mixture_price observation nontrivial half depth start count a b]
  exact Record.schedule_read_insert (source start)
    (original_tail_separates observation nontrivial half depth start) a b

private def toRange (ordinal : Nat) (values : Record.Values (ordinal+1)) :
    PriceGram.Coordinates (range (ordinal+1)) :=
  WithLp.toLp 2 fun i => values ⟨i.val,mem_range.mp i.property⟩

/-- The sparse record writes the same original graph and relation stock from one appended actual price. -/
theorem actual_sparse_price_writeback (start ordinal : Nat) (a : Record.Values (ordinal+1)) (b : ℂ) :
    let field := (∑ j : Fin (ordinal+1), a j • raw (start+j.val)) + b • R (raw (start+ordinal))
    let previous := recordedPrices observation nontrivial half depth start (ordinal+1) field
    let time := (schedule start (ordinal+2)).val (Fin.last (ordinal+1))
    let decoded := decodeRecordedPrices observation nontrivial half depth start (ordinal+1) previous
      (nativePriceAt observation half field time)
    let rebuilt := rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal decoded.1,decoded.2)
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal a,b)
    (advanceWide c observation.mathlibZero rebuilt.1,
      advanceStock c (modelInventory observation nontrivial half rebuilt.2)) =
      (next.1, modelInventory observation nontrivial half next.2) := by
  have written : R (raw (start+ordinal)) = raw (start+(ordinal+1)) := by
    rw [← Nat.add_assoc, OriginalKCombFirstFullSourceDynamics.raw_successor,
      OriginalKCombCofinalRAction.original_R_direct]
    rfl
  dsimp only
  rw [written, actual_recorded_price_birth observation nontrivial half depth start (ordinal+1) a b]
  have native := actual_born_price_writeback observation nontrivial half depth start ordinal (toRange ordinal a) b
  have next := native.2
  rw [native.1] at next
  exact next

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
