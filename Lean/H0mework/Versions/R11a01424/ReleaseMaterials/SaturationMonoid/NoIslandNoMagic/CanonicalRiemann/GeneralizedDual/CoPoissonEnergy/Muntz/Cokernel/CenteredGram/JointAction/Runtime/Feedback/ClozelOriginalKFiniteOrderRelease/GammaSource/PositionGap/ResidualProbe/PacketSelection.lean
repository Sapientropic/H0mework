import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PacketSelection

open BurnolPhysicalState Finset RootInquiryCompletion SourceNativeInquiryRuntime
open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot
open PacketFit
open private toRange from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback
open private oldColumn old_column_actual fitFrom preparation_within candidateAddress from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit
open private exists_paid_pivot from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaidPivot

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "factory" => Native.factory observation nontrivial half
local notation "prepared" => preparationSteps observation nontrivial half depth
local notation "cut" => sourceCutoff observation nontrivial half depth
local notation "bounded" => boundedPackets observation nontrivial half depth
local notation "Offsets" => CandidateOffsets observation nontrivial half depth
local notation "original" => paidPivot observation nontrivial half depth

private abbrev Reads (start count : Nat) := Fin (count+1) → Offsets start count → Packet × Packet

private def acquired (start count : Nat) :
    (Fin (count+1) → Record.Values count) × Record.Values count × Reads observation nontrivial half depth start count :=
  let held := preparedPackets observation nontrivial half depth start count
  let fit := fitFrom observation nontrivial half depth start count held
  let latest := cut start count+
    probeFuel observation half (probeBase observation start (cut start count)) count
      (Fin.snoc (fun j => -fit j) 1) (‖xiOpening observation half‖/4)
  let within : prepared start count ≤ count+latest :=
    preparation_within observation nontrivial half depth start count held
  let table : Vector Packet (count+(bounded start count).1+1) :=
    (Table.extend factory held (count+latest-prepared start count)).cast (by
      change prepared start count+(count+latest-prepared start count)+1 = count+latest+1
      omega)
  (oldColumn observation nontrivial half depth start count held,fit,fun actor offset =>
    let i := candidateAddress observation nontrivial half depth start count actor offset
    (table.get i.castSucc,table.get i.succ))

local notation "batch" => acquired observation nontrivial half depth

private theorem acquired_reads (start count : Nat) :
    (batch start count).2.2 = candidatePackets observation nontrivial half depth start count := rfl

private theorem acquired_fit (start count : Nat) :
    (batch start count).2.1 = paidOldFit observation nontrivial half depth start count :=
  prepared_fit_actual observation nontrivial half depth start count

private def mix {count : Nat} (row : Fin (count+1) → ℂ) (a : Record.Values count) (b : ℂ) : ℂ :=
  (∑ j : Fin count, a j*row j.castSucc)+b*row (Fin.last count)

private def firstFrom {start count : Nat} (fit : Record.Values count)
    (read : Reads observation nontrivial half depth start count) : Option (Offsets start count) := by
  classical
  exact Fin.find? (fun i => decide (mix (fun actor => packetPrice observation half (read actor i).1) (-fit) 1 ≠ 0))

private theorem acquired_residual (start count : Nat) (offset : Offsets start count) :
    mix (fun actor => packetPrice observation half ((batch start count).2.2 actor offset).1)
        (-(batch start count).2.1) 1 =
      paidCandidateResidual observation nontrivial half depth start count offset := by
  unfold mix paidCandidateResidual candidateMixture
  simp only [acquired_reads,acquired_fit,candidate_price_from_packets]

private theorem earlier_zero (start count : Nat) (offset : Offsets start count)
    (earlier : offset < original start count) :
    paidCandidateResidual observation nontrivial half depth start count offset = 0 := by
  classical
  by_contra live
  have minimal := Nat.find_min' (exists_paid_pivot observation nontrivial half depth start count)
    (m := offset.val) ⟨offset.isLt,live⟩
  exact (Nat.not_le_of_gt earlier) minimal

private theorem first_actual (start count : Nat) :
    firstFrom observation nontrivial half depth (batch start count).2.1 (batch start count).2.2 =
      some (original start count) := by
  classical
  apply Option.mem_def.mp
  simp only [firstFrom,Fin.mem_find?_iff,decide_eq_true_eq,acquired_residual]
  exact ⟨actual_paid_pivot_live observation nontrivial half depth start count,
    fun j before bad => bad (earlier_zero observation nontrivial half depth start count j before)⟩

structure Selection (start count : Nat) where
  offset : Offsets start count
  packets : Fin (count+1) → Packet × Packet
  oldColumns : Fin (count+1) → Record.Values count
  fit : Record.Values count

/-- Scan the residuals of the one retained source batch and return its full selected row. -/
def select (start count : Nat) : Selection observation nontrivial half depth start count :=
  let data := batch start count
  let found := firstFrom observation nontrivial half depth data.2.1 data.2.2
  let address := found.get (Option.isSome_of_eq_some
    (first_actual observation nontrivial half depth start count))
  ⟨address,fun actor => data.2.2 actor address,data.1,data.2.1⟩

theorem selected_offset_actual (start count : Nat) :
    (select observation nontrivial half depth start count).offset = original start count :=
  Option.get_of_eq_some _ (first_actual observation nontrivial half depth start count)

theorem selected_packets_actual (start count : Nat) (actor : Fin (count+1)) :
    (select observation nontrivial half depth start count).packets actor =
      candidatePackets observation nontrivial half depth start count actor (original start count) := by
  change (batch start count).2.2 actor (select observation nontrivial half depth start count).offset = _
  rw [acquired_reads,selected_offset_actual]

/-- The old columns and selected new row come from the same source batch. -/
def selectedRecords (start count : Nat) (a : Record.Values count) (b : ℂ) :
    Record.Values count × ℂ :=
  let chosen := select observation nontrivial half depth start count
  ((∑ j : Fin count, a j • chosen.oldColumns j.castSucc)+b • chosen.oldColumns (Fin.last count),
    mix (fun actor => packetPrice observation half (chosen.packets actor).1) a b)

theorem selected_records_actual (start count : Nat) (a : Record.Values count) (b : ℂ) :
    selectedRecords observation nontrivial half depth start count a b =
      (paidMixtureRecord observation nontrivial half depth start count count a b,
        candidateMixture observation nontrivial half depth start count (original start count) a b) := by
  let chosen := select observation nontrivial half depth start count
  have old : chosen.oldColumns =
      fun actor => paidPriceRecord observation nontrivial half depth start count (start+actor.val) :=
    funext (old_column_actual observation nontrivial half depth start count)
  have latest : (fun actor => packetPrice observation half (chosen.packets actor).1) =
      fun actor => candidatePrice observation nontrivial half depth start count actor (original start count) := by
    funext actor
    change packetPrice observation half ((select observation nontrivial half depth start count).packets actor).1 = _
    rw [selected_packets_actual,candidate_price_from_packets]
  change ((∑ j : Fin count, a j • chosen.oldColumns j.castSucc)+b • chosen.oldColumns (Fin.last count),
    mix (fun actor => packetPrice observation half (chosen.packets actor).1) a b) = _
  rw [old,latest]; rfl

/-- The selected actual packet and its generated born packet retain the exact original occurrences. -/
theorem selected_native_packet (start count : Nat) (actor : Fin (count+1)) :
    let selection := select observation nontrivial half depth start count
    let both := selection.packets actor
    (tapeOccurrence observation nontrivial half depth start count actor (Fin.last count)).1.engine.node =
      .active (Tape.admissionPresentation factory both.1) ∧
    Table.nextPacket factory both.1 = both.2 ∧
    (candidateSuccessor observation nontrivial half depth start count actor selection.offset).1.engine.node =
      .active (Tape.admissionPresentation factory both.2) := by
  dsimp only
  rw [selected_packets_actual,selected_offset_actual,← actual_selected_occurrence]
  exact candidate_born_from_packets observation nontrivial half depth start count actor (original start count)

/-- The selected values enter the original sparse inverse and both existing inventory writes. -/
theorem selected_writeback (start ordinal : Nat) (a : Record.Values (ordinal+1)) (b : ℂ) :
    let count := ordinal+1
    let paid := selectedRecords observation nontrivial half depth start count a b
    let decoded := decodeRecordedPrices observation nontrivial half depth start count paid.1 paid.2
    let rebuilt := rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal decoded.1,decoded.2)
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal a,b)
    (advanceWide c observation.mathlibZero rebuilt.1,
      advanceStock c (modelInventory observation nontrivial half rebuilt.2)) =
      (next.1,modelInventory observation nontrivial half next.2) := by
  dsimp only
  rw [selected_records_actual]
  exact actual_selected_paid_writeback observation nontrivial half depth start ordinal a b

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PacketSelection
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
