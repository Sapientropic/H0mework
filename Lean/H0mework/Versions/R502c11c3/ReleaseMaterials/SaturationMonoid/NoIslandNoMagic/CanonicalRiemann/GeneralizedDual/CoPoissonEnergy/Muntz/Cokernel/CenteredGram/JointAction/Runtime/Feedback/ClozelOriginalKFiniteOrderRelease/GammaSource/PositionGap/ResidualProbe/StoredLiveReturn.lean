import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.NextLiveWindow
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CountedTateReturn

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.StoredLiveReturn

open BurnolPhysicalState BurnolPhysicalState.OriginalPaPhysicalGreen
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private packet_whole_at from
  H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit
open private betaRead from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth
local notation "β" => betaRead observation half
local notation "M" => burnolTateReciprocalL2.comp burnolMobiusSourceL2
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "packet" => Native.packet observation nontrivial half depth
local notation "Packet" => PacketFit.Packet
local notation "whole" => PacketFit.packetWhole

def windowFuel (ordinal : Nat) : Nat := NextLiveWindow.fuel c β (raw ordinal) (raw (ordinal + 1))
def threshold (ordinal : Nat) : ℝ := NextLiveWindow.visibleFloor c β (raw ordinal) (raw (ordinal + 1))

local notation "limit" => windowFuel observation nontrivial half depth
local notation "floor" => threshold observation nontrivial half depth

/-- Start with the original paid admission, then extend it by the finite number of actual successors. -/
def stored (ordinal : Nat) : Vector Packet (limit ordinal + 1) :=
  PacketFit.Table.acquire factory initial cfg language (ordinal + 2) (limit ordinal)

local notation "table" => stored observation nontrivial half depth

private theorem stored_at (ordinal : Nat) (index : Fin (limit ordinal + 1)) :
    (table ordinal).get index = packet (ordinal + 1 + index.val) := by
  have paid := PacketFit.Table.acquire_at factory initial cfg language (ordinal + 2) (limit ordinal) index
  have address : ordinal + 2 + index.val = (ordinal + 1 + index.val) + 1 := by omega
  exact paid.trans (congrArg (PacketFit.Table.packetAt factory initial cfg language) address)

def candidateOrdinal (ordinal : Nat) (index : Fin (limit ordinal)) : Nat := ordinal + 2 + index.val

local notation "candidate" => candidateOrdinal observation nontrivial half depth

private def tablePair {n : Nat} (history : Vector Packet (n + 1)) (index : Fin n) : Packet × Packet :=
  (history.get index.castSucc, history.get index.succ)

def packetPair (ordinal : Nat) (index : Fin (limit ordinal)) : Packet × Packet :=
  tablePair (table ordinal) index

local notation "pairAt" => packetPair observation nontrivial half depth

private theorem actual_pair (ordinal : Nat) (index : Fin (limit ordinal)) :
    pairAt ordinal index = (packet (ordinal + 1 + index.val), packet (candidate ordinal index)) := by
  apply Prod.ext
  · exact stored_at observation nontrivial half depth ordinal index.castSucc
  · have paid := stored_at observation nontrivial half depth ordinal index.succ
    have address : ordinal + 1 + index.succ.val = candidate ordinal index := by
      unfold candidateOrdinal
      simp only [Fin.val_succ]
      omega
    exact paid.trans (congrArg packet address)

/-- The two retained packets are consecutive in the original native write, with their dependent data intact. -/
theorem stored_native_successor (ordinal : Nat) (index : Fin (limit ordinal)) :
    PacketFit.Table.nextPacket factory (pairAt ordinal index).1 = (pairAt ordinal index).2 := by
  rw [actual_pair observation nontrivial half depth ordinal index]
  change PacketFit.Table.nextPacket factory
      (PacketFit.Table.packetAt factory initial cfg language (ordinal + 1 + index.val + 1)) =
    PacketFit.Table.packetAt factory initial cfg language (candidate ordinal index + 1)
  rw [PacketFit.Table.next_packetAt]
  apply congrArg (PacketFit.Table.packetAt factory initial cfg language)
  unfold candidateOrdinal
  omega

private theorem whole_at (ordinal : Nat) : whole (packet ordinal) = raw (ordinal + 1) :=
  (packet_whole_at observation nontrivial half depth ordinal).trans
    (Native.calculated_target_raw_successor observation nontrivial half depth ordinal)

/-- The actual two complete rows are read together before subtracting any source contribution. -/
theorem actual_whole_pair (ordinal : Nat) (index : Fin (limit ordinal)) :
    (whole (pairAt ordinal index).1, whole (pairAt ordinal index).2) =
      (raw (candidate ordinal index), raw (candidate ordinal index + 1)) := by
  let project (input : Packet × Packet) : BurnolL2 × BurnolL2 :=
    (whole input.1, whole input.2)
  have address : ordinal + 1 + index.val + 1 = candidate ordinal index := by
    unfold candidateOrdinal
    omega
  have before : whole (packet (ordinal + 1 + index.val)) = raw (candidate ordinal index) :=
    (whole_at observation nontrivial half depth (ordinal + 1 + index.val)).trans (congrArg raw address)
  have after : whole (packet (candidate ordinal index)) = raw (candidate ordinal index + 1) :=
    whole_at observation nontrivial half depth (candidate ordinal index)
  have source : project (pairAt ordinal index) =
      project (packet (ordinal + 1 + index.val), packet (candidate ordinal index)) :=
    congrArg project (actual_pair observation nontrivial half depth ordinal index)
  have fields := congrArg₂ (fun first second : BurnolL2 => (first, second)) before after
  change project (packet (ordinal + 1 + index.val), packet (candidate ordinal index)) =
    (raw (candidate ordinal index), raw (candidate ordinal index + 1)) at fields
  exact source.trans fields

private def measured (before after : BurnolPaAmbientCarrier) : ℂ :=
  let predicted := sourceVolterraWindow c (M before) +
    burnolPaResolventSourceCoefficient c before •
      M (E (OriginalKDirectRCofinalPaUpdate.sourceWholeUnit observation nontrivial half : BurnolL2))
  inner ℂ (CountedTateReturn.greenTest observation half) (M after - predicted) /
    CountedTateReturn.greenGain observation half

private def pairPrice (pair : Packet × Packet) : ℂ :=
  measured observation nontrivial half (E (whole pair.1)) (E (whole pair.2))

/-- The finite window is tested by the arithmetic Green read computed from its stored actual pair. -/
def storedPrice (ordinal : Nat) (index : Fin (limit ordinal)) : ℂ :=
  pairPrice observation nontrivial half (pairAt ordinal index)

local notation "price" => storedPrice observation nontrivial half depth

private theorem arithmetic_tate (ordinal : Nat) :
    OriginalKDirectRCofinalMobiusSourceAction.actualQueryTate observation nontrivial half depth ordinal =
      M (pa ordinal) := by
  unfold OriginalKDirectRCofinalMobiusSourceAction.actualQueryTate
  rw [OriginalKDirectRCofinalMobiusSourceAction.actual_query_source]
  rfl

private theorem measured_actual (ordinal : Nat) :
    measured observation nontrivial half (pa ordinal) (pa (ordinal + 1)) = fee ordinal := by
  have paid := CountedTateReturn.actual_green_fee observation nontrivial half depth ordinal
  unfold CountedTateReturn.greenRead CountedTateReturn.tateReturn CountedTateReturn.baseTate at paid
  rw [arithmetic_tate observation nontrivial half depth (ordinal + 1),
    arithmetic_tate observation nontrivial half depth ordinal] at paid
  exact paid

theorem stored_price_actual (ordinal : Nat) (index : Fin (limit ordinal)) :
    price ordinal index = fee (candidate ordinal index) := by
  let read (fields : BurnolL2 × BurnolL2) := measured observation nontrivial half (E fields.1) (E fields.2)
  have fields := actual_whole_pair observation nontrivial half depth ordinal index
  change read (whole (pairAt ordinal index).1, whole (pairAt ordinal index).2) = _
  exact (congrArg read fields).trans
    (measured_actual observation nontrivial half depth (candidate ordinal index))

private def eligible (ordinal : Nat) (history : Vector Packet (limit ordinal + 1)) :
    Finset (Fin (limit ordinal)) := by
  classical
  exact Finset.univ.filter (fun index =>
    floor ordinal < ‖pairPrice observation nontrivial half (tablePair history index)‖)

private theorem eligible_nonempty (ordinal : Nat) (live : fee (ordinal + 1) ≠ 0) :
    (eligible observation nontrivial half depth ordinal (table ordinal)).Nonempty := by
  classical
  have window := NextLiveWindow.actual_next_window observation nontrivial half depth ordinal live
  refine window.2.elim ?_
  intro lag witness
  have within : lag ≤ limit ordinal := witness.2.1
  let index : Fin (limit ordinal) := ⟨lag - 1, by have positive := witness.1; omega⟩
  have address : candidate ordinal index = ordinal + 1 + lag := by
    have positive := witness.1
    change ordinal + 2 + (lag - 1) = _
    omega
  refine ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  change floor ordinal < ‖price ordinal index‖
  rw [stored_price_actual, address]
  exact witness.2.2

/-- Select and return the first qualifying pair from a single shared native table. -/
def selected (ordinal : Nat) (live : fee (ordinal + 1) ≠ 0) :
    Fin (limit ordinal) × (Packet × Packet) :=
  let history := table ordinal
  let allowed := eligible observation nontrivial half depth ordinal history
  let index := allowed.min' (eligible_nonempty observation nontrivial half depth ordinal live)
  (index, tablePair history index)

local notation "chosen" => selected observation nontrivial half depth

theorem selected_pair (ordinal : Nat) (live : fee (ordinal + 1) ≠ 0) :
    (chosen ordinal live).2 = pairAt ordinal (chosen ordinal live).1 := rfl

theorem selected_first (ordinal : Nat) (live : fee (ordinal + 1) ≠ 0) :
    floor ordinal < ‖price ordinal (chosen ordinal live).1‖ ∧
      ∀ index < (chosen ordinal live).1, ‖price ordinal index‖ ≤ floor ordinal := by
  classical
  let allowed := eligible observation nontrivial half depth ordinal (table ordinal)
  have inside : (chosen ordinal live).1 ∈ allowed :=
    Finset.min'_mem allowed (eligible_nonempty observation nontrivial half depth ordinal live)
  refine ⟨(Finset.mem_filter.mp inside).2, ?_⟩
  intro index earlier
  apply le_of_not_gt
  intro hit
  have inWindow : index ∈ allowed := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩
  have least : (chosen ordinal live).1 ≤ index := Finset.min'_le allowed index inWindow
  exact (not_lt_of_ge least) earlier

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.StoredLiveReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
