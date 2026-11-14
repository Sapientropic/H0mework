import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Timeline
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaidContinuation

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PacketFit

open BurnolPhysicalState SourceOperationEffects SourceOperationScalarInventoryLift
open RootInquiryCompletion SourceNativeInquiryRuntime

open private nativeLanguage from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private scheduled_time_pos paidAt materialWhole material_whole_is_target from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativePrice
open private lastOldTime old_row_le_last retainedOrdinal from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaidContinuation
open private candidateEpoch candidate_time_pos bounded_token_at paid_candidate_eq from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CandidateRead

namespace Table
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions (packetAt)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions.Timeline
  (acquire acquire_at extend actual_at_extend nextPacket next_packetAt)
end Table

abbrev Packet :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions.Timeline.Packet (W := PairValue OriginalKDirectRCofinalMaterial.C.Value)
    (X := OriginalKDirectRCofinalMaterial.C.Var) (s := ())

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

/-- Evaluate all four original branches on the material of this retained packet. -/
def packetWhole (native : Packet) : BurnolL2 :=
  let material := Native.actualMaterial native.2.1.1 native.2.2.1
  let branches := Native.collapseValue native.1 (material.state.1.eval material.environment)
  (branches.1.1+branches.1.2)+(branches.2.1+branches.2.2)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "packet" => Native.packet observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "cut" => sourceCutoff observation nontrivial half depth
local notation "Offsets" => CandidateOffsets observation nontrivial half depth
local notation "time" => candidateTime observation nontrivial half depth
local notation "epoch" => candidateEpoch observation nontrivial half depth

def packetPrice (native : Packet) : ℂ :=
  reader c (OriginalKCombCofinalPaAction.Q (packetWhole native) : BurnolL2)

private theorem packet_whole_at (ordinal : Nat) :
    packetWhole (packet ordinal) = Native.calculatedTargetRaw observation nontrivial half depth ordinal := by
  change materialWhole observation nontrivial half depth ordinal
    (paidAt observation nontrivial half depth ordinal) = _
  exact material_whole_is_target observation nontrivial half depth ordinal

def preparationSteps (start count : Nat) : Nat :=
  count+lastOldTime observation nontrivial half depth start count-1

local notation "prepared" => preparationSteps observation nontrivial half depth

/-- The old fit's actual admissions are kept in one consecutive cofinal prefix. -/
def preparedPackets (start count : Nat) : Vector Packet (prepared start count+1) :=
  Table.acquire factory initial cfg language (start+1) (prepared start count)

theorem prepared_packet_at (start count : Nat) (i : Fin (prepared start count+1)) :
    (preparedPackets observation nontrivial half depth start count).get i = packet (start+i.val) := by
  have original := Table.acquire_at factory initial cfg language (start+1) (prepared start count) i
  have address : start+1+i.val = (start+i.val)+1 := by omega
  exact original.trans (congrArg (Table.packetAt factory initial cfg language) address)

private def oldAddress (start count : Nat) (actor : Fin (count+1)) (row : Fin count) :
    Fin (prepared start count+1) := by
  refine ⟨actor.val+(schedule start count).val row-1,Nat.lt_succ_of_le ?_⟩
  have actorBound := Nat.le_of_lt_succ actor.isLt
  have rowBound := old_row_le_last observation nontrivial half depth start count row
  unfold preparationSteps
  omega

private def oldColumn (start count : Nat) (table : Vector Packet (prepared start count+1))
    (actor : Fin (count+1)) : Record.Values count :=
  WithLp.toLp 2 (fun row => packetPrice observation half (table.get
    (oldAddress observation nontrivial half depth start count actor row)))

theorem old_packet_at (start count : Nat) (actor : Fin (count+1)) (row : Fin count) :
    (preparedPackets observation nontrivial half depth start count).get
      (oldAddress observation nontrivial half depth start count actor row) =
      packet (retainedOrdinal observation nontrivial half depth start count actor row) := by
  have original := prepared_packet_at observation nontrivial half depth start count
    (oldAddress observation nontrivial half depth start count actor row)
  have positive := scheduled_time_pos observation nontrivial half depth start count row
  have address : start+(oldAddress observation nontrivial half depth start count actor row).val =
      retainedOrdinal observation nontrivial half depth start count actor row := by
    change start+(actor.val+(schedule start count).val row-1) =
      start+actor.val+(schedule start count).val row-1
    omega
  exact original.trans (congrArg packet address)

private theorem old_column_actual (start count : Nat) (actor : Fin (count+1)) :
    oldColumn observation nontrivial half depth start count
        (preparedPackets observation nontrivial half depth start count) actor =
      paidPriceRecord observation nontrivial half depth start count (start+actor.val) := by
  apply congrArg (WithLp.toLp 2)
  funext row
  let ordinal := retainedOrdinal observation nontrivial half depth start count actor row
  let read (v : BurnolL2) := reader c (OriginalKCombCofinalPaAction.Q v : BurnolL2)
  have source := (congrArg packetWhole
    (old_packet_at observation nontrivial half depth start count actor row)).trans
      (packet_whole_at observation nontrivial half depth ordinal)
  change read _ = read (materialWhole observation nontrivial half depth ordinal
    (paidAt observation nontrivial half depth ordinal))
  exact congrArg read (source.trans (material_whole_is_target observation nontrivial half depth ordinal).symm)

private def fitFrom (start count : Nat) (table : Vector Packet (prepared start count+1)) : Record.Values count :=
  Fit.coefficients (fun j : Fin count => oldColumn observation nontrivial half depth start count table j.castSucc)
    (oldColumn observation nontrivial half depth start count table (Fin.last count))

theorem prepared_fit_actual (start count : Nat) :
    fitFrom observation nontrivial half depth start count
        (preparedPackets observation nontrivial half depth start count) =
      paidOldFit observation nontrivial half depth start count := by
  have columns := funext (fun j : Fin count => old_column_actual observation nontrivial half depth start count j.castSucc)
  unfold fitFrom paidOldFit
  rw [columns,old_column_actual]
  rfl

private def boundFrom (start count : Nat) (table : Vector Packet (prepared start count+1)) : Nat :=
  cut start count+
    probeFuel observation half (probeBase observation start (cut start count)) count
      (Fin.snoc (fun j => -fitFrom observation nontrivial half depth start count table j) 1)
      (‖xiOpening observation half‖/4)

private theorem preparation_within (start count : Nat) (table : Vector Packet (prepared start count+1)) :
    prepared start count ≤ count+boundFrom observation nontrivial half depth start count table := by
  have earlier : lastOldTime observation nontrivial half depth start count ≤ cut start count := Nat.sub_le _ _
  have later : cut start count ≤ boundFrom observation nontrivial half depth start count table := Nat.le_add_right _ _
  unfold preparationSteps
  omega

/-- The retained old fit sets the horizon; its last paid packet starts the extension. -/
def boundedPackets (start count : Nat) : Σ latest : Nat, Vector Packet (count+latest+1) :=
  let table := preparedPackets observation nontrivial half depth start count
  let latest := boundFrom observation nontrivial half depth start count table
  let within := preparation_within observation nontrivial half depth start count table
  ⟨latest, (Table.extend factory table (count+latest-prepared start count)).cast (by omega)⟩

local notation "bounded" => boundedPackets observation nontrivial half depth

theorem bounded_latest_actual (start count : Nat) :
    (bounded start count).1 = paidLatestTime observation nontrivial half depth start count := by
  simp only [boundedPackets,boundFrom,paidLatestTime,prepared_fit_actual]

theorem bounded_packet_at (start count : Nat) (i : Fin (count+(bounded start count).1+1)) :
    (bounded start count).2.get i = packet (start+i.val) := by
  let held := preparedPackets observation nontrivial half depth start count
  let latest := boundFrom observation nontrivial half depth start count held
  have within := preparation_within observation nontrivial half depth start count held
  let selected := i.cast (show count+(bounded start count).1+1 =
      prepared start count+(count+latest-prepared start count)+1 from by
    change count+latest+1 = _
    omega)
  have old (j : Fin (prepared start count+1)) : held.get j =
      Table.packetAt factory initial cfg language (start+1+j.val) := by
    have address : (start+j.val)+1 = start+1+j.val := by omega
    exact (prepared_packet_at observation nontrivial half depth start count j).trans
      (congrArg (Table.packetAt factory initial cfg language) address)
  have now := Table.actual_at_extend factory initial cfg language (start+1) held old
    (count+latest-prepared start count) selected
  have address : start+1+i.val = (start+i.val)+1 := by omega
  exact now.trans (congrArg (Table.packetAt factory initial cfg language) address)

private def candidateAddress (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    Fin (count+(bounded start count).1) := by
  refine ⟨actor.val+time start count offset-1,?_⟩
  rw [bounded_latest_actual,actual_paid_latest_time]
  have actorWithin := Nat.le_of_lt_succ actor.isLt
  have candidateWithin : time start count offset ≤ latestTime observation nontrivial half depth start count :=
    Nat.add_le_add_left (Nat.le_of_lt_succ offset.isLt) (cut start count)
  have positive := candidate_time_pos observation nontrivial half depth start count offset
  omega

def candidatePackets (start count : Nat) : Fin (count+1) → Offsets start count → Packet × Packet :=
  let table := (bounded start count).2
  fun actor offset =>
    let i := candidateAddress observation nontrivial half depth start count actor offset
    (table.get i.castSucc,table.get i.succ)

theorem actual_candidate_packets (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    candidatePackets observation nontrivial half depth start count actor offset =
      (packet (epoch start count actor offset),packet (epoch start count actor offset+1)) := by
  let i := candidateAddress observation nontrivial half depth start count actor offset
  have positive := candidate_time_pos observation nontrivial half depth start count offset
  have address : start+i.val = epoch start count actor offset := by
    change start+(actor.val+time start count offset-1) = start+actor.val+time start count offset-1
    omega
  refine Prod.ext ((bounded_packet_at observation nontrivial half depth start count i.castSucc).trans
    (congrArg packet address)) ?_
  exact (bounded_packet_at observation nontrivial half depth start count i.succ).trans
    (congrArg packet (by rw [Fin.val_succ,← Nat.add_assoc,address]))

theorem candidate_price_from_packets (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    packetPrice observation half (candidatePackets observation nontrivial half depth start count actor offset).1 =
      candidatePrice observation nontrivial half depth start count actor offset := by
  let ordinal := epoch start count actor offset
  let read (v : BurnolL2) := reader c (OriginalKCombCofinalPaAction.Q v : BurnolL2)
  have same : (candidatePackets observation nontrivial half depth start count actor offset).1 =
      packet ordinal :=
    congrArg Prod.fst (actual_candidate_packets observation nontrivial half depth start count actor offset)
  have whole := (congrArg packetWhole same).trans (packet_whole_at observation nontrivial half depth ordinal)
  unfold candidatePrice
  rw [paid_candidate_eq]
  exact congrArg read (whole.trans (material_whole_is_target observation nontrivial half depth ordinal).symm)

/-- The exact packet produces the same born admission that the canonical next consumes. -/
theorem candidate_born_from_packets (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    let both := candidatePackets observation nontrivial half depth start count actor offset
    (candidateOccurrence observation nontrivial half depth start count actor offset).1.engine.node =
      .active (Tape.admissionPresentation factory both.1) ∧
    Table.nextPacket factory both.1 = both.2 ∧
      (candidateSuccessor observation nontrivial half depth start count actor offset).1.engine.node =
        .active (Tape.admissionPresentation factory both.2) := by
  dsimp only
  rw [actual_candidate_packets]
  refine ⟨(candidateAdmission observation nontrivial half depth start count actor offset).2.down,
    Table.next_packetAt factory initial cfg language (epoch start count actor offset+1),?_⟩
  unfold candidateSuccessor
  rw [bounded_token_at]
  exact Tape.actual_index factory initial cfg language (epoch start count actor offset+2)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PacketFit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
