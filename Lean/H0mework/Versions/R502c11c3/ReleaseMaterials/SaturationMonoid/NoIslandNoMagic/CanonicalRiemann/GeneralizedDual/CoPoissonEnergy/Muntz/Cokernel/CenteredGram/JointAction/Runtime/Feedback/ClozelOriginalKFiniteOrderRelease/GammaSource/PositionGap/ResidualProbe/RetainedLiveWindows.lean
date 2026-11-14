import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.StoredLiveReturn

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedLiveWindows

open BurnolPhysicalState SourceOperationScalarInventoryLift

open private nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private tablePair eligible eligible_nonempty stored_at from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.StoredLiveReturn

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "nativeAt" => PacketFit.Table.packetAt factory initial cfg language
local notation "Packet" => PacketFit.Packet
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth
local notation "limit" => StoredLiveReturn.windowFuel observation nontrivial half depth
local notation "floor" => StoredLiveReturn.threshold observation nontrivial half depth
local notation "candidate" => StoredLiveReturn.candidateOrdinal observation nontrivial half depth
local notation "table" => StoredLiveReturn.stored observation nontrivial half depth

variable (origin last : Nat) (history : Vector Packet (last + 1)) (anchor : Fin (last + 1))
local notation "base" => (origin + anchor.val)
local notation "N" => limit base

/-- Only native writes beyond the actual retained prefix are needed for the new bound. -/
def missingTail : Nat := anchor.val + N - last

local notation "extra" => missingTail observation nontrivial half depth origin last anchor
local notation "Count" => (last + extra + 1)

/-- Consume the existing original table directly and append only its missing native suffix. -/
def retained : Vector Packet Count := PacketFit.Table.extend factory history extra

local notation "extended" => retained observation nontrivial half depth origin last history anchor

private def insideWindow (index : Fin (N + 1)) : Fin Count :=
  ⟨anchor.val + index.val, by
    have within := index.isLt
    unfold missingTail
    omega⟩

local notation "absolute" => insideWindow observation nontrivial half depth origin last anchor

private def restrictWindow (rows : Vector Packet Count) : Vector Packet (N + 1) :=
  Vector.ofFn fun index => rows.get (absolute index)

local notation "slice" => restrictWindow observation nontrivial half depth origin last anchor

/-- A retained prefix is tied to the original dependent native addresses. -/
def recorded : Prop :=
  ∀ index : Fin (last + 1), history.get index = nativeAt (origin + 2 + index.val)

variable (owned : recorded observation nontrivial half depth origin last history)
include owned

/-- Every appended packet still uses the exact original dependent admission address. -/
theorem retained_at (index : Fin Count) :
    (extended).get index = nativeAt (origin + 2 + index.val) := by
  have actual (i : Fin (last + 1)) : history.get i = nativeAt (origin + 2 + i.val) := owned i
  exact PacketFit.Table.actual_at_extend
    (W := PairValue OriginalKDirectRCofinalMaterial.C.Value)
    (X := OriginalKDirectRCofinalMaterial.C.Var) (s := ())
    factory initial cfg language (origin + 2) (paid := last) history actual extra index

/-- Restrict the retained table to the exact native window already used by the Green selector. -/
theorem actual_slice : slice extended = table base := by
  apply Vector.ext
  intro i within
  let index : Fin (N + 1) := ⟨i, within⟩
  change (Vector.ofFn fun j : Fin (N + 1) => (extended).get (absolute j))[i] = (table base)[i]
  rw [Vector.getElem_ofFn]
  change (extended).get (absolute index) = (table base).get index
  have address : origin + 2 + (absolute index).val = (base + 1 + index.val) + 1 := by
    change origin + 2 + (anchor.val + index.val) = _
    omega
  have appended := retained_at observation nontrivial half depth origin last history anchor owned (absolute index)
  have paid : (table base).get index = nativeAt ((base + 1 + index.val) + 1) :=
    stored_at observation nontrivial half depth base index
  exact (appended.trans (congrArg nativeAt address)).trans paid.symm

theorem old_packet_retained (index : Fin (last + 1)) :
    (extended).get ⟨index.val, by have within := index.isLt; omega⟩ = history.get index :=
  (retained_at observation nontrivial half depth origin last history anchor owned _).trans (owned index).symm

private theorem hit_exists (live : fee (base + 1) ≠ 0) :
    (eligible observation nontrivial half depth base (slice extended)).Nonempty := by
  rw [actual_slice observation nontrivial half depth origin last history anchor owned]
  exact eligible_nonempty observation nontrivial half depth base live

private def pick (live : fee (base + 1) ≠ 0) : Fin N :=
  (eligible observation nontrivial half depth base (slice extended)).min'
    (hit_exists observation nontrivial half depth origin last history anchor owned live)

local notation "chosen" => pick observation nontrivial half depth origin last history anchor owned

/-- Return the same extended table, a strictly later cursor, and the two packets of its selected write. -/
def advance (live : fee (base + 1) ≠ 0) : Vector Packet Count × (Fin Count × (Packet × Packet)) :=
  let rows := extended
  let window := slice rows
  let index := (eligible observation nontrivial half depth base window).min'
    (hit_exists observation nontrivial half depth origin last history anchor owned live)
  (rows, absolute index.succ, tablePair window index)

local notation "moved" => advance observation nontrivial half depth origin last history anchor owned

private theorem actual_pick (live : fee (base + 1) ≠ 0) :
    chosen live = (StoredLiveReturn.selected observation nontrivial half depth base live).1 := by
  let new := eligible observation nontrivial half depth base (slice extended)
  let old := eligible observation nontrivial half depth base (table base)
  have same : new = old := congrArg (eligible observation nontrivial half depth base)
    (actual_slice observation nontrivial half depth origin last history anchor owned)
  have newMem : chosen live ∈ new :=
    Finset.min'_mem new (hit_exists observation nontrivial half depth origin last history anchor owned live)
  have oldMem : (StoredLiveReturn.selected observation nontrivial half depth base live).1 ∈ old :=
    Finset.min'_mem old (eligible_nonempty observation nontrivial half depth base live)
  exact le_antisymm (Finset.min'_le new _ (same.symm ▸ oldMem))
    (Finset.min'_le old _ (same ▸ newMem))

/-- The next returned cursor satisfies the same paid contract and keeps the exact retained admissions. -/
theorem ready_again (live : fee (base + 1) ≠ 0) :
    recorded observation nontrivial half depth origin (last + extra) (moved live).1 ∧
    anchor.val < (moved live).2.1.val ∧ fee (origin + 1 + (moved live).2.1.val) ≠ 0 := by
  refine ⟨retained_at observation nontrivial half depth origin last history anchor owned, ?_, ?_⟩
  · change anchor.val < anchor.val + ((chosen live).val + 1)
    omega
  · intro erased
    have address : origin + 1 + (moved live).2.1.val = candidate base (chosen live) := by
      change origin + 1 + (anchor.val + ((chosen live).val + 1)) =
        origin + anchor.val + 2 + (chosen live).val
      omega
    have certified := (StoredLiveReturn.selected_first observation nontrivial half depth base live).1
    rw [← actual_pick observation nontrivial half depth origin last history anchor owned live,
      StoredLiveReturn.stored_price_actual, ← address, erased, norm_zero] at certified
    exact (not_lt_of_ge
      (NextLiveWindow.actual_next_window observation nontrivial half depth base live).1.le) certified

theorem advanced_cursor_packet (live : fee (base + 1) ≠ 0) :
    (moved live).2.2.2 = (moved live).1.get (moved live).2.1 := by
  change (slice extended).get (chosen live).succ =
    (extended).get (absolute (chosen live).succ)
  change (Vector.ofFn fun index : Fin (N + 1) => (extended).get (absolute index))[(chosen live).succ.val] = _
  rw [Vector.getElem_ofFn]

/-- Both packets of the continued write are the original adjacent stored admissions. -/
theorem advanced_native_write (live : fee (base + 1) ≠ 0) :
    PacketFit.Table.nextPacket factory (moved live).2.2.1 = (moved live).2.2.2 := by
  have same := actual_slice observation nontrivial half depth origin last history anchor owned
  have row : (moved live).2.2 =
      StoredLiveReturn.packetPair observation nontrivial half depth base (chosen live) :=
    congrArg (fun rows : Vector Packet (N + 1) => tablePair rows (chosen live)) same
  change PacketFit.Table.nextPacket factory ((moved live).2.2).1 = ((moved live).2.2).2
  rw [row]
  exact StoredLiveReturn.stored_native_successor observation nontrivial half depth base (chosen live)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.RetainedLiveWindows
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
