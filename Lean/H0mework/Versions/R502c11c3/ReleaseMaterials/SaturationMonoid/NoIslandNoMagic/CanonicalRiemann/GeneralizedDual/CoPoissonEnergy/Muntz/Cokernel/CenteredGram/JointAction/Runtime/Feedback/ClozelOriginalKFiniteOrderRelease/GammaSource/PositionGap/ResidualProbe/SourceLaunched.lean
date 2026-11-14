import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedBornRequest

set_option autoImplicit false
noncomputable section
universe v

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SourceLaunched

open BurnolPhysicalState RootInquiryCompletion SourceNativeInquiryRuntime
open SourceOperationScalarInventoryLift

open private nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private packet_whole_at from
  H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit

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
local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "packetAt" => PacketFit.Table.packetAt factory initial cfg language
local notation "Packet" => PacketFit.Packet
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "whole" => PacketFit.packetWhole

private theorem opening_exists : ∃ base : Nat, fee (base + 1) ≠ 0 := by
  obtain ⟨ordinal, after, paid, _, _⟩ :=
    CountedNativeReentry.literal_return_cofinal observation nontrivial half depth 1
  cases ordinal with
  | zero => omega
  | succ base => exact ⟨base, paid⟩

/-- Least source-paid cursor among the actual consecutive admission pairs starting at packet one. -/
def opening : Nat := open Classical in Nat.find (opening_exists observation nontrivial half depth)

local notation "base" => opening observation nontrivial half depth

private theorem opening_live : fee (base + 1) ≠ 0 :=
  open Classical in Nat.find_spec (opening_exists observation nontrivial half depth)

theorem earlier_silent (index : Nat) (earlier : index < base) : fee (index + 1) = 0 := by
  classical
  by_contra nonzero
  exact (Nat.not_lt_of_ge (Nat.find_min' (opening_exists observation nontrivial half depth) nonzero)) earlier

private def acquired : Vector Packet (base + 2) :=
  PacketFit.Table.acquire factory initial cfg language 1 (base + 1)

local notation "rows" => acquired observation nontrivial half depth
local notation "last" => Fin.last base
local notation "before" => Vector.get rows (Fin.castSucc last)
local notation "after" => Vector.get rows (Fin.succ last)

private def seedTable : Vector Packet (base + 1) :=
  Vector.ofFn fun index => Vector.get rows index.succ

local notation "seed" => seedTable observation nontrivial half depth

private theorem seed_recorded :
    RetainedLiveWindows.recorded observation nontrivial half depth 0 base seed := by
  intro index
  have stored := PacketFit.Table.acquire_at factory initial cfg language 1 (base + 1) index.succ
  have address : 1 + index.succ.val = 0 + 2 + index.val := by simp only [Fin.val_succ]; omega
  change (Vector.ofFn fun i : Fin (base + 1) => Vector.get rows i.succ)[index.val] = _
  rw [Vector.getElem_ofFn]
  exact stored.trans (congrArg packetAt address)

/-- The original two acquired packets give both fees of the opening write. -/
theorem opening_recovery :
    JointFeeInverse.recover observation nontrivial half
      (JointFeeInverse.effect observation nontrivial half (whole before) (whole after)) =
      (OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (base + 1), fee (base + 1)) := by
  have firstAddress : 1 + Fin.val (Fin.castSucc last) = base + 1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    omega
  have secondAddress : 1 + Fin.val (Fin.succ last) = (base + 1) + 1 := by
    simp only [Fin.val_succ, Fin.val_last]
    omega
  have first : before = packetAt (base + 1) :=
    (PacketFit.Table.acquire_at factory initial cfg language 1 (base + 1) (Fin.castSucc last)).trans
      (congrArg packetAt firstAddress)
  have second : after = packetAt ((base + 1) + 1) :=
    (PacketFit.Table.acquire_at factory initial cfg language 1 (base + 1) (Fin.succ last)).trans
      (congrArg packetAt secondAddress)
  rw [first, second]
  change JointFeeInverse.recover observation nontrivial half
    (JointFeeInverse.effect observation nontrivial half
      (whole (Native.packet observation nontrivial half depth base))
      (whole (Native.packet observation nontrivial half depth (base + 1)))) = _
  have beforeRaw := (packet_whole_at observation nontrivial half depth base).trans
    (Native.calculated_target_raw_successor observation nontrivial half depth base)
  have afterRaw := (packet_whole_at observation nontrivial half depth (base + 1)).trans
    (Native.calculated_target_raw_successor observation nontrivial half depth (base + 1))
  rw [beforeRaw, afterRaw]
  exact JointFeeInverse.actual_recovery observation nontrivial half depth (base + 1)

private theorem seed_live : fee (0 + Fin.val last + 1) ≠ 0 := by
  simpa only [Nat.zero_add, Fin.val_last] using opening_live observation nontrivial half depth

private abbrev LaunchAt (Result : Sort v) :=
  type_of% (SelectedBornRequest.consumeSelectedBirth observation nontrivial half depth 0 base seed last
    (seed_recorded observation nontrivial half depth) (seed_live observation nontrivial half depth)
    (Result := Result) ((runtime).run 0))

/-- Start the existing sealed history and born-request consumer from the original root and source-paid initial inventory. -/
def launch {Result : Sort v} : LaunchAt observation nontrivial half depth Result :=
  SelectedBornRequest.consumeSelectedBirth observation nontrivial half depth 0 base seed last
    (seed_recorded observation nontrivial half depth) (seed_live observation nontrivial half depth)
    (Result := Result) ((runtime).run 0)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SourceLaunched
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
