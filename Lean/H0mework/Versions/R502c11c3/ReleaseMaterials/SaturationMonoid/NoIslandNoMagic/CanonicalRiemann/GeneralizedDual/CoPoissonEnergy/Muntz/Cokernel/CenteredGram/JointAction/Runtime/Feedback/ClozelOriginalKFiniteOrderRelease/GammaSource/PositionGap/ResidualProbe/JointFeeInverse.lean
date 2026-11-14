import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedNativeHistory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.JointFeeInverse

open BurnolPhysicalState BurnolPhysicalState.OriginalPaPhysicalGreen
open RootInquiryCompletion SourceNativeInquiryRuntime
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private same_pairing from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CountedTateReturn
open private arithmetic_tate tablePair from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.StoredLiveReturn
open private pick from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedLiveWindows

namespace Division
export OriginalKDirectRCofinalDivision (sourceCoefficient sourceUnit actual_Q_successor)
end Division
namespace Pa
export OriginalKCombCofinalPaAction (E Q invisible)
end Pa
namespace Query
export OriginalKDirectRCofinalMobiusSourceAction (actualReentryVector actual_query_Tate_coupled)
end Query

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R" => OriginalKCombPhysicalAction.R observation nontrivial half
local notation "U" => Division.sourceUnit observation nontrivial half
local notation "V" => Query.actualReentryVector observation half
local notation "W" => OriginalKDirectRCofinalPaUpdate.sourceWholeUnit observation nontrivial half
local notation "M" => burnolTateReciprocalL2.comp burnolMobiusSourceL2
local notation "g" => CountedTateReturn.greenTest observation half
local notation "gain" => CountedTateReturn.greenGain observation half
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "alpha" => Division.sourceCoefficient observation nontrivial half depth
local notation "beta" => ReentryDifferenceClock.fee observation nontrivial half depth

/-- The written Q and Tate increments remove their own homogeneous actions.
    The Q prediction uses the complete invisible input, including its outside field. -/
def effect (before after : BurnolL2) : BurnolPaAmbientCarrier × BurnolL2 :=
  (Pa.Q after - Pa.Q (R (Pa.invisible before)),
    M (Pa.E after) - sourceVolterraWindow c (M (Pa.E before)))

/-- The Division unit affects both faces. The re-entry column is present in the Tate face. -/
def generated (amount returning : ℂ) : BurnolPaAmbientCarrier × BurnolL2 :=
  (amount • U, amount • M (Pa.E (W : BurnolL2)) + returning • M V)

/-- Recover both fees from the written faces. The arithmetic read uses the amount
    recovered from Q, with no coefficient argument from the input Pa. -/
def recover (written : BurnolPaAmbientCarrier × BurnolL2) : ℂ × ℂ :=
  let unit := (U : BurnolL2)
  let amount := inner ℂ unit (written.1 : BurnolL2) / inner ℂ unit unit
  (amount, inner ℂ g (written.2 - amount • M (Pa.E (W : BurnolL2))) / gain)

private theorem source_unit_ne : U ≠ 0 := by
  intro erased
  let unit := burnolZeroOwnedUnitTailState observation nontrivial half.down
  change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection unit = 0 at erased
  have inside := (Submodule.starProjection_apply_eq_zero_iff _).mp erased
  rw [Submodule.orthogonal_orthogonal] at inside
  exact burnolZeroOwnedUnitTailState_notInPa observation nontrivial half.down inside

theorem recover_generated (amount returning : ℂ) :
    recover observation nontrivial half (generated observation nontrivial half amount returning) =
      (amount, returning) := by
  let unit := (U : BurnolL2)
  have energy : inner ℂ unit unit ≠ 0 :=
    fun zero => source_unit_ne observation nontrivial half (Subtype.ext (inner_self_eq_zero.mp zero))
  have active : gain ≠ 0 := by
    intro zero
    have negative := CountedTateReturn.green_gain_negative observation nontrivial half
    rw [zero, Complex.zero_re] at negative
    exact lt_irrefl _ negative
  have decoded : inner ℂ unit (amount • unit) / inner ℂ unit unit = amount := by
    rw [inner_smul_right (𝕜 := ℂ) unit unit amount, mul_div_cancel_right₀ _ energy]
  let column := M (Pa.E (W : BurnolL2))
  change (inner ℂ unit (amount • unit) / inner ℂ unit unit,
    inner ℂ g (amount • column + returning • M V -
      (inner ℂ unit (amount • unit) / inner ℂ unit unit) • column) / gain) = (amount, returning)
  rw [decoded, add_sub_cancel_left, inner_smul_right (𝕜 := ℂ) g (M V) returning]
  change (amount, returning * gain / gain) = _
  rw [mul_div_cancel_right₀ _ active]

/-- The original Division write and original registered Tate query jointly produce the two columns. -/
theorem actual_effect (ordinal : Nat) :
    effect observation nontrivial half (raw ordinal) (raw (ordinal + 1)) =
      generated observation nontrivial half (alpha ordinal) (beta ordinal) := by
  have q := Division.actual_Q_successor observation nontrivial half depth ordinal
  have tate := Query.actual_query_Tate_coupled observation nontrivial half depth ordinal
  rw [same_pairing observation nontrivial half depth ordinal,
    arithmetic_tate observation nontrivial half depth (ordinal + 1),
    arithmetic_tate observation nontrivial half depth ordinal] at tate
  apply Prod.ext
  · change Pa.Q (raw (ordinal + 1)) - Pa.Q (R (Pa.invisible (raw ordinal))) = alpha ordinal • U
    rw [q, add_sub_cancel_right]
  · have written : M (Pa.E (raw (ordinal + 1))) =
        sourceVolterraWindow c (M (Pa.E (raw ordinal))) +
          alpha ordinal • M (Pa.E (W : BurnolL2)) + beta ordinal • M V := tate
    change M (Pa.E (raw (ordinal + 1))) - sourceVolterraWindow c (M (Pa.E (raw ordinal))) =
      alpha ordinal • M (Pa.E (W : BurnolL2)) + beta ordinal • M V
    rw [written, add_assoc, add_sub_cancel_left]

theorem actual_recovery (ordinal : Nat) :
    recover observation nontrivial half (effect observation nontrivial half (raw ordinal) (raw (ordinal + 1))) =
      (alpha ordinal, beta ordinal) :=
  (congrArg (recover observation nontrivial half)
    (actual_effect observation nontrivial half depth ordinal)).trans
    (recover_generated observation nontrivial half (alpha ordinal) (beta ordinal))

local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "Packet" => PacketFit.Packet
local notation "whole" => PacketFit.packetWhole
local notation "limit" => StoredLiveReturn.windowFuel observation nontrivial half depth

variable (origin last : Nat) (table : Vector Packet (last + 1)) (cursor : Fin (last + 1))
variable (owned : RetainedLiveWindows.recorded observation nontrivial half depth origin last table)
variable (live : ReentryDifferenceClock.fee observation nontrivial half depth (origin + cursor.val + 1) ≠ 0)

local notation "base" => (origin + cursor.val)
local notation "moved" => RetainedLiveWindows.advance observation nontrivial half depth origin last table cursor owned live
local notation "read" => SelectedNativeHistory.selectedWrite observation nontrivial half depth origin last table cursor owned live
local notation "ordinal" => (origin + 1 + Fin.val (Prod.fst (Prod.snd moved)))

private theorem selected_wholes :
    (whole (moved).2.2.1, whole (moved).2.2.2) = (raw ordinal, raw (ordinal + 1)) := by
  let chosen := pick observation nontrivial half depth origin last table cursor owned live
  have window := RetainedLiveWindows.actual_slice observation nontrivial half depth origin last table cursor owned
  have pair : (moved).2.2 = StoredLiveReturn.packetPair observation nontrivial half depth base chosen :=
    congrArg (fun rows : Vector Packet (limit base + 1) => tablePair rows chosen) window
  have address : StoredLiveReturn.candidateOrdinal observation nontrivial half depth base chosen = ordinal := by
    change origin + cursor.val + 2 + chosen.val = origin + 1 + (cursor.val + (chosen.val + 1))
    omega
  have paid := StoredLiveReturn.actual_whole_pair observation nontrivial half depth base chosen
  rw [address] at paid
  exact (congrArg (fun p : Packet × Packet => (whole p.1, whole p.2)) pair).trans paid

/-- Read the two fees from the original selected packet pair and keep its same sealed write. -/
def readSelected {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (type_of% (read history)) × (ℂ × ℂ) :=
  let event := read history
  let pair := event.1.2.2
  (event, recover observation nontrivial half (effect observation nontrivial half (whole pair.1) (whole pair.2)))

theorem selected_recovery {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (readSelected observation nontrivial half depth origin last table cursor owned live history).2 =
      (alpha ordinal, beta ordinal) := by
  let undo (fields : BurnolL2 × BurnolL2) :=
    recover observation nontrivial half (effect observation nontrivial half fields.1 fields.2)
  have same := congrArg undo (selected_wholes observation nontrivial half depth origin last table cursor owned live)
  exact same.trans (actual_recovery observation nontrivial half depth ordinal)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.JointFeeInverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
