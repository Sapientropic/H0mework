import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ThreePortFibre
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.Consumer

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ThreePortFeedback

open BurnolPhysicalState SourceGeneratedActionObservationHistory
open scoped InnerProductSpace

open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private pair_fields visible from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaBJointVisibility

namespace NativePair
export OriginalKCofinalFullBranchFibre (SourcePair sourceStep actual_source_step)
export OriginalKCofinalFullBranchFibre.OutsideHistory
  (outsideRead recoverPair recover_projection actual_recorded_outside)
export OriginalKCombCofinalInverseAction (pairTotal)
end NativePair

namespace Physical
export OriginalKCombPhysicalAction (physicalProjection physicalRemainder)
export OriginalKCombFullResidualAction (split_complete)
end Physical

namespace Read
export SaturationMonoid.OrthogonalSourceObservation (observe representative representative_orthogonal)
end Read

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation)

local notation "action" => NativePair.sourceStep observation nontrivial half
local notation "observe" => NativePair.outsideRead
local notation "project" => projection action observe
local notation "advanceModel" => modelAction action observe
local notation "readback" => NativePair.recoverPair observation nontrivial half
local notation "Pair" => NativePair.SourcePair
local notation "columns" => ThreePortFibre.columns observation half
local notation "fees" => (Read.observe columns)
local notation "NativeModel" => Model action observe
local notation "Recorded" => (Fin 3 → ℂ) × NativeModel

private def visiblePair (value : Fin 3 → ℂ) : Pair :=
  let lifted := Read.representative columns value
  (Physical.physicalProjection lifted, Physical.physicalRemainder lifted)

local notation "lift" => visiblePair observation half

private def readFees (source : Pair) : Fin 3 → ℂ :=
  fees (NativePair.pairTotal source)

local notation "bill" => readFees observation half

/-- Retain the complete original outside Model of the invisible part. -/
def separate (visible : Fin 3 → ℂ) (whole : NativeModel) : Recorded :=
  (visible, whole - project (lift visible))

def encode (source : Pair) : Recorded :=
  separate observation nontrivial half (bill source) (project source)

def recover (recorded : Recorded) : Pair :=
  lift recorded.1 + readback recorded.2

/-- The original action generates the next fees and writes the new invisible correction
    into the same Model as the already retained invisible source. -/
def advance (recorded : Recorded) : Recorded :=
  let actedVisible := action (lift recorded.1)
  let actedInvisible := advanceModel recorded.2
  let whole := actedVisible + readback actedInvisible
  let next := bill whole
  (next, actedInvisible + project (actedVisible - lift next))

theorem recover_encoded (source : Pair) :
    recover observation nontrivial half (encode observation nontrivial half source) = source := by
  unfold recover encode separate
  rw [map_sub, NativePair.recover_projection, NativePair.recover_projection]
  abel

/-- The original action commutes with recovery and writes a canonical next pair of fields. -/
theorem advance_recovered (recorded : Recorded) :
    advance observation nontrivial half recorded =
      encode observation nontrivial half (action (recover observation nontrivial half recorded)) := by
  let acted := action (lift recorded.1)
  let moved := advanceModel recorded.2
  let target := acted + readback moved
  obtain ⟨hidden, represents⟩ := (actionRow action observe).restriction_surjective recorded.2
  have represented : project hidden = recorded.2 := represents
  have move : moved = project (action (readback recorded.2)) := by
    change advanceModel recorded.2 = _
    rw [← represented, modelAction_source, NativePair.recover_projection]
  have whole : target = action (recover observation nontrivial half recorded) := by
    change acted + readback moved = _
    rw [move, NativePair.recover_projection, recover, map_add]
  refine Prod.ext (congrArg bill whole) ?_
  change moved + project (acted - lift (bill target)) =
    project (action (recover observation nontrivial half recorded)) -
      project (lift (bill (action (recover observation nontrivial half recorded))))
  rw [whole, move, ← map_add project, ← map_sub project]
  apply congrArg project
  rw [recover, map_add]
  change action (readback recorded.2) +
    (action (lift recorded.1) - lift (bill (action (lift recorded.1) + action (readback recorded.2)))) = _
  abel

private abbrev physicalGap : Submodule ℂ BurnolL2 :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule

local instance gapComplete : CompleteSpace physicalGap :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete.completeSpace_coe

private theorem visible_outside_zero (value : Fin 3 → ℂ) :
    (lift value).2 = 0 := by
  let lifted := Read.representative columns value
  have physical : lifted ∈ physicalGap := by
    rw [← physicalGap.orthogonal_orthogonal]
    apply (physicalGapᗮ.mem_orthogonal' _).mpr
    intro field hidden
    have zero : burnolEvenAmbientProjection field = 0 :=
      physicalGap.orthogonalProjectionOnto_apply_of_mem_orthogonal hidden
    exact Read.representative_orthogonal columns value
      (ThreePortFibre.physical_fibre_zero observation half field zero)
  have orthogonal : lifted ∈ physicalGapᗮᗮ := physicalGap.le_orthogonal_orthogonal physical
  change physicalGapᗮ.starProjection lifted = 0
  rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal orthogonal]
  rfl

private theorem original_outside_of_zero (source : Pair)
    (silent : (encode observation nontrivial half source).2 = 0) :
    source.2 = 0 := by
  have whole := congrArg Prod.snd (recover_encoded observation nontrivial half source)
  change ((lift (bill source)) + readback (encode observation nontrivial half source).2).2 = source.2 at whole
  rw [silent, map_zero, add_zero, visible_outside_zero observation half] at whole
  exact whole.symm

variable (depth : Nat)

local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

private theorem total_actual (ordinal : Nat) : NativePair.pairTotal (input ordinal) = raw ordinal := by
  rw [← literal_split observation nontrivial half depth ordinal]
  exact Physical.split_complete _

/-- The residual is measured on the already generated literal outside slots after
    subtracting the representative's own original action. -/
theorem recorded_residual (ordinal bound : Nat) (slot : Fin (bound+1)) :
    stageRead action observe bound
      (sourceMap action observe (input ordinal - lift (bill (input ordinal)))) slot =
        (input (ordinal+slot.val)).2 - ((action^slot.val) (lift (bill (input ordinal)))).2 := by
  rw [map_sub, map_sub]
  change stageRead action observe bound (sourceMap action observe (input ordinal)) slot -
    stageRead action observe bound (sourceMap action observe (lift (bill (input ordinal)))) slot = _
  rw [NativePair.actual_recorded_outside observation nontrivial half depth ordinal, source_reads_stage]
  rfl

theorem actual_advance (ordinal : Nat) :
    advance observation nontrivial half (encode observation nontrivial half (input ordinal)) =
      encode observation nontrivial half (input (ordinal+1)) := by
  rw [advance_recovered, recover_encoded,
    NativePair.actual_source_step observation nontrivial half depth ordinal]

local notation "pairAt" => PaBJointVisibility.actualPair observation nontrivial half depth
local notation "index" => PaBJointVisibility.selected observation nontrivial half depth
local notation "whole" => PacketFit.packetWhole

private theorem outside_at (ordinal : Nat) : Physical.physicalRemainder (raw ordinal) = (input ordinal).2 :=
  congrArg Prod.snd (literal_split observation nontrivial half depth ordinal)

private theorem actual_invisible (cutoff : Nat) :
    (encode observation nontrivial half (input (index cutoff))).2 ≠ 0 ∨
    (encode observation nontrivial half (input (index cutoff+1))).2 ≠ 0 := by
  by_contra! both
  have oldOutside := original_outside_of_zero observation nontrivial half (input (index cutoff)) both.1
  have newOutside := original_outside_of_zero observation nontrivial half (input (index cutoff+1)) both.2
  have field := pair_fields observation nontrivial half depth cutoff
  have old : whole (pairAt cutoff).1 = raw (index cutoff) := congrArg Prod.fst field
  have next : whole (pairAt cutoff).2 = raw (index cutoff+1) := congrArg Prod.snd field
  have effect := (visible observation nontrivial half depth cutoff).2
  apply effect
  unfold PaBJointVisibility.outsideEffect
  simp only [old, next, outside_at observation nontrivial half depth (index cutoff+1),
    outside_at observation nontrivial half depth (index cutoff), oldOutside, newOutside, map_zero, sub_zero]

private def SelectedAt (source target : Pair) (oldField nextField : BurnolL2) : Prop :=
  let current := encode observation nontrivial half source
  let next := advance observation nontrivial half current
  recover observation nontrivial half current = source ∧
  recover observation nontrivial half next = target ∧
  current.1 = fees oldField ∧ next.1 = fees nextField ∧
  (current.2 ≠ 0 ∨ next.2 ≠ 0)

/-- The original finite joint pair consumes the feedback on its exact current and next.
    The physical outside write supplies a nonzero invisible Model at one of the two slots. -/
theorem selected_write (cutoff : Nat) :
    SelectedAt observation nontrivial half (input (index cutoff)) (input (index cutoff+1))
      (whole (pairAt cutoff).1) (whole (pairAt cutoff).2) := by
  let current := encode observation nontrivial half (input (index cutoff))
  let next := advance observation nontrivial half current
  have shifted : next = encode observation nontrivial half (input (index cutoff+1)) :=
    actual_advance observation nontrivial half depth (index cutoff)
  have fields := pair_fields observation nontrivial half depth cutoff
  have before : whole (pairAt cutoff).1 = raw (index cutoff) := congrArg Prod.fst fields
  have after : whole (pairAt cutoff).2 = raw (index cutoff+1) := congrArg Prod.snd fields
  have oldFees : current.1 = fees (whole (pairAt cutoff).1) :=
    congrArg fees ((total_actual observation nontrivial half depth (index cutoff)).trans before.symm)
  have newFees : next.1 = fees (whole (pairAt cutoff).2) := by
    rw [shifted]
    exact congrArg fees ((total_actual observation nontrivial half depth (index cutoff+1)).trans after.symm)
  have hidden : current.2 ≠ 0 ∨ next.2 ≠ 0 := by
    rw [shifted]
    exact actual_invisible observation nontrivial half depth cutoff
  exact ⟨recover_encoded observation nontrivial half _, by
    change recover observation nontrivial half next = _
    rw [shifted, recover_encoded], oldFees, newFees, hidden⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ThreePortFeedback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
