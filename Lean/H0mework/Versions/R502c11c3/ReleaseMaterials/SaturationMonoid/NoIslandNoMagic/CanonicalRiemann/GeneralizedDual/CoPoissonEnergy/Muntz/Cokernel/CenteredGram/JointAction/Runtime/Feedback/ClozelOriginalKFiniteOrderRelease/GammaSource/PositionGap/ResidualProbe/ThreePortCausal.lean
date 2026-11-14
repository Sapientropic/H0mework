import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.Feedback
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ThreePortFeedback

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ThreePortCausal

open BurnolPhysicalState
open scoped BigOperators InnerProductSpace

open private visiblePair readFees total_actual from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ThreePortFeedback
open private literal_split from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

namespace F
export SaturationMonoid.SourceLinearFeedback (residual hiddenAction response reassemble reassemble_action)
end F

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "columns" => ThreePortFibre.columns observation half
local notation "fees" => ContinuousLinearMap.toLinearMap (SaturationMonoid.OrthogonalSourceObservation.observe columns)
local notation "R" => ContinuousLinearMap.toLinearMap (OriginalKCombPhysicalAction.R observation nontrivial half)
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "record" => ThreePortFeedback.encode observation nontrivial half
local notation "total" => ThreePortFeedback.NativePair.pairTotal

private def lift : (Fin 3 → ℂ) →ₗ[ℂ] BurnolL2 where
  toFun := SaturationMonoid.OrthogonalSourceObservation.representative columns
  map_add' := by
    intro a b
    simp only [SaturationMonoid.OrthogonalSourceObservation.representative, Pi.add_apply, add_div, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a b
    simp only [SaturationMonoid.OrthogonalSourceObservation.representative, Pi.smul_apply, smul_eq_mul, mul_div_assoc, mul_smul, Finset.smul_sum]
    rfl

local notation "sectionMap" => lift observation half

private theorem visible_total (value : Fin 3 → ℂ) :
    total (visiblePair observation half value) = sectionMap value :=
  ThreePortFeedback.Physical.split_complete _

private theorem source_iterate (start n : Nat) : (R ^ n) (raw start) = raw (start+n) := by
  induction n with
  | zero => simp
  | succ n previous =>
    rw [pow_succ', Module.End.mul_apply, previous]
    exact (OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth (start+n)).symm

/-- The opening hidden field is read from the already-written original Model. -/
def opening (ordinal : Nat) : BurnolL2 :=
  total (ThreePortFeedback.NativePair.recoverPair observation nontrivial half (record (input ordinal)).2)

private theorem opening_source (ordinal : Nat) :
    opening observation nontrivial half depth ordinal = F.residual fees sectionMap (raw ordinal) := by
  let held := record (input ordinal)
  have same := congrArg total (ThreePortFeedback.recover_encoded observation nontrivial half (input ordinal))
  change total (visiblePair observation half held.1 +
    ThreePortFeedback.NativePair.recoverPair observation nontrivial half held.2) = total (input ordinal) at same
  have read : held.1 = fees (raw ordinal) :=
    congrArg fees (total_actual observation nontrivial half depth ordinal)
  rw [map_add, visible_total, read, total_actual observation nontrivial half depth ordinal] at same
  change total (ThreePortFeedback.NativePair.recoverPair observation nontrivial half held.2) =
    raw ordinal - sectionMap (fees (raw ordinal))
  exact eq_sub_of_add_eq' same

/-- This reconstruction uses the original opening Model and only reads at offsets at most `n`. -/
def field (ordinal n : Nat) : BurnolL2 :=
  F.reassemble fees sectionMap R (opening observation nontrivial half depth ordinal)
    (fun j => fees (raw (ordinal+j))) n

theorem actual_field (ordinal n : Nat) :
    field observation nontrivial half depth ordinal n = raw (ordinal+n) := by
  unfold field
  rw [opening_source]
  have reads : (fun j => fees (raw (ordinal+j))) = (fun j : Nat => fees ((R^j) (raw ordinal))) := by
    funext j
    rw [source_iterate observation nontrivial half depth ordinal j]
  rw [reads, F.reassemble_action, source_iterate observation nontrivial half depth ordinal n]

/-- The next source pair is reconstructed before the original outside Model and fees are written. -/
def nextPair (ordinal n : Nat) : ThreePortFeedback.NativePair.SourcePair :=
  let written := R (field observation nontrivial half depth ordinal n)
  (ThreePortFeedback.Physical.physicalProjection written, ThreePortFeedback.Physical.physicalRemainder written)

theorem actual_next_pair (ordinal n : Nat) :
    nextPair observation nontrivial half depth ordinal n = input (ordinal+n+1) := by
  have written : R (field observation nontrivial half depth ordinal n) = raw (ordinal+n+1) :=
    (congrArg R (actual_field observation nontrivial half depth ordinal n)).trans
      (OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth (ordinal+n)).symm
  dsimp only [nextPair]
  rw [written]
  exact literal_split observation nontrivial half depth (ordinal+n+1)

theorem actual_recorded_next (ordinal n : Nat) :
    record (nextPair observation nontrivial half depth ordinal n) =
      ThreePortFeedback.advance observation nontrivial half (record (input (ordinal+n))) := by
  rw [actual_next_pair, ThreePortFeedback.actual_advance observation nontrivial half depth]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ThreePortCausal
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
