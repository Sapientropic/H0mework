import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPrefixClock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalClock

open BurnolPhysicalState HilbertInventory SourceGeneratedActionObservationHistory

open private actual_R_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
open private right_quarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor
open private raw_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPrefixClock
open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private current from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients

local notation "R" => burnolDirectRightResolventCLM
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "D" => burnolMultiplicativeDilation
local instance : CompleteSpace PositionField :=
  positionSpace.isClosed.isComplete.completeSpace_coe

/-- Restrict the actual original R to its paid even position-gap carrier. -/
def positionR (c : BurnolCompletedMellinCoordinate) : PositionField →L[ℂ] PositionField :=
  ((R c).comp positionSpace.toSubmodule.subtypeL).codRestrict positionSpace.toSubmodule fun v =>
    ⟨CombSource.Pricing.ambient_R_positionGap _ (right_quarter c) _ v.property.1,
      mem_evenL2ClosedFace_iff.mpr ((actual_R_reflect c v).trans
        (congrArg _ (mem_evenL2ClosedFace_iff.mp v.property.2)))⟩

/-- The first read is the actual positive successor, with the original physical projection. -/
def physicalSuccessor (c : BurnolCompletedMellinCoordinate) : PositionField →L[ℂ] BurnolL2 :=
  (P).comp (positionSpace.toSubmodule.subtypeL.comp (positionR c))

private theorem position_power (c : BurnolCompletedMellinCoordinate) (v : PositionField) (n : Nat) :
    (((positionR c)^n) v : BurnolL2) = ((R c)^n) (v : BurnolL2) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_apply_eq_self, one_apply_eq_self]
  | succ n prior =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
    change R c ((((positionR c)^n) v : PositionField) : BurnolL2) = _
    rw [prior]

private theorem physical_successor_read (c : BurnolCompletedMellinCoordinate) (v : PositionField) (n : Nat) :
    physicalSuccessor c (((positionR c)^n) v) = P (((R c)^(n+1)) (v : BurnolL2)) := by
  change P (R c ((((positionR c)^n) v : PositionField) : BurnolL2)) = _
  rw [position_power, pow_succ', mul_apply_eq_comp]

private theorem zero_of_physical_silence (c : BurnolCompletedMellinCoordinate) (v : PositionField)
    (silent : ∀ n : Nat, physicalSuccessor c (((positionR c)^n) v) = 0) : v = 0 := by
  have quiet (n : Nat) : P (((R c)^(n+1)) (v : BurnolL2)) = 0 := by
    rw [← physical_successor_read, silent]
  have shifted := OriginalRSourceJointContact.OutsideHistory.DilationFromPowers.observed_inward_zero
    P c (v : BurnolL2) quiet 2 (by norm_num)
  rw [show -(2 : ℝ)/2 = -1 by norm_num] at shifted
  apply Subtype.ext
  refine physical_inward_read_injective 1 (by norm_num) v.property.1
    ((locallyConstantFace (1/4 : ℝ)).zero_mem) (mem_evenL2ClosedFace_iff.mp v.property.2)
    (map_zero reflectL2) ?_
  simpa only [Submodule.coe_zero, map_zero] using shifted

/-- The existing source-history completion has a trivial inverse fibre on the actual position carrier. -/
theorem physical_history_injective (c : BurnolCompletedMellinCoordinate) :
    Function.Injective (sourceMap (positionR c).toLinearMap (physicalSuccessor c).toLinearMap) := by
  intro x y same
  have equal := (source_fibre_iff (positionR c).toLinearMap (physicalSuccessor c).toLinearMap x y).mp same
  apply sub_eq_zero.mp
  apply zero_of_physical_silence c
  intro n
  rw [map_sub, map_sub, sub_eq_zero]
  have read := equal n
  rw [← ContinuousLinearMap.toLinearMap_pow] at read
  exact read

theorem recover_physical_history (c : BurnolCompletedMellinCoordinate) (v : PositionField) :
    Hilbert.recover (positionR c) (physicalSuccessor c)
      (projection (positionR c).toLinearMap (physicalSuccessor c).toLinearMap v) = v := by
  have gone : Hilbert.residual (positionR c) (physicalSuccessor c) v = 0 := by
    apply zero_of_physical_silence c
    intro n
    have silent := Hilbert.residual_invisible (positionR c) (physicalSuccessor c) v n
    rwa [← ContinuousLinearMap.toLinearMap_pow] at silent
  simpa only [gone, zero_add] using Hilbert.recover_residual (positionR c) (physicalSuccessor c) v

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "field" => current observation nontrivial half depth
local notation "input" => Div.input observation nontrivial half depth

private theorem literal_physical_successor (ordinal n : Nat) :
    physicalSuccessor c (((positionR c)^n) (field ordinal)) = (input (ordinal+(n+1))).1 := by
  rw [physical_successor_read]
  change P (((R c)^(n+1)) (Div.raw observation nontrivial half depth ordinal)) = _
  rw [← raw_power observation nontrivial half depth ordinal (n+1)]
  exact congrArg Prod.fst (literal_split observation nontrivial half depth _)

/-- The original live physical observations write the same history's successor by its native action. -/
theorem actual_physical_history_next (ordinal : Nat) :
    modelAction (positionR c).toLinearMap (physicalSuccessor c).toLinearMap
      (projection (positionR c).toLinearMap (physicalSuccessor c).toLinearMap (field ordinal)) =
        projection (positionR c).toLinearMap (physicalSuccessor c).toLinearMap (field (ordinal+1)) := by
  rw [modelAction_source]
  congr 1
  apply Subtype.ext
  exact (raw_power observation nontrivial half depth ordinal 1).symm

end OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
