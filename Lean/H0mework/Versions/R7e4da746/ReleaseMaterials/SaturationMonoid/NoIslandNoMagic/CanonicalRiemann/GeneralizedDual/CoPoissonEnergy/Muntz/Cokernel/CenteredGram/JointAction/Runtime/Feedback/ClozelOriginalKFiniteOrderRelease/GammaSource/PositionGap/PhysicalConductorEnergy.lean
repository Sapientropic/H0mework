import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorMomentFaithfulness
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPrefixInverse
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionBranchSecondConductor

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.ConductorFaithfulness

open BurnolPhysicalState DivisionConductor PhysicalClock
open OriginalGamma.Source.RelativeConductorGapReadback
open scoped InnerProductSpace

open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "first" => branchGammaAt observation nontrivial half depth
local notation "second" => branchSecondAt observation nontrivial half depth

/-- The physical diagonal is strictly positive exactly when its actual original slot is live. -/
theorem actual_physical_second_energy_iff (ordinal : Nat) :
    0 < (inner ℂ (input ordinal).1 (second ordinal).1).re ↔ (input ordinal).1 ≠ 0 := by
  constructor
  · intro strict erased
    rw [erased, inner_zero_left, Complex.zero_re] at strict
    exact (lt_irrefl _) strict
  · intro live
    let p := burnolEvenAmbientProjection (raw ordinal)
    have read : (p : BurnolL2) = (input ordinal).1 :=
      congrArg Prod.fst (literal_split observation nontrivial half depth ordinal)
    have firstLive : (first ordinal).1 ≠ 0 := by
      intro erased
      have graph := (actual_division_branch_conductor observation nontrivial half depth ordinal).1
      rw [← read, erased] at graph
      exact live (read.symm.trans
        (zero_of_even_position_gap_conductor (p : BurnolL2)
          (mem_evenL2ClosedFace_iff.mp p.property.2) p.property.1.1 graph))
    have diagonal := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℂ => matrix 0 0)
      (actual_division_branch_second_gram observation nontrivial half depth ordinal)
    change inner ℂ (input ordinal).1 (second ordinal).1 =
      inner ℂ (first ordinal).1 (first ordinal).1 at diagonal
    rw [diagonal]
    exact (re_inner_self_pos (𝕜 := ℂ)).mpr firstLive

/-- A literal physical successor pays its own strict second energy and an independent original K price. -/
theorem actual_division_physical_energy_visible (ordinal : Nat) :
    ∃ (j : Nat) (test : BurnolCompletedMellinCoordinate), 0 < j ∧ test.value.re = 3/4 ∧
      inner ℂ (burnolCompletedMellinRieszVector test : BurnolL2) (input (ordinal+j)).1 ≠ 0 ∧
      0 < (inner ℂ (input (ordinal+j)).1 (second (ordinal+j)).1).re := by
  obtain ⟨j, test, positive, line, price⟩ :=
    actual_division_physical_K_visible observation nontrivial half depth ordinal
  have live : (input (ordinal+j)).1 ≠ 0 := by
    intro zero
    exact price (by rw [zero, inner_zero_right])
  exact ⟨j, test, positive, line, price,
    (actual_physical_second_energy_iff observation nontrivial half depth (ordinal+j)).mpr live⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.ConductorFaithfulness
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
