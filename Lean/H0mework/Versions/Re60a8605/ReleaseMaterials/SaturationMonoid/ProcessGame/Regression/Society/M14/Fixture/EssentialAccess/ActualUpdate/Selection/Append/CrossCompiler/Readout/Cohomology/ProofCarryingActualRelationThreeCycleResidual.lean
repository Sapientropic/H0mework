import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Incidence.Source.SourceGeneratedActualRelationThreeCycle
import H0mework.Realization.Relations.P121

/-!
# P116/P117/P121 readout of the actual relation renewal cycle

Only after the unique runtime has generated three composable macro edges do
we index them by `ThreeCycleTime`.  Each native nonzero relation phase has
canonical incidence one; no event-weight table or residual is accepted.
P117 computes residual magnitude three and nontrivial H¹, while P121 makes
that magnitude invariant under coboundary changes of presentation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingActualRelationThreeCycleResidual

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal
open M14EssentialAccessRelationFixture
open M14SourceGeneratedActualRelationThreeCycle

local instance actualRelationPhaseDecidableEq :
    DecidableEq (essentialAccessRelationCompiler.Phase
      Lifecycle.actualEventGame.source) := by
  change DecidableEq EssentialAccessSector
  infer_instance

/-- Canonical integer incidence of a native relation phase: zero stays zero,
every actually nonzero phase contributes one. -/
def actualRelationCycleIncidenceAt (depth : Nat) : Int :=
  if actualRelationPhaseAt depth = 0 then 0 else 1

@[simp] theorem actualRelationCycleIncidenceAt_eq_one (depth : Nat) :
    actualRelationCycleIncidenceAt depth = 1 := by
  simp [actualRelationCycleIncidenceAt, actualRelationPhase_nonzero depth]

def actualRelationCycleDepthAt (base : Nat) : ThreeCycleTime → Nat
  | .t0 => base
  | .t1 => base + 1
  | .t2 => base + 2

def actualRelationCycleIncidenceOf
    (base : Nat) (index : ThreeCycleTime) : Int :=
  actualRelationCycleIncidenceAt (actualRelationCycleDepthAt base index)

/-- The three source actors are indexed only after the actual macro cycle has
been generated. -/
def actualRelationCycleActorAt
    (base : Nat) (index : ThreeCycleTime) :
    essentialAccessRelationCompiler.Actor :=
  actualRelationActorAt (actualRelationCycleDepthAt base index)

@[simp] theorem actualRelationCycleActorAt_source_exact
    (base : Nat) (index : ThreeCycleTime) :
    actualRelationCycleActorAt base index =
      actualRelationActorAt (actualRelationCycleDepthAt base index) :=
  rfl

/-- The index successor is the actual macro-edge target actor.  At the third
edge this consumes actor renewal at the later fourth occurrence. -/
theorem actualRelationCycleActorAt_target_exact
    (base : Nat) (index : ThreeCycleTime) :
    actualRelationCycleActorAt base (threeCycleNext index) =
      actualRelationActorAt (actualRelationCycleDepthAt base index + 1) := by
  cases index
  · rfl
  · rfl
  · change actualRelationActorAt base = actualRelationActorAt (base + 3)
    exact (sourceGeneratedActualRelationThreeCycleAt base).actorClosure.symm

theorem actualRelationCycleActorAt_injective (base : Nat) :
    Function.Injective (actualRelationCycleActorAt base) := by
  intro left right equality
  rcases actualRelationThreeCycle_actorPairwise base with
    ⟨firstSecond, secondThird, thirdFirst⟩
  cases left <;> cases right
  · rfl
  · exact False.elim (firstSecond equality.symm)
  · exact False.elim (thirdFirst equality.symm)
  · exact False.elim (firstSecond equality)
  · rfl
  · exact False.elim (secondThird equality.symm)
  · exact False.elim (thirdFirst equality)
  · exact False.elim (secondThird equality)
  · rfl

/-- The three selected edges are indexed only after the actual cycle carrier
has been generated. -/
def actualRelationCycleCochain
    (base : Nat) : ThreeCycleTime → ThreeCycleTime → Int :=
  fun source target =>
    if target = threeCycleNext source then
      actualRelationCycleIncidenceOf base source
    else
      0

@[simp] theorem actualRelationCycleCochain_selectedEdge
    (base : Nat) (index : ThreeCycleTime) :
    actualRelationCycleCochain base index (threeCycleNext index) = 1 := by
  cases index <;>
    simp [actualRelationCycleCochain, actualRelationCycleIncidenceOf,
      actualRelationCycleDepthAt, threeCycleNext]

/-- Full commuting contract from the post-producer cycle index back to the
same actual macro edge, its source/target actors and native phase incidence. -/
theorem actualRelationCycleIndex_commutes
    (base : Nat) (index : ThreeCycleTime) :
    actualRelationCycleActorAt base index =
        actualRelationActorAt (actualRelationCycleDepthAt base index) ∧
      actualRelationCycleActorAt base (threeCycleNext index) =
        actualRelationActorAt (actualRelationCycleDepthAt base index + 1) ∧
      actualRelationCycleCochain base index (threeCycleNext index) =
        actualRelationCycleIncidenceAt
          (actualRelationCycleDepthAt base index) ∧
      SourceGeneratedActualRelationMacroEdgeAt
        (actualRelationCycleDepthAt base index) :=
  ⟨rfl, actualRelationCycleActorAt_target_exact base index, by
      cases index <;>
        simp [actualRelationCycleCochain, actualRelationCycleIncidenceOf,
          actualRelationCycleDepthAt, threeCycleNext],
    sourceGeneratedActualRelationMacroEdgeAt _⟩

/-- P117's residual is calculated from the three generated nonzero
incidences. -/
theorem actualRelationCycle_residual_eq_three (base : Nat) :
    threeAgentRingResidual (actualRelationCycleCochain base) = 3 := by
  simp [threeAgentRingResidual, actualRelationCycleCochain,
    actualRelationCycleIncidenceOf, actualRelationCycleDepthAt,
    threeCycleNext]

theorem actualRelationCycle_residualMagnitude_eq_three (base : Nat) :
    threeAgentRingResidualMagnitude (actualRelationCycleCochain base) = 3 := by
  simp [threeAgentRingResidualMagnitude,
    actualRelationCycle_residual_eq_three base]

/-- P117: the generated cycle carries nontrivial H¹ without a nonzero or
residual premise in the public mouth. -/
theorem actualRelationCycle_nontrivial_h1 (base : Nat) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime Int)
      (actualRelationCycleCochain base) := by
  apply threeAgentRingResidualMagnitude_pos_h1
  rw [actualRelationCycle_residualMagnitude_eq_three]
  norm_num

/-- P116: the same actual cycle is not path-additive. -/
theorem actualRelationCycle_not_pathAdditive (base : Nat) :
    Not (PathAdditive (actualRelationCycleCochain base)) :=
  (h1Obstruction_iff_not_pathAdditive
    (actualRelationCycleCochain base)).mp
      (actualRelationCycle_nontrivial_h1 base)

theorem actualRelationCycle_not_edgeExact (base : Nat) :
    Not (ThreeAgentRingEdgeExact (actualRelationCycleCochain base)) :=
  (threeAgentRingResidualMagnitude_pos_iff_not_edgeExact
    (actualRelationCycleCochain base)).mp (by
      rw [actualRelationCycle_residualMagnitude_eq_three]
      norm_num)

/-- P121: every cohomologous presentation has the same generated magnitude. -/
theorem actualRelationCycle_magnitude_eq_of_cohomologous
    (base : Nat)
    {other : ThreeCycleTime → ThreeCycleTime → Int}
    (cohomologous :
      ThreeAgentRingCohomologous
        (actualRelationCycleCochain base) other) :
    threeAgentRingResidualMagnitude other = 3 := by
  rw [threeAgentRingResidualMagnitude_eq_of_cohomologous cohomologous,
    actualRelationCycle_residualMagnitude_eq_three]

/-- The entire cohomology class cannot be the zero-magnitude/exact class. -/
theorem actualRelationCycle_not_zeroMagnitudeClass (base : Nat) :
    Not (∀ other,
      ThreeAgentRingCohomologous
        (actualRelationCycleCochain base) other →
      threeAgentRingResidualMagnitude other = 0) := by
  intro zeroClass
  exact actualRelationCycle_not_edgeExact base
    ((threeAgentRingResidualMagnitude_zero_on_class_iff_edgeExact
      (actualRelationCycleCochain base)).mp zeroClass)

/-- The P116 two-agent line remains exact; genuine closure uses the three
generated macro edges above. -/
theorem twoAgentLine_still_cannotCarryActualCycleH1 (phase : Int) :
    Not (CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover TwoAgentLine Int)
      (twoAgentLinePhase phase)) :=
  twoAgentLinePhase_not_h1 phase

theorem actualRelationThreeCycleResidual_directConsumer (base : Nat) :
    type_of% (actualRelationThreeCycle_directConsumer base) ∧
      Function.Injective (actualRelationCycleActorAt base) ∧
      (∀ index : ThreeCycleTime,
        type_of% (actualRelationCycleIndex_commutes base index)) ∧
      (∀ index : ThreeCycleTime,
        actualRelationCycleCochain base index (threeCycleNext index) = 1) ∧
      threeAgentRingResidual (actualRelationCycleCochain base) = 3 ∧
      threeAgentRingResidualMagnitude (actualRelationCycleCochain base) = 3 ∧
      CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        (actualRelationCycleCochain base) ∧
      Not (PathAdditive (actualRelationCycleCochain base)) ∧
      Not (ThreeAgentRingEdgeExact (actualRelationCycleCochain base)) ∧
      (∀ other : ThreeCycleTime → ThreeCycleTime → Int,
        ThreeAgentRingCohomologous
          (actualRelationCycleCochain base) other →
        threeAgentRingResidualMagnitude other = 3) ∧
      Not (∀ other,
        ThreeAgentRingCohomologous
          (actualRelationCycleCochain base) other →
        threeAgentRingResidualMagnitude other = 0) :=
  ⟨actualRelationThreeCycle_directConsumer base,
    actualRelationCycleActorAt_injective base,
    actualRelationCycleIndex_commutes base,
    actualRelationCycleCochain_selectedEdge base,
    actualRelationCycle_residual_eq_three base,
    actualRelationCycle_residualMagnitude_eq_three base,
    actualRelationCycle_nontrivial_h1 base,
    actualRelationCycle_not_pathAdditive base,
    actualRelationCycle_not_edgeExact base,
    (fun _other cohomologous =>
      actualRelationCycle_magnitude_eq_of_cohomologous base cohomologous),
    actualRelationCycle_not_zeroMagnitudeClass base⟩

end
end M14ProofCarryingActualRelationThreeCycleResidual
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual.actualRelationCycle_residualMagnitude_eq_three
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual.actualRelationCycle_nontrivial_h1
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual.actualRelationCycle_not_pathAdditive
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual.actualRelationCycle_magnitude_eq_of_cohomologous
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual.actualRelationThreeCycleResidual_directConsumer
