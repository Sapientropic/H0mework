import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.ThreeAgentH1Face
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.ProcessGameInstance
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Ko.ReachableCycle

/-!
# Three-agent H1 ProcessGame regression

The fixed three-edge exposure is reached through the source-only ProcessGame
core.  Its closed FoldReadout computes the P117 ring residual, while P116 and
P121 consume the same value.  A canonical Go instance is added to this
regression only through the shared production adapter.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace ThreeAgentH1ProcessGameRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Go

def exactGoReplay :=
  KoReachableCycle.setupReplay .positionalSuperko

theorem source_compiles_the_exact_existing_exposure :
    threeAgentProcessGame.source = () ∧
      threeAgentProcessGame.occurrence = threeAgentExposure :=
  ⟨rfl, threeAgentProcessGame_occurrence_eq_exposure⟩

theorem concrete_foldReadout_value_eq_two :
    (threeAgentFoldReadout threeCyclePhaseCochain).value = (2 : Int) := by
  rw [threeAgentFoldReadout_value_eq_ringResidual]
  decide

theorem concrete_foldReadout_generates_P116_and_P117 :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        threeCyclePhaseCochain ∧
      ¬ PathAdditive threeCyclePhaseCochain := by
  have nonzero :
      (threeAgentFoldReadout threeCyclePhaseCochain).value ≠ (0 : Int) := by
    rw [concrete_foldReadout_value_eq_two]
    decide
  exact ⟨threeAgentFoldReadout_nonzero_h1
      threeCyclePhaseCochain nonzero,
    threeAgentFoldReadout_nonzero_not_pathAdditive
      threeCyclePhaseCochain nonzero⟩

theorem foldReadout_value_is_P121_cohomology_invariant
    (cochain : ThreeCycleTime → ThreeCycleTime → Int)
    (cohomologous :
      ThreeAgentRingCohomologous threeCyclePhaseCochain cochain) :
    (threeAgentFoldReadout cochain).value =
      (threeAgentFoldReadout threeCyclePhaseCochain).value :=
  threeAgentFoldReadout_eq_of_cohomologous cohomologous

theorem shared_core_fold_unique_consumer
    {A : Type*} [AddCommGroup A]
    (cochain : ThreeCycleTime → ThreeCycleTime → A)
    (candidate : RootedAccountedUnfolding ThreeAgentFoldPoint → A)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        threeAgentAlgebra cochain origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate threeAgentExposure = (threeAgentFoldReadout cochain).value :=
  threeAgentFoldReadout_candidate_unique cochain candidate commutes

/-! ## The same exact core mouths on Go and three-agent H1 -/

theorem Go_and_threeAgent_share_source_compiled_occurrence_mouth :
    (goProcessGame exactGoReplay).source = exactGoReplay ∧
      (goProcessGame exactGoReplay).occurrence =
        exactGoReplay.toOccurrence ∧
      threeAgentProcessGame.source = () ∧
      threeAgentProcessGame.occurrence = threeAgentExposure :=
  ⟨rfl, goProcessGame_occurrence exactGoReplay, rfl,
    threeAgentProcessGame_occurrence_eq_exposure⟩

theorem Go_and_threeAgent_share_closed_FoldReadout_mouth :
    (goFinalFoldReadout exactGoReplay).value = exactGoReplay.final ∧
      (threeAgentFoldReadout threeCyclePhaseCochain).value =
        threeAgentRingResidual threeCyclePhaseCochain :=
  ⟨goFinalFoldReadout_value exactGoReplay,
    threeAgentFoldReadout_value_eq_ringResidual threeCyclePhaseCochain⟩

theorem Go_and_threeAgent_share_candidate_eq_value_mouth
    (goCandidate :
      RootedAccountedUnfolding (Go.Frame 3) → Go.Frame 3)
    (goCommutes : ∀ origin branches,
      goCandidate (.occur origin branches) =
        Go.GeneratedReplay.finalAlgebra origin
          (RootedAccountedUnfolding.candidateValues goCandidate branches))
    (h1Candidate : RootedAccountedUnfolding ThreeAgentFoldPoint → Int)
    (h1Commutes : ∀ origin branches,
      h1Candidate (.occur origin branches) =
        threeAgentAlgebra threeCyclePhaseCochain origin
          (RootedAccountedUnfolding.candidateValues h1Candidate branches)) :
    goCandidate (goProcessGame exactGoReplay).occurrence =
        exactGoReplay.final ∧
      h1Candidate threeAgentExposure =
        (threeAgentFoldReadout threeCyclePhaseCochain).value :=
  ⟨goCandidateEvaluator_eq_final exactGoReplay goCandidate goCommutes,
    threeAgentFoldReadout_candidate_unique
      threeCyclePhaseCochain h1Candidate h1Commutes⟩

end ThreeAgentH1ProcessGameRegression
end ProcessGame
end SaturationMonoid
