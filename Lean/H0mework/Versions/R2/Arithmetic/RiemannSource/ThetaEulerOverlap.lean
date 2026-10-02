import H0mework.Versions.R2.Arithmetic.RiemannSource.ThetaMellinContinuation

/-!
# Same-root overlap of the theta–Mellin continuation and Euler germ

The function born from the finite theta folds agrees on `re s > 1` with the
existing determinant-generated Euler germ.  This produces an actual
`ComplexRealization` without accepting a completed analytic function from a
caller, and installs it on the literal `globalGermOccurrence`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open RootedAccountedUnfolding

noncomputable section

theorem generatedRiemannZeta_eq_globalDeterminantCoordinateGerm
    (owner : GlobalGermOwner) {s : ℂ} (rightHalfPlane : 1 < s.re) :
    generatedRiemannZeta owner s = globalDeterminantCoordinateGerm s :=
  (congrFun (generatedRiemannZeta_eq_mathlib owner) s).trans
    (globalDeterminantCoordinateGerm_eq_riemannZeta rightHalfPlane).symm

/-- The source-generated continuation is a realization of the already
generated determinant germ. -/
def sourceGeneratedComplexRealization (owner : GlobalGermOwner) :
    ComplexRealization where
  function := generatedRiemannZeta owner
  analyticAwayOne := analyticOn_generatedRiemannZeta_awayOne owner
  agreesWithGeneratedGerm := fun rightHalfPlane =>
    generatedRiemannZeta_eq_globalDeterminantCoordinateGerm
      owner rightHalfPlane

theorem sourceGeneratedComplexRealization_unique
    (owner : GlobalGermOwner) (candidate : ComplexRealization) :
    Set.EqOn candidate.function
      (sourceGeneratedComplexRealization owner).function ({1} : Set ℂ)ᶜ :=
  candidate.eqOn_awayOne (sourceGeneratedComplexRealization owner)

theorem sourceGeneratedComplexRealization_eq_mathlib
    (owner : GlobalGermOwner) {s : ℂ} (notPole : s ≠ 1) :
    (sourceGeneratedComplexRealization owner).function s = riemannZeta s := by
  exact (sourceGeneratedComplexRealization owner).eq_mathlib_of_ne_one notPole

/-- Private provenance package: the analytic realization cannot be detached
from the generated theta FE-pair that produced it. -/
structure GeneratedRiemannAnalyticContinuationAt
    (owner : GlobalGermOwner) : Type 5 where
  private mk ::
  thetaPair : GeneratedRiemannWeakFEPairAt owner
  thetaPair_eq : thetaPair = GeneratedRiemannWeakFEPairAt.generate owner
  realization : ComplexRealization
  realization_eq : realization = sourceGeneratedComplexRealization owner

namespace GeneratedRiemannAnalyticContinuationAt

def generate (owner : GlobalGermOwner) :
    GeneratedRiemannAnalyticContinuationAt owner where
  thetaPair := GeneratedRiemannWeakFEPairAt.generate owner
  thetaPair_eq := rfl
  realization := sourceGeneratedComplexRealization owner
  realization_eq := rfl

end GeneratedRiemannAnalyticContinuationAt

abbrev AnalyticContinuationPayload :=
  Σ owner : GlobalGermOwner, GeneratedRiemannAnalyticContinuationAt owner

/-- The completed analytic face is a dependent face of the literal global
arithmetic-germ occurrence. -/
def generatedRiemannAnalyticContinuationOccurrence :
    RootedAccountedUnfolding AnalyticContinuationPayload :=
  globalGermOccurrence.map fun owner =>
    ⟨owner, GeneratedRiemannAnalyticContinuationAt.generate owner⟩

theorem generatedRiemannAnalyticContinuationOccurrence_projects :
    generatedRiemannAnalyticContinuationOccurrence.map Sigma.fst =
      globalGermOccurrence := by
  rw [generatedRiemannAnalyticContinuationOccurrence,
    RootedAccountedUnfolding.map_map]
  change globalGermOccurrence.map id = globalGermOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem generatedRiemannAnalyticContinuationOccurrence_projects_to_seed :
    (generatedRiemannAnalyticContinuationOccurrence.map Sigma.fst).map
        Prod.fst = seedOccurrence := by
  rw [generatedRiemannAnalyticContinuationOccurrence_projects,
    globalGermOccurrence_projects]

/-- Forward existence, provenance, Mellin continuation, functional equation,
and Euler overlap are simultaneously available from one exact owner. -/
theorem generatedRiemannAnalyticContinuation_directConsumer :
    let generated := generatedRiemannAnalyticContinuationOccurrence.root
    generated.1 = globalGermOccurrence.root ∧
      generated.2.realization.function =
        generatedRiemannZeta generated.1 ∧
      AnalyticOnNhd ℂ generated.2.realization.function ({1} : Set ℂ)ᶜ ∧
      (∀ {s : ℂ}, 1 < s.re →
        generated.2.realization.function s =
          globalDeterminantCoordinateGerm s) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact analyticOn_generatedRiemannZeta_awayOne _
  · intro s rightHalfPlane
    exact generatedRiemannZeta_eq_globalDeterminantCoordinateGerm
      _ rightHalfPlane

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
