import H0mework.Arithmetic.SonineSource.CanonicalSourceIntegralOrbitAction

/-!
# Low-universe Müntz source-current graph

The actual integral event is retained together with both of its source-test
orbits and both graph-cokernel images.  This is the complete low-universe
dependent face needed by the runtime projection law; it does not collapse a
Schwartz relation or quotient class to a scalar character.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph

open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

structure GeneratedRuntimeMuntzSourceCurrentGraphAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : Type where
  private mk ::
  selectedTestOrbit : IntegralScaleCarrier →ₗ[ℤ]
    QuarterMellinL2Test (selectedCoPoissonMuntzParameter observation)
  reversalTestOrbit : IntegralScaleCarrier →ₗ[ℤ]
    QuarterMellinL2Test (reversalCoPoissonMuntzParameter observation)
  selectedQuotientOrbit : IntegralScaleCarrier →ₗ[ℤ]
    CoPoissonMuntzGraphCokernel
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
  reversalQuotientOrbit : IntegralScaleCarrier →ₗ[ℤ]
    CoPoissonMuntzGraphCokernel
      (reversalCoPoissonMuntzParameter observation)
      (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
      (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
  selectedTestOrbit_eq : selectedTestOrbit =
    selectedIntegralDilationTestOrbit observation nontrivial
  reversalTestOrbit_eq : reversalTestOrbit =
    reversalIntegralDilationTestOrbit observation nontrivial
  selectedQuotientOrbit_eq : selectedQuotientOrbit =
    selectedCanonicalSourceIntegralOrbit observation nontrivial
  reversalQuotientOrbit_eq : reversalQuotientOrbit =
    reversalCanonicalSourceIntegralOrbit observation nontrivial
  selectedSourceMap_square : selectedQuotientOrbit =
    (coPoissonMuntzGraphSourceMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      |>.restrictScalars ℤ).comp selectedTestOrbit
  reversalSourceMap_square : reversalQuotientOrbit =
    (coPoissonMuntzGraphSourceMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      |>.restrictScalars ℤ).comp reversalTestOrbit

def generateRuntimeMuntzSourceCurrentGraph
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GeneratedRuntimeMuntzSourceCurrentGraphAt observation nontrivial where
  selectedTestOrbit := selectedIntegralDilationTestOrbit observation nontrivial
  reversalTestOrbit := reversalIntegralDilationTestOrbit observation nontrivial
  selectedQuotientOrbit :=
    selectedCanonicalSourceIntegralOrbit observation nontrivial
  reversalQuotientOrbit :=
    reversalCanonicalSourceIntegralOrbit observation nontrivial
  selectedTestOrbit_eq := rfl
  reversalTestOrbit_eq := rfl
  selectedQuotientOrbit_eq := rfl
  reversalQuotientOrbit_eq := rfl
  selectedSourceMap_square := rfl
  reversalSourceMap_square := rfl

theorem GeneratedRuntimeMuntzSourceCurrentGraphAt.selected_graph_apply
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (graph : GeneratedRuntimeMuntzSourceCurrentGraphAt observation nontrivial)
    (event : IntegralScaleCarrier) :
    graph.selectedQuotientOrbit event =
      coPoissonMuntzGraphSourceMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (graph.selectedTestOrbit event) := by
  rw [graph.selectedSourceMap_square]
  rfl

theorem GeneratedRuntimeMuntzSourceCurrentGraphAt.reversal_graph_apply
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (graph : GeneratedRuntimeMuntzSourceCurrentGraphAt observation nontrivial)
    (event : IntegralScaleCarrier) :
    graph.reversalQuotientOrbit event =
      coPoissonMuntzGraphSourceMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (graph.reversalTestOrbit event) := by
  rw [graph.reversalSourceMap_square]
  rfl

end
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
