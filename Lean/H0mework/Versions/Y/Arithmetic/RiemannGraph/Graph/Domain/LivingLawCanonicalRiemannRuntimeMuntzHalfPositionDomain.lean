import H0mework.Versions.Y.Arithmetic.RiemannGraph.Graph.LivingLawCanonicalRiemannRuntimeMuntzGraphLogPositionCone
import H0mework.Versions.Y.Arithmetic.MellinConductor.Cokernel.LivingLawCanonicalCoPoissonHalfPositionMappingCone
import H0mework.Versions.Y.Arithmetic.MellinConductor.Source.LivingLawCanonicalNormalizedShellHalfPositionOrbit

/-!
# Runtime half-position mapping-cone projection

The selected and reversal test orbits at the installed integral boundary
enter the maximal half-position source domain by generated shell support and
integral-basis coverage.  Their new mapping-cone source classes project in
the unique lawful direction to the quotient orbits already stored in the
same runtime face.
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
namespace Conductor
namespace Graph
namespace Domain

open ClozelGeneralizedDual
open ClozelGeneralizedDual.MuntzConductor.HalfPositionSource
open Material
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Consumer

noncomputable section

def runtimeSelectedHalfPositionValue
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    quarterMellinHalfPositionSourceDomain
      (selectedCoPoissonMuntzParameter observation) :=
  ⟨face.muntzSourceCurrentGraph.selectedTestOrbit
      (runtimeFaceIntegralSourceBoundary face), by
    rw [face.muntzSourceCurrentGraph.selectedTestOrbit_eq]
    exact selectedIntegralDilationFeature_mem_domain
      observation nontrivial (runtimeFaceIntegralSourceBoundary face)⟩

def runtimeReversalHalfPositionValue
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    quarterMellinHalfPositionSourceDomain
      (reversalCoPoissonMuntzParameter observation) :=
  ⟨face.muntzSourceCurrentGraph.reversalTestOrbit
      (runtimeFaceIntegralSourceBoundary face), by
    rw [face.muntzSourceCurrentGraph.reversalTestOrbit_eq]
    exact reversalIntegralDilationFeature_mem_domain
      observation nontrivial (runtimeFaceIntegralSourceBoundary face)⟩

theorem runtimeSelectedMuntzHalfPositionCone_projects
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    halfPositionMuntzGraphProjection
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (halfPositionMuntzGraphSourceMap
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          (runtimeSelectedHalfPositionValue face)) =
      face.muntzSourceCurrentGraph.selectedQuotientOrbit
        (runtimeFaceIntegralSourceBoundary face) := by
  rw [halfPositionMuntzGraphProjection_source_readback]
  exact (GeneratedRuntimeMuntzSourceCurrentGraphAt.selected_graph_apply
    face.muntzSourceCurrentGraph
    (runtimeFaceIntegralSourceBoundary face)).symm

theorem runtimeReversalMuntzHalfPositionCone_projects
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    halfPositionMuntzGraphProjection
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (halfPositionMuntzGraphSourceMap
          (reversalCoPoissonMuntzParameter observation)
          (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
          (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          (runtimeReversalHalfPositionValue face)) =
      face.muntzSourceCurrentGraph.reversalQuotientOrbit
        (runtimeFaceIntegralSourceBoundary face) := by
  rw [halfPositionMuntzGraphProjection_source_readback]
  exact (GeneratedRuntimeMuntzSourceCurrentGraphAt.reversal_graph_apply
    face.muntzSourceCurrentGraph
    (runtimeFaceIntegralSourceBoundary face)).symm

/-- Both actual runtime graph classes are restrictions of the new closed
half-position mapping cone at the same installed boundary. -/
theorem runtimeMuntzHalfPositionCone_projects
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    type_of% (runtimeSelectedMuntzHalfPositionCone_projects face) ∧
      type_of% (runtimeReversalMuntzHalfPositionCone_projects face) :=
  ⟨runtimeSelectedMuntzHalfPositionCone_projects face,
    runtimeReversalMuntzHalfPositionCone_projects face⟩

end
end Domain
end Graph
end Conductor
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
