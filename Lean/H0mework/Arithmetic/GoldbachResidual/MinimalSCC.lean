import H0mework.Arithmetic.GoldbachResidual.ClosedDecay
import H0mework.Foundation.Finite.ClosedSCC

/-!
# First-residual minimal combined-decay SCC

Extracts the exact minimum-cardinality nonempty subsector of the latest
repair/emission residual that is closed under every decay channel.  The
generic kernel proves actual dependent paths between every ordered pair.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFirstResidualFullFactorDecaySCCProducer

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFirstResidualFullFactorDecayProducer
open CanonicalUnitArithmeticFullFactorDecayReachabilityProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticGlobalGoldbachDisposition
open SourceGeneratedFiniteClosedReachableMinimalSCC
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

abbrev FirstResidualFullFactorDecaySCCAt
    (failure : FirstResidualOccurrence) :=
  MinimalClosedSCCAt (generateFirstResidualFullFactorDecayClosed failure)

structure RootGeneratedFirstResidualFullFactorDecaySCCAt
    (failure : FirstResidualOccurrence) : Type 7 where
  private mk ::
  decay : RootGeneratedFirstResidualFullFactorDecayAt failure
  decay_eq : decay = generateFirstResidualFullFactorDecay failure
  scc : MinimalClosedSCCAt decay.residual
  scc_eq : scc = generateMinimalClosedSCC decay.residual
  sectorNonempty : scc.sector.states.Nonempty
  sectorSubsetResidual : scc.sector.states ⊆ decay.residual.states
  everyStateNonterminal : ∀ state, state ∈ scc.sector.states →
    ¬ Nonempty (PrimePairTerminalAt state)
  everyDecayChannelClosed : ∀ state, state ∈ scc.sector.states →
    (channel : FactorDecayChannelAt state) →
      channel.target ∈ scc.sector.states
  pathBetween : ∀ source, source ∈ scc.sector.states →
    ∀ target, target ∈ scc.sector.states →
      GeneratedPathAt (fullFactorDecayLaw failure.index) source target
  occurrenceRoot :
    decay.decay.occurrence.root.rootOccurrence =
      CanonicalUnitArithmeticRoot.initialStep.generated.occurrence

noncomputable def generateFirstResidualFullFactorDecaySCC
    (failure : FirstResidualOccurrence) :
    RootGeneratedFirstResidualFullFactorDecaySCCAt failure := by
  let decay := generateFirstResidualFullFactorDecay failure
  let scc := generateMinimalClosedSCC decay.residual
  exact
    { decay := decay
      decay_eq := rfl
      scc := scc
      scc_eq := rfl
      sectorNonempty := scc.sector.nonempty
      sectorSubsetResidual := scc.sector.subsetResidual
      everyStateNonterminal := by
        intro state stateMem
        exact decay.residual.terminalEmpty state
          (scc.sector.subsetResidual stateMem)
      everyDecayChannelClosed := scc.sector.stepClosed
      pathBetween := scc.pathBetween
      occurrenceRoot := decay.occurrenceRoot }

end
end CanonicalUnitArithmeticFirstResidualFullFactorDecaySCCProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
