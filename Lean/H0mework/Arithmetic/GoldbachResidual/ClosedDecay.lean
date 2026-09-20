import H0mework.Arithmetic.Goldbach.GlobalDisposition
import H0mework.Arithmetic.GoldbachDynamics.DecayReachability

/-!
# First residual forces a repair/emission closed sector

Any terminal of the combined decay graph materializes the same effective
additive fibre.  A hypothetical first residual therefore forces the complete
reachable branch closed under both factor repair and prime-factor emission.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFirstResidualFullFactorDecayProducer

open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticFullFactorDecayReachabilityProducer
open CanonicalUnitArithmeticGlobalGoldbachDisposition

noncomputable section

abbrev FirstResidualFullFactorDecayClosedAt
    (failure : FirstResidualOccurrence) :=
  FullFactorDecayClosedResidualAt failure.index failure.indexInRange

structure FirstResidualFullFactorDecayClosedSelectionAt
    (failure : FirstResidualOccurrence) : Type where
  private mk ::
  residual : FirstResidualFullFactorDecayClosedAt failure
  disposition_eq : generatedFullFactorDecayDisposition
    failure.index failure.indexInRange = .closed residual

noncomputable def generateFirstResidualFullFactorDecayClosedSelection
    (failure : FirstResidualOccurrence) :
    FirstResidualFullFactorDecayClosedSelectionAt failure := by
  cases dispositionEq : generatedFullFactorDecayDisposition
      failure.index failure.indexInRange with
  | inhabited _reachability fibre _fibre_eq =>
      exact (failure.fibreEmpty ⟨fibre⟩).elim
  | closed residual => exact ⟨residual, dispositionEq⟩

noncomputable def generateFirstResidualFullFactorDecayClosed
    (failure : FirstResidualOccurrence) :
    FirstResidualFullFactorDecayClosedAt failure :=
  (generateFirstResidualFullFactorDecayClosedSelection failure).residual

theorem generatedFullFactorDecayDisposition_eq_closed
    (failure : FirstResidualOccurrence) :
    generatedFullFactorDecayDisposition failure.index failure.indexInRange =
      .closed (generateFirstResidualFullFactorDecayClosed failure) :=
  (generateFirstResidualFullFactorDecayClosedSelection failure).disposition_eq

structure RootGeneratedFirstResidualFullFactorDecayAt
    (failure : FirstResidualOccurrence) : Type 7 where
  private mk ::
  decay : RootGeneratedFullFactorDecayReachabilityAt
    failure.index failure.indexInRange
  decay_eq : decay = generatedFullFactorDecayReachabilityFace
    failure.index failure.indexInRange
  residual : FirstResidualFullFactorDecayClosedAt failure
  residual_eq : residual = generateFirstResidualFullFactorDecayClosed failure
  dispositionIsClosed : decay.disposition = .closed residual
  occurrenceRoot :
    decay.occurrence.root.rootOccurrence =
      CanonicalUnitArithmeticRoot.initialStep.generated.occurrence
  currentFibreEmpty : ¬ Nonempty (EffectiveAdditiveFibreAt failure.index)

noncomputable def generateFirstResidualFullFactorDecay
    (failure : FirstResidualOccurrence) :
    RootGeneratedFirstResidualFullFactorDecayAt failure := by
  let decay := generatedFullFactorDecayReachabilityFace
    failure.index failure.indexInRange
  let residual := generateFirstResidualFullFactorDecayClosed failure
  exact
    { decay := decay
      decay_eq := rfl
      residual := residual
      residual_eq := rfl
      dispositionIsClosed := by
        change generatedFullFactorDecayDisposition
          failure.index failure.indexInRange = .closed residual
        exact generatedFullFactorDecayDisposition_eq_closed failure
      occurrenceRoot := decay.occurrenceRoot
      currentFibreEmpty := failure.fibreEmpty }

end
end CanonicalUnitArithmeticFirstResidualFullFactorDecayProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
