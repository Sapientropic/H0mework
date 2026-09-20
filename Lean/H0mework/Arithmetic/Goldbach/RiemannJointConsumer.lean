import H0mework.Arithmetic.UnitArithmetic.SettlementFacade

/-!
# Joint Goldbach--Riemann consumer on the canonical arithmetic occurrence

This consumer simultaneously opens the named pointwise Goldbach disposition,
unit-normalized relation history, full-Euler determinant action,
prime-power rigidity, and perfect determinant/unit faces.  Every named face
is consumed together with the facade's exact runtime occurrence,
whole-ledger write-back, and generated next current.

No Goldbach branch, Euler action, rigidity result, determinant object, ledger
receipt, or successor is a caller premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticGoldbachRiemannJointConsumer

open CanonicalUnitArithmeticEffectiveAdditiveConsumer
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticGeneratedSettlementFacade
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticUnitNormalizedEulerDeterminantAction
open CanonicalUnitArithmeticUnitNormalizedRelationHistory

noncomputable section

/-- Exact named-face coverage paired with the one runtime receipt. -/
abbrev NamedFaceFactorizesAt (face : FaceAt) : Prop :=
  CoversAt generatedFacade face ∧
    (runtimeAt 0).tick.generated.occurrence =
      (runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (runtimeAt 0).current.visit.current ∧
    HEq (runtimeAt 0).tick.generated.wholeLedgerWriteBack
      ((runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt 0).current.visit.current) ∧
    (runtimeAt 0).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt 0).state)

theorem namedFaceFactorizes (face : FaceAt) :
    NamedFaceFactorizesAt face :=
  coversAt_factorizes face

/-- Direct joint consumer.  The Goldbach branch remains data in `Type`; the
other fields are the concrete named-face laws already generated from the same
canonical runtime. -/
structure JointConsumesAt (index : Nat) : Type 7 where
  goldbach :
    TotalConsumesAt index (generatedFacade.additiveDisposition index)
  goldbachCoefficientFace :
    NamedFaceFactorizesAt .goldbachAdditiveCoefficient
  goldbachFace : NamedFaceFactorizesAt .goldbachAdditiveDisposition
  goldbachFactorRepairFace :
    NamedFaceFactorizesAt .goldbachFactorRepairOrbit
  goldbachFullFactorReachabilityFace :
    NamedFaceFactorizesAt .goldbachFullFactorReachability
  goldbachFullFactorDecayReachabilityFace :
    NamedFaceFactorizesAt .goldbachFullFactorDecayReachability
  relationHistoryFace : NamedFaceFactorizesAt .unitNormalizedRelationHistory
  fullEulerFace : NamedFaceFactorizesAt .fullEulerDeterminantAction
  rigidityFace : NamedFaceFactorizesAt .primePowerRigidity
  determinantUnitFace : NamedFaceFactorizesAt .perfectDeterminantUnit
  runtimeFace : NamedFaceFactorizesAt .runtimeWholeLedgerAndNext
  eulerRoot_eq_history : twoLevelDeterminantNaturality.root = history.root
  historyRoot_eq_factorization :
    history.root =
      CanonicalUnitArithmeticUnitNormalizedRelationHistory.rootOccurrence
  historyRoot_projects_to_runtime :
    history.root.map Sigma.fst = runtimeOccurrence 0
  goldbachRoot_eq_runtime :
    (evenTargetOccurrence index).root.rootOccurrence =
      (runtimeAt 0).tick.generated.occurrence
  wholeLedger :
    HEq (runtimeAt 0).tick.generated.wholeLedgerWriteBack
      ((runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt 0).current.visit.current)
  generatedNext :
    (runtimeAt 0).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt 0).state)

/-- The joint consumer is generated solely from the fixed named facade. -/
noncomputable def consume (index : Nat) : JointConsumesAt index := by
  let goldbach := goldbachDispositionCoverage index
  let relation := namedFaceFactorizes .unitNormalizedRelationHistory
  let euler := namedFaceFactorizes .fullEulerDeterminantAction
  exact
    { goldbach := goldbach
      goldbachCoefficientFace :=
        namedFaceFactorizes .goldbachAdditiveCoefficient
      goldbachFace := namedFaceFactorizes .goldbachAdditiveDisposition
      goldbachFactorRepairFace :=
        namedFaceFactorizes .goldbachFactorRepairOrbit
      goldbachFullFactorReachabilityFace :=
        namedFaceFactorizes .goldbachFullFactorReachability
      goldbachFullFactorDecayReachabilityFace :=
        namedFaceFactorizes .goldbachFullFactorDecayReachability
      relationHistoryFace := relation
      fullEulerFace := euler
      rigidityFace := namedFaceFactorizes .primePowerRigidity
      determinantUnitFace := namedFaceFactorizes .perfectDeterminantUnit
      runtimeFace := namedFaceFactorizes .runtimeWholeLedgerAndNext
      eulerRoot_eq_history := euler.1.2.1
      historyRoot_eq_factorization := relation.1.2.1
      historyRoot_projects_to_runtime := by
        rw [relation.1.2.1]
        exact factorizationOccurrence_projects_to_runtime 0
      goldbachRoot_eq_runtime :=
        goldbach.occurrenceRoot.trans goldbach.runtimeOccurrence.symm
      wholeLedger := goldbach.wholeLedger
      generatedNext := goldbach.generatedNext }

theorem consumes_all_named_authority (index : Nat) :
    Nonempty (JointConsumesAt index) :=
  ⟨consume index⟩

end
end CanonicalUnitArithmeticGoldbachRiemannJointConsumer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
