import H0mework.Arithmetic.Goldbach.GlobalDisposition
import H0mework.Arithmetic.GoldbachDynamics.Runtime

/-!
# Operational identification of the first residual

`FirstResidualOccurrence` no longer mints an occurrence.  Its least-index
proof only identifies the already existing canonical runtime visit at depth
`index - 1`.  The residual disposition is read from that visit's installed
operational projection, with the visit's own ledger and generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticOperationalFirstResidualProducer

open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticGlobalGoldbachDisposition
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open SourceGeneratedEffectiveFibreDisposition

noncomputable section

def failureDepth (failure : FirstResidualOccurrence) : Nat :=
  failure.index - 1

theorem failureDepth_succ_eq_index (failure : FirstResidualOccurrence) :
    failureDepth failure + 1 = failure.index := by
  unfold failureDepth
  have indexInRange := failure.indexInRange
  omega

theorem failureRuntimeIndex (failure : FirstResidualOccurrence) :
    scanIndex (runtimeAt (failureDepth failure)).current.visit.current =
      failure.index := by
  rw [runtimeAt_scanIndex, failureDepth_succ_eq_index]

def residualDisposition {index : Nat}
    (residual : EffectiveAdditiveResidualAt index) :
    EffectiveAdditiveDispositionAt index :=
  .residual residual

theorem runtimePayload_disposition_heq_residual
    (failure : FirstResidualOccurrence) :
    HEq (runtimePayload (failureDepth failure)).additiveDisposition
      (residualDisposition failure.residual) := by
  rw [(runtimePayload (failureDepth failure)).additiveDisposition_eq]
  rw [failureRuntimeIndex failure]
  exact heq_of_eq failure.disposition_eq

structure RootGeneratedOperationalFirstResidualAt
    (failure : FirstResidualOccurrence) : Type 7 where
  private mk ::
  residual : EffectiveAdditiveResidualAt failure.index
  residual_eq : residual = failure.residual
  runtimeIndex :
    scanIndex (runtimeAt (failureDepth failure)).current.visit.current =
      failure.index
  dispositionIsResidual : HEq
    (runtimePayload (failureDepth failure)).additiveDisposition
      (residualDisposition residual)
  namedReadout :
    runtimeFacade.readoutAt (runtimeAt (failureDepth failure))
        .operationalGoldbach =
      .inl ⟨runtimeActive (failureDepth failure),
        runtimePayload (failureDepth failure)⟩
  sourceOccurrence :
    (runtimePayload (failureDepth failure)).sourceOccurrence =
      (runtimeAt (failureDepth failure)).emittedOccurrence
  targetRoot :
    (runtimePayload (failureDepth failure)).targetOccurrence.root.rootOccurrence =
      (runtimeAt (failureDepth failure)).emittedOccurrence
  emittedOccurrence :
    runtimeFacade.process.toAnswerNextCausalWorld.emitted
          (ULift.up (runtimeAt (failureDepth failure)).state) =
      ULift.up (runtimeAt (failureDepth failure)).tick.generated
  occurrenceRoot :
    (runtimeAt (failureDepth failure)).tick.generated.occurrence =
      (runtimeAt (failureDepth failure)).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (runtimeAt (failureDepth failure)).current.visit.current
  wholeLedger :
    HEq (runtimeAt (failureDepth failure)).tick.generated.wholeLedgerWriteBack
      ((runtimeAt (failureDepth failure)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt (failureDepth failure)).current.visit.current)
  projectionFactorizes :
    HEq
      (runtimeFacade.readoutAt (runtimeAt (failureDepth failure))
        .operationalGoldbach)
      ((runtimeAt (failureDepth failure)).tick.generated.projectionOutcome
        ((runtimeFacade.installationAt
          (runtimeAt (failureDepth failure)) .operationalGoldbach).embed
          (runtimeFacade.projectionAt
            (runtimeAt (failureDepth failure)) .operationalGoldbach)))
  generatedNext :
    (runtimeAt (failureDepth failure)).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor
          (runtimeAt (failureDepth failure)).state)

noncomputable def generateOperationalFirstResidual
    (failure : FirstResidualOccurrence) :
    RootGeneratedOperationalFirstResidualAt failure := by
  have factorization := coversAt_factorizes
    (runtimeAt (failureDepth failure)) .operationalGoldbach
  exact
    { residual := failure.residual
      residual_eq := rfl
      runtimeIndex := failureRuntimeIndex failure
      dispositionIsResidual :=
        runtimePayload_disposition_heq_residual failure
      namedReadout := runtimeReadout_is_operational (failureDepth failure)
      sourceOccurrence :=
        (runtimePayload (failureDepth failure)).sourceOccurrence_eq
      targetRoot := (runtimePayload (failureDepth failure)).targetRoot
      emittedOccurrence := factorization.1
      occurrenceRoot := factorization.2.1
      wholeLedger := factorization.2.2.1
      projectionFactorizes := factorization.2.2.2.1
      generatedNext := factorization.2.2.2.2 }

end
end CanonicalUnitArithmeticOperationalFirstResidualProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
