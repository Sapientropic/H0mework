import H0mework.Foundation.Inquiry.EmptyObstruction
import H0mework.Foundation.Responsibility.DebtU7
import H0mework.Arithmetic.FockResponsibility.DebtActivation
import H0mework.Arithmetic.FockResponsibility.ProvenanceRecurrence

/-!
# Occurrence recurrence admitted to the activated debt U7 world

The path-generated Goldbach recurrence is the obstruction of the complete
occurrence-sensitive debt law.  The canonical arithmetic root has an empty
old obstruction surface, so its unique vacuous U7 calculus extends into the
activated debt world.  The recurrence then generates the live occurrence
debt row itself and the exact theory-audit receipt.

The original runtime occurrence, whole ledger and next remain explicit
provenance.  Installing this generated row in a target living root remains a
separate downstream responsibility.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockOccurrenceDebtU7Admission

open CanonicalUnitArithmeticGlobalGoldbachDisposition
open CanonicalUnitArithmeticOperationalFirstResidualProducer
open DebtActivationWorld
open ParticleWaveFockOccurrenceDebtActivation
open ParticleWaveFockOccurrenceResponsibility
open ParticleWaveFockOperationalProvenanceRecurrence
open RootGeneratedDebtActivationU7
open RootGeneratedEmptyObstructionU7

noncomputable section

def focus (failure : FirstResidualOccurrence) :
    CanonicalUnitArithmeticRoot.N.Support :=
  (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
    (failureDepth failure)).current.visit.current

abbrev Law (failure : FirstResidualOccurrence) :=
  activationLaw failure.index

abbrev DebtN (failure : FirstResidualOccurrence) :=
  DebtActivationWorld.ExtendedNetwork CanonicalUnitArithmeticRoot.N
    (Law failure)

def activeSupport (failure : FirstResidualOccurrence) :
    (DebtN failure).Support :=
  ⟨focus failure, some (returnedHistoryState failure)⟩

def recurrenceObstruction (failure : FirstResidualOccurrence) :
    (DebtN failure).ObstructionAt (activeSupport failure) :=
  debtObstruction (N := CanonicalUnitArithmeticRoot.N)
    (law := Law failure) (focus failure)
    (projectionRecurrenceResidual failure)

def oldU7 : U7ProducerCalculus CanonicalUnitArithmeticRoot.N :=
  RootGeneratedEmptyObstructionU7.producer
    CanonicalUnitArithmeticRoot.N
    CanonicalUnitArithmeticRoot.rootObstructionAt_isEmpty

def oldU7Calculus :
    U7ObstructionEvolutionCalculus CanonicalUnitArithmeticRoot.N oldU7 :=
  RootGeneratedEmptyObstructionU7.calculus
    CanonicalUnitArithmeticRoot.N
    CanonicalUnitArithmeticRoot.rootObstructionAt_isEmpty

abbrev debtU7 (failure : FirstResidualOccurrence) :
    U7ProducerCalculus (DebtN failure) :=
  RootGeneratedDebtActivationU7.extendU7 oldU7

abbrev debtU7Calculus (failure : FirstResidualOccurrence) :
    U7ObstructionEvolutionCalculus (DebtN failure) (debtU7 failure) :=
  RootGeneratedDebtActivationU7.extendU7Calculus oldU7 oldU7Calculus

def recurrenceU7Event (failure : FirstResidualOccurrence) :=
  (debtU7Calculus failure).source.emit
    (recurrenceObstruction failure)

def recurrenceDebtEntry (failure : FirstResidualOccurrence) :
    OpenResponsibilityAt (DebtN failure) (activeSupport failure) :=
  debtEntry (N := CanonicalUnitArithmeticRoot.N)
    (law := Law failure) (focus failure) (returnedHistoryState failure)

theorem recurrenceU7Event_entry (failure : FirstResidualOccurrence) :
    U7ActualSuccessorSource.demandEntry (recurrenceU7Event failure) =
      recurrenceDebtEntry failure :=
  RootGeneratedDebtActivationU7.debt_demand_entry oldU7 oldU7Calculus
    (law := Law failure)
    (focus failure) (projectionRecurrenceResidual failure)

theorem recurrenceU7Event_disposition
    (failure : FirstResidualOccurrence) :
    ((debtU7Calculus failure).compile
      (recurrenceU7Event failure)).disposition =
      .requiresTheoryAudit
        (debtObstructionReceipt (N := CanonicalUnitArithmeticRoot.N)
          (law := Law failure) (focus failure)
          (projectionRecurrenceResidual failure)) :=
  RootGeneratedDebtActivationU7.debt_compiled_disposition
    (law := Law failure)
    oldU7 oldU7Calculus (focus failure)
      (projectionRecurrenceResidual failure)

def recurrenceU7TheoryAudit (failure : FirstResidualOccurrence) :
    SourceNativeU7TheoryAuditAt
      (debtU7Calculus failure) (recurrenceU7Event failure) :=
  RootGeneratedDebtActivationU7.debt_theoryAudit
    (law := Law failure)
    oldU7 oldU7Calculus (focus failure)
      (projectionRecurrenceResidual failure)

@[simp] theorem recurrenceDebtEntry_claim
    (failure : FirstResidualOccurrence) :
    (recurrenceDebtEntry failure).claim =
      (DebtN failure).obstructionClaim (recurrenceObstruction failure) :=
  rfl

/-- Exact debt U7 row and original runtime provenance in one package. -/
structure RootLinkedOccurrenceDebtU7AdmissionAt
    (failure : FirstResidualOccurrence) : Type 7 where
  private mk ::
  rootedRecurrence : RootGeneratedOperationalProjectionRecurrenceAt failure
  rootedRecurrence_eq : rootedRecurrence = generateRooted failure
  obstruction : (DebtN failure).ObstructionAt (activeSupport failure)
  obstruction_eq : obstruction = recurrenceObstruction failure
  row : OpenResponsibilityAt (DebtN failure) (activeSupport failure)
  row_eq : row = recurrenceDebtEntry failure
  event : (debtU7Calculus failure).source.EventAt obstruction
    ((debtU7 failure).generateDemand obstruction)
  event_heq : HEq event (recurrenceU7Event failure)
  demandEntry_heq : HEq (U7ActualSuccessorSource.demandEntry event) row
  theoryAudit : SourceNativeU7TheoryAuditAt
    (debtU7Calculus failure) event
  sourceOccurrence :
    (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimePayload
      (failureDepth failure)).sourceOccurrence =
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
        (failureDepth failure)).emittedOccurrence
  wholeLedger :
    HEq
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
        (failureDepth failure)).tick.generated.wholeLedgerWriteBack
      ((CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
        (failureDepth failure)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
          (failureDepth failure)).current.visit.current)
  generatedNext :
    (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
      (failureDepth failure)).tick.nextCurrent =
      CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeFacade.process.stateAt
        (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeFacade.process.successor
          (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
            (failureDepth failure)).state)

noncomputable def generate
    (failure : FirstResidualOccurrence) :
    RootLinkedOccurrenceDebtU7AdmissionAt failure :=
  { rootedRecurrence := generateRooted failure
    rootedRecurrence_eq := rfl
    obstruction := recurrenceObstruction failure
    obstruction_eq := rfl
    row := recurrenceDebtEntry failure
    row_eq := rfl
    event := recurrenceU7Event failure
    event_heq := HEq.rfl
    demandEntry_heq := heq_of_eq (recurrenceU7Event_entry failure)
    theoryAudit := recurrenceU7TheoryAudit failure
    sourceOccurrence := (generateRooted failure).sourceOccurrence
    wholeLedger := (generateRooted failure).wholeLedger
    generatedNext := (generateRooted failure).generatedNext }

end

end ParticleWaveFockOccurrenceDebtU7Admission
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
