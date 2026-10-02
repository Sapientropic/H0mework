import H0mework.Foundation.Ledger.ProofRelevantRestructuring
import H0mework.Foundation.Responsibility.DebtPositiveLedger
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

/-! # Authoritative root for a direct positive debt activation -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedDebtActivationDirectPositive

open DebtActivationLedger
open RootGeneratedDebtActivationDirect
open RootGeneratedProofRelevantRestructuring

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {LowerV : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure N LowerV}
variable {lowerCurrent : LowerV.Current}
variable {activation : OccurrenceIndexedSourceAt lower lowerCurrent}
variable (positive : GeneratedPositiveAt activation)

def restructuringLaw : SourceNativeLedgerRestructuringLaw
    (rootSource positive) :=
  RootGeneratedProofRelevantRestructuring.law activation.World
    (supportAt positive .live) (rootSource positive)

def restructuringCertification
    {current : (V positive).Current}
    (occurrence :
      (rootSource positive).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (restructuringLaw positive) ((ledgerCompiler positive).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event with
  | terminal => exact PUnit.unit
  | payment =>
      change ExactLedgerRestructuringCertificationAt
        (restructuringLaw positive) (paymentOccurrence positive)
        (paymentPatch positive).toLedgerWriteEvolution
      rw [paymentPatch_evolution]
      exact ExactLedgerRestructuringCertificationAt.ofInjective
        (by
          intro left right equality
          rw [← stepLedgerEvolution_destination_origin
            activation.lowerSupport positive.step left,
            ← stepLedgerEvolution_destination_origin
              activation.lowerSupport positive.step right]
          exact congrArg
            (fun entry =>
              ((paymentEvolution positive).destination entry).1) equality)
        (by
          intro left right equality
          rw [← stepLedgerEvolution_origin_destination
            activation.lowerSupport positive.step left,
            ← stepLedgerEvolution_origin_destination
              activation.lowerSupport positive.step right]
          exact congrArg
            (fun entry => ((paymentEvolution positive).origin entry).1) equality)

def restructuringCompiler : SourceNativeRestructuringLedgerCompiler
    (rootSource positive) where
  ledgerCompiler := ledgerCompiler positive
  restructuringLaw := restructuringLaw positive
  certifyRestructuring := restructuringCertification positive

def restructuringSource : SourceNativeRestructuringLedgerSource
    activation.World (V positive) where
  source := rootSource positive
  compiler := restructuringCompiler positive

def projectionLaw : SourceNativeProjectionLaw (ledgerSource positive) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _ {current} _ _ =>
    match current with
    | .live => ULift.{u, 0}
        (PLift (activation.generatedDisposition = .step positive.step))
    | .paid => activation.law.SupportTerminalAt positive.target
  project := by
    intro projection current occurrence active
    cases current with
    | live => exact ULift.up (PLift.up positive.generated_eq)
    | paid => exact positive.terminal

theorem paidActualOutgoing_isEmpty :
    IsEmpty (SourceNativeActualOutgoingEventAt (ledgerSource positive) .paid) := by
  constructor
  rintro ⟨⟨support, event⟩, successor⟩
  cases event with
  | terminal => exact nomatch successor

def eventInventoryAdmission : SourceNativeCompleteEventInventoryAdmission
    (restructuringSource positive) :=
  SourceNativeCompleteEventInventoryAdmission.refl
    (restructuringSource positive) <| by
      intro current occurrence terminalPayload terminal_eq
      cases current with
      | live => exact False.elim (nomatch terminalPayload)
      | paid => exact paidActualOutgoing_isEmpty positive

def authoritySource : SourceNativeAuthoritySource activation.World (V positive) where
  restructuringSource := restructuringSource positive
  eventInventoryAdmission := eventInventoryAdmission positive
  lawSurface := .rootSemantic activation.World
  projectionLaw := projectionLaw positive

def authoritativeRoot : SourceNativeAuthoritativeRootClosure
    activation.World (V positive) where
  source := authoritySource positive
  emitted := (ledgerRoot positive).emitted
  compiler_commutes := (ledgerRoot positive).compiler_commutes

def initialVisit : RootVisit (authoritativeRoot positive).toRoot :=
  (authoritativeRoot positive).toRoot.initialVisit

def paidVisit : RootVisit (authoritativeRoot positive).toRoot :=
  (initialVisit positive).next (by rfl)

def paidTerminalAuthority : SourceFaithfulTerminalOccurrenceAt
    (authoritySource positive)
    ((authoritativeRoot positive).emitted (paidVisit positive).current) where
  terminal := positive.terminal
  structural_eq := rfl
  ledgerEvolution := (terminalPatch positive).toLedgerTerminalEvolution
  generated_eq := rfl

end


end RootGeneratedDebtActivationDirectPositive
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
