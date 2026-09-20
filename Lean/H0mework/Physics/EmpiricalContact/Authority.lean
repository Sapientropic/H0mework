import H0mework.Physics.EmpiricalContact.Source

/-! Authority of the contact epoch: all original physical projections remain
available, alongside the same-account contact/residual and generated demand. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite

noncomputable section

def u7 : U7ProducerCalculus N where
  DemandAt := fun {where_} _ => OpenResponsibilityAt N where_
  generateDemand := fun {where_} _ => entry where_

private def successorSource : U7ActualSuccessorSource N u7 where
  EventAt := fun obstruction demand => SourceGeneratedU7DemandAt u7 obstruction demand
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {where_} {_obstruction} {_demand} _ => entry where_

private def continuingReceipt (where_ : Support) : N.DispositionAt where_ .transfer := by
  cases where_ with
  | mk physical contact =>
      cases physical with
      | inl current => exact .inherited (.inherited (.transfer (rootActionAt current)))
      | inr state => exact .inherited (.transfer (materialActionAt (.running state)))

/-- Continuing the same account does not claim to have explained the discrepancy. -/
def calculus : U7ObstructionEvolutionCalculus N u7 where
  source := successorSource
  compile := fun {where_} {obstruction} {_demand} _event =>
    { disposition := .redirected (successor := obstruction)
        ⟨continuingReceipt where_, rfl⟩
      demandEntryDisposition :=
        ⟨.transferred (continuingReceipt where_) rfl rfl (Nat.le_refl _), rfl⟩ }

inductive Projection
  | inherited (coordinate : SpinPair.Projection)
  | field
  | ledger
  | residual
  | contact
  | auditDemand
  | compilation
  | consumer

private def projectionLaw : SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .inherited coordinate => SpinPair.authoritativeRoot.source.projectionLaw.PayloadAt
        coordinate (SpinPair.emitted (underlying current)) PUnit.unit
    | .field => Stage9DEF.Source.OccupiedField
    | .ledger => SourceNativeLedgerEvolutionAt source occurrence
    | .residual => Responsibility
    | .contact => Option ReleasedContact
    | .auditDemand => Option (N.ObstructionAt (support current))
    | .compilation => SourceNativeInquiryCompilationTokenAt
        (U7 := u7) (calculus := calculus) (oldTheory := TheoryState.rootSemantic N)
        (entry (support current)) PUnit.unit (ULift.up.{1, 0} occurrence)
        .answered (Option (N.ObstructionAt (support current)))
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit
        (ULift.up.{1, 0} occurrence) (entry (support current)) (auditDemand current)
  project := fun projection {current} occurrence _ => match projection with
    | .inherited coordinate => SpinPair.authoritativeRoot.source.projectionLaw.project
        coordinate (SpinPair.emitted (underlying current)) PUnit.unit
    | .field => fieldAt current
    | .ledger => generatedEvolution occurrence
    | .residual => residual (support current)
    | .contact => (support current).2
    | .auditDemand => auditDemand current
    | .compilation => .canonical (auditDemand current)
    | .consumer => .canonical

private def authoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := restructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal restructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def initialVisit : SourceNativeTemporalVisitAt livingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite livingRoot.toAuthoritativeRoot.toRoot.initialVisit

def initialGenerated := livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit initialVisit

def initialEntryRow : initialGenerated.GeneratedEntryRowAt (entry (support .ingress)) :=
  (initialGenerated.canonicalGeneratedEntryRow? (entry (support .ingress))).get (by rfl)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    initialGenerated.occurrence initialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? initialGenerated.wholeLedgerWriteBack).get (by rfl)

theorem first_contact : (support firstSuccessor.targetCurrent).2 = some releasedContact := rfl

theorem first_residual : (residual (support firstSuccessor.targetCurrent)).2 =
    some (releasedContact, contactResidual releasedContact) := rfl

theorem first_demand : (auditDemand firstSuccessor.targetCurrent).isSome = true := received_auditDemand

def visit : Nat → SourceNativeTemporalVisitAt livingRoot.toAuthoritativeRoot.toLedgerRoot
  | 0 => initialVisit
  | n + 1 => (visit n).next rfl

def authorityAt : (n : Nat) → SourceNativeLivingTemporalCausalEntryAuthorityAt
    livingRoot (visit n) (entry (support (visit n).current))
  | 0 => .generatedFromInitialRow livingRoot (entry (support .ingress)) initialEntryRow
  | n + 1 => (authorityAt n).next rfl

def answerFace (n : Nat) : SourceNativeRootSemanticFaceAt livingRoot (visit n) :=
  ⟨.auditDemand, PUnit.unit, rfl⟩

def answerConsumer (n : Nat) : SourceNativeInquiryAnswerConsumerAt PUnit.unit
    (ULift.up.{1, 0} (livingRoot.emitted (visit n).current))
    (entry (support (visit n).current)) (answerFace n) :=
  ⟨.consumer, PUnit.unit, rfl, HEq.rfl⟩

def readProgram (n : Nat) : SourceNativeInquiryCompilationProgramAt livingRoot (visit n)
    u7 calculus (TheoryState.rootSemantic N) PUnit.unit
    (ULift.up.{1, 0} (livingRoot.emitted (visit n).current))
    (entry (support (visit n).current)) (authorityAt n) where
  compile := fun _ => .answered (answerFace n) (answerConsumer n)

def readState (n : Nat) : RootInquiryStateAt N V where
  root := livingRoot
  visit := visit n
  U7 := u7
  calculus := calculus
  Query := PUnit
  entryAt := fun _ => entry (support (visit n).current)
  authorityAt := fun _ => authorityAt n
  compilationProgramAt := fun query => by cases query; exact readProgram n
  compilationFaceAt := fun query => by cases query; exact ⟨.compilation, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by intro query obstruction audit equality; cases query; cases equality

def readPresentation (n : Nat) : RootInquiryStatePresentation := ⟨N, V, .create (readState n)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch
