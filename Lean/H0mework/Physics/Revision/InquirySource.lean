import H0mework.Foundation.Inquiry.Protocol
import H0mework.Physics.GravityTail.FixedRootNativeWrite

/-! Primitive inquiry inputs for the fixed physical source. The U7 demand
retains its existing name and row. The neutral transfer calculus is used only
as the type index of positive inquiry compilation; it supplies neither a
strict U7 answer nor an expressibility-audit gate. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField

noncomputable section

namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext

structure RootResidualDemandAt
    {support : N.Support} (_obstruction : N.ObstructionAt support) : Type where
  private mk ::
  entry : OpenResponsibilityAt N support
  entry_eq : entry = rootLedgerEntry support

namespace RootResidualDemandAt

def generated
    {support : N.Support} (obstruction : N.ObstructionAt support) :
    RootResidualDemandAt obstruction :=
  ⟨rootLedgerEntry support, rfl⟩

theorem eq_generated
    {support : N.Support} {obstruction : N.ObstructionAt support}
    (demand : RootResidualDemandAt obstruction) :
    demand = generated obstruction := by
  rcases demand with ⟨entry, entry_eq⟩
  cases entry_eq
  rfl

end RootResidualDemandAt

def rootU7 : U7ProducerCalculus N where
  DemandAt := RootResidualDemandAt
  generateDemand := RootResidualDemandAt.generated

end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext

namespace Stage9C.Revision.InquirySource

open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext

def source : U7ActualSuccessorSource N rootU7 where
  EventAt := fun obstruction demand =>
    SourceGeneratedU7DemandAt rootU7 obstruction demand
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {support} {_obstruction} {_demand} _ => rootLedgerEntry support

def calculus : U7ObstructionEvolutionCalculus N rootU7 where
  source := source
  compile := fun {support} {obstruction} {_demand} _event =>
    { disposition := .redirected (successor := obstruction)
        ⟨.transfer (rootActionAt support), rfl⟩
      demandEntryDisposition :=
        ⟨.transferred (.transfer (rootActionAt support)) rfl rfl (Nat.le_refl _), rfl⟩ }

theorem calculus_has_no_strict_answer {support : N.Support}
    (obstruction : N.ObstructionAt support) :
    IsEmpty (SourceNativeU7AnswersAt calculus obstruction) :=
  ⟨fun answer => Nat.lt_irrefl _ answer.down.down⟩

abbrev ConfigurationTokenAt {current : RootCurrent}
    (occurrence : rootLedgerSource.source.toRootSource.actual.OccurrenceAt current) :
    Type := SourceNativeInquiryCompilationTokenAt
      (U7 := rootU7) (calculus := calculus)
      (oldTheory := TheoryState.rootSemantic N)
      (rootLedgerEntry current) PUnit.unit
      (ULift.up.{1, 0} occurrence) .answered StageNineHolonomicConfiguration

def configurationToken {current : RootCurrent}
    (occurrence : rootLedgerSource.source.toRootSource.actual.OccurrenceAt current) :
    ConfigurationTokenAt occurrence :=
  .canonical current.configuration

def cartanActionToken {current : RootCurrent}
    (occurrence : rootLedgerSource.source.toRootSource.actual.OccurrenceAt current) :
    ConfigurationTokenAt occurrence :=
  .canonical
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      positiveSmoothUnifiedSource current.configuration)

def configurationConsumerToken {current : RootCurrent}
    (occurrence : rootLedgerSource.source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit
      (ULift.up.{1, 0} occurrence) (rootLedgerEntry current) current.configuration :=
  .canonical

end Stage9C.Revision.InquirySource
end
end SaturationMonoid.PhysicsCore
