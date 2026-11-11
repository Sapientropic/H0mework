import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteStep
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStepPayment
open SourceOperationEffects SourceOperationExecution DebtActivationWorld

namespace BF
export OriginalKBFiniteCalculation (Value Var Base reader)
end BF
namespace Step
export OriginalTotalSourceBFiniteStep (read)
end Step
namespace Pay
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment
  (entry debtCurrent activePayment activeContinuation lineage destination_entry current_state budget wellFounded)
end Pay

private def PaidAt
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Sorts : Type} {Value Var : Sorts → Type} [∀ target, AddCommGroup (Value target)] {sort : Sorts}
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := sort))
    (index : Fin (remaining (RootGeneratedDebtActivationJointSource.OwnerFree.raw old origin reader).expression)) :=
  PProd (SourceNativeRootDebtPaymentStepAt (Pay.debtCurrent old origin reader index.1))
    (PProd (SourceNativePaidRootDebtMacroContinuationAt (Pay.debtCurrent old origin reader index.1))
      (PProd (RootDebtLineageAt _ (Pay.entry old origin reader 0) (Pay.entry old origin reader index.1))
        ((Pay.entry old origin reader index.1).claim =
          .inr (RootGeneratedDebtActivationJointSource.OwnerFree.raw old origin reader).expression ∧
        ((RootGeneratedDebtActivationJointSource.OwnerFree.whole old origin reader
            (RootGeneratedDebtActivationJointSource.OwnerFree.finiteVisit old origin reader index.1).current).destination
          (Pay.entry old origin reader index.1)).1 = Pay.entry old origin reader (index.1 + 1) ∧
        (RootGeneratedDebtActivationJointSource.OwnerFree.finiteVisit old origin reader index.1).current =
          RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state old origin reader index.1 ∧
        (Pay.debtCurrent old origin reader index.1).budget =
          remaining (RootGeneratedDebtActivationJointSource.OwnerFree.raw old origin reader).expression - index.1 ∧
        WellFounded (SourceNativePaidRootDebtContinuationRel
          (process := RootGeneratedDebtActivationJointSource.OwnerFree.process old origin reader)
          (origin := Pay.entry old origin reader 0)))))

private def paidAt
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Sorts : Type} {Value Var : Sorts → Type} [∀ target, AddCommGroup (Value target)] {sort : Sorts}
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := sort))
    (index : Fin (remaining (RootGeneratedDebtActivationJointSource.OwnerFree.raw old origin reader).expression)) :
    PaidAt old origin reader index :=
  ⟨Pay.activePayment old origin reader index, Pay.activeContinuation old origin reader index,
    Pay.lineage old origin reader index.1, rfl, Pay.destination_entry old origin reader index.1,
    Pay.current_state old origin reader index.1, Pay.budget old origin reader index.1,
    Pay.wellFounded old origin reader⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
variable {current : CanonicalUnitArithmeticRoot.V.Current}
variable (occurrence : BF.Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current)

private def ResultAt :=
  Σ actual : type_of% (Step.read observation nontrivial half occurrence),
    PProd (actual = Step.read observation nontrivial half occurrence)
      (PaidAt (Value := BF.Value) (Var := BF.Var) (sort := ()) BF.Base current
        (fun _ => BF.reader observation nontrivial half occurrence) actual.1.2)

/-- The R cursor chooses the original BF syntax row's paid stage; its full read is retained. -/
opaque read : ResultAt observation nontrivial half occurrence :=
  let actual := Step.read observation nontrivial half occurrence
  ⟨actual, rfl, paidAt (Value := BF.Value) (Var := BF.Var) (sort := ()) BF.Base current
    (fun _ => BF.reader observation nontrivial half occurrence) actual.1.2⟩

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStepPayment
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
