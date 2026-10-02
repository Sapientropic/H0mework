import H0mework.Foundation.Responsibility.JointSource.Native.Receipt

/-! Actual native source images transport their complete successor and joint
payer. These proofs are independent of the target authority vocabulary. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.TargetCommon
open SourceOperationEffects DebtActivationWorld DebtActivationLedger
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

theorem successor_support {base : SourceNativeSource N V} {current : V.Current}
    {occurrence : base.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt base occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    {write : V.NativeWriteAt current}
    {structural : base.toRootSource.actual.compile occurrence = .nativeWrite write}
    {target : base.toRootSource.actual.OccurrenceAt (V.nativeTarget write)}
    {evolution : LedgerWriteEvolutionAt N ⟨base.toRootSource.account.supportOf occurrence⟩
      ⟨base.toRootSource.account.supportOf target⟩}
    (same : generated = .nativeWrite write structural target evolution) :
    base.toRootSource.account.supportOf successor.targetOccurrence = base.toRootSource.account.supportOf target := by
  cases same
  rfl

theorem successor_ledger {base : SourceNativeSource N V} {current : V.Current}
    {occurrence : base.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt base occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    {write : V.NativeWriteAt current}
    {structural : base.toRootSource.actual.compile occurrence = .nativeWrite write}
    {target : base.toRootSource.actual.OccurrenceAt (V.nativeTarget write)}
    {evolution : LedgerWriteEvolutionAt N ⟨base.toRootSource.account.supportOf occurrence⟩
      ⟨base.toRootSource.account.supportOf target⟩}
    (same : generated = .nativeWrite write structural target evolution) :
    HEq successor.ledgerEvolution evolution := by
  cases same
  rfl

theorem joint_destination {law : DebtActivationLaw.{u}}
    {sourceSupport leftSupport rightSupport : N.Support}
    {left : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨leftSupport⟩}
    {right : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨rightSupport⟩}
    (supports : leftSupport = rightSupport) (same : HEq left right)
    (owner : OpenResponsibilityAt N sourceSupport)
    {before after : law.DebtState} (step : law.StepAt before after) :
    HEq (jointStepLedgerEvolution left owner step).destination
      (jointStepLedgerEvolution right owner step).destination := by
  cases supports
  exact heq_of_eq (congrArg (fun evolution => (jointStepLedgerEvolution evolution owner step).destination)
    (eq_of_heq same))

end RootGeneratedDebtActivationJointSource.Native.Request.TargetCommon
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
