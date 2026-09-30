import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Joint
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeAction.Elimination

/-! The genuine Type 3 action receipt is covered as a complete dependent
family, with its selected value recovered from the actual factory output.
This is the receipt field of the action; other action fields are assembled
from their own already formed source values. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionReceipt
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit event entry authority

theorem every_target_receipt (target : Target) (oldRank : Ordinal.{0})
    (oldMaterial : MotherArenaHigher.Material oldRank) :
    ∃ rank : Ordinal.{3}, ∃ material : MotherReceiptHigher.Material rank,
      ∃ originalAddress : MotherArenaHigher.Base oldRank ↪ MotherReceiptHigher.Base rank,
      ∃ formed : (MotherReceiptPayload.formJoint material).isSome,
      ∃ presentation : MotherReceiptPayload.Presentation target.Answer target.Receipt
          ⟨target.answer, target.receipt⟩ ((MotherReceiptPayload.formJoint material).get formed),
        MotherReceiptPayload.readArena oldRank originalAddress material = oldMaterial ∧
        presentation.restrict = ⟨target.answer, target.receipt⟩ ∧
        Function.LeftInverse (MotherReceiptHigher.restrictArena oldRank rank originalAddress)
          (MotherReceiptHigher.includeArena oldRank rank originalAddress) := by
  obtain ⟨rank, material, value, address, formed, recovered, ⟨presentation⟩, retains⟩ :=
    MotherReceiptPayload.every_payload_and_arena oldRank oldMaterial target.Answer target.Receipt
      ⟨target.answer, target.receipt⟩
  have available : (MotherReceiptPayload.formJoint material).isSome := by rw [formed]; rfl
  have output : (MotherReceiptPayload.formJoint material).get available = value := by simp only [formed, Option.get_some]
  let actual : MotherReceiptPayload.Presentation target.Answer target.Receipt
      ⟨target.answer, target.receipt⟩ ((MotherReceiptPayload.formJoint material).get available) :=
    output.symm ▸ presentation
  exact ⟨rank, material, address, available, actual, recovered, actual.restrict_eq, retains⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionReceipt
