import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Context
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.AtRank

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

local notation "canonical" => root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit
local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit canonical entry authority

abbrev sourceCurrent : SourceNativeLivingRootCurrentAt N := ⟨V, root, visit⟩
def initialCurrent {G : WorldRelationNetwork.{0}} {W : ConstructiveRoot.Vocabulary.{0}}
    (living : SourceNativeLivingRootClosure G W) : SourceNativeLivingRootCurrentAt G :=
  ⟨W, living, .finite living.toAuthoritativeRoot.toRoot.initialVisit⟩

variable {lower : Ordinal.{0}} {upper : Ordinal.{3}}
    {sourceMaterials : MotherArenaHigher.Material lower × MotherArenaHigher.Material lower × MotherArenaHigher.Material lower}
    (source : MotherNativeCurrent.Restriction lower (sourceCurrent (root := root) (visit := visit)) sourceMaterials)
    (target : SourceNativeSequentialActualActionTargetAt root visit
      (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit) entry authority)
    {targetMaterials : MotherArenaHigher.Material lower × MotherArenaHigher.Material lower × MotherArenaHigher.Material lower}
    (targetSource : MotherNativeCurrent.Restriction lower (initialCurrent target.targetRoot) targetMaterials)

def formTargetBody (material : MotherArenaHigher.Material lower) :
    Option (MotherActionBody.Body (root := root) (visit := visit) (event := canonical) (entry := entry) target.targetRoot) :=
  formBodyAtContext (event := canonical) (entry := entry) (context targetSource) (context_eq targetSource)
    (networkCoordinates source) (occurrenceCoordinates source visit.current)
    ⟨networkCoordinates targetSource,
      occurrenceCoordinates targetSource target.targetRoot.toAuthoritativeRoot.toRoot.source.initial⟩ material

structure TargetOrigin (originalAddress : MotherArenaHigher.Base lower ↪ MotherReceiptHigher.Base upper)
    (material : MotherReceiptHigher.Material upper) where
  receiptAvailable : (MotherReceiptPayload.formJoint material).isSome
  receipt : MotherReceiptPayload.Presentation target.Answer target.Receipt ⟨target.answer, target.receipt⟩
    ((MotherReceiptPayload.formJoint material).get receiptAvailable)
  bodyAvailable : (formTargetBody source target targetSource (MotherReceiptPayload.readArena lower originalAddress material)).isSome
  bodySame : (formTargetBody source target targetSource (MotherReceiptPayload.readArena lower originalAddress material)).get bodyAvailable =
    MotherActionBody.ofTarget target

variable {source target targetSource}
    {originalAddress : MotherArenaHigher.Base lower ↪ MotherReceiptHigher.Base upper}
    {material : MotherReceiptHigher.Material upper}

def TargetOrigin.read (origin : TargetOrigin source target targetSource originalAddress material) : Target :=
  assembleContext target (context targetSource) (context_eq targetSource)
    ((formTargetBody source target targetSource (MotherReceiptPayload.readArena lower originalAddress material)).get origin.bodyAvailable)
    origin.receipt.restrict

theorem TargetOrigin.read_eq (origin : TargetOrigin source target targetSource originalAddress material) : origin.read = target :=
  assembleContext_recovers target (context targetSource) (context_eq targetSource) _ origin.bodySame origin.receipt

variable (source target targetSource originalAddress)

theorem target_origin_at (indexCode : target.Answer ↪ MotherReceiptHigher.Base upper)
    (receiptCode : (Sigma target.Receipt) ↪ MotherReceiptHigher.Base upper) :
    ∃ material : MotherReceiptHigher.Material upper,
      Nonempty (TargetOrigin source target targetSource originalAddress material) := by
  obtain ⟨bodyMaterial, bodyFormed⟩ := MotherActionBody.every_body target.targetRoot
    (networkCoordinates source) (networkCoordinates targetSource)
    (occurrenceCoordinates source visit.current)
    (occurrenceCoordinates targetSource target.targetRoot.toAuthoritativeRoot.toRoot.source.initial)
    (MotherActionBody.ofTarget target)
  obtain ⟨material, value, formed, recovered, ⟨receipt⟩⟩ := MotherReceiptPayload.payload_and_arena_at
    lower bodyMaterial target.Answer target.Receipt ⟨target.answer, target.receipt⟩ indexCode receiptCode originalAddress
  have receiptAvailable : (MotherReceiptPayload.formJoint material).isSome := by rw [formed]; rfl
  have outputSame : (MotherReceiptPayload.formJoint material).get receiptAvailable = value :=
    Option.some.inj ((Option.some_get receiptAvailable).trans formed)
  let actualReceipt : MotherReceiptPayload.Presentation target.Answer target.Receipt ⟨target.answer, target.receipt⟩
      ((MotherReceiptPayload.formJoint material).get receiptAvailable) := outputSame.symm ▸ receipt
  have bodyFormed : formTargetBody source target targetSource (MotherReceiptPayload.readArena lower originalAddress material) =
      some (MotherActionBody.ofTarget target) := by
    rw [recovered]
    unfold formTargetBody
    rw [formBodyAtContext_eq]
    exact bodyFormed
  have bodyAvailable : (formTargetBody source target targetSource (MotherReceiptPayload.readArena lower originalAddress material)).isSome := by
    rw [bodyFormed]
    rfl
  refine ⟨material, ⟨⟨receiptAvailable, actualReceipt, bodyAvailable, ?_⟩⟩⟩
  exact Option.some.inj ((Option.some_get bodyAvailable).trans bodyFormed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
