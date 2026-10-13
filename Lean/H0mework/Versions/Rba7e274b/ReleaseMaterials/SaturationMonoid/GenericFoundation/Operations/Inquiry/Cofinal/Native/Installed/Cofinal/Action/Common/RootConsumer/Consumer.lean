import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalRootResidualConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations
namespace Future
export ActualCofinalCommonAction (actions model_fibre)
export ActualCofinalNativeTower (stageInventory)
end Future
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance consumerGroups (grade : Nat) (target : Sorts) : AddCommGroup (CA.Value W grade target) := CA.groups W grade target
variable (factory : CA.Factory W X s)
variable (initial : CA.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : CA.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

/-- Every future native joint observation consumes the original next responsibility's request. -/
theorem actual_root_future (ordinal : Nat) (history : List PUnit.{u+1}) (target : Nat) :
 Future.stageInventory factory initial cfg language target
  (SourceGeneratedActionWords.run (Future.actions factory initial cfg language) history
   (DFinsupp.single (ordinal+1)
    (Finsupp.single (rootedRequest factory initial cfg language ordinal).expression 1))) =
 Future.stageInventory factory initial cfg language target
  (SourceGeneratedActionWords.run (Future.actions factory initial cfg language) history
   (DFinsupp.single (ordinal+1) (boundaryWord factory initial cfg language ordinal))) :=
 (Future.model_fibre factory initial cfg language _ _).mp
  (rooted_request_model factory initial cfg language ordinal) history target

/-- Dependent elimination uses the source-owned request and the original actual compiler/whole-ledger branch. -/
def actual_root_eliminate {Result : Sort v} (ordinal : Nat)
 (consumer : (request : C.RequestAtCurrent
   (Value := CA.NativeValue factory initial cfg language (ordinal+1)) (Var := X) (s := s)
   (generatedCurrent factory initial cfg language ordinal)) →
  CA.projection factory initial cfg language
   (DFinsupp.single (ordinal+1) (Finsupp.single request.expression 1)) =
   CA.projection factory initial cfg language
    (DFinsupp.single (ordinal+1) (boundaryWord factory initial cfg language ordinal)) →
  type_of% (original_compiles factory initial cfg language ordinal) →
  type_of% (original_whole factory initial cfg language ordinal) → Result) : Result :=
 let data := consume factory initial cfg language ordinal
 consumer data.1 data.2.1.down data.2.2.1.down data.2.2.2.down

end ActualCofinalRootResidualConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
