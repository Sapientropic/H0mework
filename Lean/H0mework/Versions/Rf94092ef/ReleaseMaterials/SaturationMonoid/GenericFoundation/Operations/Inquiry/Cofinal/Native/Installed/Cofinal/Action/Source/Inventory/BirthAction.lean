import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Installation.ActionIncrement.Birth

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction

open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
namespace Environment
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (born_raw)
end Environment
namespace Birth
export SourceOperationInquiry.Context.Installation (executedEnvironmentIncrement born_local_increment_zero)
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
export ActualNativeRelationTransport.AS (stockDecodedEnvironment)
end Birth

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
attribute [local instance] familyGroups
variable (factory : SF.Factory W X s)
variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))

/-- The completed native receipt's decoder generates the actual birth increment. -/
def birthIncrement : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar :=
  Birth.stockDecodedEnvironment (selected factory packet) (nativePacket factory packet).2.2.1 -
    (selected factory packet).activeEnvironment

theorem birth_registered_environment :
    (sourceBorn factory packet).2.1.1.rawRead.environment = (selected factory packet).activeEnvironment :=
  Environment.born_raw (AS.stockCfg (nativePacket factory packet).2.2.1) (selected factory packet)

theorem birth_decoded_environment :
    let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (selected factory packet).activeEnvironment
    before + birthIncrement factory packet = (sourceBorn factory packet).2.1.1.activeEnvironment := by
  intro before
  let after : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar :=
    Birth.stockDecodedEnvironment (selected factory packet) (nativePacket factory packet).2.2.1
  have actual := ActualNativeRelationTransport.decoded_environment (selected factory packet)
    (nativePacket factory packet).2.2.1
  have written : before + birthIncrement factory packet = after := by
    change before + (after-before) = after
    abel
  exact written.trans actual.symm

theorem first_birth_local_increment :
    Birth.executedEnvironmentIncrement (Birth.epoch (sourceBorn factory packet).2.1.1)
      (S.actualOccurrence (sourceBorn factory packet).2.1.1) = 0 :=
  Birth.born_local_increment_zero (selected factory packet) (AS.stockCfg (nativePacket factory packet).2.2.1)

/-- The carried source word is evaluated across the actual completed birth action. -/
def birthWordInventory :
    Formal ℤ (L.Value W packet.1) X s →ₗ[ℤ] PairValue (L.Value W (packet.1+1)) s :=
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (selected factory packet).activeEnvironment
  (updateInventory (R := ℤ) before (birthIncrement factory packet)).comp (sourceWordAction packet)

theorem birth_word_reads_written (word : Formal ℤ (L.Value W packet.1) X s) :
    (birthWordInventory factory packet word).1+(birthWordInventory factory packet word).2 =
      evaluation (R := ℤ) (sourceBorn factory packet).2.1.1.activeEnvironment (sourceWordAction packet word) := by
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (selected factory packet).activeEnvironment
  let increment := birthIncrement factory packet
  let acted := sourceWordAction packet word
  have paid := LinearMap.congr_fun (evaluation_update (R := ℤ) (s := s) before increment) acted
  change evaluation (R := ℤ) (before+increment) acted =
    (birthWordInventory factory packet word).1+(birthWordInventory factory packet word).2 at paid
  exact paid.symm.trans (congrArg (fun environment => evaluation (R := ℤ) environment acted)
    (birth_decoded_environment factory packet))

end ActualCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
