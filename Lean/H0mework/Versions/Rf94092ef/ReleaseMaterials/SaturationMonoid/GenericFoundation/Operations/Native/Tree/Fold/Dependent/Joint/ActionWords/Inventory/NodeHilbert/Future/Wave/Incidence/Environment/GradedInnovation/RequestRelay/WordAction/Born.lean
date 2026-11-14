import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.RequestRelay.WordAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated

open SourceOperationEffects

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (sourceFrame : JointMeasured.Frame (K := K))

/-- The literal second birth reads its innovation on the original coefficient fibre of a carried word. -/
theorem actual_born_consumes_relayed_word (ordinal : Nat) :
    let previous : RelayPacket (K := K) X := site read sourceFrame ordinal
    let packet : RelayPacket (K := K) X := site read sourceFrame (ordinal+1)
    let exactPacket := next_packet_is_actual read sourceFrame ordinal
    ∀ (prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) previous.1) (X := X) (s := .joint))
      (present : previous.2.1.1.inventory = some prior) (event : Fin prior.trace.length),
    let output := featureValue packet.1 (nextJointValue read sourceFrame (ordinal+1))
    let environment := Native.environmentTransport packet.2.2.2.down
      (Request.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment
    let feature := featureEnvironment packet.1 environment
    let total := fun target name => (feature target name).1+(feature target name).2
    let decoded := J.decode (total .joint PUnit.unit)
    let frame := A.epoch packet.2.1.1
    let occurrence := S.actualOccurrence packet.2.1.1
    let increment := (JointMeasured.inputTerm read).eval decoded
    let response := columnRead read packet.1 (relayedWordValue read previous packet exactPacket prior present event)
    output.1+output.2 =
      (PaidSourceMacroHistory.programme.eval (JointMeasured.oldEnvironment decoded),
        columnActionInnovation read packet.1 frame occurrence (increment+response)) := by
  intro previous packet exactPacket prior present event output environment feature total decoded frame occurrence increment response
  have born := actual_next_from_column_actions read sourceFrame (ordinal+1)
  have payment := relayed_word_innovation read previous packet exactPacket prior present event increment
  have same := congrArg (Prod.mk (PaidSourceMacroHistory.programme.eval (JointMeasured.oldEnvironment decoded)))
    payment.symm
  have written := born.trans same
  exact written

end PaidSourceContentEnvironment.GradedInnovation.Integrated
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
