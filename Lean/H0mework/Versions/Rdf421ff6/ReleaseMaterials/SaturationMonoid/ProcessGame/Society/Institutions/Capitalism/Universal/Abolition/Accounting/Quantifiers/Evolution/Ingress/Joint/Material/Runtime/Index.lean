import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Process

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion SourceNativeInquiryRuntime
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

private theorem next_native_node (n : Nat) (engine : Engine (process seed claim))
    (same : engine.node = .active (answerPresentation seed claim n))
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    (engine.ask activation).next.node = .active (answerPresentation seed claim (n + 1)) := by
  rcases engine with ⟨stage⟩
  have actual : stage = Stage.native n :=
    (process seed claim).erase_injective rfl rfl (congrArg RootInquiryProcessNode.erase same)
  subst stage
  rfl

theorem every_actual_runtime_stage_is_the_original_native_visit (n : Nat) :
    ((runtime seed claim).stateAt (n + 1)).engine.node = .active (answerPresentation seed claim n) := by
  induction n with
  | zero => exact the_first_activated_next_is_the_actual_body_successor seed claim
  | succ n earlier =>
      exact next_native_node seed claim n ((runtime seed claim).stateAt (n + 1)).engine earlier
        ((runtime seed claim).stateAt (n + 1)).activation

theorem every_actual_tick_keeps_the_same_whole_generated_next (n : Nat) :
    ((runtime seed claim).stateAt n).engine.node.PreservesGeneratedLivingLawAt
      ((runtime seed claim).stateAt n).activation.query ((runtime seed claim).tickAt n).next.node :=
  ((runtime seed claim).tickAt n).next_preservesGeneratedLivingLaw

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
