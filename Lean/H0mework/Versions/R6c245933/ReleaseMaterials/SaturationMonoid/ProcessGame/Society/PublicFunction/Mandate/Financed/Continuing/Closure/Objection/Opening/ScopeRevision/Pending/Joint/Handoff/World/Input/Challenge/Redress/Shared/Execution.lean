import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Trace.Native
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.Native

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Execution
variable {epoch : Epoch} (inventory : Inventory epoch)

def after : Inventory epoch := World.submit inventory (Shared.word inventory)
theorem after_exact : after inventory = Shared.after inventory := rfl
@[csimp] theorem after_codegen : @Shared.after = @after := rfl

def answer := (Input.Event.Future.Expiry.Progress.produce
  (Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.after (Shared.after inventory))).1

theorem answer_exact : answer inventory = Shared.Runtime.answer inventory := rfl
@[csimp] theorem answer_codegen : @Shared.Runtime.answer = @answer := rfl

def native : Input.Event.Evolution ⟨epoch,inventory⟩ (Shared.Runtime.answer inventory).packet :=
  let saved := Shared.after inventory
  let trace := (Input.Event.Future.Expiry.Progress.produce
    (Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.after saved)).1
  .append (.submit inventory (Shared.word inventory))
    (.append (Input.Event.inputEvolution saved (Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.intent saved))
      (Input.Event.Future.Expiry.Progress.Native.evolution trace))

theorem native_exact : native inventory = Shared.Runtime.native inventory := by
  simp only [native,Shared.Runtime.native,Input.Event.Future.Expiry.Progress.Responsibility.Dispatch.native,
    Input.Event.Future.Expiry.Progress.Native.evolution_exact]
  rfl

@[csimp] theorem native_codegen : @Shared.Runtime.native = @native := by
  funext epoch inventory
  exact (native_exact inventory).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Execution
