import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Native

variable {epoch : Epoch}
def packet : {inventory : Inventory epoch} → Trace inventory → Packet
  | _,.finish _ answer _ _ => answer.event.packet
  | _,.advance _ _ _ _ _ _ tail => packet tail

theorem packet_exact {epoch : Epoch} {inventory : Inventory epoch} (trace : Trace inventory) :
    packet trace = trace.packet := by
  induction trace with
  | finish => rfl
  | advance _ _ _ _ _ _ _ ih => exact ih

@[csimp] theorem packet_codegen : @Trace.packet = @packet := by
  funext epoch inventory trace
  exact (packet_exact trace).symm

def evolution : {inventory : Inventory epoch} → (trace : Trace inventory) →
    Evolution ⟨epoch,inventory⟩ trace.packet
  | _,.finish _ answer _ _ => answer.event.native
  | _,.advance saved answer _ next same _ tail =>
      let first : Evolution ⟨epoch,saved⟩ ⟨epoch,next⟩ :=
        Eq.mp (congrArg (Evolution ⟨epoch,saved⟩) same) answer.event.native
      .append first (evolution tail)

theorem evolution_exact {epoch : Epoch} {inventory : Inventory epoch} (trace : Trace inventory) :
    evolution trace = trace.native := by
  induction trace with
  | finish => rfl
  | advance saved answer actual next same included tail ih =>
      simp only [evolution,Trace.native,ih]
      rfl

@[csimp] theorem evolution_codegen : @Trace.native = @evolution := by
  funext epoch inventory trace
  exact (evolution_exact trace).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Native
