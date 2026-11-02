import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement.Runtime

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement.Runtime.Readback
variable {epoch : Epoch} (inventory : Inventory epoch)

def response : Disposition inventory := Replacement.produce inventory

theorem response_exact : response inventory = fromRoot inventory := rfl

@[csimp] theorem fromRoot_codegen : @fromRoot = @response := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement.Runtime.Readback
