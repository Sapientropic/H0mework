import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Source
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Original
open Lean Elab Command
open Protocol.SymbolicAuthentication
-- Alias the existing producer with its exact dependent type; addDecl retains kernel checking.
elab "retain_provider_actual" : command => do
  let info ← Lean.getConstInfo ``ProviderMaterialConsumer.every_material_request_keeps_the_complete_actual_joint_occurrence
  let mut equation:=info.type
  for argument in #[Lean.mkNatLit 3,Lean.mkConst ``Bool.true,Lean.mkConst ``Bool.true] do
    match equation with
    | .forallE _ _ body _ => equation:=body.instantiate1 argument
    | _ => throwError "original provider source parameter shape changed"
  unless equation.isAppOf ``Eq do throwError "provider occurrence equality required"
  let physical:=equation.getAppArgs[1]!
  unless physical.isAppOf ``FreshSigningReplay.physical do throwError "original physical source required"
  let actual:=physical.getAppArgs.back!
  unless actual.isAppOf ``JointReceptionSource.State.actual do throwError "complete joint source required"
  let producer:=actual.getAppArgs.back!
  unless producer.isAppOf ``JointReceptionSource.advance do throwError "original source continuation required"
  let projection ← Lean.getConstInfo ``JointReceptionSource.State.actual
  let mut projectionType:=projection.type
  for argument in actual.getAppArgs.pop do
    match projectionType with
    | .forallE _ _ body _ => projectionType:=body.instantiate1 argument
    | _ => throwError "original source state projection parameter shape changed"
  let .forallE _ exactType _ _ := projectionType | throwError "original source state required"
  let name := (← getCurrNamespace) ++ Name.mkSimple "initial"
  liftCoreM <| addDecl (.defnDecl {
    name := name
    levelParams := []
    type := exactType
    value := producer
    hints := .abbrev
    safety := .safe })
retain_provider_actual
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Original
