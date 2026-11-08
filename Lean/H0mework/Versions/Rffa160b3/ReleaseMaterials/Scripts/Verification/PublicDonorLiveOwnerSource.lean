import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Donor.Wire

open Lean SaturationMonoid.ProcessGame.Society
open PublicFunction.Productivity.Cell.Audit.Scoped PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal
open Regeneration.Supply Institutions.Capitalism.Universal.Root

def donorOrigins {plan : Plan} (state : Finance.State plan) : Json := toJson (state.account.current.slots.map fun slot =>
  let claim := Financial.Family.slotClaim Finance.sources slot
  Json.mkObj [("instrument",toJson (Privacy.Wire.instrumentName claim.2.instrument)),
    ("debtor",Privacy.Wire.actorJson claim.2.debtor),("holder",Privacy.Wire.actorJson claim.2.holder),
    ("quantity",toJson (toString claim.2.quantity)),("traceIndex",toJson claim.2.origin.traceIndex?),
    ("index",toJson claim.2.instruction.index),("before",Privacy.Wire.stateJson claim.2.instruction.before),
    ("request",Privacy.Wire.actionJson claim.2.instruction.request)])

def main (args : List String) : IO Unit := do
  let branch := args.headD ""
  if branch != "private-one" && branch != "private-two" then throw (IO.userError "CLOSED_DONOR_OWNER_BRANCH_REQUIRED")
  let request ← IO.ofExcept (Json.parse (←(←IO.getStdin).getLine))
  let execution ← IO.ofExcept (Productive.ExternalArrival.Donor.Wire.execute (branch="private-two") request)
  let state := execution.state.legacy.service
  (←IO.getStdout).putStrLn ((Json.mkObj [("old",toJson execution.old),("output",toJson execution.output),
    ("origins",donorOrigins state),
    ("ownFrame",toJson (toString (Privacy.ownFrame state.session.current))),
    ("history",toJson state.session.history.length),("nativeSlots",toJson state.account.current.slots.length),
    ("nativeOutstanding",toJson (toString (Financial.Family.ledgerClaims Finance.sources state.account.current .delivery supplier receiver))),
    ("spent",toJson execution.state.legacy.spent),("attempts",toJson execution.state.receipts.length),
    ("source",Productive.ExternalArrival.Wire.sourceJson (Productive.ExternalArrival.Consume.sourceCurrent execution.state.legacy))]).compress)
