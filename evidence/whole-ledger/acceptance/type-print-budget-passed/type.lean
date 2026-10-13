import H0mework.Papers.WholeLedgerAccountingRb67aa48c

import Lean
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option pp.all true
set_option pp.deepTerms true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.explicit true
set_option pp.notation false
set_option pp.maxSteps 20000000
open Lean Elab Command Meta
private def wholeLedgerName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous
run_cmd do
  let env ← getEnv
  let owners : List String := ["H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Compiler", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"]
  let wanted : List String := ["SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt"]
  for name in wanted do
    unless (env.checked.get.find? (wholeLedgerName name)).isSome do
      throwError "MISSING_WHOLE_LEDGER_DECLARATION {name}"
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[index]!.toString
    unless owners.contains owner do continue
    unless wanted.contains name.toString do continue
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let type ← liftTermElabM do
      return (← ppExpr info.type).pretty (width := 100)
    let axioms ← liftTermElabM do collectAxioms name
    let row := Json.mkObj [
      ("qualified_name", toJson name.toString), ("module", toJson owner),
      ("kind", toJson kind), ("type", toJson type),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.toList.map Name.toString)),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial)]
    logInfo m!"WHOLE_LEDGER_DECLARATION {row.compress}"
