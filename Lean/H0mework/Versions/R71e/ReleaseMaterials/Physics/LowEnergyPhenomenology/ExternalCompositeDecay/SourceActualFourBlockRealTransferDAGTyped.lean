import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGStructural
import Mathlib.Analysis.Meromorphic.Order
import Lean.Elab.Tactic

set_option autoImplicit false
namespace LowEnergy.ActualFourBlockRealTransfer
open Lean Meta Elab Tactic

private def originalGroupName (index : Nat) : Name :=
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorCanonical79Data 0) "LowEnergy")
    "MixedSpectatorCanonical79Data"
  Name.str ns ("nodeGroup" ++ toString index)

private def analyticGroupName (index : Nat) : Name :=
  Name.str `LowEnergy.ActualFourBlockRealTransfer
    ("actual_canonical_group" ++ toString index ++ "_analytic")

private def analyticType (f z : Expr) : MetaM Expr :=
  mkAppM ``AnalyticAt #[mkConst ``Complex,f,z]

/-- Each checked proof is ascribed its original remaining source expression.
This keeps kernel conversion local to one source let instead of comparing
two fully expanded function-DAG representations. -/
private partial def liftLets (group : Nat) (x z index current : Expr)
    (proofs : Array Expr) (facts : Array (Expr × Expr)) : TacticM Expr := do
  match current with
  | .letE name type value body _ =>
      let originalFunction ← mkLambdaFVars #[x] (mkApp current index)
      let originalProperty ← analyticType originalFunction z
      let function ← mkLambdaFVars #[x] value
      let functionType ← inferType function
      withLocalDeclD name functionType fun f => do
        let text := name.toString
        let (property,proof) ← if text.startsWith "t" then do
          let some node := (text.drop 1).toString.toNat? | throwError "Unknown original node"
          unless node / 128 = group do throwError "Original node outside group"
          let property ← analyticType f z
          let actualProperty ← analyticType function z
          let proof ← proveSourcePolynomial x z value facts
          unless ← isDefEq (← inferType proof) actualProperty do
            throwError "Structural analytic proof does not describe its actual node"
          pure (property,proof)
        else if text.startsWith "g" then do
          let some previous := (text.drop 1).toString.toNat? | throwError "Unknown original group"
          unless previous < group do throwError "Original group is not an earlier dependency"
          let .forallE _ domain _ _ := (← whnf type) | throwError "Expected an original vector"
          let property ← withLocalDeclD `j domain fun j => do
            let projected ← mkLambdaFVars #[x] (mkApp (mkApp f x) j)
            mkForallFVars #[j] (← analyticType projected z)
          let actualProperty ← withLocalDeclD `j domain fun j => do
            let projected ← mkLambdaFVars #[x] (mkApp (mkApp function x) j)
            mkForallFVars #[j] (← analyticType projected z)
          let proof := mkApp (mkConst (analyticGroupName previous)) z
          unless ← isDefEq (← inferType proof) actualProperty do
            throwError "Earlier analytic group is not this original source function"
          pure (property,proof)
        else throwError "Unexpected binder in original polynomial DAG"
        let proofName := name.appendAfter "_analytic"
        withLocalDeclD proofName property fun h => do
          let next := body.instantiate1 (mkApp f x)
          let rest ← liftLets group x z index next
            (if text.startsWith "t" then proofs.push h else proofs) (facts.push (f,h))
          let proofLet := Expr.letE proofName property proof (rest.abstract #[h]) false
          let result := Expr.letE name functionType function (proofLet.abstract #[f]) false
          pure <| Expr.letE (name.appendAfter "_source_type") originalProperty result
            (.bvar 0) false
  | _ =>
      let projected ← mkLambdaFVars #[x] (mkApp current index)
      let property ← analyticType projected z
      let proof ← mkFreshExprMVar property
      let saved ← getGoals
      setGoals [proof.mvarId!]
      let indexSyntax := mkIdent (← index.fvarId!.getUserName)
      evalTactic (← `(tactic| fin_cases $indexSyntax:ident))
      let goals ← getGoals
      unless goals.length = proofs.size do throwError "Original return vector has changed"
      for (goal,nodeProof) in goals.zip proofs.toList do
        unless ← isDefEq (← goal.getType) (← inferType nodeProof) do
          throwError m!"Original vector projection does not return its own node: {← goal.getType}"
        goal.assign nodeProof
      setGoals saved
      instantiateMVars proof

elab "analytic_canonical_group_typed" number:num : tactic => withMainContext do
  let group := number.getNat
  unless group < 33 do throwError "Not an original canonical group"
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.constName? = some ``AnalyticAt && args.size ≥ 3 do
    throwError "Expected a scalar analytic source coordinate"
  let z := args.back!
  let function := args[args.size-2]!
  let .lam _ _ body _ := function | throwError "Expected an original source coordinate lambda"
  let index := body.getAppArgs.back!
  unless index.isFVar do throwError "Expected the original free coordinate"
  let info ← getConstInfo (originalGroupName group)
  let some value := info.value? | throwError "Original group definition missing"
  let proof ← withLocalDeclD `source_x (mkConst ``Complex) fun x => do
    let zero ← Term.elabTerm (← `(term| (0 : ℂ))) none
    let current := value.beta #[x,zero]
    let result ← liftLets group x z index current #[] #[]
    if result.containsFVar x.fvarId! then throwError "Source variable escaped analytic proof"
    pure result
  unless ← isDefEq (← inferType proof) target do
    throwError "The analytic certificate does not describe the original source group"
  goal.assign proof
  replaceMainGoal []

end LowEnergy.ActualFourBlockRealTransfer
