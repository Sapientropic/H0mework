import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGStructural
import Mathlib.Analysis.Meromorphic.Order
import Lean.Elab.Tactic

set_option autoImplicit false
namespace LowEnergy.ActualFourBlockRealTransfer
open Lean Meta Elab Tactic

private def analyticGroupName (index : Nat) : Name :=
  Name.str `LowEnergy.ActualFourBlockRealTransfer
    ("actual_canonical_group" ++ toString index ++ "_analytic")

private def analyticType (f z : Expr) : MetaM Expr :=
  mkAppM ``AnalyticAt #[mkConst ``Complex,f,z]

private theorem source_vec_empty_analytic (z : ℂ) :
    ∀ a : Fin 0, AnalyticAt ℂ (fun _ : ℂ => (Matrix.vecEmpty : Fin 0 → ℂ) a) z := by
  intro a
  exact Fin.elim0 a

private theorem source_vec_cons_analytic {n : Nat} {z : ℂ}
    (f : ℂ → ℂ) (g : ℂ → Fin n → ℂ)
    (hf : AnalyticAt ℂ f z) (hg : ∀ a, AnalyticAt ℂ (fun x => g x a) z) :
    ∀ a : Fin (n+1), AnalyticAt ℂ (fun x => Matrix.vecCons (f x) (g x) a) z := by
  intro a
  refine Fin.cases ?_ (fun i => ?_) a
  · exact hf
  · exact hg i

private partial def proveSourceVector (x z vector : Expr)
    (facts : Array (Expr × Expr)) : MetaM Expr := do
  let args := vector.getAppArgs
  match vector.getAppFn.constName? with
  | some ``Matrix.vecEmpty => mkAppM ``source_vec_empty_analytic #[z]
  | some ``Matrix.vecCons =>
      unless args.size = 4 do throwError "Malformed original numerator vector"
      let entry := args[2]!
      let tail := args[3]!
      let hf ← proveSourcePolynomial x z entry facts
      let hg ← proveSourceVector x z tail facts
      let f ← mkLambdaFVars #[x] entry
      let g ← mkLambdaFVars #[x] tail
      mkAppM ``source_vec_cons_analytic #[f,g,hf,hg]
  | _ => throwError "Original numerator return is not its literal source vector"

/-- Keep prior source functions opaque during local closure, then restore
their exact original function values and proofs as shared lets. -/
private partial def liftLets (localGroups : Bool) (x z index current : Expr) (facts : Array (Expr × Expr)) : TacticM Expr := do
  match current with
  | .letE name type value body _ =>
      let originalFunction ← mkLambdaFVars #[x] current
      let originalProperty ← analyticType originalFunction z
      let function ← mkLambdaFVars #[x] value
      let functionType ← inferType function
      withLocalDeclD name functionType fun f => do
        let text := name.toString
        let (property,proof) ← if text.startsWith "g" then do
          let some previous := (text.drop 1).toString.toNat? | throwError "Unknown original group"
          unless previous < 33 do throwError "Outside original group family"
          let .forallE _ domain _ _ := (← whnf type) | throwError "Expected an original vector"
          let property ← withLocalDeclD `j domain fun j => do
            let projected ← mkLambdaFVars #[x] (mkApp (mkApp f x) j)
            mkForallFVars #[j] (← analyticType projected z)
          let actualProperty ← withLocalDeclD `j domain fun j => do
            let projected ← mkLambdaFVars #[x] (mkApp (mkApp function x) j)
            mkForallFVars #[j] (← analyticType projected z)
          let proof ← if localGroups then do
            let localDecl ← getLocalDeclFromUserName (Name.mkSimple ("h" ++ toString previous))
            pure localDecl.toExpr
          else pure (mkApp (mkConst (analyticGroupName previous)) z)
          unless ← isDefEq (← inferType proof) actualProperty do
            throwError "Earlier analytic group is not this original source function"
          pure (property,proof)
        else throwError "Unexpected binder in original polynomial DAG"
        let proofName := name.appendAfter "_analytic"
        withLocalDeclD proofName property fun h => do
          let next := body.instantiate1 (mkApp f x)
          let rest ← liftLets localGroups x z index next (facts.push (f,h))
          let proofLet := Expr.letE proofName property proof (rest.abstract #[h]) false
          let result := Expr.letE name functionType function (proofLet.abstract #[f]) false
          pure <| Expr.letE (name.appendAfter "_source_type") originalProperty result
            (.bvar 0) false
  | _ =>
      unless current.isApp && current.appArg! == index do
        throwError "Original numerator does not evaluate its literal vector at the source index"
      let vectorProof ← proveSourceVector x z current.appFn! facts
      let result := mkApp vectorProof index
      let property ← analyticType (← mkLambdaFVars #[x] current) z
      unless ← isDefEq (← inferType result) property do
        throwError "Structural vector proof does not describe its original numerator"
      pure result

private def closeNumerator (localGroups : Bool) : TacticM Unit := withMainContext do
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
  let info ← getConstInfo ``LowEnergy.MixedSpectatorCanonical79Data.numeratorPolynomial
  let some value := info.value? | throwError "Original group definition missing"
  let proof ← withLocalDeclD `source_x (mkConst ``Complex) fun x => do
    let zero ← Term.elabTerm (← `(term| (0 : ℂ))) none
    let current := value.beta #[x,zero,index]
    let result ← liftLets localGroups x z index current #[]
    if result.containsFVar x.fvarId! then throwError "Source variable escaped analytic proof"
    pure result
  unless ← isDefEq (← inferType proof) target do
    throwError "The analytic certificate does not describe the original source group"
  goal.assign proof
  replaceMainGoal []

elab "analytic_canonical_numerator" : tactic => closeNumerator false
elab "analytic_canonical_numerator_from_groups" : tactic => closeNumerator true

end LowEnergy.ActualFourBlockRealTransfer
