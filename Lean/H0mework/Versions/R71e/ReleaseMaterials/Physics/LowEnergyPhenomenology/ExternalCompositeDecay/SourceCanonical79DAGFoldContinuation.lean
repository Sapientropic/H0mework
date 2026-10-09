import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79ImaginaryGroup0
import Lean.Elab.Tactic
import Lean.Util.FoldConsts

set_option autoImplicit false
namespace LowEnergy.ActualCanonical79Imaginary
open Lean Meta Elab Tactic

private def originalGroupName (index : Nat) : Name :=
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorCanonical79Data 0) "LowEnergy")
    "MixedSpectatorCanonical79Data"
  Name.str ns ("nodeGroup" ++ toString index)

private def groupValueName (index : Nat) : Name :=
  Name.str `LowEnergy.ActualCanonical79Imaginary ("group" ++ toString index ++ "Value")

private def nodePoint (group position : Nat) : MetaM Expr := do
  let length := if group = 32 then 106 else 128
  let h ← mkDecideProof (← mkLT (mkNatLit position) (mkNatLit length))
  let index := mkApp3 (mkConst ``Fin.mk) (mkNatLit length) (mkNatLit position) h
  return mkApp (mkConst (groupValueName group)) index

private def proveNode (group : Nat) (value point : Expr) : TacticM Expr := do
  let type ← mkEq value point
  let proof ← mkFreshExprMVar type
  let saved ← getGoals
  setGoals [proof.mvarId!]
  let dataIds := (Array.range (group+1)).map fun i => mkIdent (groupValueName i)
  evalTactic (← `(tactic| norm_num [$[$dataIds:ident],*]))
  for goal in (← getGoals) do
    let ids := (← goal.getType).getUsedConstants.filterMap fun name =>
      if name.toString.startsWith "LowEnergy.ActualCanonical79Imaginary.nodeCoefficient" then
        some (mkIdent name) else none
    setGoals [goal]
    evalTactic (← `(tactic| norm_num [$[$ids:ident],*, Complex.I_sq, Complex.I_mul_I,
      Complex.I_pow_eq_pow_mod']))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| norm_num [Complex.I_sq]))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| ring_nf))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| simp only [Complex.I_pow_eq_pow_mod', Nat.reduceMod,
        pow_zero, pow_one, Complex.I_sq, Complex.I_pow_three]))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| norm_num [Complex.I_sq, Complex.I_mul_I]))
    unless (← getGoals).isEmpty do
      let pending ← (← getMainGoal).getType
      throwError m!"Original source node arithmetic did not close: {pending}"
  unless (← getGoals).isEmpty do throwError "Original source node arithmetic did not close"
  setGoals saved
  instantiateMVars proof

/-- Fold one original let only after its own equality has been proved.
This avoids expanding a shared arithmetic DAG into a repeated expression tree. -/
private partial def foldLets (group : Nat) (resultType current target : Expr) : TacticM Expr := do
  match current with
  | .letE name type value body _ =>
      let text := name.toString
      let (point, proof) ← if text.startsWith "t" then do
        let some index := (text.drop 1).toString.toNat? | throwError "Unknown source node name"
        unless index / 128 = group do throwError "Source node is outside its original group"
        let point ← nodePoint group (index % 128)
        let proof ← try proveNode group value point catch error =>
          throwError m!"At original node {name}: {error.toMessageData}"
        pure (point, proof)
      else if text.startsWith "g" then do
        let some index := (text.drop 1).toString.toNat? | throwError "Unknown source group name"
        unless index < group do throwError "Source group is not an earlier DAG dependency"
        let point := mkConst (groupValueName index)
        let proofName := Name.str `LowEnergy.ActualCanonical79Imaginary
          ("actual_group" ++ toString index ++ "_point")
        pure (point, mkConst proofName)
      else throwError "Unexpected binder in the original source DAG"
      let function := Expr.lam name type body .default
      let next := body.instantiate1 point
      let u ← getLevel type
      let v ← getLevel resultType
      let step := mkApp6 (mkConst ``congrArg [u,v]) type resultType value point function proof
      let rest ← foldLets group resultType next target
      return mkApp6 (mkConst ``Eq.trans [v]) resultType current next target step rest
  | _ =>
      let type ← mkEq current target
      let proof ← mkFreshExprMVar type
      let saved ← getGoals
      setGoals [proof.mvarId!]
      evalTactic (← `(tactic| funext a; fin_cases a <;> rfl))
      unless (← getGoals).isEmpty do throwError "Original source vector return did not close"
      setGoals saved
      instantiateMVars proof

elab "fold_canonical_group_continuation" index:num : tactic => withMainContext do
  let group := index.getNat
  unless group < 33 do throwError "Not an original canonical79 node group"
  let goal ← getMainGoal
  let target ← goal.getType
  let some (resultType,left,right) := target.eq? | throwError "Expected a source group equality"
  unless left.getAppFn.constName? = some (originalGroupName group) do
    throwError "The goal does not read the original source group"
  let info ← getConstInfo (originalGroupName group)
  let some value := info.value? | throwError "The original source node group has no definition"
  let body := value.beta left.getAppArgs
  let proof ← foldLets group resultType body right
  goal.assign proof
  replaceMainGoal []

end LowEnergy.ActualCanonical79Imaginary
