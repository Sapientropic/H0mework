import Lean.Elab.Tactic
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Transport

set_option autoImplicit false

universe u v w

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-- Proof construction only: project an actual recursor through its own
dependent payload; the resulting term is checked by the ordinary kernel. -/
theorem rec_projection_heq {α : Sort u} {first last : α}
    {Payload : (next : α) → first = next → Sort v}
    {Output : (next : α) → first = next → Sort w}
    (body : Payload first rfl) (same : first = last)
    (project : ∀ next proof, Payload next proof → Output next proof) :
    HEq (project last same (Eq.rec (motive := Payload) body same))
      (project first rfl body) := by
  cases same
  rfl


open Lean Elab Tactic Meta

elab "joint_paid_peel_rhs" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``HEq 4 do throwError "expected HEq: {target}"
  let goalArgs := target.getAppArgs
  let lhs := goalArgs[1]!
  let rhs := goalArgs[3]!
  let some recursor := rhs.find? (fun expression => expression.isAppOfArity ``Eq.rec 6)
    | throwError "no Eq.rec in rhs"
  let args := recursor.getAppArgs
  let alpha := args[0]!
  let first := args[1]!
  let motive := args[2]!
  let body := args[3]!
  let last := args[4]!
  let back := args[5]!
  let (project, output) ← withLocalDeclD `next alpha fun next => do
    withLocalDeclD `proof (← mkEq first next) fun proof => do
      withLocalDeclD `payload (mkAppN motive #[next,proof]) fun payload => do
        let observed ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[back],proof]
        let value := mkApp payload observed
        let ledger ← mkAppM ``Subtype.val #[value]
        let destination ← mkAppM ``LedgerWriteEvolutionAt.destination #[ledger]
        let outputType ← inferType destination
        pure (← mkLambdaFVars #[next,proof,payload] destination,
          ← mkLambdaFVars #[next,proof] outputType)
  let witness ← mkAppOptM ``SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.rec_projection_heq #[some alpha,some first,some last,
    some motive,some output,some body,some back,some project]
  let witnessType ← inferType witness
  let proofArgs := witnessType.getAppArgs
  unless ← isDefEq proofArgs[1]! rhs do throwError "projected rhs is not exact"
  let branch := proofArgs[3]!
  let nextGoal ← mkFreshExprSyntheticOpaqueMVar (← mkHEq lhs branch)
  let result ← mkAppM ``HEq.trans #[nextGoal,← mkAppM ``HEq.symm #[witness]]
  goal.assign result
  replaceMainGoal [nextGoal.mvarId!]


elab "joint_paid_peel_lhs_wrapped" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``HEq 4 do throwError "expected HEq"
  let goalArgs := target.getAppArgs
  let lhs ← Core.betaReduce goalArgs[1]!
  let rhs := goalArgs[3]!
  let some wrapper := lhs.find? (fun expression =>
      expression.isAppOf ``SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.identityTransport &&
        expression.getAppNumArgs > 5)
    | throwError "no original identityTransport"
  let wrapperFn := wrapper.getAppFn
  let wrapperArgs := wrapper.getAppArgs
  let info ← getFunInfo wrapperFn
  unless info.paramInfo.size ≥ wrapperArgs.size do throwError "overapplied identityTransport"
  let mut explicit := #[]
  for index in [:wrapperArgs.size] do
    if info.paramInfo[index]!.binderInfo.isExplicit then explicit := explicit.push wrapperArgs[index]!
  unless explicit.size == 5 do throwError "unexpected explicit wrapper arity: {explicit.size}"
  let financial := explicit[2]!
  let some recursor := financial.find? (fun expression => expression.isAppOfArity ``Eq.rec 6)
    | throwError "no inner Eq.rec"
  let args := recursor.getAppArgs
  let alpha := args[0]!
  let first := args[1]!
  let motive := args[2]!
  let body := args[3]!
  let last := args[4]!
  let back := args[5]!
  let (project, output) ← withLocalDeclD `next alpha fun next => do
    withLocalDeclD `proof (← mkEq first next) fun proof => do
      withLocalDeclD `payload (mkAppN motive #[next,proof]) fun payload => do
        let observed ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[back],proof]
        let value := mkApp payload observed
        let ledger ← mkAppM ``Subtype.val #[value]
        let wrapped ← mkAppM wrapperFn.constName! #[explicit[0]!,explicit[1]!,ledger,explicit[3]!,explicit[4]!]
        let destination ← mkAppM ``LedgerWriteEvolutionAt.destination #[wrapped]
        pure (← mkLambdaFVars #[next,proof,payload] destination,
          ← mkLambdaFVars #[next,proof] (← inferType destination))
  let witness ← mkAppOptM ``SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.rec_projection_heq #[some alpha,some first,some last,
    some motive,some output,some body,some back,some project]
  let witnessType ← inferType witness
  let proofArgs := witnessType.getAppArgs
  unless ← isDefEq proofArgs[1]! lhs do throwError "projected lhs is not exact"
  let branch := proofArgs[3]!
  let nextGoal ← mkFreshExprSyntheticOpaqueMVar (← mkHEq branch rhs)
  goal.assign (← mkAppM ``HEq.trans #[witness,nextGoal])
  replaceMainGoal [nextGoal.mvarId!]


end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
