import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Cache
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Checks
open Lean Elab Term Command SourceSignedEvaluator SourceExponential SourceIntegerGrid SourceRectangle

 def Saturated (a : Pair) (r : Nat × Nat) : Prop :=
   (|reducedArgument a.1 r.1| ≤ 1/2 ∧ |reducedArgument a.2 r.2| ≤ 1/2) ∧
   ((r.1=8 ∧ reducedArgument a.1 r.1 ≤ -7/16) ∨ (9≤r.1 ∧ reducedArgument a.1 r.1 ≤ -7/32)) ∧
   ((r.2=8 ∧ reducedArgument a.2 r.2 ≤ -7/16) ∨ (9≤r.2 ∧ reducedArgument a.2 r.2 ≤ -7/32))
 instance (a : Pair) (r : Nat × Nat) : Decidable (Saturated a r) := by unfold Saturated; infer_instance
 theorem saturated_exp (a : Pair) (r : Nat × Nat) (h : Saturated a r) :
    exponential a r.1 r.2 = (0,1/scale) :=
   Prod.ext (WholeBandSaturation.leaf_saturated h.1.1 h.2.1).1
     (WholeBandSaturation.leaf_saturated h.1.2 h.2.2).2

 theorem cached_exponential (m : WholeBandCache.Material) (g : Group) (r : Nat × Nat)
    (stored : grid (expInteger m g) = (0,1/scale))
    (input : Saturated (WholeBandCache.cachedRadial m g) r) :
    grid (expInteger m g) = exponential (WholeBandCache.cachedRadial m g) r.1 r.2 :=
   stored.trans (saturated_exp _ _ input).symm

private def exactComputation (type : Expr) : TermElabM Expr := do
  let type ← Meta.whnf type
  if type.isAppOfArity ``Eq 3 then return ← Meta.mkEqRefl type.getAppArgs[2]!
  let decider ← Meta.synthInstance (mkApp (Lean.mkConst ``Decidable) type)
  pure (mkApp3 (Lean.mkConst ``of_decide_eq_true) type decider (← Meta.mkEqRefl (Lean.mkConst ``Bool.true)))

elab "checkHighJetGroups" : command => liftTermElabM do
  let root ← getCurrNamespace
  let box := Lean.mkConst (root ++ `localBox)
  let reductions := Lean.mkConst (root ++ `localReductions)
  let material := Lean.mkConst (root ++ `material)
  let some (.defnInfo flagData) := (← getEnv).find? (root ++ `rawSaturation) | throwError "source saturation flags"
  let some flags ← Meta.getArrayLit? flagData.value | throwError "literal saturation flags"
  unless flags.size == 94 do throwError "source saturation census"
  for i in [:94] do
    let group ← CacheReification.finExpr i 94
    let type := mkApp4 (Lean.mkConst ``HighJet.GroupComputed) box reductions material group
    let goal ← Meta.mkFreshExprMVar type
    let fields ← goal.mvarId!.apply (Lean.mkConst ``HighJet.GroupComputed.mk)
    unless fields.length == 5 do throwError "original five calculation fields"
    for k in [:5] do
      let f := fields[k]!
      if k == 2 then
        let isSaturated := flags[i]!.isConstOf ``Bool.true
        if isSaturated then
          let subgoals ← f.apply (mkApp3 (Lean.mkConst ``cached_exponential) material group (mkApp reductions group))
          for subgoal in subgoals do subgoal.assign (← exactComputation (← subgoal.getType))
        else f.assign (← exactComputation (← f.getType))
      else f.assign (← exactComputation (← f.getType))
    let value ← instantiateMVars goal
    addDecl (.thmDecl { name := root ++ Name.mkSimple s!"group{i}",levelParams := [],type,value })

elab "checkHighJetOrbitals" : command => liftTermElabM do
  let root ← getCurrNamespace
  let n := Lean.mkConst (root ++ `jetCount)
  let bounded := Lean.mkConst (root ++ `countBound)
  let programs := Lean.mkConst ``HighJet.registeredProgram
  let material := Lean.mkConst (root ++ `material)
  for b in [:98] do
    let type := mkApp5 (Lean.mkConst ``HighJet.OrbitalComputed) n bounded programs material (← CacheReification.finExpr b 98)
    let value ← exactComputation type
    addDecl (.thmDecl { name := root ++ Name.mkSimple s!"orbital{b}",levelParams := [],type,value })

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Checks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
