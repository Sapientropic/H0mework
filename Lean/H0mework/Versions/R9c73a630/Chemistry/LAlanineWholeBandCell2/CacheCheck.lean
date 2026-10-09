import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell2.CacheReifier
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCache.SaturationRuntimeRegression

/-! The original GroupComputed constructor receives 36 installed Root62 proofs and
58 independently computed exponentials. Relative/radial/polynomial laws remain actual calculations. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.CacheChecks

open Lean Elab Term Command SourceExponential SourceSignedEvaluator SourceGaussianModel
open SourceRectangle WholeBandSource WholeBandCache WholeBandSaturation CacheReification

theorem group_computed_from_root62 (g : SaturatedGroup) (cache : Material)
    (relative : List.ofFn (cachedRelative cache (groupAt g)) =
      List.ofFn (SourceSignedEvaluator.relative (groupTerm (groupAt g)) (callBox 128)))
    (radial : cachedRadial cache (groupAt g) = radialPair (groupTerm (groupAt g)) (callBox 128))
    (stored : cachedExp cache (groupAt g) = (0,1/scale))
    (polynomial :
      List.ofFn (fun a => List.ofFn (fun p => List.ofFn (cachedPoly cache (groupAt g) a p))) =
      List.ofFn (fun a : Fin 3 => List.ofFn (fun p : Fin 3 => List.ofFn (fun d : Fin 3 =>
        jetHorner (groupExponent (groupAt g)) p.val d.val (cachedRelative cache (groupAt g) a))))) :
    GroupComputed (callBox 128) (callReductions 128) cache (groupAt g) :=
  (WholeBandSaturation.Runtime.sourceGeneratedPhysicalCell2SaturationNext.originalCacheKernel
    WholeBandSaturation.Runtime.saturationRuntimeAfterFirst).2 0 g cache relative radial stored polynomial

private def exactComputation (type : Expr) : TermElabM Expr := do
  let type ← Meta.whnf type
  if type.isAppOfArity ``Eq 3 then
    return ← Meta.mkEqRefl type.getAppArgs[2]!
  let decider ← Meta.synthInstance (mkApp (Lean.mkConst ``Decidable) type)
  return mkApp3 (Lean.mkConst ``of_decide_eq_true) type decider
    (← Meta.mkEqRefl (Lean.mkConst ``Bool.true))

elab "checkRoot62Call128Groups" : command => liftTermElabM do
  let root ← getCurrNamespace
  let box := Lean.mkConst (root ++ `localBox)
  let reductions := Lean.mkConst (root ++ `localReductions)
  let material := Lean.mkConst (root ++ `material)
  let saturated ← saturatedGroups
  let mut installedCount : Nat := 0
  for i in [:94] do
    let g ← finExpr i 94
    let type := mkApp4 (Lean.mkConst ``GroupComputed) box reductions material g
    let goal ← Meta.mkFreshExprMVar type
    let mut selected : Option Nat := none
    for s in [:saturated.size] do
      if saturated[s]! == i then selected := some s
    let fields ← match selected with
      | some s => do
          installedCount := installedCount + 1
          let constructor := mkApp2 (Lean.mkConst ``group_computed_from_root62) (← finExpr s 36) material
          goal.mvarId!.apply constructor
      | none => goal.mvarId!.apply (Lean.mkConst ``GroupComputed.mk)
    unless fields.length == (if selected.isSome then 4 else 5) do
      throwError "original cache field census changed"
    for field in fields do field.assign (← exactComputation (← field.getType))
    let value ← instantiateMVars goal
    addDecl (.thmDecl { name := root ++ Name.mkSimple s!"group{i}", levelParams := [], type, value })
    if i % 10 == 9 || i == 93 then
      liftM (m := IO) do
        let output ← IO.getStdout
        output.putStrLn s!"call128 groups: {i+1}/94; installed saturation {installedCount}"
        output.flush
  unless installedCount == 36 do throwError "Root62 installed group coverage changed"

end LAlanine40K2025.BasinRefinement.WholeBandCell2.CacheChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
