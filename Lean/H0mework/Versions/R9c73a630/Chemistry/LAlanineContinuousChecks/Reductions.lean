import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousGroupCache.Complete

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks

open Lean Elab Term Command Tactic SourceRectangle SourceGroupCache SourceSignedEvaluator SourceExponential

noncomputable def cachedReduction (g : Group) : Prop :=
  |reducedArgument (cachedRadial g).1 (groupSteps 0 g).1| ≤ 1/2 ∧
    |reducedArgument (cachedRadial g).2 (groupSteps 0 g).2| ≤ 1/2

elab "checkAllCachedReductions" : command => liftTermElabM do
  for i in [:94] do
    let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 94))
    let g := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 94) (mkNatLit i) inside
    let type ← Meta.whnf (mkApp (Lean.mkConst ``cachedReduction) g)
    let decider ← Meta.synthInstance (mkApp (Lean.mkConst ``Decidable) type)
    let truth ← Meta.mkEqRefl (Lean.mkConst ``Bool.true)
    let value := mkApp3 (Lean.mkConst ``of_decide_eq_true) type decider truth
    let name := (← getCurrNamespace) ++ Name.mkSimple s!"cachedReduction_{i}"
    addDecl (.thmDecl { name, levelParams := [], type, value })

checkAllCachedReductions

elab "closeCachedReductions" : tactic => do
  let goals ← getGoals
  unless goals.length == 94 do throwError "complete source group census"
  let base := (← getCurrNamespace)
  for (goal, i) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ Name.mkSimple s!"cachedReduction_{i}"))
  setGoals []

theorem all_cached_reductions (g : Group) : cachedReduction g := by
  fin_cases g
  closeCachedReductions

theorem all_group_reductions (g : Group) :
    TermReductionValid (groupTerm g) (actualBox 0) (groupSteps 0 g).1 (groupSteps 0 g).2 := by
  have h := all_cached_reductions g
  unfold cachedReduction at h
  rw [radial_eq_source] at h
  exact h

theorem all_source_reductions (basis : SourceFiniteData.Basis) (term : SourceGaussianModel.Term)
    (member : term ∈ source_terms basis) :
    TermReductionValid term (actualBox 0) (steps 0 term).1 (steps 0 term).2 :=
  reduction_from_groups 0 all_group_reductions basis term member

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks
