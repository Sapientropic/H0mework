import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.FiniteChecks
import H0mework.Chemistry.LAlanineRefinementDensity.GaussianCoefficients

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceJetChecksA

open Lean Elab Term Command SourceGaussianModel SourceFiniteData

def jet (d : Fin 12) : JetIndex := ⟨d.val + 0, by omega⟩

def jetCondition (d : Fin 12) : Prop := ∀ j : Basis,
  GaussianCoefficients.orbitalBound (sourceTerms j) (jetMulti (jet d)) boxCentre boxRadius ≤ orbitalBound (jet d) j

elab "proveLocalJetEnvelopes" : command => liftTermElabM do
  for i in [:12] do
    let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 12))
    let index := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 12) (mkNatLit i) inside
    let type := mkApp (Lean.mkConst ``jetCondition) index
    let expanded := (← getConstInfo ``jetCondition).value!.bindingBody!.instantiate1 index
    let value ← instantiateMVars (← Meta.mkDecideProof expanded)
    addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple s!"jet{i}", levelParams := [], type, value })

proveLocalJetEnvelopes

elab "useLocalJetEnvelopes" : tactic => do
  let goals ← Lean.Elab.Tactic.getGoals
  unless goals.length == 12 do throwError "Jet proof census"
  for (goal, i) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"jet{i}"))
  Lean.Elab.Tactic.setGoals []

theorem each_jet (d : Fin 12) : jetCondition d := by
  fin_cases d
  useLocalJetEnvelopes

theorem actual_envelopes (d : Fin 12) (j : Basis) :
    orbitalEnvelope (sourceTerms j) (jetMulti (jet d)) boxCentre boxRadius ≤ orbitalBound (jet d) j := by
  rw [GaussianCoefficients.orbitalEnvelope_eq_bound]
  exact each_jet d j

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceJetChecksA
