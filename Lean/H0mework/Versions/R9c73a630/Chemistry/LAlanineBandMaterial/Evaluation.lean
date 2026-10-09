import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Material

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid SourceRectangle
noncomputable section

/-- Concrete calculation values retained by the installed band material. -/
structure Evaluation (scope : HighJet.Scope) where
  box : Rectangle
  reductions : Group → Nat × Nat
  gaussian : WholeBandCache.Material
  matrix : HighJet.Matrix.Rows (HighJet.jetCount scope)
  density : Fin (HighJet.jetCount scope) → Interval

structure EvaluationSound {scope : HighJet.Scope} (e : Evaluation scope) : Prop where
  groups : ∀ g, HighJet.GroupComputed e.box e.reductions e.gaussian g
  orbitals : ∀ b, HighJet.OrbitalComputed (HighJet.count_le scope) HighJet.registeredProgram e.gaussian b
  matrix : HighJet.Matrix.Certificate e.matrix (fun j b => grid (HighJet.aoInteger e.gaussian b j))
  density : ∀ j, e.density j = HighJet.densityInteger scope (HighJet.Matrix.bilinearAt e.matrix) j

theorem evaluation_actual_density {scope : HighJet.Scope} (e : Evaluation scope) (sound : EvaluationSound e)
    (j : Fin (HighJet.jetCount scope)) (x : Point) (inside : InRectangle e.box x) :
    Holds (grid (e.density j)) (Taylor.sourceJet (HighJet.prefixJet (HighJet.count_le scope) j) x) :=
  HighJet.material_density scope e.box e.reductions e.gaussian e.matrix sound.groups sound.orbitals
    sound.matrix e.density sound.density j x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
