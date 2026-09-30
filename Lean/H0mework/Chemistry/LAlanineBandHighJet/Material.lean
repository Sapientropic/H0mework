import H0mework.Chemistry.LAlanineBandHighJet.Density
import H0mework.Chemistry.LAlanineBandHighJet.Matrix
import H0mework.Chemistry.LAlanineBandHighJet.ProgramRecognition

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid SourceRectangle
noncomputable section

/-- One verified material supplies every requested original mixed density derivative. -/
theorem material_density (scope : Scope) (box : Rectangle) (r : Group → Nat × Nat)
    (m : WholeBandCache.Material) (rows : Matrix.Rows (jetCount scope))
    (groups : ∀ g, GroupComputed box r m g)
    (orbitals : ∀ b, OrbitalComputed (count_le scope) registeredProgram m b)
    (matrix : Matrix.Certificate rows (fun j b => grid (aoInteger m b j)))
    (density : Fin (jetCount scope) → Interval)
    (computed : ∀ j, density j = densityInteger scope (Matrix.bilinearAt rows) j)
    (j : Fin (jetCount scope)) (x : Point) (inside : InRectangle box x) :
    Holds (grid (density j)) (Taylor.sourceJet (prefixJet (count_le scope) j) x) := by
  rw [computed]
  apply densityInteger_contains
  intro l k
  apply Matrix.bilinear_contains rows _ matrix (fun i => jetMulti (prefixJet (count_le scope) i)) box
  · intro i b y hy
    exact actual_orbital (count_le scope) box r registeredProgram programs_are_original m groups orbitals b i y hy
  · exact inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
