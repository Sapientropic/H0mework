import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Material
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid
noncomputable section

/-- Values outside the paid prefix are never consumed by its Taylor responsibility. -/
def densityBounds (scope : Scope) (rows : Fin (jetCount scope) → Interval) (j : JetIndex) : Pair :=
  if h : j.val < jetCount scope then grid (rows ⟨j.val,h⟩) else (0,0)

theorem densityBounds_contains (scope : Scope) (rows : Fin (jetCount scope) → Interval)
    (j : JetIndex) (h : jetOrder (jetMulti j) ≤ degree scope) (x : Point)
    (contains : ∀ k, Holds (grid (rows k)) (Taylor.sourceJet (prefixJet (count_le scope) k) x)) :
    Holds (densityBounds scope rows j) (Taylor.sourceJet j x) := by
  have hj := (index_iff scope j).mpr h
  simpa only [densityBounds,dif_pos hj,prefixJet] using contains ⟨j.val,hj⟩

theorem centerBounds (c : Fin 3 → ℚ) (rows : Fin (jetCount 0) → Interval)
    (contains : ∀ j, Holds (grid (rows j)) (Taylor.sourceJet (prefixJet (count_le 0) j) (Taylor.centerPoint c))) :
    Taylor.CenterBounds c (densityBounds 0 rows) := by
  intro j hj
  exact densityBounds_contains 0 rows j hj _ contains

theorem fourthBounds (hull : Rectangle) (rows : Fin (jetCount 1) → Interval)
    (contains : ∀ j x, InRectangle hull x →
      Holds (grid (rows j)) (Taylor.sourceJet (prefixJet (count_le 1) j) x)) :
    Taylor.FourthBounds hull (densityBounds 1 rows) := by
  intro j hj x hx
  apply densityBounds_contains 1 rows j (by change jetOrder (jetMulti j) ≤ 4; omega)
  exact fun k => contains k x hx

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
