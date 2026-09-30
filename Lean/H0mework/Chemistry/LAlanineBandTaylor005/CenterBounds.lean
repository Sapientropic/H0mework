import H0mework.Chemistry.LAlanineBandTaylor005.CenterAssembly
import H0mework.Chemistry.LAlanineBandHighJet.Bounds

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Sample010
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid
noncomputable section

def center : Fin 3 → ℚ := fun a => (rawCenter[a.val]! : ℚ)/SourceExponential.scale
def bounds : JetIndex → Pair := HighJet.densityBounds 0 densityRows

theorem center_box (a : Fin 3) : localBox a = (center a,center a) := by
  fin_cases a <;> decide +kernel

theorem center_inside : InRectangle localBox (Taylor.centerPoint center) := by
  intro a
  rw [center_box]
  exact ⟨le_refl _,le_refl _⟩

theorem center_bounds : Taylor.CenterBounds center bounds :=
  HighJet.centerBounds center densityRows (fun j => actual_density j _ center_inside)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Sample010
