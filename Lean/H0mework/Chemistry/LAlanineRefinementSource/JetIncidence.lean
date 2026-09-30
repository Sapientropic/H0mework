import H0mework.Chemistry.LAlanineRefinementSource.ContinuousChecks
import H0mework.Chemistry.LAlanineRefinementDensity.DensityBounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceJetIncidence

open SourceFiniteData SourceContinuousChecks SourceGaussianModel

def sourceJetCode (d : MultiIndex) : Nat :=
  let n := d 0 + d 1 + d 2
  n * (n+1) * (n+2) / 6 + (d 1 + d 2) * (d 1 + d 2 + 1) / 2 + d 2

def sourceJetIndex (d : MultiIndex) : JetIndex := ⟨sourceJetCode d % 35, Nat.mod_lt _ (by decide)⟩

theorem bounded_source_census : ∀ a b c : Fin 5,
    a.val + b.val + c.val ≤ 4 →
      jetMulti (sourceJetIndex ![a.val, b.val, c.val]) = ![a.val, b.val, c.val] := by
  decide +kernel

theorem source_jet_recovered (d : MultiIndex) (order : jetOrder d ≤ 4) :
    jetMulti (sourceJetIndex d) = d := by
  have h0 : d 0 < 5 := by unfold jetOrder at order; omega
  have h1 : d 1 < 5 := by unfold jetOrder at order; omega
  have h2 : d 2 < 5 := by unfold jetOrder at order; omega
  have original : ![d 0, d 1, d 2] = d := by ext axis; fin_cases axis <;> rfl
  simpa only [original] using bounded_source_census ⟨d 0, h0⟩ ⟨d 1, h1⟩ ⟨d 2, h2⟩ order

noncomputable def sourceOrbitalBound (d : MultiIndex) (basis : Basis) : ℚ :=
  orbitalBound (sourceJetIndex d) basis

theorem full_source_jets_bounded (x : Point) (inside : InsideCube boxCentre boxRadius x)
    (d : MultiIndex) (order : jetOrder d ≤ 4) (basis : Basis) :
    |orbital (sourceTerms basis) d x| ≤ (sourceOrbitalBound d basis : ℝ) := by
  have source := source_jet_continuous_bound (sourceJetIndex d) basis x inside
  rwa [source_jet_recovered d order] at source

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceJetIncidence
