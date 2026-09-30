import H0mework.Chemistry.LAlanineRefinementSource.JetChecksA
import H0mework.Chemistry.LAlanineRefinementSource.JetChecksB
import H0mework.Chemistry.LAlanineRefinementSource.JetChecksC

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceContinuousChecks

open SourceGaussianModel SourceFiniteData SourceFiniteChecks

theorem actual_all_jet_envelopes :
    ∀ d : JetIndex, ∀ j : Basis,
      orbitalEnvelope (sourceTerms j) (jetMulti d) boxCentre boxRadius ≤ orbitalBound d j := by
  intro d j
  by_cases first : d.val < 12
  · let index : Fin 12 := ⟨d.val, first⟩
    have same : SourceJetChecksA.jet index = d := by ext; simp [SourceJetChecksA.jet, index]
    simpa only [same] using SourceJetChecksA.actual_envelopes index j
  · by_cases second : d.val < 24
    · let index : Fin 12 := ⟨d.val-12, by omega⟩
      have same : SourceJetChecksB.jet index = d := by ext; dsimp [SourceJetChecksB.jet, index]; omega
      simpa only [same] using SourceJetChecksB.actual_envelopes index j
    · let index : Fin 11 := ⟨d.val-24, by omega⟩
      have same : SourceJetChecksC.jet index = d := by ext; dsimp [SourceJetChecksC.jet, index]; omega
      simpa only [same] using SourceJetChecksC.actual_envelopes index j

theorem source_jet_continuous_bound (d : JetIndex) (j : Basis) (x : Point)
    (inside : InsideCube boxCentre boxRadius x) :
    |orbital (sourceTerms j) (jetMulti d) x| ≤ (orbitalBound d j : ℝ) := by
  exact (orbital_abs_bound (sourceTerms j) (jetMulti d) boxCentre boxRadius x
    (source_exponents_nonnegative j) inside).trans (by exact_mod_cast actual_all_jet_envelopes d j)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceContinuousChecks
