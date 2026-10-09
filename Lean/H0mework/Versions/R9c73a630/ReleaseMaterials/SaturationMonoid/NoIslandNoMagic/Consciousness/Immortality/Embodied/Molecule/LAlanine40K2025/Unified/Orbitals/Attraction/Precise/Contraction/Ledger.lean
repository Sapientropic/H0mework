import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Weighted
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.RecordedSum.Combine

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

def independentElectronNuclear : ℝ :=
  (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .electronNuclear).independentIntegral : ℤ) : ℝ) /
    10^9

theorem recorded_attraction_sum_real_within :
    |recordedAttractionSum - independentElectronNuclear| ≤ (2/10^10 : ℝ) := by
  have castSum : recordedAttractionSum = (recordedAttractionSumQ : ℝ) := by
    rw [recordedAttractionSum, recordedAttractionSumQ_eq, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Rat.cast_mul]
  rw [castSum, independentElectronNuclear]
  have bound :
      (((|recordedAttractionSumQ -
        (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .electronNuclear).independentIntegral : ℤ) : ℚ) /
          10^9| : ℚ)) : ℝ) ≤ ((2/10^10 : ℚ) : ℝ) :=
    Rat.cast_le.mpr recorded_attraction_sum_within
  norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_ofNat] at bound
  convert bound using 1 <;> norm_num

/-- The complete source-row certificate is consumed with the original D3,
    producing the independent electron–nuclear energy comparison. -/
theorem total_within_independent_of_upper
    (row : ∀ a : Fin 4851,
      |aoIntegral (targetLeft a.val) (targetRight a.val) -
        (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
          (1/10^12 : ℝ)) :
    |totalIntegral - independentElectronNuclear| ≤ (4/10^10 : ℝ) := by
  have ao := total_within_recorded_of_upper row
  have ledger := recorded_attraction_sum_real_within
  calc
    |totalIntegral - independentElectronNuclear| ≤
        |totalIntegral - recordedAttractionSum| +
          |recordedAttractionSum - independentElectronNuclear| := by
      have split : totalIntegral - independentElectronNuclear =
          (totalIntegral - recordedAttractionSum) +
            (recordedAttractionSum - independentElectronNuclear) := by ring
      rw [split]
      exact abs_add_le _ _
    _ ≤ (4/10^10 : ℝ) := by linarith

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
