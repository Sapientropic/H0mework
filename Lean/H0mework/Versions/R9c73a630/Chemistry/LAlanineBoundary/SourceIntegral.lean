import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.CalculusActual
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.SourceQuarterFaces
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.SourceSpatialBoundary

/-! The actual oriented boundary gradient flux consumes the already-generated spatial integral. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel WholeCellPartition WholeCellSpatial Set MeasureTheory
open scoped BigOperators
noncomputable section

theorem netFlux_eq_spatialIntegral : netFlux = fullLaplacianIntegral := by
  rw [netFlux_eq_integral_divergence pulledFlux_contDiff,
    sourceGeneratedWholeCellClosure.spatialCommuting]
  unfold fullSignedIntegral
  apply setIntegral_congr_fun full_measurable
  intro p _
  exact div_pulledFlux p

theorem quarterFlux_eq_spatialReadout (q : Quarter) : quarterNetFlux q = quarterSignedIntegral q := by
  rw [quarterNetFlux_eq_divergence pulledFlux_contDiff]
  unfold quarterSignedIntegral
  apply setIntegral_congr_fun (quarter_measurable q)
  intro p _
  exact div_pulledFlux p

theorem netFlux_eq_four_quarters : netFlux = ∑ q : Quarter, quarterNetFlux q := by
  rw [netFlux_eq_spatialIntegral, sourceGeneratedWholeCellClosure.signedPartition]
  exact Finset.sum_congr rfl (fun q _ => (quarterFlux_eq_spatialReadout q).symm)

theorem actual_gradient_flux_strict :
    (-623 / 10000000000 : ℝ) < netFlux ∧ netFlux < (-39 / 10000000000 : ℝ) := by
  rw [netFlux_eq_spatialIntegral]
  exact sourceGeneratedWholeCellClosure.signedStrict

theorem all_six_zero_flux_rejected : ¬∀ face : Face, faceIntegral face = 0 := by
  intro zero
  have empty : netFlux = 0 := by simp only [netFlux, zero, add_zero, Finset.sum_const_zero]
  have negative := actual_gradient_flux_strict.2
  rw [empty] at negative
  norm_num at negative

theorem actual_negative_face : ∃ face : Face, faceIntegral face < 0 := by
  by_contra none
  push Not at none
  have nonnegative : 0 ≤ netFlux :=
    Finset.sum_nonneg (fun i _ => add_nonneg (none (i,true)) (none (i,false)))
  have negative := actual_gradient_flux_strict.2
  linarith

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
