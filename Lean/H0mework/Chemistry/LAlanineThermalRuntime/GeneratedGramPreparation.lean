import H0mework.Quantum.GNS.NormalizedGram
import H0mework.Chemistry.LAlaninePropagation.GeneratedNativeClock
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Positive one-electron preparation from the actual molecular current

The registered operation is D ↦ D D* / Tr(D D*), not an assertion that
the quantized 48-electron D was already a positive trace-one density.
The Hamiltonian itself generates the energy basis, not a supplied eigensystem.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Preparation

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Producer
open scoped ComplexOrder

noncomputable section

def preparedDensity (time : ℝ) : Matrix Basis Basis ℂ :=
  normalizedGram (densityMatrix electronicSource time)

theorem sourceDensity_nonzero (time : ℝ) : densityMatrix electronicSource time ≠ 0 := by
  intro hz
  have trace := sourceElectronicTrace time
  rw [hz, Matrix.trace_zero] at trace
  norm_num at trace

theorem preparedDensity_posSemidef (time : ℝ) : (preparedDensity time).PosSemidef :=
  normalizedGram_posSemidef _

theorem preparedDensity_trace (time : ℝ) : (preparedDensity time).trace = 1 :=
  normalizedGram_trace _ (sourceDensity_nonzero time)

def sourceEnergyFrame : Matrix.unitaryGroup Basis ℂ :=
  (activeMatrix_hermitian electronicSource).eigenvectorUnitary

def sourceEnergies : Basis → ℝ :=
  (activeMatrix_hermitian electronicSource).eigenvalues

def energyCoordinates (A : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  star (sourceEnergyFrame : Matrix Basis Basis ℂ) * A * sourceEnergyFrame

theorem energyCoordinates_posSemidef {A : Matrix Basis Basis ℂ} (hA : A.PosSemidef) :
    (energyCoordinates A).PosSemidef :=
  hA.conjTranspose_mul_mul_same (sourceEnergyFrame : Matrix Basis Basis ℂ)

theorem energyCoordinates_trace (A : Matrix Basis Basis ℂ) :
    (energyCoordinates A).trace = A.trace := by
  simpa only [energyCoordinates, Unitary.coe_star, star_star] using
    unitary_conjugation_trace (star sourceEnergyFrame) A

theorem sourceHamiltonian_diagonal :
    energyCoordinates (activeMatrix electronicSource) =
      Matrix.diagonal (fun i => (sourceEnergies i : ℂ)) := by
  have diagonal := (activeMatrix_hermitian electronicSource).conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at diagonal
  exact diagonal

def preparedEnergyDensity (time : ℝ) : Matrix Basis Basis ℂ :=
  energyCoordinates (preparedDensity time)

theorem preparedEnergyDensity_posSemidef (time : ℝ) :
    (preparedEnergyDensity time).PosSemidef :=
  energyCoordinates_posSemidef (preparedDensity_posSemidef time)

theorem preparedEnergyDensity_trace (time : ℝ) : (preparedEnergyDensity time).trace = 1 := by
  rw [preparedEnergyDensity, energyCoordinates_trace, preparedDensity_trace]

def preparedPopulation (time : ℝ) (i : Basis) : ℝ :=
  (preparedEnergyDensity time i i).re

theorem preparedPopulation_nonnegative (time : ℝ) (i : Basis) :
    0 ≤ preparedPopulation time i :=
  (Complex.nonneg_iff.mp (preparedEnergyDensity_posSemidef time).diag_nonneg).1

theorem preparedPopulation_normalized (time : ℝ) : ∑ i, preparedPopulation time i = 1 := by
  change (∑ i : Basis, (preparedEnergyDensity time i i).re) = 1
  have trace := congrArg Complex.re (preparedEnergyDensity_trace time)
  simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.one_re] using trace

end

/-- The registered preparation begins at the actual first native current. -/
noncomputable def collisionCurrentTime : ℚ := 1 + nativeClockStep

theorem collisionCurrentTime_exact :
    collisionCurrentTime = 36228402618028463 / 36212777618028463 := firstNativeClockTarget_exact

end LAlanine40K2025.Thermal.Preparation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
