import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Second.Assembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Cast
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Vector
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Isolation

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Producer
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def original : Matrix Basis Basis ℂ := activeMatrix Propagation.Source.electronicSource
def witness (i : Basis) : ℂ := (Witness.vector[i.val]! : ℂ)
def scaledWitness (i : Basis) : ℂ := witness i / 1000000

theorem original_hermitian : original.IsHermitian :=
  Propagation.Dynamics.activeMatrix_hermitian _

theorem upper_hermitian : (Cast.complexMatrix Upper.numerator).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (Upper.numerator j i : ℂ) = (Upper.numerator i j : ℂ)
  rw [Upper.source_entries, Upper.source_entries, Propagation.Dynamics.activeNumerator_swap _ j i]
  by_cases same : i = j
  · subst j
    simp
  · simp [same, Ne.symm same]

theorem second_hermitian : (Cast.complexMatrix Second.numerator).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (Second.numerator j i : ℂ) = (Second.numerator i j : ℂ)
  rw [Second.source_entries, Second.source_entries, Propagation.Dynamics.activeNumerator_swap _ j i]
  by_cases same : i = j
  · subst j
    simp
  · simp [same, Ne.symm same]
    ring

theorem upper_scale : (1/1000000000000000 : ℝ) • Cast.complexMatrix Upper.numerator =
    ((63/20 : ℝ) : ℂ) • 1 - original := by
  ext i j
  change ((1/1000000000000000 : ℝ) : ℂ) * (Upper.numerator i j : ℂ) =
    ((63/20 : ℝ) : ℂ) * (if i = j then 1 else 0) -
      (activeNumerator Propagation.Source.electronicSource i j : ℂ) / 1000000000000000
  rw [Upper.source_entries]
  by_cases same : i = j
  · subst j
    push_cast
    simp
    ring
  · simp [same, Ne.symm same]
    ring

theorem second_scale : (1/1000000000000000 : ℝ) • Cast.complexMatrix Second.numerator =
    (3 : ℂ) • 1 - original + Soundness.rankOne scaledWitness := by
  ext i j
  change ((1/1000000000000000 : ℝ) : ℂ) * (Second.numerator i j : ℂ) =
    (3 : ℂ) * (if i = j then 1 else 0) -
      (activeNumerator Propagation.Source.electronicSource i j : ℂ) / 1000000000000000 +
        scaledWitness i * star (scaledWitness j)
  rw [Second.source_entries]
  simp only [scaledWitness, witness]
  by_cases same : i = j
  · subst j
    push_cast
    simp
    ring
  · simp [same, Ne.symm same]
    ring

theorem upper_positive : (((63/20 : ℝ) : ℂ) • 1 - original).PosDef := by
  have integerPositive := Cast.gram_positive Upper.numerator Upper.basisChange Upper.firstProduct Upper.gram
    Upper.first_exact Upper.gram_exact Upper.margins upper_hermitian
  have scaled := integerPositive.smul (show 0 < (1/1000000000000000 : ℝ) by norm_num)
  rw [upper_scale] at scaled
  exact scaled

theorem second_positive : ((3 : ℂ) • 1 - original + Soundness.rankOne scaledWitness).PosDef := by
  have integerPositive := Cast.gram_positive Second.numerator Second.basisChange Second.firstProduct Second.gram
    Second.first_exact Second.gram_exact Second.margins second_hermitian
  have scaled := integerPositive.smul (show 0 < (1/1000000000000000 : ℝ) by norm_num)
  rw [second_scale] at scaled
  exact scaled

theorem witness_norm : star witness ⬝ᵥ witness = (Rows.dot Witness.vector Witness.vector : Int) := by
  change (∑ i : Basis, star (Witness.vector[i.val]! : ℂ) * (Witness.vector[i.val]! : ℂ)) = _
  rw [Rows.dot_eq_sum _ _ Vector.length Vector.length]
  simp only [Rows.read, Int.cast_sum, Int.cast_mul, star_intCast]

theorem witness_applied (i : Basis) : (original *ᵥ witness) i =
    (Witness.appliedVector[i.val]! : ℂ) / 1000000000000000 := by
  change (∑ j : Basis, ((activeNumerator Propagation.Source.electronicSource i j : ℂ) / 1000000000000000) *
    (Witness.vector[j.val]! : ℂ)) = _
  rw [Vector.applied_component]
  simp only [Int.cast_sum, Int.cast_mul, div_mul_eq_mul_div, Finset.sum_div]

theorem witness_energy : star witness ⬝ᵥ (original *ᵥ witness) =
    ((Rows.dot Witness.vector Witness.appliedVector : Int) : ℂ) / 1000000000000000 := by
  change (∑ i : Basis, star (witness i) * (original *ᵥ witness) i) = _
  simp_rw [witness_applied]
  rw [Rows.dot_eq_sum _ _ Vector.length Vector.appliedLength]
  simp only [witness, Rows.read, star_intCast, Int.cast_sum, Int.cast_mul, mul_div_assoc, Finset.sum_div]

theorem source_rayleigh : (31/10 : ℝ) * (star witness ⬝ᵥ witness).re <
    (star witness ⬝ᵥ (original *ᵥ witness)).re := by
  rw [witness_norm, witness_energy]
  norm_num only [Complex.intCast_re, Complex.div_ofNat_re]
  have exactInequality := Vector.rayleigh
  have realInequality : (31 : ℝ)*1000000000000000*(Rows.dot Witness.vector Witness.vector : Int) <
      10*(Rows.dot Witness.vector Witness.appliedVector : Int) := by exact_mod_cast exactInequality
  apply (lt_div_iff₀ (show (0 : ℝ) < 1000000000000000 by norm_num)).mpr
  linarith

theorem source_top_lower : (31/10 : ℝ) < Preparation.sourceEnergies Spectrum.firstIndex := by
  change (31/10 : ℝ) < original_hermitian.eigenvalues (Spectrum.firstIndex (ι := Basis))
  exact Soundness.maximum_gt_of_rayleigh original original_hermitian (31/10) witness
    Spectrum.firstIndex (Spectrum.eigenvalue_le_first original original_hermitian) source_rayleigh

theorem source_top_upper : Preparation.sourceEnergies Spectrum.firstIndex < (63/20 : ℝ) := by
  change original_hermitian.eigenvalues (Spectrum.firstIndex (ι := Basis)) < (63/20 : ℝ)
  exact Soundness.shift_posDef_upper original original_hermitian (63/20) upper_positive _

theorem source_second_upper : Preparation.sourceEnergies secondEnergyIndex < (3 : ℝ) := by
  change original_hermitian.eigenvalues secondEnergyIndex < (3 : ℝ)
  have different : (Spectrum.firstIndex (ι := Basis)) ≠ secondEnergyIndex := by
    intro equality
    have indices := congrArg (fun i : Basis => (Work.Capacity.spectralIndex i).val) equality
    norm_num [Spectrum.firstIndex, secondEnergyIndex] at indices
  exact Soundness.rankOne_second_upper original original_hermitian 3 scaledWitness second_positive
    Spectrum.firstIndex secondEnergyIndex different
    (Spectrum.eigenvalue_le_first original original_hermitian secondEnergyIndex)

theorem actual_top_pair : SourceTopPairBounds :=
  ⟨source_top_lower, source_top_upper, source_second_upper⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
