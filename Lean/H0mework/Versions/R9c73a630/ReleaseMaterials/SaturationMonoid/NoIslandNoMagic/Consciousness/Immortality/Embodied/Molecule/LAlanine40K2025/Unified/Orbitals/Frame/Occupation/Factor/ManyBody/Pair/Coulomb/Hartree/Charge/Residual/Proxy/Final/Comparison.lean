import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final.Assembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final.SecondBridge
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.ActualBound
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Bound

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem recorded_original_gamma_real (i j : Basis) :
    |Correction.recordedD3 i j - (rawGamma i j).re| < (1 / 10^12 : ℝ) := by
  have castBound :
      |(Second.retainedProduct i j : ℝ) -
        (Reentry.Source.targetRealNumerator i j : ℝ) / (gammaScale : ℝ)| <
        (1 / 10^12 : ℝ) := by
    have hcast :
        ((|Second.retainedProduct i j -
          (Reentry.Source.targetRealNumerator i j : ℚ) / (gammaScale : ℚ)| : ℚ) : ℝ) <
          ((1 / 10^12 : ℚ) : ℝ) := by
      exact_mod_cast recorded_proxy_original_gamma i j
    simpa using hcast
  simpa only [recorded_d3_second_source,Second.retainedProduct_computed,
    original_gamma_real_entry] using castBound

theorem recorded_projector_entry (i j : Basis) :
    |Correction.recordedD3 i j - 2 * (projector24 i j).re| < (1 / 10^9 : ℝ) :=
  proxy_projector_entry i j _ (recorded_original_gamma_real i j)

def actualMatrixEnvelope : ℝ :=
  (392 / 10^9 : ℝ) * ‖complexMatrix Correction.trueD3‖ * (2 + 392 / 10^9 : ℝ) +
    ((392 / 10^11 : ℝ) * ‖complexMatrix Correction.d3AO‖ *
        ‖complexMatrix Correction.trueFirst‖ +
      ‖complexMatrix Correction.recordedFirst‖ * ‖complexMatrix Correction.d3AO‖ *
        (392 / 10^11 : ℝ))

def residualEnvelope : ℝ := actualMatrixEnvelope + (1 / 10^9 : ℝ)

private theorem matrix_entry_norm_le (A : Matrix Basis Basis ℂ) (i j : Basis) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ Basis := PiLp.single 2 j 1
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Basis) A
  have entry : (T e).ofLp i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    simp only [Matrix.mulVec_single_one,Matrix.col_apply]
  calc
    _ = ‖(T e).ofLp i‖ := congrArg norm entry.symm
    _ ≤ ‖T e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = ‖A‖ := by simp only [e,PiLp.norm_single,norm_one,mul_one]; rfl

theorem actual_recorded_D3_entry (i j : Basis) :
    |normalizedDensityMatrix i j - Correction.recordedD3 i j| ≤
      actualMatrixEnvelope := by
  have bound := Correction.actual_D3_complex_operator_bound
  change ‖complexMatrix (normalizedDensityMatrix - Correction.recordedD3)‖ ≤
    actualMatrixEnvelope at bound
  calc
    |normalizedDensityMatrix i j - Correction.recordedD3 i j| =
      ‖complexMatrix (normalizedDensityMatrix - Correction.recordedD3) i j‖ := by
        rw [complex_entry_norm,Matrix.sub_apply]
    _ ≤ ‖complexMatrix (normalizedDensityMatrix - Correction.recordedD3)‖ :=
      matrix_entry_norm_le _ i j
    _ ≤ actualMatrixEnvelope := bound

theorem actual_residual_entry (i j : Basis) :
    |residualMatrix i j| < residualEnvelope := by
  have actual := actual_recorded_D3_entry i j
  have proxy := recorded_projector_entry i j
  have triangle := abs_add_le
    (normalizedDensityMatrix i j - Correction.recordedD3 i j)
    (Correction.recordedD3 i j - 2 * (projector24 i j).re)
  have identity : residualMatrix i j =
      (normalizedDensityMatrix i j - Correction.recordedD3 i j) +
        (Correction.recordedD3 i j - 2 * (projector24 i j).re) := by
    simp only [residualMatrix]
    ring
  rw [identity]
  dsimp [residualEnvelope]
  linarith

theorem actual_hartree_residual_bound :
    |Interaction.d3HartreeEnergy - directEnergy.re| ≤
      (1 / 2 : ℝ) * residualEnvelope *
        (Interaction.interactionWeight Interaction.d3Matrix +
          Interaction.interactionWeightRight Interaction.occupationMatrix) := by
  have each (i k : Basis) :
      |Interaction.deltaMatrix i k| ≤ residualEnvelope := by
    simpa only [Interaction.deltaMatrix] using le_of_lt (actual_residual_entry i k)
  exact Interaction.hartree_residual_abs_le residualEnvelope each

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
