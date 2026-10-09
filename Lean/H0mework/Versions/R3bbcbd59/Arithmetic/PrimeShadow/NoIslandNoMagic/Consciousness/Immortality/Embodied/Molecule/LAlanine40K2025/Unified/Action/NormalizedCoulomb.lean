import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.ActionNormalization
import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.CoulombEnergy
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenConfiguration

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage10.ActionNormalization Stage9C.Material.SpinPair Stage10.CanonicalGauss
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient
noncomputable section

theorem normalized_actual_pair_hamiltonian (first second : Basis) (scale : ℝ) (point : BasePoint) :
    hamiltonian (Stage10.CanonicalGauss.withMatter (abelianPotential GreenSource.fieldPotential)
      (GaussSource.preparedMatter second scale) (GaussSource.preparedDual first scale)) point =
      actionScale*Stage10.StaticHamiltonian.hamiltonianDensity Stage10.Runtime.source
        (Stage10.CanonicalGauss.withMatter (abelianPotential GreenSource.fieldPotential)
          (GaussSource.preparedMatter second scale) (GaussSource.preparedDual first scale)) point :=
  source_hamiltonian _ (GreenSource.generated_prepared_smooth first second scale) point

theorem normalized_electron_current (point : Point) : actionScale*GreenSource.sourceCurrent point = -sourceDensity point := by
  rw [GreenSource.sourceCurrent_value, actionScale_source]
  field_simp [spinScale_pos.ne']

theorem normalized_nuclear_current (time lengthUnit : ℝ) (test : Point → ℝ) :
    actionScale*PreciseNuclear.nativeCoupling time lengthUnit test =
      ∑ atom : Fin 13, WholeBandBasin.Family.All.Nuclear.nuclearCharge atom*test (PreciseNuclear.sourcePosition lengthUnit atom) := by
  rw [PreciseNuclear.original_coupling, actionScale_source]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro atom _
  field_simp [spinScale_pos.ne']

def coulombCoefficient : ℝ := (4*spinScale)/(8*Real.pi*lapse)

theorem coulombCoefficient_positive : 0 < coulombCoefficient := by
  unfold coulombCoefficient
  exact div_pos (mul_pos (by norm_num) spinScale_pos) (mul_pos (mul_pos (by norm_num) Real.pi_pos) lapse_pos)

theorem normalized_full_target_coulomb :
    actionScale*PreciseNuclear.electrostaticEnergy = coulombCoefficient*
      (UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.d3HartreeEnergy+
        UnifiedOrbitals.Attraction.Precise.totalIntegral+
          WholeBandBasin.Family.All.Nuclear.PreciseTarget.totalRepulsion) := by
  rw [PreciseNuclear.original_full_target_coulomb_energy, actionScale_source]
  unfold coulombCoefficient
  field_simp [spinScale_pos.ne']

theorem rejects_matter_only_normalization : coulombCoefficient ≠ (8*Real.pi*lapse)⁻¹ := by
  intro same
  have positive : 0 < 8*Real.pi*lapse := mul_pos (mul_pos (by norm_num) Real.pi_pos) lapse_pos
  have multiplied := congrArg (fun value : ℝ => value*(8*Real.pi*lapse)) same
  unfold coulombCoefficient at multiplied
  rw [div_mul_cancel₀ _ positive.ne', inv_mul_cancel₀ positive.ne'] at multiplied
  nlinarith [spinScale_sq]

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
