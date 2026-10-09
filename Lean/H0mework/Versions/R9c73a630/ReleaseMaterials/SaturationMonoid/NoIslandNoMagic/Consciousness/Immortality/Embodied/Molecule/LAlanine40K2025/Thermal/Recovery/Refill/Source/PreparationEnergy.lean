import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefillField.GibbsEnergy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.PreparationEnergy

open Collision Preparation Propagation.Interface Propagation.Source Propagation.Dynamics
open scoped Matrix ComplexOrder
noncomputable section

def electronicUnitary (time : ℝ) : Matrix.unitaryGroup Basis ℂ :=
  ⟨matrixOperatorEquiv.symm (propagator electronicSource time),
    Unitary.map_mem matrixOperatorEquiv.symm (propagator_unitary electronicSource time)⟩

theorem electronicUnitary_commutes (time : ℝ) :
    Commute (activeMatrix electronicSource) (electronicUnitary time : Matrix Basis Basis ℂ) := by
  apply Commute.of_map matrixOperatorEquiv.injective
  change Commute (hamiltonian electronicSource)
    (matrixOperatorEquiv (matrixOperatorEquiv.symm (propagator electronicSource time)))
  rw [StarAlgEquiv.apply_symm_apply]
  exact (((Commute.refl (hamiltonian electronicSource)).smul_right (-Complex.I)).smul_right
    (time : ℂ)).exp_right

theorem preparedDensity_actual (time : ℝ) : preparedDensity time =
    (electronicUnitary time : Matrix Basis Basis ℂ) *
      normalizedGram (initialDensityMatrix electronicSource) *
        star (electronicUnitary time : Matrix Basis Basis ℂ) := by
  unfold preparedDensity Propagation.Consumer.densityMatrix densityEvolution
  change normalizedGram (matrixOperatorEquiv.symm
    (propagator electronicSource time * initialDensity electronicSource *
      propagator electronicSource (-time))) = _
  have starRead : matrixOperatorEquiv.symm (star (propagator electronicSource time)) =
      star (matrixOperatorEquiv.symm (propagator electronicSource time)) :=
    map_star matrixOperatorEquiv.symm (propagator electronicSource time)
  rw [propagator_neg_eq_star, map_mul, map_mul, starRead]
  have initialRead : matrixOperatorEquiv.symm (initialDensity electronicSource) =
      initialDensityMatrix electronicSource := matrixOperatorEquiv.symm_apply_apply _
  rw [initialRead]
  change normalizedGram ((electronicUnitary time : Matrix Basis Basis ℂ) *
    initialDensityMatrix electronicSource * star (electronicUnitary time : Matrix Basis Basis ℂ)) = _
  exact normalizedGram_conjugation _ _

theorem commuting_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ)
    (commutes : Commute H (U : Matrix ι ι ℂ)) :
    energy H ((U : Matrix ι ι ℂ) * rho * star (U : Matrix ι ι ℂ)) = energy H rho := by
  unfold energy
  congr 1
  calc
    _ = ((U : Matrix ι ι ℂ) * (H * rho) * star (U : Matrix ι ι ℂ)).trace := by
      rw [← mul_assoc, ← mul_assoc, commutes.eq]
      simp only [mul_assoc]
    _ = _ := unitary_conjugation_trace U _

theorem preparedDensity_energy (time : ℝ) :
    energy (activeMatrix electronicSource) (preparedDensity time) =
      energy (activeMatrix electronicSource) (normalizedGram (initialDensityMatrix electronicSource)) := by
  rw [preparedDensity_actual]
  exact commuting_energy _ _ (electronicUnitary time) (electronicUnitary_commutes time)

theorem source_system_mean_gt_neg_eight :
    -8 < energy Thermal.Source.energyHamiltonian Thermal.Source.systemCurrent := by
  have invariant := Work.Capacity.energy_unitary_conjugation
    (activeMatrix electronicSource) (preparedDensity (collisionCurrentTime : ℝ))
    (star sourceEnergyFrame)
  change energy (Quantum.conjugation (star sourceEnergyFrame) (activeMatrix electronicSource))
    (Quantum.conjugation (star sourceEnergyFrame) (preparedDensity (collisionCurrentTime : ℝ))) = _ at invariant
  rw [Powered.Source.sourceHamiltonian_in_shared_frame, Powered.Source.sourceCoordinates_as_conjugation] at invariant
  change -8 < energy Thermal.Source.energyHamiltonian (energyCoordinates (preparedDensity _))
  rw [invariant, preparedDensity_energy]
  exact SourcePrimitive.sourceGramEnergy_gt_neg_eight

theorem source_mean_gap_gt_five : 5 <
    energy Thermal.Source.energyHamiltonian Thermal.Source.systemCurrent -
      energy Thermal.Source.energyHamiltonian Thermal.Source.bathCurrent := by
  linarith [source_system_mean_gt_neg_eight, GibbsEnergy.source_bath_mean_lt_neg_thirteen]

end
end LAlanine40K2025.Thermal.Recovery.PreparationEnergy
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
