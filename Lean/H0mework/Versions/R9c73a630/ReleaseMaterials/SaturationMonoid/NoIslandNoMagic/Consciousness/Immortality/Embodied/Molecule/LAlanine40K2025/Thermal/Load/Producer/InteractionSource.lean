import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.FiniteTimeRemainder
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.InitialEnergyGap
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.EnvironmentAlgebra

/-! # The actual load source pays the interaction-picture error -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open StrictThermal FiniteRemainder
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace StrictThermal

theorem ceLift_diagonal {P : Type*} [DecidableEq P]
    (values : Fin 2 × Fin 2 → ℂ) :
    ceLift (P := P) (Matrix.diagonal values) =
      Matrix.diagonal (fun x : (P × Fin 2) × Fin 2 => values (x.1.2, x.2)) := by
  ext ⟨⟨p, c⟩, e⟩ ⟨⟨q, d⟩, f⟩
  simp only [ceLift, Matrix.submatrix_apply, Equiv.prodAssoc_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem loadInteraction_norm_le_one : ‖loadInteraction‖ ≤ 1 := by
  have square : controllerEnvironmentExchange * controllerEnvironmentExchange =
      Matrix.diagonal (fun x : Fin 2 × Fin 2 => if x.1 = x.2 then (0 : ℂ) else 1) := by
    ext ⟨c, e⟩ ⟨d, f⟩
    fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
      norm_num [controllerEnvironmentExchange, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Matrix.single_apply, Matrix.diagonal_apply]
  have squareNorm : ‖loadInteraction * loadInteraction‖ ≤ 1 := by
    change ‖ceLift (P := Pair) controllerEnvironmentExchange * ceLift controllerEnvironmentExchange‖ ≤ 1
    rw [← ceLift_mul, square, ceLift_diagonal, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro x
    split_ifs <;> norm_num
  have squared := CStarRing.norm_star_mul_self (x := loadInteraction)
  change ‖loadInteractionᴴ * loadInteraction‖ = ‖loadInteraction‖ * ‖loadInteraction‖ at squared
  rw [loadInteraction_hermitian.eq] at squared
  nlinarith [norm_nonneg loadInteraction]

theorem loadBareHamiltonian_norm_le : ‖bareHamiltonian Powered.Producer.poweredTotalHamiltonian 2‖ ≤ 245 := by
  apply (norm_add_le _ _).trans
  have left := NonUnitalStarAlgHom.norm_apply_le (tensorLeft (κ := Fin 2)) Powered.Producer.poweredTotalHamiltonian
  have right := NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := PairController)) (controllerHamiltonian 2)
  change ‖Matrix.kronecker Powered.Producer.poweredTotalHamiltonian 1‖ ≤ _ at left
  change ‖Matrix.kronecker 1 (controllerHamiltonian 2)‖ ≤ _ at right
  linarith [poweredTotalHamiltonian_norm_le, controllerHamiltonian_norm_le]

end StrictThermal

/-- A presentation of the original full flow; this unitary is never substituted for the actual writer. -/
def loadInteractionPicture (elapsed : ℝ) : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  flowUnitary Powered.Producer.poweredTotalHamiltonian 2 0
    Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero (-elapsed) *
      loadUnitary elapsed

theorem loadInteractionPicture_energy (elapsed : ℝ) (current : LoadedJoint) :
    environmentEnergy (Unitary.conjStarAlgAut ℂ _ (loadInteractionPicture elapsed) current) =
      environmentEnergy (loadAdvance elapsed current) := by
  unfold loadInteractionPicture
  rw [Unitary.conjStarAlgAut_mul_apply]
  change controllerEnergy 2
    (coupledNext Powered.Producer.poweredTotalHamiltonian 2 0
      Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero
      (-elapsed) (loadAdvance elapsed current)) = controllerEnergy 2 (loadAdvance elapsed current)
  rw [← environmentObservable_energy, ← environmentObservable_energy]
  apply energy_of_commuting_observable
  simpa only [totalHamiltonian, add_zero, environmentObservable] using
    (bare_environment_commute Powered.Producer.poweredTotalHamiltonian).symm

theorem loadInteractionPicture_actual_error :
    ‖(loadInteractionPicture (Propagation.Producer.nativeClockStep : ℝ) : LoadedJoint) - 1 -
      (Propagation.Producer.nativeClockStep : ℝ) • (-Complex.I • loadInteraction)‖ ≤
        (Propagation.Producer.nativeClockStep : ℝ) / 4 :=
  interactionPicture_quarterStep_error Powered.Producer.poweredTotalHamiltonian 2 loadInteraction
    Powered.Producer.poweredTotalHamiltonian_hermitian loadInteraction_hermitian
    (Propagation.Producer.nativeClockStep : ℝ) nativeClock_small.1.le nativeClock_small.2.le
    loadBareHamiltonian_norm_le loadInteraction_norm_le_one

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
