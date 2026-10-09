import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.PairPerturbation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.SourceMoment

open Collision Moment Load.Producer.StrictThermal Propagation.Interface Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem source_observable_norm : ‖observable Thermal.Source.energyHamiltonian‖ ≤ 6400 := by
  unfold observable
  calc
    _ ≤ ‖(Powered.Source.raising Thermal.Source.energyHamiltonian)ᴴ‖ *
        ‖Powered.Source.raising Thermal.Source.energyHamiltonian‖ := norm_mul_le _ _
    _ ≤ 80 * 80 := by
      rw [← Matrix.star_eq_conjTranspose, norm_star]
      exact mul_le_mul sourceRaising_norm_le sourceRaising_norm_le (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem pairH_difference_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H K : SystemMatrix ι) (g : ℝ) : ‖pairH H g - pairH K g‖ ≤ 2 * ‖H - K‖ := by
  have difference : pairH H g - pairH K g =
      tensorLeft (κ := ι) (H - K) + tensorRight (ι := ι) (H - K) := by
    rw [map_sub, map_sub]
    change (Matrix.kronecker H 1 + Matrix.kronecker 1 H + _) -
      (Matrix.kronecker K 1 + Matrix.kronecker 1 K + _) =
      (Matrix.kronecker H 1 - Matrix.kronecker K 1) + (Matrix.kronecker 1 H - Matrix.kronecker 1 K)
    abel
  rw [difference]
  calc
    _ ≤ ‖tensorLeft (κ := ι) (H - K)‖ + ‖tensorRight (ι := ι) (H - K)‖ := norm_add_le _ _
    _ ≤ ‖H - K‖ + ‖H - K‖ := add_le_add
      (NonUnitalStarAlgHom.norm_apply_le tensorLeft _)
      (NonUnitalStarAlgHom.norm_apply_le tensorRight _)
    _ = _ := by ring

theorem source_pair_difference_norm :
    ‖pairH Work.Drive.fieldOffHamiltonian Thermal.Source.pairCoupling -
      pairH Thermal.Source.energyHamiltonian Thermal.Source.pairCoupling‖ ≤ 2 / 5 := by
  have field : ‖Thermal.Source.energyHamiltonian - Work.Drive.fieldOffHamiltonian‖ ≤ 1 / 5 := by
    rw [SourcePrimitive.source_field_energy_coordinates, conjugation_norm]
    exact SourcePrimitive.sourceFieldDelta_norm_le_fifth
  have bound := pairH_difference_norm Work.Drive.fieldOffHamiltonian Thermal.Source.energyHamiltonian
    Thermal.Source.pairCoupling
  rw [norm_sub_rev Work.Drive.fieldOffHamiltonian Thermal.Source.energyHamiltonian] at bound
  linarith

theorem source_received_moment_gt_four :
    4 < energy (observable Thermal.Source.energyHamiltonian) Powered.Producer.sourceReceivedPair := by
  have drift := PairPerturbation.energy_drift Work.Drive.fieldOffHamiltonian Thermal.Source.energyHamiltonian
    Work.Drive.fieldOffHamiltonian_hermitian Thermal.Source.pairCoupling (nativeClockStep : ℝ)
    (by exact_mod_cast nativeClockStep_positive.le)
    (observable Thermal.Source.energyHamiltonian) Work.Drive.sourceFieldCycleCurrent
    Work.Drive.sourceFieldCycleCurrent_positive_normalized.1
    Work.Drive.sourceFieldCycleCurrent_positive_normalized.2
    (pair_commutes_observable _ Thermal.Source.energyHamiltonian_hermitian _)
  have normBound :
      2 * ‖observable Thermal.Source.energyHamiltonian‖ *
        ‖pairH Work.Drive.fieldOffHamiltonian Thermal.Source.pairCoupling -
          pairH Thermal.Source.energyHamiltonian Thermal.Source.pairCoupling‖ ≤ 5120 := by
    calc
      _ ≤ 2 * 6400 * (2 / 5 : ℝ) := by
        gcongr
        · exact source_observable_norm
        · exact source_pair_difference_norm
      _ = _ := by norm_num
  have small : 5120 * (nativeClockStep : ℝ) < 9 / 4 := by
    norm_num [nativeClockStep_exact]
  have timeNonnegative : (0 : ℝ) ≤ nativeClockStep := by exact_mod_cast nativeClockStep_positive.le
  have bound := drift.trans (mul_le_mul_of_nonneg_right normBound timeNonnegative)
  rw [Powered.Producer.sourceReceivedPair_eq_fieldTarget]
  change 4 < energy (observable Thermal.Source.energyHamiltonian)
    (pairAdvance Work.Drive.fieldOffHamiltonian Thermal.Source.pairCoupling
      (nativeClockStep : ℝ) Work.Drive.sourceFieldCycleCurrent)
  have lower := (abs_le.mp bound).1
  linarith [source_before_field_moment_gt]

end
end LAlanine40K2025.Thermal.Recovery.SourceMoment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
