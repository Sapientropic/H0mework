import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source.DiagonalBounds
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.InitialEnergyGap

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Trace

open Collision Powered.Dynamics Propagation.Interface
open scoped Matrix ComplexOrder
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem swap_trace : (swapOperator : JointMatrix ι).trace = Fintype.card ι := by
  have entry (i a : ι) : (swapOperator : JointMatrix ι) (i, a) (i, a) = if i = a then 1 else 0 := by
    have product := swap_mul_apply (1 : JointMatrix ι) i a i a
    rw [Matrix.mul_one] at product
    rw [product]
    by_cases same : i = a
    · subst a
      simp
    · simp [same, Ne.symm same, Prod.mk.injEq]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, entry]
  simp

theorem interaction_trace (H : SystemMatrix ι) : (Powered.Source.interaction H).trace = 0 := by
  have zero : Powered.Source.lowering.trace = 0 := by
    norm_num [Powered.Source.lowering, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.single_apply]
  simp only [Powered.Source.interaction, Powered.Source.transfer, Matrix.trace_add,
    Matrix.trace_conjTranspose, Matrix.kronecker, Matrix.trace_kronecker, zero, mul_zero, star_zero, add_zero]

theorem source_trace_frame : Thermal.Source.energyHamiltonian.trace =
    (Propagation.Interface.activeMatrix Propagation.Source.electronicSource).trace := by
  change (Matrix.diagonal (fun i => (Preparation.sourceEnergies i : ℂ))).trace = _
  rw [← Preparation.sourceHamiltonian_diagonal]
  exact Preparation.energyCoordinates_trace _

theorem source_pc_trace : Powered.Producer.poweredTotalHamiltonian.trace =
    (392 : ℂ) * Thermal.Source.energyHamiltonian.trace + 19404 := by
  change (totalHamiltonian Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction).trace = _
  simp only [totalHamiltonian, bareHamiltonian, Matrix.trace_add, Matrix.kronecker,
    Matrix.trace_kronecker, Matrix.trace_one]
  have interaction : Powered.Source.sourceInteraction.trace = 0 := interaction_trace _
  rw [interaction]
  change _ = _
  have pair : Work.Drive.fieldBaseline.trace = 196 * Thermal.Source.energyHamiltonian.trace + 98 := by
    change (Thermal.Dynamics.pairH Thermal.Source.energyHamiltonian 1).trace = _
    simp only [Thermal.Dynamics.pairH, Thermal.Dynamics.freePairH, jointHamiltonian,
      Matrix.trace_add, Matrix.kronecker, Matrix.trace_kronecker, Matrix.trace_one,
      Complex.ofReal_one, one_smul, swap_trace]
    norm_num
    ring
  rw [pair]
  norm_num [controllerHamiltonian, Matrix.trace_diagonal, Fin.sum_univ_two]
  ring

theorem source_pc_trace_gt_dimension : (Fintype.card Load.Source.PairController : ℝ) <
    Powered.Producer.poweredTotalHamiltonian.trace.re := by
  rw [source_pc_trace, source_trace_frame]
  norm_num [Complex.mul_re]
  linarith [SourceBounds.source_trace_positive]

end
end LAlanine40K2025.Thermal.Recovery.Charging.Trace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
