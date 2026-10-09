import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerEnvironmentIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Environment

open Powered.Dynamics
open scoped Matrix ComplexOrder
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem reframe_positive
    (M : Matrix ((ι × κ) ⊕ (ι × κ)) ((ι × κ) ⊕ (ι × κ)) ℂ)
    (positive : M.PosSemidef) : (reframe M).PosSemidef := positive.submatrix incidence

omit [DecidableEq ι] [DecidableEq κ] in
theorem reframe_trace
    (M : Matrix ((ι × κ) ⊕ (ι × κ)) ((ι × κ) ⊕ (ι × κ)) ℂ) :
    (reframe M).trace = M.trace := submatrix_equiv_trace M incidence

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem systemReduce_prepared (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    systemReduce (reframe (prepared joint)) = prepared (systemReduce joint) := by
  ext i j
  cases i <;> cases j
  · rfl
  all_goals
    change (∑ _ : κ, (0 : ℂ)) = 0
    simp

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem controllerReduce_prepared (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    controllerReduce (reframe (prepared joint)) = controllerReduce joint := by
  ext a b
  change (∑ i : ι ⊕ ι, reframe (prepared joint) (i, a) (i, b)) =
    ∑ i : ι, joint (i, a) (i, b)
  simp [reframe, incidence, prepared, Matrix.fromBlocks, Matrix.submatrix, Fintype.sum_sum_type]

variable [Nonempty κ]

theorem prepared_gibbs_joint (rho : Matrix ι ι ℂ) (energies : κ → ℝ) (beta : ℝ)
    (U : Matrix.unitaryGroup (ι × κ) ℂ) :
    Load.Quantum.unitaryGibbsJoint (prepared rho) energies beta
      (reframeUnitary (blockUnitary U U)) =
    reframe (prepared (Load.Quantum.unitaryGibbsJoint rho energies beta U)) := by
  have generated := actual_joint_gibbs rho energies beta U 1
  simpa only [one_mul, Quantum.conjugation_apply, OneMemClass.coe_one, Matrix.one_mul,
    star_one, Matrix.mul_one] using generated.symm

theorem entropyProduction_prepared (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) (energies : κ → ℝ) (beta : ℝ)
    (U : Matrix.unitaryGroup (ι × κ) ℂ) :
    Load.Quantum.entropyProduction (prepared rho) (prepared_positive rho positive)
      ((prepared_trace rho).trans normalized) energies beta (reframeUnitary (blockUnitary U U)) =
    Load.Quantum.entropyProduction rho positive normalized energies beta U := by
  have system := congrArg systemReduce (prepared_gibbs_joint rho energies beta U)
  rw [systemReduce_prepared] at system
  have environment := congrArg controllerReduce (prepared_gibbs_joint rho energies beta U)
  rw [controllerReduce_prepared] at environment
  have oldPositive := Load.Quantum.unitaryGibbsJoint_posSemidef rho positive energies beta U
  have oldTrace := Load.Quantum.unitaryGibbsJoint_trace rho normalized energies beta U
  have outputEntropy := prepared_entropy
    (systemReduce (Load.Quantum.unitaryGibbsJoint rho energies beta U))
    (systemReduce_posSemidef _ oldPositive) ((systemReduce_trace _).trans oldTrace)
  unfold Load.Quantum.entropyProduction Load.Quantum.environmentEnergyChange
  simp only [system, environment]
  rw [outputEntropy, prepared_entropy rho positive normalized]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Environment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
