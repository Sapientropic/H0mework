import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.PreparedReservoirTransfer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Native

open Collision Propagation.Producer Load.Source Load.Producer.StrictThermal
open Powered.Dynamics Work.Capacity
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def sourceCoupling : ℝ := (Real.pi / 2 - (nativeClockStep : ℝ)) / (nativeClockStep : ℝ)

def freePCUnitary (time : ℝ) : Matrix.unitaryGroup PairController ℂ :=
  flowUnitary Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
    Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian time

def pairFlow (time : ℝ) : Matrix.unitaryGroup (PairController × PairController) ℂ :=
  Dynamics.pairUnitary Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian sourceCoupling time

theorem sourceCoupling_clock : sourceCoupling * (nativeClockStep : ℝ) =
    Real.pi / 2 - (nativeClockStep : ℝ) := div_mul_cancel₀ _ (ne_of_gt nativeClock_small.1)

theorem sourceCoupling_positive : 0 < sourceCoupling := by
  apply div_pos _ nativeClock_small.1
  have small : (nativeClockStep : ℝ) < 1 := by rw [nativeClockStep_exact]; norm_num
  linarith [Real.pi_gt_three]

theorem pairFlow_factor (time : ℝ) :
    pairFlow time = Quantum.localUnitary (freePCUnitary time) (freePCUnitary time) *
      Exchange.exchangeUnitary (sourceCoupling * time) := by
  apply Subtype.ext
  change Dynamics.pairPropagatorMatrix Powered.Producer.poweredTotalHamiltonian sourceCoupling time =
    Matrix.kronecker (freePCUnitary time : Matrix PairController PairController ℂ)
      (freePCUnitary time : Matrix PairController PairController ℂ) *
      partialSwap (Real.cos (sourceCoupling * time)) (Real.sin (sourceCoupling * time))
  rw [Dynamics.pairPropagatorMatrix_factorization]
  congr 1
  have split : (-Complex.I * (time : ℂ)) • Dynamics.freePairH Powered.Producer.poweredTotalHamiltonian =
      Matrix.kronecker (time • (-Complex.I • Powered.Producer.poweredTotalHamiltonian)) 1 +
        Matrix.kronecker 1 (time • (-Complex.I • Powered.Producer.poweredTotalHamiltonian)) := by
    ext i j
    simp [Dynamics.freePairH, jointHamiltonian, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.smul_apply, Complex.real_smul]
    ring
  rw [split, Load.Recovery.Control.exp_tensor_sum]
  simp only [freePCUnitary, flowUnitary_matrix_exp]
  rfl

theorem freePC_energy (time : ℝ) (rho : Matrix PairController PairController ℂ) :
    energy Powered.Producer.poweredTotalHamiltonian (Quantum.conjugation (freePCUnitary time) rho) =
      energy Powered.Producer.poweredTotalHamiltonian rho :=
  totalEnergy_conserved _ _ _ _ _ _ _

def pairTarget : JointMatrix PairController := Quantum.conjugation (pairFlow (nativeClockStep : ℝ)) Source.pairOrigin

theorem pairTarget_read :
    pairTarget = Quantum.localConjugation (freePCUnitary (nativeClockStep : ℝ))
      (freePCUnitary (nativeClockStep : ℝ)) Source.pairTarget := by
  unfold pairTarget
  rw [pairFlow_factor, sourceCoupling_clock]
  change Unitary.conjStarAlgAut ℂ (JointMatrix PairController)
    (Quantum.localUnitary (freePCUnitary _) (freePCUnitary _) * Exchange.nearTransfer _)
    Source.pairOrigin = _
  rw [Unitary.conjStarAlgAut_mul_apply]
  rfl

theorem pairTarget_pc :
    Collision.systemReduce pairTarget = Quantum.conjugation (freePCUnitary (nativeClockStep : ℝ)) Source.pcTarget := by
  rw [pairTarget_read, Quantum.systemReduce_local_conjugation]
  rfl

theorem pairTarget_donor :
    Collision.bathReduce pairTarget = Quantum.conjugation (freePCUnitary (nativeClockStep : ℝ)) Source.donorTarget := by
  rw [pairTarget_read, Quantum.bathReduce_local_conjugation]
  rfl

theorem pc_energy_gain : 6 < energy Powered.Producer.poweredTotalHamiltonian (Collision.systemReduce pairTarget) -
    energy Powered.Producer.poweredTotalHamiltonian (Load.Producer.RecoveryLedger.pcRead Source.received).joint := by
  rw [pairTarget_pc, freePC_energy]
  exact Source.pc_energy_gain

theorem donor_paid_gain : 6 < energy Powered.Producer.poweredTotalHamiltonian Source.donor -
    energy Powered.Producer.poweredTotalHamiltonian (Collision.bathReduce pairTarget) := by
  rw [pairTarget_donor, freePC_energy]
  exact Source.donor_paid_gain

theorem source_energy_balance :
    (energy Powered.Producer.poweredTotalHamiltonian (Collision.systemReduce pairTarget) -
      energy Powered.Producer.poweredTotalHamiltonian (Load.Producer.RecoveryLedger.pcRead Source.received).joint) +
    (energy Powered.Producer.poweredTotalHamiltonian (Collision.bathReduce pairTarget) -
      energy Powered.Producer.poweredTotalHamiltonian Source.donor) = 0 := by
  rw [pairTarget_pc, pairTarget_donor, freePC_energy, freePC_energy]
  exact Source.source_energy_balance

theorem pc_capacity_gain :
    6 < ergotropy Powered.Producer.poweredTotalHamiltonian
      (Quantum.conjugation (freePCUnitary (nativeClockStep : ℝ)) Source.pcTarget)
      Powered.Producer.poweredTotalHamiltonian_hermitian
      (Quantum.conjugation_posSemidef _ _ Source.pcTarget_positive).isHermitian -
      Powered.Producer.poweredJointCapacity (Load.Producer.RecoveryLedger.pcRead Source.received) := by
  have balance := ergotropy_unitary_change Powered.Producer.poweredTotalHamiltonian Source.pcTarget
    Powered.Producer.poweredTotalHamiltonian_hermitian Source.pcTarget_positive.isHermitian (freePCUnitary (nativeClockStep : ℝ))
  change _ - _ = energy Powered.Producer.poweredTotalHamiltonian
    (Quantum.conjugation (freePCUnitary _) Source.pcTarget) - _ at balance
  rw [freePC_energy, sub_self] at balance
  have preserved : ergotropy Powered.Producer.poweredTotalHamiltonian
      (Quantum.conjugation (freePCUnitary (nativeClockStep : ℝ)) Source.pcTarget)
      Powered.Producer.poweredTotalHamiltonian_hermitian
      (Quantum.conjugation_posSemidef _ _ Source.pcTarget_positive).isHermitian =
    ergotropy Powered.Producer.poweredTotalHamiltonian Source.pcTarget
      Powered.Producer.poweredTotalHamiltonian_hermitian Source.pcTarget_positive.isHermitian := sub_eq_zero.mp balance
  rw [preserved]
  exact Source.pc_capacity_gain

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Native
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
