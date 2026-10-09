import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedReservoirCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.JointObservableIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Physical

open Collision Load.Source Powered.Dynamics Load.Producer.StrictThermal
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Current
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def pairHamiltonian : JointMatrix PairController :=
  Dynamics.pairH Powered.Producer.poweredTotalHamiltonian Native.sourceCoupling

theorem pairHamiltonian_hermitian : pairHamiltonian.IsHermitian :=
  Dynamics.pairH_hermitian _ Powered.Producer.poweredTotalHamiltonian_hermitian _

def baselineHamiltonian : FullJoint :=
  Incidence.bodyObservable loadTotalHamiltonian + Incidence.donorObservable Powered.Producer.poweredTotalHamiltonian

def controlHamiltonian : FullJoint := bareHamiltonian pairHamiltonian 2

def boundaryHamiltonian : FullJoint := Incidence.bodyObservable loadInteraction

theorem pulse_is_full_flow (time : ℝ) :
    flowUnitary pairHamiltonian 2 0 pairHamiltonian_hermitian Matrix.isHermitian_zero time = pulse time := by
  apply Subtype.ext
  change (flowUnitary pairHamiltonian 2 0 pairHamiltonian_hermitian Matrix.isHermitian_zero time : FullJoint) =
    Matrix.kronecker (Dynamics.pairPropagatorMatrix Powered.Producer.poweredTotalHamiltonian Native.sourceCoupling time)
      (Load.Recovery.Control.environmentUnitary time : Matrix (Fin 2) (Fin 2) ℂ)
  rw [flowUnitary_matrix_exp, Dynamics.pairPropagatorMatrix_eq_exp]
  change NormedSpace.exp (time • (-Complex.I • (bareHamiltonian pairHamiltonian 2 + 0))) =
    Matrix.kronecker (NormedSpace.exp ((-Complex.I * (time : ℂ)) • pairHamiltonian))
      (NormedSpace.exp (time • (-Complex.I • controllerHamiltonian 2)))
  rw [add_zero]
  have scalar : (-Complex.I * (time : ℂ)) • pairHamiltonian = time • (-Complex.I • pairHamiltonian) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    ring
  rw [scalar]
  have split : time • (-Complex.I • bareHamiltonian pairHamiltonian 2) =
      Matrix.kronecker (time • (-Complex.I • pairHamiltonian)) 1 +
        Matrix.kronecker 1 (time • (-Complex.I • controllerHamiltonian 2)) := by
    ext i j
    simp [bareHamiltonian, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Complex.real_smul]
    ring
  rw [split, Load.Recovery.Control.exp_tensor_sum]

def baselineEnergy (current : State) : ℝ := energy baselineHamiltonian current.joint
def controlEnergy (current : State) : ℝ := energy controlHamiltonian current.joint
def boundaryEnergy (current : State) : ℝ := energy boundaryHamiltonian current.joint

def switchInWork (current : State) : ℝ := controlEnergy current - baselineEnergy current
def switchOutWork (current : State) : ℝ := baselineEnergy current - controlEnergy current
def sourceWork (current : State) : ℝ := switchInWork current + switchOutWork (supplyNext current)

theorem supply_preserves_control_energy (current : State) :
    controlEnergy (supplyNext current) = controlEnergy current := by
  have conserved := totalEnergy_conserved pairHamiltonian 2 0 pairHamiltonian_hermitian
    Matrix.isHermitian_zero (Propagation.Producer.nativeClockStep : ℝ) current.joint
  unfold coupledNext at conserved
  rw [pulse_is_full_flow] at conserved
  change energy (controlHamiltonian + 0) (Quantum.conjugation (pulse (Propagation.Producer.nativeClockStep : ℝ)) current.joint) =
    energy (controlHamiltonian + 0) current.joint at conserved
  rw [add_zero, ← supplyNext_joint] at conserved
  exact conserved

theorem sourceWork_actual (current : State) :
    sourceWork current = baselineEnergy (supplyNext current) - baselineEnergy current := by
  unfold sourceWork switchInWork switchOutWork
  rw [supply_preserves_control_energy]
  ring

theorem boundary_read (current : State) :
    boundaryEnergy current = Load.Source.boundaryEnergy (Incidence.bodyRead current.joint) :=
  Incidence.bodyObservable_energy loadInteraction current.joint

theorem boundary_abs_le_one (current : State) : |boundaryEnergy current| ≤ 1 := by
  rw [boundary_read]
  exact (energy_abs_le_norm loadInteraction (Incidence.bodyRead current.joint)
    (Incidence.bodyRead_positive _ current.positive)
    ((Incidence.bodyRead_trace _).trans current.normalized)).trans loadInteraction_norm_le_one

theorem loadPulse_baseline (time : ℝ) :
    (loadPulse time : FullJoint) = NormedSpace.exp (time • (-Complex.I • baselineHamiltonian)) := by
  have oldFlow : (loadUnitary time : LoadedJoint) = NormedSpace.exp (time • (-Complex.I • loadTotalHamiltonian)) :=
    flowUnitary_matrix_exp _ _ _ _ _ _
  have donorFlow : (Native.freePCUnitary time : Matrix PairController PairController ℂ) =
      NormedSpace.exp (time • (-Complex.I • Powered.Producer.poweredTotalHamiltonian)) :=
    flowUnitary_matrix_exp _ _ _ _ _ _
  change (Matrix.kronecker (loadUnitary time : LoadedJoint)
    (Native.freePCUnitary time : Matrix PairController PairController ℂ)).submatrix
      Incidence.bodyReservoir Incidence.bodyReservoir = _
  rw [oldFlow, donorFlow, ← Load.Recovery.Control.exp_tensor_sum, ← Incidence.exp_regroup]
  congr 1
  ext i j
  simp only [baselineHamiltonian, Incidence.bodyObservable, Incidence.donorObservable,
    Matrix.submatrix_apply, Incidence.bodyReservoir, Equiv.coe_fn_mk, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  have oneRead (a b : PairController × Fin 2) : (1 : LoadedJoint) a b =
      (1 : Matrix PairController PairController ℂ) a.1 b.1 * (1 : Matrix (Fin 2) (Fin 2) ℂ) a.2 b.2 := by
    change (1 : LoadedJoint) a b = (Matrix.kronecker (1 : Matrix PairController PairController ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ)) a b
    simp only [Matrix.kronecker, Matrix.one_kronecker_one]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  rw [oneRead]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Physical
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
