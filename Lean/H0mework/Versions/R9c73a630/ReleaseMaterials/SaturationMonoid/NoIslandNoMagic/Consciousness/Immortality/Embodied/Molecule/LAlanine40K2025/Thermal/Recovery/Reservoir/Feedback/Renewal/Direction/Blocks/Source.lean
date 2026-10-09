import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Algebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Source
import Mathlib.Data.Sym.Card

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks

open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

section SourceOrbit
open Propagation.Interface Load.Source

def pairOrbit (p : Basis × Basis) : Sym2 Basis := s(p.1,p.2)
def pcOrbit (p : PairController) : Sym2 Basis := pairOrbit p.1
def pceOrbit (p : PairController × Fin 2) : Sym2 Basis := pcOrbit p.1

theorem source_orbit_count : Fintype.card (Sym2 Basis) = 4851 := by
  rw [Sym2.card]
  norm_num [Basis, Nat.choose_two_right]

theorem pc_fiber_card_le_four (k : Sym2 Basis) :
    Fintype.card {p : PairController // pcOrbit p = k} ≤ 4 := by
  classical
  obtain ⟨⟨a,b⟩, rfl⟩ := Sym2.mk_surjective k
  let encode : {p : PairController // pcOrbit p = s(a,b)} → Bool × Fin 2 :=
    fun p => (decide (p.val.1 = (a,b)), p.val.2)
  have orientation (x : {p : PairController // pcOrbit p = s(a,b)}) :
      x.val.1 = (a,b) ∨ x.val.1 = (b,a) := by
    have same := x.property
    change s(x.val.1.1,x.val.1.2) = s(a,b) at same
    exact Sym2.mk_eq_mk_iff.mp same
  have injective : Function.Injective encode := by
    intro x y same
    have flag : decide (x.val.1 = (a,b)) = decide (y.val.1 = (a,b)) :=
      congrArg Prod.fst same
    have controller : x.val.2 = y.val.2 :=
      congrArg (fun p : Bool × Fin 2 => p.2) same
    apply Subtype.ext
    apply Prod.ext _ controller
    by_cases hx : x.val.1 = (a,b)
    · have hy : y.val.1 = (a,b) := by
        by_contra outside
        simp [hx, outside] at flag
      exact hx.trans hy.symm
    · have hy : y.val.1 ≠ (a,b) := by
        intro inside
        simp [hx, inside] at flag
      exact ((orientation x).resolve_left hx).trans ((orientation y).resolve_left hy).symm
  convert Fintype.card_le_of_injective encode injective using 1 <;> simp
  exact Fintype.card_congr (Equiv.refl _)

theorem pce_fiber_card_le_eight (k : Sym2 Basis) :
    Fintype.card {p : PairController × Fin 2 // pceOrbit p = k} ≤ 8 := by
  let equivalence : {p : PairController × Fin 2 // pceOrbit p = k} ≃
      {p : PairController // pcOrbit p = k} × Fin 2 :=
    { toFun := fun p => (⟨p.val.1,p.property⟩,p.val.2)
      invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr equivalence, Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_right 2 (pc_fiber_card_le_four k)

theorem swap_preserves_pair : Preserves pairOrbit (swapOperator : JointMatrix Basis) := by
  intro ⟨i,a⟩ ⟨j,b⟩ separated
  have entry := swap_mul_apply (1 : JointMatrix Basis) i a j b
  rw [Matrix.mul_one] at entry
  rw [entry]
  have distinct : (a,i) ≠ (j,b) := by
    intro equal
    apply separated
    exact (Sym2.eq_swap : s(i,a) = s(a,i)).trans (congrArg pairOrbit equal)
  simp [distinct]

theorem diagonal_left_preserves (d : Basis → ℂ) :
    Preserves pairOrbit (Matrix.kronecker (Matrix.diagonal d) (1 : Matrix Basis Basis ℂ)) := by
  simpa only [Function.comp_def, id_eq] using
    preserves_relabel (preserves_tensor (preserves_diagonal id d)
      (preserves_one (id : Basis → Basis))) pairOrbit

theorem diagonal_right_preserves (d : Basis → ℂ) :
    Preserves pairOrbit (Matrix.kronecker (1 : Matrix Basis Basis ℂ) (Matrix.diagonal d)) := by
  simpa only [Function.comp_def, id_eq] using
    preserves_relabel (preserves_tensor (preserves_one (id : Basis → Basis))
      (preserves_diagonal id d)) pairOrbit

theorem pair_hamiltonian_preserves (d : Basis → ℂ) (g : ℝ) :
    Preserves pairOrbit (Dynamics.pairH (Matrix.diagonal d) g) :=
  preserves_add (preserves_add (diagonal_left_preserves d) (diagonal_right_preserves d))
    (preserves_smul swap_preserves_pair (g : ℂ))

theorem raising_preserves (d : Basis → ℂ) :
    Preserves pairOrbit (Powered.Source.raising (Matrix.diagonal d)) := by
  have difference : Preserves pairOrbit (Powered.Source.difference (Matrix.diagonal d)) :=
    preserves_sub (diagonal_left_preserves d) (diagonal_right_preserves d)
  exact preserves_smul (preserves_add difference (preserves_mul swap_preserves_pair difference))
    (1/2 : ℂ)

theorem interaction_preserves (d : Basis → ℂ) :
    Preserves pcOrbit (Powered.Source.interaction (Matrix.diagonal d)) := by
  have transfer : Preserves pcOrbit (Powered.Source.transfer (Matrix.diagonal d)) :=
    preserves_tensor_left (raising_preserves d) Powered.Source.lowering
  exact preserves_add transfer (preserves_star transfer)

theorem source_hpc_preserves : Preserves pcOrbit Powered.Producer.poweredTotalHamiltonian := by
  have pair : Preserves pairOrbit Work.Drive.fieldBaseline :=
    pair_hamiltonian_preserves (fun i => (Preparation.sourceEnergies i : ℂ))
      LAlanine40K2025.Thermal.Source.pairCoupling
  have interaction : Preserves pcOrbit Powered.Source.sourceInteraction :=
    interaction_preserves (fun i => (Preparation.sourceEnergies i : ℂ))
  exact preserves_add
    (preserves_add (preserves_tensor_left pair 1)
      (preserves_tensor_left (preserves_one pairOrbit) (Powered.Dynamics.controllerHamiltonian 2)))
    interaction

theorem source_load_interaction_preserves : Preserves pceOrbit Load.Source.loadInteraction := by
  intro i j separated
  have distinct : i.1.1 ≠ j.1.1 := fun same => separated (congrArg pairOrbit same)
  change (1 : Matrix Pair Pair ℂ) i.1.1 j.1.1 *
    Load.Source.controllerEnvironmentExchange (i.1.2,i.2) (j.1.2,j.2) = 0
  simp [distinct]

theorem source_load_preserves : Preserves pceOrbit Load.Source.loadTotalHamiltonian :=
  preserves_add
    (preserves_add (preserves_tensor_left source_hpc_preserves 1)
      (preserves_tensor_left (preserves_one pcOrbit) (Powered.Dynamics.controllerHamiltonian 2)))
    source_load_interaction_preserves

theorem source_free_pc_preserves (time : ℝ) :
    Preserves pcOrbit (Native.freePCUnitary time : Matrix PairController PairController ℂ) := by
  unfold Native.freePCUnitary
  rw [Load.Producer.StrictThermal.flowUnitary_matrix_exp]
  exact preserves_exp (preserves_smul (preserves_smul source_hpc_preserves (-Complex.I)) time)

theorem source_load_flow_preserves (time : ℝ) :
    Preserves pceOrbit (Load.Source.loadUnitary time : LoadedJoint) := by
  unfold Load.Source.loadUnitary
  rw [Load.Producer.StrictThermal.flowUnitary_matrix_exp]
  exact preserves_exp (preserves_smul (preserves_smul source_load_preserves (-Complex.I)) time)

theorem source_recovery_pc_preserves (time : ℝ) :
    Preserves pcOrbit (Load.Recovery.Control.minimalPCUnitary time : Matrix PairController PairController ℂ) := by
  have pair : Preserves pairOrbit Work.Drive.fieldBaseline :=
    pair_hamiltonian_preserves (fun i => (Preparation.sourceEnergies i : ℂ))
      LAlanine40K2025.Thermal.Source.pairCoupling
  have interaction : Preserves pcOrbit (-Powered.Source.sourceInteraction) :=
    preserves_neg (interaction_preserves (fun i => (Preparation.sourceEnergies i : ℂ)))
  have controlled : Preserves pcOrbit Recovery.Producer.recoveryHamiltonian :=
    preserves_add
      (preserves_add (preserves_tensor_left pair 1)
        (preserves_tensor_left (preserves_one pairOrbit) (Powered.Dynamics.controllerHamiltonian 2)))
      interaction
  unfold Load.Recovery.Control.minimalPCUnitary
  rw [Load.Producer.StrictThermal.flowUnitary_matrix_exp]
  exact preserves_exp (preserves_smul (preserves_smul controlled (-Complex.I)) time)

theorem source_load_block_exp (time : ℝ) (k : Sym2 Basis) :
    restrict pceOrbit k (Load.Source.loadUnitary time : LoadedJoint) =
      NormedSpace.exp (time • (-Complex.I • restrict pceOrbit k Load.Source.loadTotalHamiltonian)) := by
  unfold Load.Source.loadUnitary
  rw [Load.Producer.StrictThermal.flowUnitary_matrix_exp]
  change restrict pceOrbit k (NormedSpace.exp (time • (-Complex.I • Load.Source.loadTotalHamiltonian))) = _
  rw [restrict_exp (preserves_smul (preserves_smul source_load_preserves (-Complex.I)) time)]
  rfl

theorem source_load_block_evolution (time : ℝ) (rho : LoadedJoint) (k : Sym2 Basis) :
    restrict pceOrbit k (Load.Source.loadAdvance time rho) =
      NormedSpace.exp (time • (-Complex.I • restrict pceOrbit k Load.Source.loadTotalHamiltonian)) *
        restrict pceOrbit k rho *
        (NormedSpace.exp (time • (-Complex.I • restrict pceOrbit k Load.Source.loadTotalHamiltonian)))ᴴ := by
  change restrict pceOrbit k (Quantum.conjugation (Load.Source.loadUnitary time) rho) = _
  rw [restrict_conjugation _ (source_load_flow_preserves time), source_load_block_exp]

theorem recovery_source_block_evolution (current : Load.Producer.LoadState) (k : Sym2 Basis) :
    restrict pceOrbit k (Recovery.Producer.recoveryStep current).joint =
      restrict pceOrbit k
        (Load.Quantum.localUnitary
          (Load.Recovery.Control.minimalPCUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ)))
          (Load.Recovery.Control.environmentUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ))) : LoadedJoint) *
        restrict pceOrbit k current.joint *
        (restrict pceOrbit k
          (Load.Quantum.localUnitary
            (Load.Recovery.Control.minimalPCUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ)))
            (Load.Recovery.Control.environmentUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ))) : LoadedJoint))ᴴ := by
  rw [Recovery.Producer.recoveryStep_joint]
  apply restrict_conjugation
  exact preserves_tensor_left (source_recovery_pc_preserves _) _

end SourceOrbit

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
