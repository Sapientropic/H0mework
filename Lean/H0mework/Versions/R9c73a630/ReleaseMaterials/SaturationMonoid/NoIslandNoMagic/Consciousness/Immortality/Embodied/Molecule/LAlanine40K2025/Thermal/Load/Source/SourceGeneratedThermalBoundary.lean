import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalLoad.GeneratedControllerEnvironment

/-! # The complete PC, environment, and interaction energy ledger -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Source

open scoped Matrix ComplexOrder

noncomputable section

def pcEnergy (current : LoadedJoint) : ℝ :=
  Powered.Dynamics.systemEnergy Powered.Producer.poweredTotalHamiltonian current

def environmentEnergy (current : LoadedJoint) : ℝ := Powered.Dynamics.controllerEnergy 2 current

def boundaryEnergy (current : LoadedJoint) : ℝ := Collision.energy loadInteraction current

theorem totalEnergy_split_generic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (gap : ℝ) (V current : Powered.Dynamics.ControllerJoint ι) :
    Collision.energy (Powered.Dynamics.totalHamiltonian H gap V) current =
      Powered.Dynamics.systemEnergy H current + Powered.Dynamics.controllerEnergy gap current + Collision.energy V current := by
  calc
    _ = Collision.energy (Powered.Dynamics.bareHamiltonian H gap) current + Collision.energy V current := by
      simp only [Powered.Dynamics.totalHamiltonian, Collision.energy, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    _ = _ := congrArg (fun e => e + Collision.energy V current) (Powered.Dynamics.bareEnergy_split H gap current)

theorem totalEnergy_split (current : LoadedJoint) :
    Collision.energy loadTotalHamiltonian current = pcEnergy current + environmentEnergy current + boundaryEnergy current :=
  totalEnergy_split_generic Powered.Producer.poweredTotalHamiltonian 2 loadInteraction current

theorem loadAdvance_energyBalance (elapsed : ℝ) (current : LoadedJoint) :
    (pcEnergy (loadAdvance elapsed current) - pcEnergy current) +
      (environmentEnergy (loadAdvance elapsed current) - environmentEnergy current) +
      (boundaryEnergy (loadAdvance elapsed current) - boundaryEnergy current) = 0 := by
  have total := Powered.Dynamics.totalEnergy_conserved Powered.Producer.poweredTotalHamiltonian 2 loadInteraction
    Powered.Producer.poweredTotalHamiltonian_hermitian loadInteraction_hermitian elapsed current
  change Collision.energy loadTotalHamiltonian (loadAdvance elapsed current) = Collision.energy loadTotalHamiltonian current at total
  rw [totalEnergy_split, totalEnergy_split] at total
  linarith

theorem loadBoundary_initial_zero_generic {P : Type*} [Fintype P] [DecidableEq P]
    (rho : Matrix (P × Fin 2) (P × Fin 2) ℂ) (weights : Fin 2 → ℂ) :
    Collision.energy ((Matrix.kronecker (1 : Matrix P P ℂ) controllerEnvironmentExchange).submatrix
      (Equiv.prodAssoc P (Fin 2) (Fin 2)) (Equiv.prodAssoc P (Fin 2) (Fin 2)))
      (Matrix.kronecker rho (Matrix.diagonal weights)) = 0 := by
  let coupling := (Matrix.kronecker (1 : Matrix P P ℂ) controllerEnvironmentExchange).submatrix
    (Equiv.prodAssoc P (Fin 2) (Fin 2)) (Equiv.prodAssoc P (Fin 2) (Fin 2))
  have zero (i j : (P × Fin 2) × Fin 2) :
      coupling i j * Matrix.kronecker rho (Matrix.diagonal weights) j i = 0 := by
    rcases i with ⟨⟨p, c⟩, e⟩
    rcases j with ⟨⟨q, d⟩, f⟩
    fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
      simp [coupling, Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
        controllerEnvironmentExchange]
  change Collision.energy coupling (Matrix.kronecker rho (Matrix.diagonal weights)) = 0
  simp only [Collision.energy, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    zero, Finset.sum_const_zero, Complex.zero_re]

theorem loadBoundary_initial_zero (rho : Matrix PairController PairController ℂ) :
    boundaryEnergy (Matrix.kronecker rho environmentState) = 0 :=
  loadBoundary_initial_zero_generic rho _


end

end LAlanine40K2025.Thermal.Load.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
