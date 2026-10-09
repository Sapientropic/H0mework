import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Producer.SourceRaisingMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.ControllerVacancy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.VacancyAlgebra

open Collision Powered.Dynamics Load.Producer.HeatProbability
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Q_disjoint : Q (ι := ι) 0 * Q 1 = 0 := by
  rw [Q, Q, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases same : i = j
  · subst j
    rcases i with ⟨i, c⟩
    fin_cases c <;> simp
  · simp [Matrix.diagonal_apply_ne _ same]

theorem Q_charged_support (rho : Matrix ι ι ℂ) :
    Q 1 * chargedInput rho = chargedInput rho ∧ chargedInput rho * Q 1 = chargedInput rho := by
  constructor <;> ext ⟨i, c⟩ ⟨j, d⟩ <;> fin_cases c <;> fin_cases d <;>
    simp [Q, chargedInput, excitedController, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.kronecker, Matrix.kroneckerMap_apply]

theorem Q_receives_interaction (H : SystemMatrix ι) :
    Q 0 * Powered.Source.interaction H * Q 1 = Powered.Source.interaction H * Q 1 := by
  ext ⟨i, c⟩ ⟨j, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Q, Matrix.diagonal_mul, Matrix.mul_diagonal, Powered.Source.interaction,
      Powered.Source.transfer, Powered.Source.lowering, Matrix.conjTranspose_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply]

theorem lowering_products :
    Powered.Source.lowering * Powered.Source.lowering = 0 ∧
    Powered.Source.loweringᴴ * Powered.Source.lowering = excitedController ∧
    Powered.Source.lowering * Powered.Source.loweringᴴ * excitedController = 0 ∧
    excitedController * excitedController = excitedController := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Powered.Source.lowering, excitedController, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

theorem interaction_squared (H : SystemMatrix ι) :
    (Powered.Source.interaction H)ᴴ * Powered.Source.interaction H =
      Matrix.kronecker (Powered.Source.raising H * (Powered.Source.raising H)ᴴ)
        (Powered.Source.lowering * Powered.Source.loweringᴴ) +
      Matrix.kronecker ((Powered.Source.raising H)ᴴ * Powered.Source.raising H) excitedController := by
  have backward : Powered.Source.loweringᴴ * Powered.Source.loweringᴴ = 0 := by
    have adjoint := congrArg Matrix.conjTranspose lowering_products.1
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero] using adjoint
  rw [(Powered.Source.interaction_hermitian H).eq]
  simp only [Powered.Source.interaction, Powered.Source.transfer,
    Matrix.kronecker, Matrix.conjTranspose_kronecker, add_mul, mul_add,
    ← Matrix.mul_kronecker_mul, lowering_products.1, lowering_products.2.1, backward,
    Matrix.kronecker_zero, add_zero, zero_add]
  exact add_comm _ _

theorem interaction_charged_moment (H : SystemMatrix ι) (rho : JointMatrix ι) :
    energy ((Powered.Source.interaction H)ᴴ * Powered.Source.interaction H) (chargedInput rho) =
      energy (Moment.observable H) rho := by
  rw [interaction_squared]
  simp only [energy, chargedInput, Matrix.add_mul, Matrix.kronecker,
    ← Matrix.mul_kronecker_mul, lowering_products.2.2.1, lowering_products.2.2.2,
    Matrix.kronecker_zero, zero_add, Matrix.trace_kronecker, excitedController_trace,
    mul_one, Moment.observable]

theorem empty_probability (joint : ControllerJoint ι) (normalized : joint.trace = 1) :
    2 * energy (Q 0) joint + controllerEnergy 2 joint = 2 := by
  have observable : Load.Producer.StrictThermal.emptyObservable = (2 : ℂ) • Q (ι := ι) 0 := by
    ext ⟨i, c⟩ ⟨j, d⟩
    fin_cases c <;> fin_cases d <;>
      simp [Load.Producer.StrictThermal.emptyObservable, Load.Producer.StrictThermal.emptyHamiltonian,
        Q, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal_apply, Prod.mk.injEq]
  have complement := Load.Producer.StrictThermal.controller_complement joint normalized
  rw [observable] at complement
  simpa [energy, Matrix.trace_smul, Complex.mul_re] using complement

end
end LAlanine40K2025.Thermal.Recovery.VacancyAlgebra
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
