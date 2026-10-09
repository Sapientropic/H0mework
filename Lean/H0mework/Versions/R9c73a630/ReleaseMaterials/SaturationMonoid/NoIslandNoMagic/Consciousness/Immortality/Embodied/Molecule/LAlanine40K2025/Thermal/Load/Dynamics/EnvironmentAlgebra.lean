import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalLoad.GeneratedControllerEnvironment

/-! # Environment exchange algebra and its initial heat jet -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace StrictThermal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem trace_energy_commutator (H O rho : Matrix ι ι ℂ) :
    (O * (H * rho - rho * H)).trace = ((O * H - H * O) * rho).trace := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, ← Matrix.mul_assoc]
  congr 1
  exact Matrix.trace_mul_cycle O rho H

variable {P : Type*} [Fintype P] [DecidableEq P]

def ceLift (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix ((P × Fin 2) × Fin 2) ((P × Fin 2) × Fin 2) ℂ :=
  (Matrix.kronecker (1 : Matrix P P ℂ) A).submatrix
    (Equiv.prodAssoc P (Fin 2) (Fin 2)) (Equiv.prodAssoc P (Fin 2) (Fin 2))

theorem ceLift_mul (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ceLift (P := P) (A * B) = ceLift A * ceLift B := by
  simp only [ceLift, Matrix.submatrix_mul_equiv, Matrix.kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

omit [Fintype P] in
theorem ceLift_sub (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ceLift (P := P) (A - B) = ceLift A - ceLift B := by
  ext i j
  simp [ceLift, Matrix.kronecker, Matrix.kroneckerMap_apply, mul_sub]

def ceEnvironmentEnergy : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (controllerHamiltonian 2)

def ceControllerEnergy : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (controllerHamiltonian 2) (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem ceExchange_doubleCommutator :
    -(controllerEnvironmentExchange *
      (controllerEnvironmentExchange * ceEnvironmentEnergy -
        ceEnvironmentEnergy * controllerEnvironmentExchange) -
      (controllerEnvironmentExchange * ceEnvironmentEnergy -
        ceEnvironmentEnergy * controllerEnvironmentExchange) * controllerEnvironmentExchange) =
      (2 : ℂ) • (ceControllerEnergy - ceEnvironmentEnergy) := by
  ext ⟨c, e⟩ ⟨d, f⟩
  fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
    norm_num [controllerEnvironmentExchange, ceEnvironmentEnergy, ceControllerEnergy,
      controllerHamiltonian, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply]

omit [Fintype P] in
theorem ceLift_smul (z : ℂ) (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ceLift (P := P) (z • A) = z • ceLift A := by
  ext i j
  simp [ceLift, Matrix.kronecker, Matrix.kroneckerMap_apply, mul_left_comm]

omit [Fintype P] in
theorem ceLift_environment :
    ceLift (P := P) ceEnvironmentEnergy =
      Matrix.kronecker (1 : Matrix (P × Fin 2) (P × Fin 2) ℂ) (controllerHamiltonian 2) := by
  ext ⟨⟨p, c⟩, e⟩ ⟨⟨q, d⟩, f⟩
  simp [ceLift, ceEnvironmentEnergy, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

def environmentObservable : ControllerJoint (P × Fin 2) :=
  Matrix.kronecker 1 (controllerHamiltonian 2)

def environmentCommutator : ControllerJoint (P × Fin 2) :=
  ceLift controllerEnvironmentExchange * environmentObservable -
    environmentObservable * ceLift controllerEnvironmentExchange

def environmentOffdiagonal (A : ControllerJoint (P × Fin 2)) : Prop :=
  ∀ x y e, A (x, e) (y, e) = 0

omit [DecidableEq P] in
theorem offdiagonal_trace_zero (A : ControllerJoint (P × Fin 2))
    (offdiagonal : environmentOffdiagonal A)
    (rho : Matrix (P × Fin 2) (P × Fin 2) ℂ) (weights : Fin 2 → ℂ) :
    (A * Matrix.kronecker rho (Matrix.diagonal weights)).trace = 0 := by
  have zero (i j : (P × Fin 2) × Fin 2) :
      A i j * Matrix.kronecker rho (Matrix.diagonal weights) j i = 0 := by
    rcases i with ⟨x, e⟩
    rcases j with ⟨y, f⟩
    by_cases same : f = e
    · subst f
      simp [offdiagonal x y e]
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, same]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, zero, Finset.sum_const_zero]

theorem environmentCommutator_offdiagonal :
    environmentOffdiagonal (environmentCommutator (P := P)) := by
  have small : ∀ c d e,
      (controllerEnvironmentExchange * ceEnvironmentEnergy -
        ceEnvironmentEnergy * controllerEnvironmentExchange) (c, e) (d, e) = 0 := by
    intro c d e
    fin_cases c <;> fin_cases d <;> fin_cases e <;>
      norm_num [controllerEnvironmentExchange, ceEnvironmentEnergy, controllerHamiltonian,
        Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply]
  have same : environmentCommutator (P := P) = ceLift
      (controllerEnvironmentExchange * ceEnvironmentEnergy -
        ceEnvironmentEnergy * controllerEnvironmentExchange) := by
    rw [ceLift_sub, ceLift_mul, ceLift_mul, ceLift_environment]
    rfl
  intro ⟨p, c⟩ ⟨q, d⟩ e
  rw [same]
  simp [ceLift, Matrix.kronecker, Matrix.kroneckerMap_apply, small]

theorem bare_environment_commute (H : Matrix (P × Fin 2) (P × Fin 2) ℂ) :
    Commute (bareHamiltonian H 2) (environmentObservable (P := P)) := by
  show _ * _ = _ * _
  simp only [bareHamiltonian, environmentObservable, add_mul, mul_add, Matrix.kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem total_environment_commutator (H : Matrix (P × Fin 2) (P × Fin 2) ℂ) :
    totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) * environmentObservable -
      environmentObservable * totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) =
      environmentCommutator (P := P) := by
  simp only [totalHamiltonian, add_mul, mul_add, (bare_environment_commute H).eq,
    environmentCommutator]
  abel

theorem bare_mul_offdiagonal (H : Matrix (P × Fin 2) (P × Fin 2) ℂ)
    (A : ControllerJoint (P × Fin 2)) (offdiagonal : environmentOffdiagonal A) :
    environmentOffdiagonal (bareHamiltonian H 2 * A) := by
  change ∀ x y e, A (x, e) (y, e) = 0 at offdiagonal
  intro x y e
  fin_cases e <;>
  simp [bareHamiltonian, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, controllerHamiltonian, Matrix.one_apply, offdiagonal]

theorem offdiagonal_mul_bare (H : Matrix (P × Fin 2) (P × Fin 2) ℂ)
    (A : ControllerJoint (P × Fin 2)) (offdiagonal : environmentOffdiagonal A) :
    environmentOffdiagonal (A * bareHamiltonian H 2) := by
  change ∀ x y e, A (x, e) (y, e) = 0 at offdiagonal
  intro x y e
  fin_cases e <;>
  simp [bareHamiltonian, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, controllerHamiltonian, Matrix.one_apply, offdiagonal]

theorem initial_heat_tangent_zero (H rho : Matrix (P × Fin 2) (P × Fin 2) ℂ)
    (weights : Fin 2 → ℂ) :
    Collision.energy (environmentObservable (P := P))
      (-Complex.I •
        (totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) *
            Matrix.kronecker rho (Matrix.diagonal weights) -
          Matrix.kronecker rho (Matrix.diagonal weights) *
            totalHamiltonian H 2 (ceLift controllerEnvironmentExchange))) = 0 := by
  have commutator := total_environment_commutator H
  have reversed : environmentObservable * totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) -
      totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) * environmentObservable =
        -environmentCommutator (P := P) := by rw [← commutator]; abel
  simp only [Collision.energy, mul_smul_comm, Matrix.trace_smul, smul_eq_mul,
    trace_energy_commutator, reversed, Matrix.neg_mul, Matrix.trace_neg,
    offdiagonal_trace_zero _ environmentCommutator_offdiagonal, neg_zero, mul_zero, Complex.zero_re]

theorem initial_heat_doubleCommutator (H rho : Matrix (P × Fin 2) (P × Fin 2) ℂ)
    (weights : Fin 2 → ℂ) :
    ((-(totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) * environmentCommutator -
      environmentCommutator * totalHamiltonian H 2 (ceLift controllerEnvironmentExchange))) *
        Matrix.kronecker rho (Matrix.diagonal weights)).trace =
    ((ceLift (P := P) ((2 : ℂ) • (ceControllerEnergy - ceEnvironmentEnergy))) *
      Matrix.kronecker rho (Matrix.diagonal weights)).trace := by
  have leftZero := offdiagonal_trace_zero _
    (bare_mul_offdiagonal H environmentCommutator environmentCommutator_offdiagonal) rho weights
  have rightZero := offdiagonal_trace_zero _
    (offdiagonal_mul_bare H environmentCommutator environmentCommutator_offdiagonal) rho weights
  have exchange : -(ceLift (P := P) controllerEnvironmentExchange * environmentCommutator -
      environmentCommutator * ceLift controllerEnvironmentExchange) =
        ceLift ((2 : ℂ) • (ceControllerEnergy - ceEnvironmentEnergy)) := by
    rw [← ceExchange_doubleCommutator]
    have liftNeg (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
        ceLift (P := P) (-A) = -ceLift A := by
      simpa only [neg_one_smul] using ceLift_smul (P := P) (-1) A
    rw [liftNeg, ceLift_sub, ceLift_mul, ceLift_mul, ceLift_sub,
      ceLift_mul, ceLift_mul, ceLift_environment]
    rfl
  rw [← exchange]
  simp only [totalHamiltonian, add_mul, mul_add, sub_mul, neg_mul,
    Matrix.trace_neg, Matrix.trace_sub, Matrix.trace_add, leftZero, rightZero]
  ring

omit [Fintype P] in
theorem ceLift_controller :
    ceLift (P := P) ceControllerEnergy =
      Matrix.kronecker (Matrix.kronecker (1 : Matrix P P ℂ) (controllerHamiltonian 2))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext ⟨⟨p, c⟩, e⟩ ⟨⟨q, d⟩, f⟩
  simp [ceLift, ceControllerEnergy, Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]

theorem environmentObservable_energy (rho : ControllerJoint ι) :
    Collision.energy (Matrix.kronecker (1 : Matrix ι ι ℂ) (controllerHamiltonian 2)) rho =
      controllerEnergy 2 rho := by
  have read := jointEnergy_real_eq_reduced (0 : Matrix ι ι ℂ) (controllerHamiltonian 2) rho
  simpa [Matrix.kronecker, Collision.energy, controllerEnergy] using read

theorem curvature_energy_read (rho : Matrix (P × Fin 2) (P × Fin 2) ℂ)
    (tau : Matrix (Fin 2) (Fin 2) ℂ) (normalized : tau.trace = 1) :
    Collision.energy (ceLift (P := P) ((2 : ℂ) • (ceControllerEnergy - ceEnvironmentEnergy)))
      (Matrix.kronecker rho tau) =
    2 * (controllerEnergy 2 rho - controllerEnergy 2 (Matrix.kronecker rho tau)) := by
  have system : Collision.energy (ceLift (P := P) ceControllerEnergy) (Matrix.kronecker rho tau) =
      controllerEnergy 2 rho := by
    rw [ceLift_controller]
    unfold Collision.energy
    simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.trace_kronecker, normalized, mul_one]
    exact environmentObservable_energy rho
  calc
    _ = 2 * (Collision.energy (ceLift ceControllerEnergy) (Matrix.kronecker rho tau) -
        Collision.energy (ceLift ceEnvironmentEnergy) (Matrix.kronecker rho tau)) := by
      rw [ceLift_smul, ceLift_sub]
      simp [Collision.energy, Matrix.sub_mul, Matrix.trace_sub, Complex.mul_re]
    _ = _ := by rw [system, ceLift_environment, environmentObservable_energy]

omit [DecidableEq ι] in
theorem trace_doubleTangent (H O rho : Matrix ι ι ℂ) :
    (O * (-Complex.I • (H * (-Complex.I • (H * rho - rho * H)) -
      (-Complex.I • (H * rho - rho * H)) * H))).trace =
    ((-(H * (H * O - O * H) - (H * O - O * H) * H)) * rho).trace := by
  simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul,
    neg_mul_neg, Complex.I_mul_I, neg_one_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg]
  rw [trace_energy_commutator, trace_energy_commutator]
  congr 1
  congr 1
  noncomm_ring

theorem initial_heat_curvature_read (H rho : Matrix (P × Fin 2) (P × Fin 2) ℂ)
    (weights : Fin 2 → ℂ) (normalized : (Matrix.diagonal weights).trace = 1) :
    Collision.energy (environmentObservable (P := P))
      (-Complex.I •
        (totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) *
            (-Complex.I • (totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) *
              Matrix.kronecker rho (Matrix.diagonal weights) -
                Matrix.kronecker rho (Matrix.diagonal weights) *
                  totalHamiltonian H 2 (ceLift controllerEnvironmentExchange))) -
          (-Complex.I • (totalHamiltonian H 2 (ceLift controllerEnvironmentExchange) *
            Matrix.kronecker rho (Matrix.diagonal weights) -
              Matrix.kronecker rho (Matrix.diagonal weights) *
                totalHamiltonian H 2 (ceLift controllerEnvironmentExchange))) *
            totalHamiltonian H 2 (ceLift controllerEnvironmentExchange))) =
      2 * (controllerEnergy 2 rho -
        controllerEnergy 2 (Matrix.kronecker rho (Matrix.diagonal weights))) := by
  unfold Collision.energy
  rw [trace_doubleTangent, total_environment_commutator, initial_heat_doubleCommutator]
  exact curvature_energy_read rho (Matrix.diagonal weights) normalized

end StrictThermal

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
