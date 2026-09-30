import H0mework.Physics.LowEnergy.FullQuantum.HistoryLaplace.Stationary

/-! Weak solutions generate membership in the actual free-generator domain; its symmetry gives uniqueness. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
open FullSpace GaugeGreen GaugeHistory
noncomputable section

theorem weak_free_kernel_zero (energy damping : ℝ) (positive : 0<damping) (field : FullMatterL2)
    (weak : ∀ test : Quantum.Generator.domain freeAction,
      ((energy : ℂ)+Complex.I*(damping : ℂ))*inner ℂ (test : FullMatterL2) field-
        inner ℂ (Quantum.Generator.hamiltonian freeAction test) field=0) : field=0 := by
  let z : ℂ := (energy : ℂ)+Complex.I*(damping : ℂ)
  have derivative : HasDerivAt (Quantum.Generator.orbit freeAction field) ((-Complex.I*z) • field) 0 := by
    apply Quantum.Generator.orbit_hasDerivAt_of_weak freeAction freeAction_continuous
    intro test
    have equation := (sub_eq_zero.mp (weak test)).symm
    change inner ℂ (Complex.I • Quantum.Generator.generator freeAction test) field=
      z*inner ℂ (test : FullMatterL2) field at equation
    rw [inner_smul_left,Complex.conj_I] at equation
    rw [inner_smul_right]
    calc
      _ = Complex.I*((-Complex.I)*inner ℂ (Quantum.Generator.generator freeAction test) field) := by
        rw [← mul_assoc]
        simp
      _ = Complex.I*(z*inner ℂ (test : FullMatterL2) field) := congrArg (fun c : ℂ => Complex.I*c) equation
      _ = _ := by ring
  let point : Quantum.Generator.domain freeAction := ⟨field,derivative.differentiableAt⟩
  have value : Quantum.Generator.hamiltonian freeAction point=z • field := by
    change Complex.I • deriv (Quantum.Generator.orbit freeAction field) 0=_
    rw [derivative.deriv,smul_smul]
    rw [← mul_assoc]
    simp
  have symmetry := Quantum.Generator.hamiltonian_symmetric freeAction point point
  change inner ℂ (Quantum.Generator.hamiltonian freeAction point) field=
    inner ℂ field (Quantum.Generator.hamiltonian freeAction point) at symmetry
  rw [value,inner_smul_left,inner_smul_right,inner_self_eq_norm_sq_to_K] at symmetry
  have imaginary := congrArg Complex.im symmetry
  simp [z,Complex.mul_re,Complex.mul_im,pow_two] at imaginary
  have product : damping*(‖field‖*‖field‖)=0 := by linarith
  have square := (mul_eq_zero.mp product).resolve_left (ne_of_gt positive)
  have vanished : ‖field‖=0 := (mul_eq_zero.mp square).elim id id
  exact norm_eq_zero.mp vanished

theorem weak_free_unique (energy damping : ℝ) (positive : 0<damping)
    (left right : FullMatterL2)
    (same : ∀ test : Quantum.Generator.domain freeAction,
      ((energy : ℂ)+Complex.I*(damping : ℂ))*inner ℂ (test : FullMatterL2) left-
        inner ℂ (Quantum.Generator.hamiltonian freeAction test) left=
      ((energy : ℂ)+Complex.I*(damping : ℂ))*inner ℂ (test : FullMatterL2) right-
        inner ℂ (Quantum.Generator.hamiltonian freeAction test) right) : left=right := by
  apply sub_eq_zero.mp
  apply weak_free_kernel_zero energy damping positive (left-right)
  intro test
  simp only [inner_sub_right]
  linear_combination same test

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
