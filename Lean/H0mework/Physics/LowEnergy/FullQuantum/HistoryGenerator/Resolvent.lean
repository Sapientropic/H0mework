import H0mework.Physics.LowEnergy.FullQuantum.HistoryGreen.Domain

/-! The actual source weak equation generates the complete free-generator domain and its value. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGenerator
open FullSpace GaugeGreen GaugeHistory HistoryGreen
noncomputable section

theorem weak_free_derivative (energy damping : ℝ) (field source : FullMatterL2)
    (weak : ∀ test : Quantum.Generator.domain freeAction,
      ((energy : ℂ)+Complex.I*(damping : ℂ))*inner ℂ (test : FullMatterL2) field-
        inner ℂ (Quantum.Generator.hamiltonian freeAction test) field=inner ℂ (test : FullMatterL2) source) :
    HasDerivAt (Quantum.Generator.orbit freeAction field)
      (-Complex.I • (((energy : ℂ)+Complex.I*(damping : ℂ)) • field-source)) 0 := by
  apply Quantum.Generator.orbit_hasDerivAt_of_weak freeAction freeAction_continuous
  intro test
  have paired : inner ℂ (Complex.I • Quantum.Generator.generator freeAction test) field=
      inner ℂ (test : FullMatterL2) (((energy : ℂ)+Complex.I*(damping : ℂ)) • field-source) := by
    simp only [inner_sub_right,inner_smul_right]
    change inner ℂ (Quantum.Generator.hamiltonian freeAction test) field=_
    linear_combination -(weak test)
  rw [inner_smul_left,Complex.conj_I] at paired
  rw [inner_smul_right]
  calc
    _ = Complex.I*((-Complex.I)*inner ℂ (Quantum.Generator.generator freeAction test) field) := by
      rw [← mul_assoc]
      simp
    _ = Complex.I*inner ℂ (test : FullMatterL2)
        (((energy : ℂ)+Complex.I*(damping : ℂ)) • field-source) := congrArg (fun c : ℂ => Complex.I*c) paired
    _ = _ := by ring

theorem freeR_generator_domain (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    freeR 0 energy damping positive source ∈ Quantum.Generator.domain freeAction :=
  (weak_free_derivative energy damping _ source
    (fun test => freeR_weak energy damping positive test source)).differentiableAt

theorem freeR_generator_value (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    Quantum.Generator.hamiltonian freeAction
      ⟨freeR 0 energy damping positive source,freeR_generator_domain energy damping positive source⟩=
      ((energy : ℂ)+Complex.I*(damping : ℂ)) • freeR 0 energy damping positive source-source := by
  change Complex.I • deriv (Quantum.Generator.orbit freeAction (freeR 0 energy damping positive source)) 0=_
  rw [(weak_free_derivative energy damping _ source
    (fun test => freeR_weak energy damping positive test source)).deriv,smul_smul]
  simp

theorem generator_resolvent_recovers (energy damping : ℝ) (positive : 0<damping)
    (field : Quantum.Generator.domain freeAction) :
    (field : FullMatterL2)=freeR 0 energy damping positive
      (((energy : ℂ)+Complex.I*(damping : ℂ)) • (field : FullMatterL2)-Quantum.Generator.hamiltonian freeAction field) := by
  apply weak_free_unique energy damping positive
  intro test
  rw [freeR_weak,inner_sub_right,inner_smul_right,
    Quantum.Generator.hamiltonian_symmetric freeAction test field]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGenerator
