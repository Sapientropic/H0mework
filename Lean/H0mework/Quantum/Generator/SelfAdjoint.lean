import H0mework.Quantum.Generator.Weak
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The physical Hamiltonian is a partial linear operator on its actual
orbit-derivative domain. Mathlib's adjoint pairing yields a weak derivative;
the source weak-to-strong theorem forces every adjoint-domain vector back
into the original domain with the same value. This proves exact self-adjointness. -/

set_option autoImplicit false

open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.Quantum.Generator

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E))

def hamiltonianOperator : E →ₗ.[ℂ] E where
  domain := domain U
  toFun := hamiltonian U

theorem hamiltonianOperator_formalAdjoint :
    (hamiltonianOperator U).IsFormalAdjoint (hamiltonianOperator U) :=
  hamiltonian_symmetric U

variable [CompleteSpace E]
  (continuousOrbit : ∀ x, Continuous (orbit U x))

include continuousOrbit

theorem hamiltonianOperator_le_adjoint :
    hamiltonianOperator U ≤ (hamiltonianOperator U)† :=
  LinearPMap.IsFormalAdjoint.le_adjoint (domain_dense U continuousOrbit)
    (hamiltonianOperator_formalAdjoint U)

theorem adjoint_orbit_hasDerivAt (y : ((hamiltonianOperator U)†).domain) :
    HasDerivAt (orbit U (y : E)) (-Complex.I • (hamiltonianOperator U)† y) 0 := by
  apply orbit_hasDerivAt_of_weak U continuousOrbit
  intro x
  have pairing := (LinearPMap.adjoint_isFormalAdjoint
    (T := hamiltonianOperator U) (domain_dense U continuousOrbit)).symm x y
  change ⟪Complex.I • generator U x, (y : E)⟫_ℂ =
    ⟪(x : E), (hamiltonianOperator U)† y⟫_ℂ at pairing
  rw [inner_smul_left] at pairing
  rw [inner_smul_right]
  have multiplied := congrArg (fun value : ℂ => Complex.I * value) pairing
  simpa [mul_assoc, ← mul_assoc Complex.I, Complex.I_sq] using multiplied

theorem adjoint_mem_domain (y : ((hamiltonianOperator U)†).domain) :
    (y : E) ∈ domain U :=
  (adjoint_orbit_hasDerivAt U continuousOrbit y).differentiableAt

theorem hamiltonian_adjoint_value (y : ((hamiltonianOperator U)†).domain) :
    hamiltonian U ⟨(y : E), adjoint_mem_domain U continuousOrbit y⟩ =
      (hamiltonianOperator U)† y := by
  change Complex.I • deriv (orbit U (y : E)) 0 = _
  rw [(adjoint_orbit_hasDerivAt U continuousOrbit y).deriv, smul_smul]
  simp

theorem hamiltonianOperator_selfAdjoint : IsSelfAdjoint (hamiltonianOperator U) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨fun y hy => adjoint_mem_domain U continuousOrbit ⟨y, hy⟩, ?_⟩
    intro y x same
    have equality := hamiltonian_adjoint_value U continuousOrbit y
    rw [← equality]
    exact congrArg (hamiltonian U) (Subtype.ext same)
  · exact hamiltonianOperator_le_adjoint U continuousOrbit

theorem hamiltonianOperator_closed : (hamiltonianOperator U).IsClosed :=
  (hamiltonianOperator_selfAdjoint U continuousOrbit).isClosed

end
end SaturationMonoid.Quantum.Generator
