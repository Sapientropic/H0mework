import H0mework.Realization.Perfectification.Quantum.Forms.Graph

/-! One actual closed dense derivative graph generates a self-adjoint
nonnegative Hamiltonian. Its full operator domain lies in the original
derivative domain and represents exactly that graph's quadratic form. -/

set_option autoImplicit false

open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.Quantum.Forms

noncomputable section

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (dense : Dense (A.domain : Set H))

def hamiltonian : H →ₗ.[ℂ] H :=
  Inverse.operator (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense)

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian A closed dense) :=
  Inverse.operator_selfAdjoint _ _ (Graph.resolvent_selfAdjoint A closed)

theorem hamiltonian_closed : (hamiltonian A closed dense).IsClosed :=
  (hamiltonian_selfAdjoint A closed dense).isClosed

theorem hamiltonian_domain_dense : Dense ((hamiltonian A closed dense).domain : Set H) :=
  (hamiltonian_selfAdjoint A closed dense).dense_domain

def derivativePoint (f : (hamiltonian A closed dense).domain) : A.domain :=
  Graph.solution A closed (Inverse.preimage (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense) f)

theorem derivativePoint_val (f : (hamiltonian A closed dense).domain) :
    (derivativePoint A closed dense f).val = f.val := Inverse.preimage_apply _ _ f

theorem hamiltonian_form (f : (hamiltonian A closed dense).domain) (g : A.domain) :
    inner ℂ (hamiltonian A closed dense f) g.val =
      inner ℂ (A (derivativePoint A closed dense f)) (A g) := by
  have relation := Graph.variational A closed
    (Inverse.preimage (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense) f) g
  have same : Graph.resolvent A closed
      (Inverse.preimage (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense) f) = f.val :=
    Inverse.preimage_apply _ _ f
  rw [same] at relation
  exact relation

theorem hamiltonian_energy (f : (hamiltonian A closed dense).domain) :
    (inner ℂ (hamiltonian A closed dense f) f.val).re = ‖A (derivativePoint A closed dense f)‖ ^ 2 := by
  have form := congrArg Complex.re (hamiltonian_form A closed dense f (derivativePoint A closed dense f))
  rw [derivativePoint_val] at form
  exact form.trans (inner_self_eq_norm_sq (𝕜 := ℂ) _)

theorem hamiltonian_nonnegative (f : (hamiltonian A closed dense).domain) :
    0 ≤ (inner ℂ (hamiltonian A closed dense f) f.val).re := by
  rw [hamiltonian_energy]
  exact sq_nonneg _

def resolventPoint (x : H) : (hamiltonian A closed dense).domain :=
  Inverse.point (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense) x

theorem resolvent_equation (x : H) :
    hamiltonian A closed dense (resolventPoint A closed dense x) + Graph.resolvent A closed x = x := by
  change Inverse.operator (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense)
    (Inverse.point (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense) x) +
      Graph.resolvent A closed x = x
  rw [Inverse.operator_point, sub_add_cancel]

end
end SaturationMonoid.Quantum.Forms
