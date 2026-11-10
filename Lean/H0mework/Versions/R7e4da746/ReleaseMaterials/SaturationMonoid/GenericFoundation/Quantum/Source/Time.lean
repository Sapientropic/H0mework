import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Source.Carrier
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Generator.Intertwining
import H0mework.Quantum.Generator.SelfAdjoint

/-! The source time acts on its whole completed action carrier. Its generator
has exactly the original domain and energy; the preparation is allowed to move. -/

set_option autoImplicit false
open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.Quantum.Source
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Ω : H) (unit : ‖Ω‖ = 1)
  (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))

def time : Multiplicative ℝ →* (Carrier Ω ≃ₗᵢ[ℂ] Carrier Ω) where
  toFun t := ((realization Ω unit).trans (U t)).trans (realization Ω unit).symm
  map_one' := by
    ext x
    simp
  map_mul' s t := by
    ext x
    simp

theorem realization_time (t : Multiplicative ℝ) (x : Carrier Ω) :
    realization Ω unit (time Ω unit U t x) = U t (realization Ω unit x) :=
  (realization Ω unit).apply_symm_apply _

theorem time_continuous (continuousTime : ∀ x, Continuous (Generator.orbit U x))
    (x : Carrier Ω) : Continuous (Generator.orbit (time Ω unit U) x) := by
  exact (realization Ω unit).symm.continuous.comp (continuousTime (realization Ω unit x))

def hamiltonian : Carrier Ω →ₗ.[ℂ] Carrier Ω := Generator.hamiltonianOperator (time Ω unit U)

theorem hamiltonian_selfAdjoint (continuousTime : ∀ x, Continuous (Generator.orbit U x)) :
    IsSelfAdjoint (hamiltonian Ω unit U) :=
  Generator.hamiltonianOperator_selfAdjoint _ (time_continuous Ω unit U continuousTime)

theorem domain_iff (x : Carrier Ω) :
    realization Ω unit x ∈ (Generator.hamiltonianOperator U).domain ↔
      x ∈ (hamiltonian Ω unit U).domain :=
  Generator.Intertwining.domain_iff (time Ω unit U) U
    (realization Ω unit).toLinearIsometry (realization_time Ω unit U) x

def domainPoint (x : (hamiltonian Ω unit U).domain) : (Generator.hamiltonianOperator U).domain :=
  Generator.Intertwining.domainPoint (time Ω unit U) U
    (realization Ω unit).toLinearIsometry (realization_time Ω unit U) x

theorem hamiltonian_readback (x : (hamiltonian Ω unit U).domain) :
    realization Ω unit (hamiltonian Ω unit U x) = Generator.hamiltonianOperator U (domainPoint Ω unit U x) :=
  Generator.Intertwining.hamiltonian_value (time Ω unit U) U
    (realization Ω unit).toLinearIsometry (realization_time Ω unit U) x

theorem energy_readback (x : (hamiltonian Ω unit U).domain) :
    inner ℂ (hamiltonian Ω unit U x) x.val =
      inner ℂ (Generator.hamiltonianOperator U (domainPoint Ω unit U x))
        (realization Ω unit x.val) := by
  rw [← hamiltonian_readback, (realization Ω unit).inner_map_map]

def preparation (t : Multiplicative ℝ) : Carrier Ω :=
  time Ω unit U t (vector Ω 1)

theorem preparation_readback (t : Multiplicative ℝ) :
    realization Ω unit (preparation Ω unit U t) = U t Ω := by
  rw [preparation, realization_time, realization_vector]
  rfl

theorem moving_expectation (t : Multiplicative ℝ) (A : H →L[ℂ] H) :
    inner ℂ (preparation Ω unit U t) (action Ω unit A (preparation Ω unit U t)) =
      inner ℂ (U t Ω) (A (U t Ω)) := by
  rw [← (realization Ω unit).inner_map_map, realization_action, preparation_readback]

theorem action_covariant (t : Multiplicative ℝ) (A : H →L[ℂ] H) (x : Carrier Ω) :
    time Ω unit U t (action Ω unit A x) =
      action Ω unit ((U t).conjStarAlgEquiv A) (time Ω unit U t x) := by
  apply (realization Ω unit).injective
  rw [realization_time, realization_action, realization_action, realization_time]
  simp

end
end SaturationMonoid.Quantum.Source
