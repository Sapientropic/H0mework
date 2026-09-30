import H0mework.Realization.Operations.ObservationModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.OperatorRecurrence

universe r u
variable {R : Type r} [CommRing R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]

def advance (bound : Nat) (coefficients : Fin (bound + 1) → B →ₗ[R] B) :
    PrefixCarrier B bound →ₗ[R] PrefixCarrier B bound :=
  LinearMap.pi fun index => Fin.lastCases
    (∑ source : Fin (bound + 1), (coefficients source).comp (LinearMap.proj source))
    (fun source : Fin bound => LinearMap.proj source.succ) index

theorem advance_last (bound : Nat) (coefficients : Fin (bound + 1) → B →ₗ[R] B) (values : PrefixCarrier B bound) :
    advance bound coefficients values (Fin.last bound) = ∑ index : Fin (bound + 1), coefficients index (values index) := by
  simp only [advance, LinearMap.pi_apply, Fin.lastCases_last, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem advance_castSucc (bound : Nat) (coefficients : Fin (bound + 1) → B →ₗ[R] B)
    (values : PrefixCarrier B bound) (index : Fin bound) :
    advance bound coefficients values index.castSucc = values index.succ := by
  simp only [advance, LinearMap.pi_apply, Fin.lastCases_castSucc, LinearMap.proj_apply]

variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B)

theorem advance_source (bound : Nat) (coefficients : Fin (bound + 1) → B →ₗ[R] B)
    (sourceLaw : observation.comp (action ^ (bound + 1)) =
      ∑ index : Fin (bound + 1), (coefficients index).comp (stageEvaluator action observation index.val)) :
    (advance bound coefficients).comp (prefixEvaluator action observation bound) =
      (prefixEvaluator action observation bound).comp action := by
  apply LinearMap.ext
  intro value
  funext index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · change advance bound coefficients (prefixEvaluator action observation bound value) (Fin.last bound) = _
    rw [advance_last]
    have generated := LinearMap.congr_fun sourceLaw value
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at generated
    apply generated.symm.trans
    change observation ((action ^ (bound + 1)) value) = observation ((action ^ bound) (action value))
    rw [pow_succ]
    rfl
  · change advance bound coefficients (prefixEvaluator action observation bound value) earlier.castSucc = _
    rw [advance_castSucc]
    change observation ((action ^ (earlier.val + 1)) value) = observation ((action ^ earlier.val) (action value))
    rw [pow_succ]
    rfl

end SourceGeneratedActionObservationHistory.OperatorRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
