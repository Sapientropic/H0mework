import H0mework.Realization.Operations.OperatorRecurrence

/-! A source observation recurrence generates a closed finite-prefix action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.FiniteRecurrence

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]

def advance (bound : Nat) (coefficients : Fin (bound + 1) → R) :
    PrefixCarrier B bound →ₗ[R] PrefixCarrier B bound :=
  OperatorRecurrence.advance bound (fun index => coefficients index • (LinearMap.id : B →ₗ[R] B))

theorem advance_last (bound : Nat) (coefficients : Fin (bound + 1) → R) (values : PrefixCarrier B bound) :
    advance bound coefficients values (Fin.last bound) = ∑ index : Fin (bound + 1), coefficients index • values index := by
  simpa only [advance, LinearMap.smul_apply, LinearMap.id_apply] using
    OperatorRecurrence.advance_last bound (fun index => coefficients index • (LinearMap.id : B →ₗ[R] B)) values

theorem advance_castSucc (bound : Nat) (coefficients : Fin (bound + 1) → R)
    (values : PrefixCarrier B bound) (index : Fin bound) :
    advance bound coefficients values index.castSucc = values index.succ :=
  OperatorRecurrence.advance_castSucc bound (fun index => coefficients index • (LinearMap.id : B →ₗ[R] B)) values index

variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B)
variable (bound : Nat) (coefficients : Fin (bound + 1) → R)

theorem advance_source
    (sourceLaw : observation.comp (action ^ (bound + 1)) =
      ∑ index : Fin (bound + 1), coefficients index • stageEvaluator action observation index.val) :
    (advance bound coefficients).comp (prefixEvaluator action observation bound) =
      (prefixEvaluator action observation bound).comp action := by
  apply LinearMap.ext
  intro value
  funext index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · change advance bound coefficients (prefixEvaluator action observation bound value) (Fin.last bound) = _
    rw [advance_last]
    have generated := LinearMap.congr_fun sourceLaw value
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply] at generated
    apply generated.symm.trans
    change observation ((action ^ (bound + 1)) value) = observation ((action ^ bound) (action value))
    rw [pow_succ]
    rfl
  · change advance bound coefficients (prefixEvaluator action observation bound value) earlier.castSucc = _
    rw [advance_castSucc]
    change observation ((action ^ (earlier.val + 1)) value) = observation ((action ^ earlier.val) (action value))
    rw [pow_succ]
    rfl

end
end SourceGeneratedActionObservationHistory.FiniteRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
