import H0mework.Fock.SourceHistoryClock.BinomialPrefixAction

/-! The full missing direction of two raw reads becomes visible under the actual action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Prefix

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def short : Model →ₗ[ℤ] (Fin 2 → ℤ) :=
  SourceGeneratedActionObservationHistory.prefixEvaluator action secondRead 1

theorem short_apply (value : Model) : short value = ![secondRead value, secondRead value + clockRead value] := by
  funext index
  fin_cases index
  · rfl
  · exact secondRead_action value

def hidden : Model := recover (fun index => if index.val = 2 then 1 else 0)

theorem hidden_moments : massRead hidden = 1 ∧ clockRead hidden = 0 ∧ secondRead hidden = 0 := by
  have source := recover_moments (fun index => if index.val = 2 then 1 else 0)
  norm_num at source
  exact source

def hiddenWord : Nat →₀ ℤ :=
  (3 : ℤ) • SourceOperationNative.point (runtimeAt 0) -
    (3 : ℤ) • SourceOperationNative.point (runtimeAt 1) + SourceOperationNative.point (runtimeAt 2)

theorem hidden_is_source : hidden = projection hiddenWord := by
  rw [hidden, recover_apply, Frame.rebuild_apply, hiddenWord]
  change (1 : ℤ) • Fock.point 0 + (-1 : ℤ) • Frame.effect 0 + (1 : ℤ) • Frame.secondEffect 0 = _
  simp only [map_add, map_sub, map_smul, one_smul, neg_one_smul]
  rw [effect_is_actual, secondEffect_is_actual]
  change _ = (3 : ℤ) • Fock.point 0 - (3 : ℤ) • Fock.point 1 + Fock.point 2
  abel

theorem short_hidden : short hidden = 0 := by
  rw [short_apply, hidden_moments.2.1, hidden_moments.2.2]
  funext index
  fin_cases index <;> rfl

theorem short_fibre (value : Model) : short value = 0 ↔ value = massRead value • hidden := by
  constructor
  · intro zero
    have first : secondRead value = 0 := congrFun zero 0
    have second : secondRead value + clockRead value = 0 :=
      (secondRead_action value).symm.trans (congrFun zero 1)
    have clockZero : clockRead value = 0 := by simpa only [first, zero_add] using second
    apply (model_ext_iff _ _).mpr
    simp only [map_smul, hidden_moments.1, hidden_moments.2.1, hidden_moments.2.2,
      smul_eq_mul, mul_one, mul_zero]
    exact ⟨True.intro, clockZero, first⟩
  · intro retained
    rw [retained, map_smul, short_hidden, smul_zero]

theorem short_action_hidden : short (action hidden) = ![0, 1] := by
  rw [short_apply, secondRead_action, clockRead_action, hidden_moments.1, hidden_moments.2.1, hidden_moments.2.2]
  rfl

theorem no_short_next :
    ¬ ∃ update : (Fin 2 → ℤ) → (Fin 2 → ℤ), ∀ value : Model, update (short value) = short (action value) := by
  rintro ⟨update, commutes⟩
  have sameInput : short hidden = short 0 := short_hidden.trans (map_zero short).symm
  have sameOutput := (commutes hidden).symm.trans ((congrArg update sameInput).trans (commutes 0))
  rw [short_action_hidden, map_zero, map_zero] at sameOutput
  have impossible : (1 : ℤ) = 0 := congrFun sameOutput 1
  norm_num at impossible

end
end SourceBinomialClock.Prefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
