import H0mework.Fock.CopyGraph.CorrectionObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCost

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceConditionalCorrection
open SourceConditionalGraphDecoder (action)
open SourceCopyProgram (Index scale)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem explicit_gain (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖SourceConditionalGraph.copyRead depth bound index (residual (historyPMF bound) query value)‖ ^ 2 =
      ‖SourceConditionalGraphDecoder.residual depth bound index query (SourceConditionalGraph.copyRead depth bound index value)‖ ^ 2 +
        ‖action depth bound index query (update depth bound index query value)‖ ^ 2 := by
  have original := SourceConditionalGraphDecoder.conditional_gain depth bound index query value
  rw [decoder_formula, add_sub_cancel_left] at original
  exact original

theorem direction_gram (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    (action depth bound index query).adjoint (action depth bound index query (direction bound query)) =
      (denominator depth bound index query : ℂ) • clockMean bound query := by
  rw [gram, direction_law, direction_pairing]
  have combined := add_smul (1 : ℂ)
    ((scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * (coupling bound query : ℂ)) (clockMean bound query)
  simp only [one_smul] at combined
  rw [← combined]
  congr 1
  unfold denominator strength
  push_cast
  ring

theorem direction_energy (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    ‖action depth bound index query (direction bound query)‖ ^ 2 = coupling bound query * denominator depth bound index query := by
  have reverse : inner ℂ (direction bound query) (clockMean bound query) = (coupling bound query : ℂ) := by
    rw [← inner_conj_symm (direction bound query) (clockMean bound query), direction_pairing, Complex.conj_ofReal]
  have pairing := (action depth bound index query).adjoint_inner_right (direction bound query)
    (action depth bound index query (direction bound query))
  rw [direction_gram, inner_smul_right, reverse] at pairing
  have realPart := congrArg Complex.re pairing
  rw [← Complex.ofReal_mul, Complex.ofReal_re] at realPart
  have normRead : (inner ℂ (action depth bound index query (direction bound query))
      (action depth bound index query (direction bound query))).re =
        ‖action depth bound index query (direction bound query)‖ ^ 2 := by
    rw [← RCLike.re_eq_complex_re]
    with_reducible exact inner_self_eq_norm_sq (𝕜 := ℂ) (action depth bound index query (direction bound query))
  rw [normRead] at realPart
  linarith only [realPart]

end
end SourceConditionalCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
