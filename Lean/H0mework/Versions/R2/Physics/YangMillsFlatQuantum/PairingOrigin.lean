import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingFields

/-! At the original source origin, the spin exchange fixes the prepared
vector. The unmodified mother response itself therefore reads the positive
full-matter pairing, with no exchange inserted into its observable. -/

set_option autoImplicit false
open scoped InnerProductSpace ComplexOrder

namespace SaturationMonoid.PhysicsCore.YangMills.FullPairing

open DiracExteriorMatterAction Stage9C.Material.SpinPair Stage9DEF
open Flat.Quantum.History
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedComplexFeaturePerfectification

noncomputable section

private theorem origin_vector_flip (index : Source.Index) :
    Source.vector 0 (Compatibility.flip index) = Source.vector 0 index := by
  rcases index with ⟨spin, color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [Source.vector_zero, Compatibility.flip, Compatibility.spinFlip, spinPairCoefficients]

theorem dual_origin (matter : DiracExteriorMatterCarrier) :
    actual.conjugateMatter 0 matter =
      2 * (spinScale : ℂ) * inner ℂ (prepared 0) (naturalCoordinates matter) := by
  rw [Compatibility.actual_dual_evaluation, prepared, inner_embed, Finset.mul_sum]
  simp_rw [Compatibility.dualCoefficient_source_star, origin_vector_flip]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem origin_response (action : Mother) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0) (Compatibility.responseMatrix action) =
      inner ℂ (prepared 0) (operator action (prepared 0)) := by
  have generated := Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.quantumClosure.sourceResponse 0 action
  rw [Runtime.firstQuantumTick_answer, Runtime.fieldAt_eq_vector] at generated
  rw [Stage10.Runtime.tick_vector]
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0)
    (Complex.ofReal_ne_zero.mpr spinScale_pos.ne'))
  rw [← generated, dual_origin, ← operator_coordinates, actual_eq_twice_prepared,
    map_smul, inner_smul_right]
  ring

theorem operator_fromOperator (action : Hilbert →L[ℂ] Hilbert) :
    operator (fromOperator action) = action := by
  ext vector
  simp [operator, fromOperator]

theorem origin_gram (first second : Mother) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (fromOperator ((operator first).adjoint.comp (operator second)))) =
      inner ℂ (operator first (prepared 0)) (operator second (prepared 0)) := by
  rw [origin_response, operator_fromOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem physical_pair_origin (configuration : StageNineHolonomicField.StageNineHolonomicConfiguration)
    (P Q : Polynomial) :
    inner ℂ (vector configuration 0 P) (vector configuration 0 Q) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (fromOperator
          ((operator (evaluate configuration P)).adjoint.comp (operator (evaluate configuration Q))))) := by
  rw [← (hilbertAmbientRealization (feature configuration 0)).inner_map_map]
  simp only [vector, hilbertAmbientRealization_source_readback, feature_value]
  exact (origin_gram _ _).symm

end
end SaturationMonoid.PhysicsCore.YangMills.FullPairing
