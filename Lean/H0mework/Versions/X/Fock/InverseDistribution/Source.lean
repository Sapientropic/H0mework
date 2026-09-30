import H0mework.Fock.InverseDistribution.Native
import H0mework.Versions.X.Fock.HistoryConditional.NativeInverseSource
import H0mework.Versions.X.Fock.HistoryConditional.NativeKeysWord

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeInverseDistribution

noncomputable section

def inverseEntry (entry : Option (Nat × ℚ)) : Nat →₀ ℚ :=
  match entry with
  | none => 0
  | some (state, weight) => Finsupp.single state weight

def recovered (bound : Nat) (program : Nat × Nat) (weights : Fin (bound + 1) → ℚ) : Nat →₀ ℚ :=
  ∑ actor, inverseEntry (split bound program weights actor).1

def residual (bound : Nat) (program : Nat × Nat) (weights : Fin (bound + 1) → ℚ) : Nat →₀ ℚ :=
  SourceConditionalNativeKeys.word bound (fun actor => (split bound program weights actor).2)

def action (program : Nat × Nat) : (Nat →₀ ℚ) →ₗ[ℚ] Nat →₀ ℚ :=
  Finsupp.lmapDomain ℚ ℚ (SourceCopyWordAffine.execute program)

theorem entry_equation (program : Nat × Nat) (positive : 0 < program.1) (target : Nat) (weight : ℚ) :
    action program (inverseEntry (splitEntry program target weight).1) +
      Finsupp.single target (splitEntry program target weight).2 = Finsupp.single target weight := by
  cases computed : SourceNativeProgramInverse.decode program target with
  | none => simp only [splitEntry, computed, inverseEntry, map_zero, zero_add]
  | some state =>
      have actual := (SourceNativeProgramInverse.decode_some_iff program positive target state).mp computed
      simp only [splitEntry, computed, inverseEntry, action, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single, actual, Finsupp.single_zero, add_zero]

theorem reconstruction (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1)
    (weights : Fin (bound + 1) → ℚ) :
    action program (recovered bound program weights) + residual bound program weights = SourceConditionalNativeKeys.word bound weights := by
  simp only [recovered, residual, SourceConditionalNativeKeys.word, LinearMap.coe_mk, AddHom.coe_mk,
    SourceConditionalNativeKeys.source_single, Finsupp.smul_single, smul_eq_mul, mul_one, map_sum, ← Finset.sum_add_distrib, split]
  apply Finset.sum_congr rfl
  intro actor _
  exact entry_equation program positive _ _

theorem residual_image_zero (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1)
    (weights : Fin (bound + 1) → ℚ) (state : Nat) :
    residual bound program weights (SourceCopyWordAffine.execute program state) = 0 := by
  simp only [residual, SourceConditionalNativeKeys.word, LinearMap.coe_mk, AddHom.coe_mk,
    SourceConditionalNativeKeys.source_single, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro actor _
  by_cases same : actor.val + 1 = SourceCopyWordAffine.execute program state
  · simp only [split, splitEntry, same, SourceNativeProgramInverse.decode_execute program positive,
      Finsupp.single_zero, Finsupp.zero_apply]
  · simp only [Finsupp.single_apply, if_neg same]

end
end SourceNativeInverseDistribution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
