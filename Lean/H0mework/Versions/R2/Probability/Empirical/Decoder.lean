import H0mework.Versions.R2.Probability.Empirical.ConditionalFormula

/-! An arbitrary raw decoder has a source-generated L² representative on the actual finite next inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory
open scoped InnerProductSpace Classical

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

local instance : MeasurableSpace (Field read) := fieldBorel read

def sampleRead (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1)) :
    Space read runtime bound →ₗ[ℂ] ℂ where
  toFun value := value (fieldSample read runtime bound index)
  map_add' left right := ae_at_sample read runtime bound index (Lp.coeFn_add left right)
  map_smul' scalar value := ae_at_sample read runtime bound index (Lp.coeFn_smul scalar value)

theorem sampleRead_apply (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1))
    (value : Space read runtime bound) : sampleRead read runtime bound index value =
      value (fieldSample read runtime bound index) := rfl

theorem sample_norm_sq (runtime : LivingRuntimeState process) (bound : Nat) (value : Space read runtime bound) :
    ‖value‖ ^ 2 = ∑ index : Fin (bound + 1), (historyPMF bound index).toReal *
      ‖value (fieldSample read runtime bound index)‖ ^ 2 := by
  have realPart := congrArg Complex.re (inner_source_sum read runtime bound value value)
  calc
    _ = Complex.re ⟪value, value⟫_ℂ := norm_sq_eq_re_inner (𝕜 := ℂ) value
    _ = ∑ index : Fin (bound + 1), (historyPMF bound index).toReal *
        Complex.re ⟪value (fieldSample read runtime bound index), value (fieldSample read runtime bound index)⟫_ℂ := by
      simpa only [Complex.re_sum, Complex.smul_re, smul_eq_mul] using realPart
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      exact congrArg ((historyPMF bound index).toReal * ·)
        (norm_sq_eq_re_inner (𝕜 := ℂ) (value (fieldSample read runtime bound index))).symm

def atoms (runtime : LivingRuntimeState process) (bound : Nat) : Finset (Field read) :=
  Finset.univ.image (nextAtom read runtime bound)

def decoderValue (runtime : LivingRuntimeState process) (bound : Nat) (decoder : Field read → ℂ) :
    Space read runtime.tick.next bound :=
  ∑ atom ∈ atoms read runtime bound, decoder atom • atomTest read runtime bound atom

theorem decoderValue_at_next (runtime : LivingRuntimeState process) (bound : Nat)
    (decoder : Field read → ℂ) (index : Fin (bound + 1)) :
    decoderValue read runtime bound decoder (nextAtom read runtime bound index) =
      decoder (nextAtom read runtime bound index) := by
  rw [nextAtom_eq_next_sample]
  change sampleRead read runtime.tick.next bound index (decoderValue read runtime bound decoder) = _
  simp only [decoderValue, map_sum, map_smul, sampleRead_apply,
    ← nextAtom_eq_next_sample, atomTest_at_sample, smul_eq_mul]
  rw [Finset.sum_eq_single (nextAtom read runtime bound index)]
  · simp
  · intro atom _ distinct
    simp only [if_neg (Ne.symm distinct), mul_zero]
  · intro absent
    exact (absent (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)).elim

theorem residual_decoder_orthogonal (runtime : LivingRuntimeState process) (bound : Nat)
    (value : Space read runtime bound) (decoder : Field read → ℂ) :
    ⟪pullback read runtime bound (transfer read runtime bound value - decoderValue read runtime bound decoder),
      residual read runtime bound value⟫_ℂ = 0 :=
  residual_orthogonal read runtime bound value (transfer read runtime bound value - decoderValue read runtime bound decoder)

end
end SourceConditionalRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
