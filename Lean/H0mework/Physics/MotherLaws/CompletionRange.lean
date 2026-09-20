import H0mework.Physics.MotherLaws.CompletionPolynomial

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawCompletion

open Set UniformSpace
open scoped Topology

noncomputable section

namespace RangeCompletion

variable {Code : Type*} {n m : ℕ}

abbrev Raw (family : Code → C((Fin n → ℝ), (Fin m → ℝ))) := Set.range family
abbrev Law (family : Code → C((Fin n → ℝ), (Fin m → ℝ))) := Completion (Raw family)

def lawRead (family : Code → C((Fin n → ℝ), (Fin m → ℝ))) :
    Law family → C((Fin n → ℝ), (Fin m → ℝ)) :=
  Completion.extension Subtype.val

theorem lawRead_coe (family : Code → C((Fin n → ℝ), (Fin m → ℝ))) (raw : Raw family) :
    lawRead family (raw : Law family) = raw.val :=
  Completion.extension_coe uniformContinuous_subtype_val raw

theorem lawRead_uniformEmbedding (family : Code → C((Fin n → ℝ), (Fin m → ℝ))) :
    IsUniformEmbedding (lawRead family) :=
  (Completion.isUniformInducing_extension
    isUniformEmbedding_subtype_val.isUniformInducing).isUniformEmbedding

theorem lawRead_surjective (family : Code → C((Fin n → ℝ), (Fin m → ℝ)))
    (dense : DenseRange family) : Function.Surjective (lawRead family) := by
  have included : Set.range family ⊆ Set.range (lawRead family) := by
    rintro _ ⟨code, rfl⟩
    let raw : Raw family := ⟨family code, ⟨code, rfl⟩⟩
    exact ⟨(raw : Law family), lawRead_coe family raw⟩
  have closed := (lawRead_uniformEmbedding family).isClosedEmbedding.isClosed_range
  intro f
  exact closure_minimal included closed (dense f)

/-- Fixed-point evaluation extends the native finite-law evaluator. -/
def eval (family : Code → C((Fin n → ℝ), (Fin m → ℝ)))
    (law : Law family) (x : Fin n → ℝ) : Fin m → ℝ :=
  Completion.extension (fun raw : Raw family => raw.val x) law

theorem eval_eq (family : Code → C((Fin n → ℝ), (Fin m → ℝ)))
    (law : Law family) (x : Fin n → ℝ) : eval family law x = lawRead family law x := by
  have agrees : (fun value : Law family => eval family value x) =
      (fun value : Law family => lawRead family value x) := by
    apply Completion.ext Completion.continuous_extension
      ((uniformContinuous_evaluation x).continuous.comp Completion.continuous_extension)
    intro raw
    change Completion.extension (fun a : Raw family => a.val x) (raw : Law family) =
      (lawRead family (raw : Law family)) x
    have uniform : UniformContinuous (fun a : Raw family => a.val x) :=
      (uniformContinuous_evaluation x).comp uniformContinuous_subtype_val
    rw [Completion.extension_coe uniform, lawRead_coe]
  exact congrFun agrees law

theorem eval_coe (family : Code → C((Fin n → ℝ), (Fin m → ℝ)))
    (raw : Raw family) (x : Fin n → ℝ) : eval family (raw : Law family) x = raw.val x := by
  rw [eval_eq, lawRead_coe]

theorem eval_jointly_continuous (family : Code → C((Fin n → ℝ), (Fin m → ℝ))) :
    Continuous (fun pair : Law family × (Fin n → ℝ) => eval family pair.1 pair.2) := by
  simp only [eval_eq]
  exact continuous_eval.comp (Completion.continuous_extension.prodMap continuous_id)

end RangeCompletion
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawCompletion
