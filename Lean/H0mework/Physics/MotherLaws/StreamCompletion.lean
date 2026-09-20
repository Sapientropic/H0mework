import H0mework.Physics.MotherLaws.StreamDensity

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws

open Set UniformSpace MotherFamilyOccurrence
open scoped Topology

noncomputable section

abbrev Raw := Set.range finiteNativeLaw
abbrev Law := Completion Raw

/-- Compact-convergence completion of the one fixed mother-history law factory. -/
def lawRead : Law → C(Stream, Stream) := Completion.extension Subtype.val

theorem lawRead_coe (raw : Raw) : lawRead (raw : Law) = raw.val :=
  Completion.extension_coe uniformContinuous_subtype_val raw

theorem lawRead_uniformEmbedding : IsUniformEmbedding lawRead :=
  (Completion.isUniformInducing_extension
    isUniformEmbedding_subtype_val.isUniformInducing).isUniformEmbedding

theorem lawRead_surjective : Function.Surjective lawRead := by
  have included : Set.range finiteNativeLaw ⊆ Set.range lawRead := by
    rintro _ ⟨visit, rfl⟩
    let raw : Raw := ⟨finiteNativeLaw visit, ⟨visit, rfl⟩⟩
    exact ⟨(raw : Law), lawRead_coe raw⟩
  have closed := lawRead_uniformEmbedding.isClosedEmbedding.isClosed_range
  intro f
  exact closure_minimal included closed (finiteNativeLaw_dense f)

/-- At a fixed complete input, the evaluator is the completion extension of native evaluation. -/
def eval (law : Law) (input : Stream) : Stream :=
  Completion.extension (fun raw : Raw => raw.val input) law

theorem eval_eq (law : Law) (input : Stream) : eval law input = lawRead law input := by
  have agrees : (fun value : Law => eval value input) =
      (fun value : Law => lawRead value input) := by
    apply Completion.ext Completion.continuous_extension
      ((MotherLawCompletion.uniformContinuous_evaluation input).continuous.comp
        Completion.continuous_extension)
    intro raw
    change Completion.extension (fun a : Raw => a.val input) (raw : Law) =
      (lawRead (raw : Law)) input
    have uniform : UniformContinuous (fun a : Raw => a.val input) :=
      (MotherLawCompletion.uniformContinuous_evaluation input).comp uniformContinuous_subtype_val
    rw [Completion.extension_coe uniform, lawRead_coe]
  exact congrFun agrees law

theorem eval_uniformContinuous (input : Stream) :
    UniformContinuous (fun law : Law => eval law input) :=
  Completion.uniformContinuous_extension

theorem eval_continuous_input (law : Law) : Continuous (eval law) := by
  have same : eval law = lawRead law := funext (eval_eq law)
  rw [same]
  exact (lawRead law).continuous

def ofVisit (visit : MotherVisit) : Law :=
  (⟨finiteNativeLaw visit, ⟨visit, rfl⟩⟩ : Raw)

theorem ofVisit_read (visit : MotherVisit) : lawRead (ofVisit visit) = finiteNativeLaw visit :=
  lawRead_coe _

theorem ofVisit_eval (visit : MotherVisit) (input : Stream) :
    eval (ofVisit visit) input = finiteNativeLaw visit input := by
  rw [eval_eq, ofVisit_read]

theorem every_continuous_law (target : C(Stream, Stream)) :
    ∃! law : Law, lawRead law = target := by
  obtain ⟨law, generated⟩ := lawRead_surjective target
  exact ⟨law, generated, fun other same =>
    lawRead_uniformEmbedding.injective (same.trans generated.symm)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws
