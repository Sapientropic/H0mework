import H0mework.Physics.MotherDeclarationsPhysical.LawsDensity

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws

open Set UniformSpace MotherStreamLaws
open scoped Topology

noncomputable section

abbrev Raw := Set.range finiteLaw
abbrev Law := Completion Raw

def lawRead : Law → (Input → Stream) := Completion.extension Subtype.val

theorem lawRead_coe (raw : Raw) : lawRead (raw : Law) = raw.val :=
  Completion.extension_coe uniformContinuous_subtype_val raw

theorem lawRead_uniformEmbedding : IsUniformEmbedding lawRead :=
  (Completion.isUniformInducing_extension
    isUniformEmbedding_subtype_val.isUniformInducing).isUniformEmbedding

theorem lawRead_surjective : Function.Surjective lawRead := by
  have included : Set.range finiteLaw ⊆ Set.range lawRead := by
    rintro _ ⟨programme, rfl⟩
    let raw : Raw := ⟨finiteLaw programme, ⟨programme, rfl⟩⟩
    exact ⟨(raw : Law), lawRead_coe raw⟩
  have closed := lawRead_uniformEmbedding.isClosedEmbedding.isClosed_range
  intro target
  exact closure_minimal included closed (finiteLaw_dense target)

/-- Fixed-input evaluation is the extension of actual finite source evaluation. -/
def eval (law : Law) (input : Input) : Stream :=
  Completion.extension (fun raw : Raw => raw.val input) law

theorem eval_eq (law : Law) (input : Input) : eval law input = lawRead law input := by
  have agrees : (fun value : Law => eval value input) = fun value : Law => lawRead value input := by
    apply Completion.ext Completion.continuous_extension
      ((Pi.uniformContinuous_proj (fun _ : Input => Stream) input).continuous.comp
        Completion.continuous_extension)
    intro raw
    change Completion.extension (fun value : Raw => value.val input) (raw : Law) = (lawRead (raw : Law)) input
    have uniform : UniformContinuous (fun value : Raw => value.val input) :=
      (Pi.uniformContinuous_proj (fun _ : Input => Stream) input).comp uniformContinuous_subtype_val
    rw [Completion.extension_coe uniform, lawRead_coe]
  exact congrFun agrees law

def ofProgramme (programme : Programme) : Law :=
  (⟨finiteLaw programme, ⟨programme, rfl⟩⟩ : Raw)

theorem ofProgramme_eval (programme : Programme) (input : Input) :
    eval (ofProgramme programme) input = finiteLaw programme input := by
  rw [eval_eq]
  exact congrFun (lawRead_coe _) input

theorem every_law (target : Input → Stream) :
    ∃! law : Law, ∀ input, eval law input = target input := by
  obtain ⟨law, generated⟩ := lawRead_surjective target
  refine ⟨law, fun input => (eval_eq law input).trans (congrFun generated input), ?_⟩
  intro other same
  have readSame : lawRead other = target :=
    funext fun input => (eval_eq other input).symm.trans (same input)
  exact lawRead_uniformEmbedding.injective (readSame.trans generated.symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws
