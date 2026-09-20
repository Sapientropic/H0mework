import H0mework.Physics.MotherLaws.PointwiseDensity

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws

open Set UniformSpace MotherStreamLaws MotherFamilyOccurrence
open scoped Topology

noncomputable section

abbrev Raw := Set.range finiteLaw
/-- General Cauchy-filter completion; it makes no sequential or integral-limit assertion. -/
abbrev Law := Completion Raw

/-- The pointwise completion uses the original fixed function-space product uniformity. -/
def lawRead : Law → (Stream → Stream) := Completion.extension Subtype.val

theorem lawRead_coe (raw : Raw) : lawRead (raw : Law) = raw.val :=
  Completion.extension_coe uniformContinuous_subtype_val raw

theorem lawRead_uniformEmbedding : IsUniformEmbedding lawRead :=
  (Completion.isUniformInducing_extension
    isUniformEmbedding_subtype_val.isUniformInducing).isUniformEmbedding

theorem lawRead_surjective : Function.Surjective lawRead := by
  have included : Set.range finiteLaw ⊆ Set.range lawRead := by
    rintro _ ⟨visit, rfl⟩
    let raw : Raw := ⟨finiteLaw visit, ⟨visit, rfl⟩⟩
    exact ⟨(raw : Law), lawRead_coe raw⟩
  have closed := lawRead_uniformEmbedding.isClosedEmbedding.isClosed_range
  intro target
  exact closure_minimal included closed (finiteLaw_dense target)

/-- Actual evaluation extends native evaluation at this fixed complete input. -/
def eval (law : Law) (input : Stream) : Stream :=
  Completion.extension (fun raw : Raw => raw.val input) law

theorem eval_eq (law : Law) (input : Stream) : eval law input = lawRead law input := by
  have agrees : (fun value : Law => eval value input) =
      (fun value : Law => lawRead value input) := by
    apply Completion.ext Completion.continuous_extension
      ((Pi.uniformContinuous_proj (fun _ : Stream => Stream) input).continuous.comp
        Completion.continuous_extension)
    intro raw
    change Completion.extension (fun a : Raw => a.val input) (raw : Law) =
      (lawRead (raw : Law)) input
    have uniform : UniformContinuous (fun a : Raw => a.val input) :=
      (Pi.uniformContinuous_proj (fun _ : Stream => Stream) input).comp
        uniformContinuous_subtype_val
    rw [Completion.extension_coe uniform, lawRead_coe]
  exact congrFun agrees law

theorem eval_uniformContinuous (input : Stream) :
    UniformContinuous (fun law : Law => eval law input) :=
  Completion.uniformContinuous_extension

def ofVisit (visit : MotherVisit) : Law :=
  (⟨finiteLaw visit, ⟨visit, rfl⟩⟩ : Raw)

theorem ofVisit_read (visit : MotherVisit) : lawRead (ofVisit visit) = finiteLaw visit :=
  lawRead_coe _

theorem ofVisit_eval (visit : MotherVisit) (input : Stream) :
    eval (ofVisit visit) input = finiteNativeLaw visit input := by
  rw [eval_eq, ofVisit_read]
  rfl

theorem every_law (target : Stream → Stream) :
    ∃! law : Law, ∀ input, eval law input = target input := by
  obtain ⟨law, generated⟩ := lawRead_surjective target
  refine ⟨law, fun input => (eval_eq law input).trans (congrFun generated input), ?_⟩
  intro other same
  have readSame : lawRead other = target :=
    funext fun input => (eval_eq other input).symm.trans (same input)
  exact lawRead_uniformEmbedding.injective (readSame.trans generated.symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws
