import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Sources

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory MotherObligationOrigin MotherRestructuringReceipts
open ResponsibilityLifecycle LivingLawEvolution
open scoped Classical
noncomputable section

def presentationFromEquiv {A C : Type} (e : A ≃ C) : ConstructivePresentation A C :=
  ⟨e, e.symm, e.symm_apply_apply, e.apply_symm_apply⟩

theorem presentation_bijective {A C : Type} (p : ConstructivePresentation A C) : Function.Bijective p.forward :=
  ⟨fun _ _ same => (p.backward_forward _).symm.trans ((congrArg p.backward same).trans (p.backward_forward _)),
    fun value => ⟨p.backward value, p.forward_backward value⟩⟩

private theorem presentation_ext {A C : Type} (left right : ConstructivePresentation A C)
    (forward : left.forward = right.forward) (backward : left.backward = right.backward) : left = right := by
  cases left
  cases right
  cases forward
  cases backward
  rfl

theorem presentationFromForward_recovers {A C : Type} (p : ConstructivePresentation A C) :
    presentationFromEquiv (Equiv.ofBijective p.forward (presentation_bijective p)) = p := by
  refine presentation_ext (presentationFromEquiv (Equiv.ofBijective p.forward (presentation_bijective p))) p rfl ?_
  funext value
  apply (presentation_bijective p).1
  exact (Equiv.ofBijective p.forward (presentation_bijective p)).apply_symm_apply value |>.trans (p.forward_backward value).symm

variable {I : Type} {A C : I → Type} (index : I ↪ B) (left : ∀ i, A i ↪ B) (right : ∀ i, C i ↪ B)

def formPresentationSection (material : M) : Option ((i : I) → ConstructivePresentation (A i) (C i)) :=
  (NativeSection.form (sigmaEmbedding index left) (fun value => right value.1) material).bind (fun forward =>
    if bijective : ∀ i, Function.Bijective (fun value : A i => forward ⟨i, value⟩) then
      some (fun i => presentationFromEquiv (Equiv.ofBijective (fun value => forward ⟨i, value⟩) (bijective i)))
    else none)

/-- The inverse program is uniquely determined by the forward program and
the original inverse laws. The complete native presentation still recovers. -/
theorem every_presentation_section (original : (i : I) → ConstructivePresentation (A i) (C i)) :
    ∃ material : M, formPresentationSection index left right material = some original := by
  obtain ⟨material, formed⟩ := NativeSection.every_section (sigmaEmbedding index left) (fun value => right value.1)
    (fun value => (original value.1).forward value.2)
  have bijective : ∀ i, Function.Bijective (fun value : A i => (original i).forward value) := fun i => presentation_bijective (original i)
  refine ⟨material, ?_⟩
  simp only [formPresentationSection, formed, Option.bind_some, dif_pos bijective]
  exact congrArg some (funext fun i => presentationFromForward_recovers (original i))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
