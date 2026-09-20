import H0mework.Physics.MotherDeclarationsPhysical.LawsCompletion

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTypeFormation

open MotherStreamLaws

noncomputable section

abbrev Law := MotherPhysicalLaws.Law
abbrev Current := MotherPhysicalLaws.Current

/-- The entire dependent carrier is formed by the already completed mother law. -/
def Fiber (law : Law) (current : Current) : Type :=
  {value : Stream // MotherPhysicalLaws.eval law (current, value) 0 = 0}

theorem every_family (target : Current → Stream → Prop) :
    ∃ law : Law,
      (∀ current value,
        MotherPhysicalLaws.eval law (current, value) 0 = 0 ↔ target current value) ∧
      (fun current => Fiber law current) =
        (fun current => {value : Stream // target current value}) := by
  classical
  obtain ⟨law, generated, _⟩ := MotherPhysicalLaws.every_law
    (fun input => fun _ => if target input.1 input.2 then 0 else 1)
  have exactPredicate (current : Current) (value : Stream) :
      MotherPhysicalLaws.eval law (current, value) 0 = 0 ↔ target current value := by
    rw [generated]
    simp
  refine ⟨law, exactPredicate, ?_⟩
  funext current
  exact congrArg Subtype (funext fun value => propext (exactPredicate current value))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTypeFormation
