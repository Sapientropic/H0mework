import H0mework.Realization.JointState.ActionOrbit

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedIntegralCoherentJointAction.MotherOrbitWords

noncomputable section

universe i h q
variable {I : Type i} {H : Type h} {Q : Type q}
variable [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]

def orbit (input : Input I H Q) (index : ℕ × I) : input.Carrier :=
  (input.omega ^ index.1) (input.seedLift index.2)

def total (input : Input I H Q) : List (ℕ × I) → input.Carrier
  | [] => 0
  | index :: rest => orbit input index + total input rest

theorem total_append (input : Input I H Q) (first last : List (ℕ × I)) :
    total input (first ++ last) = total input first + total input last := by
  induction first with
  | nil => simp [total]
  | cons index rest ih => simp only [List.cons_append, total, ih, add_assoc]

theorem orbit_smul (input : Input I H Q) (coefficient : ℤ) (index : ℕ × I) :
    orbit input (index.1, coefficient • index.2) = coefficient • orbit input index := by
  simp only [orbit, map_smul]

theorem total_smul (input : Input I H Q) (coefficient : ℤ) (terms : List (ℕ × I)) :
    total input (terms.map fun index => (index.1, coefficient • index.2)) =
      coefficient • total input terms := by
  induction terms with
  | nil => simp [total]
  | cons index rest ih => simp only [List.map_cons, total, orbit_smul, ih, smul_add]

theorem orbit_val (input : Input I H Q) (index : ℕ × I) :
    (orbit input index).val = input.orbitGenerator index := by
  rcases index with ⟨stage, event⟩
  induction stage with
  | zero => simp [orbit, Input.orbitGenerator, Input.seedLift]
  | succ stage ih =>
      simp only [orbit, Input.orbitGenerator, pow_succ', Module.End.mul_apply]
      change input.ambientAction ((orbit input (stage, event)).val) =
        input.ambientAction (input.orbitGenerator (stage, event))
      exact congrArg input.ambientAction ih

theorem integral_orbit (input : Input I H Q) (index : ℕ × I) :
    input.integralFace (orbit input index) = (input.integralAction ^ index.1) index.2 := by
  rcases index with ⟨stage, event⟩
  induction stage with
  | zero => simp [orbit, Input.seedLift, Input.integralFace, Input.seed]
  | succ stage ih =>
      simp only [orbit, pow_succ', Module.End.mul_apply]
      change input.integralAction (input.integralFace (orbit input (stage, event))) =
        input.integralAction ((input.integralAction ^ stage) event)
      exact congrArg input.integralAction ih

/-- Intrinsic span membership produces a finite list; no target is stored in its alphabet. -/
theorem every_value (input : Input I H Q) (value : input.Carrier) :
    ∃ terms : List (ℕ × I), total input terms = value := by
  have generate (state : input.Ambient) (member : state ∈ input.carrier) :
      ∃ terms : List (ℕ × I), total input terms = ⟨state, member⟩ := by
    refine Submodule.span_induction
      (p := fun state member => ∃ terms : List (ℕ × I), total input terms = ⟨state, member⟩)
      ?_ ?_ ?_ ?_ member
    · rintro _ ⟨index, rfl⟩
      refine ⟨[index], ?_⟩
      simpa only [total, add_zero] using Subtype.ext (orbit_val input index)
    · exact ⟨[], rfl⟩
    · intro left right _ _ leftFormed rightFormed
      obtain ⟨first, firstEq⟩ := leftFormed
      obtain ⟨last, lastEq⟩ := rightFormed
      exact ⟨first ++ last, (total_append input first last).trans (congrArg₂ (· + ·) firstEq lastEq)⟩
    · intro coefficient state _ formed
      obtain ⟨terms, termsEq⟩ := formed
      exact ⟨terms.map (fun index => (index.1, coefficient • index.2)),
        (total_smul input coefficient terms).trans (congrArg (coefficient • ·) termsEq)⟩
  exact generate value.val value.property

end
end SourceGeneratedIntegralCoherentJointAction.MotherOrbitWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
