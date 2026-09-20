import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Source-generated integral/coherent/measurement joint action orbit

Five actual maps determine one minimal action-stable state module.  The seed
embeds an integral event together with its coherent and measurement reads;
the ambient action applies the three given actions coordinatewise.  The
generated carrier is the `ℤ`-span of every forward orbit of every seed.

Consequently one endomorphism `omega` acts on one carrier and its integral,
coherent and measurement projections commute by construction.  No
action--measurement square is a premise.  Failure of the original seed graph
to be invariant is retained as an explicit joint incidence residual whose
two observable faces are exactly the old covariance residuals.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralCoherentJointAction

noncomputable section

universe i h q

variable {I : Type i} {H : Type h} {Q : Type q}
variable [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]

/-- Raw maps of one joint action occurrence.  They are maps only: no
commuting square or residual verdict is stored. -/
structure Input (I : Type i) (H : Type h) (Q : Type q)
    [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q] where
  integralAction : I →ₗ[ℤ] I
  coherentAction : H →ₗ[ℤ] H
  measurementAction : Q →ₗ[ℤ] Q
  coherentRead : I →ₗ[ℤ] H
  measurementRead : I →ₗ[ℤ] Q

namespace Input

abbrev Ambient (_input : Input I H Q) := I × (H × Q)

def ambientAction (input : Input I H Q) :
    input.Ambient →ₗ[ℤ] input.Ambient where
  toFun := fun state =>
    ⟨input.integralAction state.1,
      input.coherentAction state.2.1,
      input.measurementAction state.2.2⟩
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro coefficient state
    ext <;> simp

/-- Actual event with all three sibling reads. -/
def seed (input : Input I H Q) : I →ₗ[ℤ] input.Ambient where
  toFun := fun event =>
    ⟨event, input.coherentRead event, input.measurementRead event⟩
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro coefficient event
    ext <;> simp

def orbitGenerator (input : Input I H Q) (index : Nat × I) :
    input.Ambient :=
  (input.ambientAction ^ index.1) (input.seed index.2)

/-- Minimal source-generated action-stable ambient candidate. -/
def carrier (input : Input I H Q) : Submodule ℤ input.Ambient :=
  Submodule.span ℤ <| Set.range input.orbitGenerator

abbrev Carrier (input : Input I H Q) := input.carrier

theorem seed_mem_carrier (input : Input I H Q) (event : I) :
    input.seed event ∈ input.carrier := by
  apply Submodule.subset_span
  exact ⟨⟨0, event⟩, by simp [orbitGenerator]⟩

theorem ambientAction_mem_carrier (input : Input I H Q)
    {state : input.Ambient} (state_mem : state ∈ input.carrier) :
    input.ambientAction state ∈ input.carrier := by
  refine Submodule.span_induction (p := fun candidate _ =>
      input.ambientAction candidate ∈ input.carrier)
    ?_ ?_ ?_ ?_ state_mem
  · intro orbit orbit_mem
    rcases orbit_mem with ⟨⟨stage, event⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨⟨stage + 1, event⟩, by
      simp [orbitGenerator, pow_succ']⟩
  · simp
  · intro left right _ _ left_mem right_mem
    simpa using Submodule.add_mem _ left_mem right_mem
  · intro coefficient state _ state_mem
    simpa using Submodule.smul_mem _ coefficient state_mem

/-- The single joint action `Ω` on the orbit carrier. -/
def omega (input : Input I H Q) : input.Carrier →ₗ[ℤ] input.Carrier where
  toFun := fun state =>
    ⟨input.ambientAction state,
      input.ambientAction_mem_carrier state.2⟩
  map_add' := by
    intro left right
    apply Subtype.ext
    simp
  map_smul' := by
    intro coefficient state
    apply Subtype.ext
    simp

def seedLift (input : Input I H Q) : I →ₗ[ℤ] input.Carrier where
  toFun := fun event => ⟨input.seed event, input.seed_mem_carrier event⟩
  map_add' := by
    intro left right
    apply Subtype.ext
    simp
  map_smul' := by
    intro coefficient event
    apply Subtype.ext
    simp

def integralFace (input : Input I H Q) : input.Carrier →ₗ[ℤ] I where
  toFun := fun state => state.1.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def coherentFace (input : Input I H Q) : input.Carrier →ₗ[ℤ] H where
  toFun := fun state => state.1.2.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def measurementFace (input : Input I H Q) : input.Carrier →ₗ[ℤ] Q where
  toFun := fun state => state.1.2.2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem integralFace_seedLift (input : Input I H Q) :
    input.integralFace.comp input.seedLift = LinearMap.id := by
  ext event
  rfl

@[simp] theorem coherentFace_seedLift (input : Input I H Q) :
    input.coherentFace.comp input.seedLift = input.coherentRead := by
  ext event
  rfl

@[simp] theorem measurementFace_seedLift (input : Input I H Q) :
    input.measurementFace.comp input.seedLift = input.measurementRead := by
  ext event
  rfl

/-- Integral face of the single joint action. -/
theorem integralFace_omega (input : Input I H Q) :
    input.integralFace.comp input.omega =
      input.integralAction.comp input.integralFace := by
  ext state
  rfl

/-- Coherent face of the single joint action. -/
theorem coherentFace_omega (input : Input I H Q) :
    input.coherentFace.comp input.omega =
      input.coherentAction.comp input.coherentFace := by
  ext state
  rfl

/-- Measurement/q-rich face of the single joint action. -/
theorem measurementFace_omega (input : Input I H Q) :
    input.measurementFace.comp input.omega =
      input.measurementAction.comp input.measurementFace := by
  ext state
  rfl

/-- Failure of the original seed graph to be invariant under `Ω`. -/
def incidenceResidual (input : Input I H Q) (event : I) : input.Carrier :=
  input.omega (input.seedLift event) -
    input.seedLift (input.integralAction event)

@[simp] theorem incidenceResidual_integralFace
    (input : Input I H Q) (event : I) :
    input.integralFace (input.incidenceResidual event) = 0 := by
  simp [incidenceResidual, omega, seedLift, integralFace, ambientAction, seed]

@[simp] theorem incidenceResidual_coherentFace
    (input : Input I H Q) (event : I) :
    input.coherentFace (input.incidenceResidual event) =
      input.coherentAction (input.coherentRead event) -
        input.coherentRead (input.integralAction event) :=
  rfl

@[simp] theorem incidenceResidual_measurementFace
    (input : Input I H Q) (event : I) :
    input.measurementFace (input.incidenceResidual event) =
      input.measurementAction (input.measurementRead event) -
        input.measurementRead (input.integralAction event) :=
  rfl

/-- The old action--readout squares are exactly the zero fibre of one
source-generated incidence coordinate. -/
theorem incidenceResidual_eq_zero_iff
    (input : Input I H Q) (event : I) :
    input.incidenceResidual event = 0 ↔
      input.coherentAction (input.coherentRead event) =
          input.coherentRead (input.integralAction event) ∧
        input.measurementAction (input.measurementRead event) =
          input.measurementRead (input.integralAction event) := by
  constructor
  · intro residual_zero
    have coherent_zero := congrArg input.coherentFace residual_zero
    have measurement_zero := congrArg input.measurementFace residual_zero
    exact ⟨sub_eq_zero.mp (by simpa using coherent_zero),
      sub_eq_zero.mp (by simpa using measurement_zero)⟩
  · rintro ⟨coherent_commutes, measurement_commutes⟩
    apply Subtype.ext
    apply Prod.ext
    · simp [incidenceResidual, omega, seedLift, ambientAction, seed]
    · apply Prod.ext
      · simpa [incidenceResidual, omega, seedLift, ambientAction, seed]
          using sub_eq_zero.mpr coherent_commutes
      · simpa [incidenceResidual, omega, seedLift, ambientAction, seed]
          using sub_eq_zero.mpr measurement_commutes

theorem seedLift_injective (input : Input I H Q) :
    Function.Injective input.seedLift := by
  intro left right equality
  exact congrArg input.integralFace equality

/-- Universal property: every action-stable submodule containing the actual
seed contains the generated orbit carrier. -/
theorem carrier_minimal (input : Input I H Q)
    (candidate : Submodule ℤ input.Ambient)
    (containsSeed : ∀ event, input.seed event ∈ candidate)
    (stable : ∀ state, state ∈ candidate →
      input.ambientAction state ∈ candidate) :
    input.carrier ≤ candidate := by
  apply Submodule.span_le.mpr
  intro state state_mem
  rcases state_mem with ⟨⟨stage, event⟩, rfl⟩
  induction stage with
  | zero => simpa [orbitGenerator] using containsSeed event
  | succ stage ih =>
      simpa [orbitGenerator, pow_succ'] using stable _ ih

end Input
end
end SourceGeneratedIntegralCoherentJointAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
