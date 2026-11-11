import H0mework.Realization.JointState.ActionOccurrence

/-!
# Naturality of the source-generated joint action orbit

A morphism contains only the three actual face maps and their source/action
squares.  It induces a map of the minimal orbit carriers, preserving the
seed, the single action, all three projections and the joint incidence
residual.  Identity and composition are literal, so dependent faces cannot
acquire a second transport law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralCoherentJointAction

noncomputable section

universe i h q i' h' q' i'' h'' q''

variable {I : Type i} {H : Type h} {Q : Type q}
variable {I' : Type i'} {H' : Type h'} {Q' : Type q'}
variable {I'' : Type i''} {H'' : Type h''} {Q'' : Type q''}
variable [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]
variable [AddCommGroup I'] [AddCommGroup H'] [AddCommGroup Q']
variable [AddCommGroup I''] [AddCommGroup H''] [AddCommGroup Q'']

/-- Actual maps between two joint-action inputs.  No carrier map or residual
verdict is supplied by the caller. -/
structure Morphism (input : Input I H Q) (target : Input I' H' Q') where
  integralMap : I →ₗ[ℤ] I'
  coherentMap : H →ₗ[ℤ] H'
  measurementMap : Q →ₗ[ℤ] Q'
  integral_natural : integralMap.comp input.integralAction =
    target.integralAction.comp integralMap
  coherent_natural : coherentMap.comp input.coherentAction =
    target.coherentAction.comp coherentMap
  measurement_natural : measurementMap.comp input.measurementAction =
    target.measurementAction.comp measurementMap
  coherent_read_natural : coherentMap.comp input.coherentRead =
    target.coherentRead.comp integralMap
  measurement_read_natural : measurementMap.comp input.measurementRead =
    target.measurementRead.comp integralMap

namespace Morphism

variable {input : Input I H Q} {target : Input I' H' Q'}

def ambientMap (morphism : Morphism input target) :
    input.Ambient →ₗ[ℤ] target.Ambient where
  toFun := fun state =>
    ⟨morphism.integralMap state.1,
      morphism.coherentMap state.2.1,
      morphism.measurementMap state.2.2⟩
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro coefficient state
    ext <;> simp

theorem ambientMap_seed (morphism : Morphism input target) :
    morphism.ambientMap.comp input.seed =
      target.seed.comp morphism.integralMap := by
  apply LinearMap.ext
  intro event
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact LinearMap.congr_fun morphism.coherent_read_natural event
    · exact LinearMap.congr_fun morphism.measurement_read_natural event

theorem ambientMap_action (morphism : Morphism input target) :
    morphism.ambientMap.comp input.ambientAction =
      target.ambientAction.comp morphism.ambientMap := by
  apply LinearMap.ext
  intro state
  apply Prod.ext
  · exact LinearMap.congr_fun morphism.integral_natural state.1
  · apply Prod.ext
    · exact LinearMap.congr_fun morphism.coherent_natural state.2.1
    · exact LinearMap.congr_fun morphism.measurement_natural state.2.2

theorem ambientMap_orbitGenerator (morphism : Morphism input target)
    (stage : Nat) (event : I) :
    morphism.ambientMap (input.orbitGenerator (stage, event)) =
      target.orbitGenerator (stage, morphism.integralMap event) := by
  induction stage with
  | zero =>
      exact LinearMap.congr_fun morphism.ambientMap_seed event
  | succ stage ih =>
      simp only [Input.orbitGenerator, pow_succ', Module.End.mul_apply]
      rw [← LinearMap.comp_apply, morphism.ambientMap_action,
        LinearMap.comp_apply]
      exact congrArg target.ambientAction
        (by simpa [Input.orbitGenerator] using ih)

theorem ambientMap_mem_carrier (morphism : Morphism input target)
    {state : input.Ambient} (state_mem : state ∈ input.carrier) :
    morphism.ambientMap state ∈ target.carrier := by
  refine Submodule.span_induction (p := fun candidate _ =>
      morphism.ambientMap candidate ∈ target.carrier)
    ?_ ?_ ?_ ?_ state_mem
  · intro orbit orbit_mem
    rcases orbit_mem with ⟨⟨stage, event⟩, rfl⟩
    rw [morphism.ambientMap_orbitGenerator]
    apply Submodule.subset_span
    exact ⟨⟨stage, morphism.integralMap event⟩, rfl⟩
  · simp
  · intro left right _ _ left_mem right_mem
    simpa using Submodule.add_mem _ left_mem right_mem
  · intro coefficient state _ mapped_mem
    simpa using Submodule.smul_mem _ coefficient mapped_mem

/-- The source morphism induces the carrier map; it is never caller data. -/
def carrierMap (morphism : Morphism input target) :
    input.Carrier →ₗ[ℤ] target.Carrier where
  toFun := fun state =>
    ⟨morphism.ambientMap state, morphism.ambientMap_mem_carrier state.2⟩
  map_add' := by
    intro left right
    apply Subtype.ext
    simp
  map_smul' := by
    intro coefficient state
    apply Subtype.ext
    simp

@[simp] theorem carrierMap_seedLift (morphism : Morphism input target) :
    morphism.carrierMap.comp input.seedLift =
      target.seedLift.comp morphism.integralMap := by
  apply LinearMap.ext
  intro event
  apply Subtype.ext
  exact LinearMap.congr_fun morphism.ambientMap_seed event

theorem carrierMap_omega (morphism : Morphism input target) :
    morphism.carrierMap.comp input.omega =
      target.omega.comp morphism.carrierMap := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  exact LinearMap.congr_fun morphism.ambientMap_action state

@[simp] theorem integralFace_carrierMap (morphism : Morphism input target) :
    target.integralFace.comp morphism.carrierMap =
      morphism.integralMap.comp input.integralFace := by
  ext state
  rfl

@[simp] theorem coherentFace_carrierMap (morphism : Morphism input target) :
    target.coherentFace.comp morphism.carrierMap =
      morphism.coherentMap.comp input.coherentFace := by
  ext state
  rfl

@[simp] theorem measurementFace_carrierMap (morphism : Morphism input target) :
    target.measurementFace.comp morphism.carrierMap =
      morphism.measurementMap.comp input.measurementFace := by
  ext state
  rfl

/-- The one incidence residual transports with the integral source event. -/
theorem carrierMap_incidenceResidual (morphism : Morphism input target)
    (event : I) :
    morphism.carrierMap (input.incidenceResidual event) =
      target.incidenceResidual (morphism.integralMap event) := by
  rw [Input.incidenceResidual, Input.incidenceResidual, map_sub]
  rw [show morphism.carrierMap (input.omega (input.seedLift event)) =
      target.omega (morphism.carrierMap (input.seedLift event)) from
    LinearMap.congr_fun morphism.carrierMap_omega (input.seedLift event)]
  rw [show morphism.carrierMap (input.seedLift event) =
      target.seedLift (morphism.integralMap event) from
    LinearMap.congr_fun morphism.carrierMap_seedLift event]
  rw [show morphism.carrierMap
        (input.seedLift (input.integralAction event)) =
      target.seedLift
        (morphism.integralMap (input.integralAction event)) from
    LinearMap.congr_fun morphism.carrierMap_seedLift
      (input.integralAction event)]
  rw [show morphism.integralMap (input.integralAction event) =
      target.integralAction (morphism.integralMap event) from
    LinearMap.congr_fun morphism.integral_natural event]

/-- The complete accounted joint occurrence is natural, not only its root. -/
theorem jointOccurrence_natural (morphism : Morphism input target)
    (occurrence : RootedAccountedUnfolding I) :
    (input.jointOccurrence occurrence).map morphism.carrierMap =
      target.jointOccurrence (occurrence.map morphism.integralMap) := by
  rw [Input.jointOccurrence, RootedAccountedUnfolding.map_map,
    Input.jointOccurrence, RootedAccountedUnfolding.map_map]
  apply congrArg (fun transform : I → target.Carrier =>
    occurrence.map transform)
  funext event
  exact LinearMap.congr_fun morphism.carrierMap_seedLift event

/-- The residual face transports in the same accounted tree. -/
theorem residualOccurrence_natural (morphism : Morphism input target)
    (occurrence : RootedAccountedUnfolding I) :
    (input.residualOccurrence occurrence).map morphism.carrierMap =
      target.residualOccurrence (occurrence.map morphism.integralMap) := by
  rw [Input.residualOccurrence, RootedAccountedUnfolding.map_map,
    Input.residualOccurrence, RootedAccountedUnfolding.map_map]
  apply congrArg (fun transform : I → target.Carrier =>
    occurrence.map transform)
  funext event
  exact morphism.carrierMap_incidenceResidual event

def id (input : Input I H Q) : Morphism input input where
  integralMap := LinearMap.id
  coherentMap := LinearMap.id
  measurementMap := LinearMap.id
  integral_natural := rfl
  coherent_natural := rfl
  measurement_natural := rfl
  coherent_read_natural := rfl
  measurement_read_natural := rfl

def comp {final : Input I'' H'' Q''}
    (second : Morphism target final) (first : Morphism input target) :
    Morphism input final where
  integralMap := second.integralMap.comp first.integralMap
  coherentMap := second.coherentMap.comp first.coherentMap
  measurementMap := second.measurementMap.comp first.measurementMap
  integral_natural := by
    rw [LinearMap.comp_assoc, first.integral_natural,
      ← LinearMap.comp_assoc, second.integral_natural, LinearMap.comp_assoc]
  coherent_natural := by
    rw [LinearMap.comp_assoc, first.coherent_natural,
      ← LinearMap.comp_assoc, second.coherent_natural, LinearMap.comp_assoc]
  measurement_natural := by
    rw [LinearMap.comp_assoc, first.measurement_natural,
      ← LinearMap.comp_assoc, second.measurement_natural, LinearMap.comp_assoc]
  coherent_read_natural := by
    rw [LinearMap.comp_assoc, first.coherent_read_natural,
      ← LinearMap.comp_assoc, second.coherent_read_natural, LinearMap.comp_assoc]
  measurement_read_natural := by
    rw [LinearMap.comp_assoc, first.measurement_read_natural,
      ← LinearMap.comp_assoc, second.measurement_read_natural, LinearMap.comp_assoc]

@[simp] theorem carrierMap_id (input : Input I H Q) :
    (id input).carrierMap = LinearMap.id := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  rfl

@[simp] theorem carrierMap_comp {final : Input I'' H'' Q''}
    (second : Morphism target final) (first : Morphism input target) :
    (comp second first).carrierMap =
      second.carrierMap.comp first.carrierMap := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  rfl

end Morphism

end

end SourceGeneratedIntegralCoherentJointAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
