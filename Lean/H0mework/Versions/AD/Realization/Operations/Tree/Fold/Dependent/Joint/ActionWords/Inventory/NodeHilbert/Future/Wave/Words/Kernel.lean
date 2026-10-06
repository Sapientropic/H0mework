import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Orbit.Consumer
import Lean.LibrarySuggestions.Basic
-- Keep complete root-indexed runtime signatures out of automatic suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceWordOrbit"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointActionWords
variable {L I H Q : Type u} [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]
structure Input (L I H Q : Type u) [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q] where
  integralAction : L → I →ₗ[ℤ] I
  coherentAction : L → H →ₗ[ℤ] H
  measurementAction : L → Q →ₗ[ℤ] Q
  coherentRead : I →ₗ[ℤ] H
  measurementRead : I →ₗ[ℤ] Q
namespace Input
abbrev Ambient (_input : Input L I H Q) := I × (H × Q)
def single (input : Input L I H Q) (letter : L) : SourceGeneratedIntegralCoherentJointAction.Input I H Q :=
  ⟨input.integralAction letter,input.coherentAction letter,input.measurementAction letter,input.coherentRead,input.measurementRead⟩
def ambientAction (input : Input L I H Q) (letter : L) : input.Ambient →ₗ[ℤ] input.Ambient :=
  (input.single letter).ambientAction.toAddMonoidHom.toIntLinearMap
def seed (input : Input L I H Q) : I →ₗ[ℤ] input.Ambient where
  toFun := fun event => (event,input.coherentRead event,input.measurementRead event)
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp
def generator (input : Input L I H Q) (index : List L × I) : input.Ambient :=
  SourceGeneratedActionWords.run input.ambientAction index.1 (input.seed index.2)
def carrier (input : Input L I H Q) : Submodule ℤ input.Ambient := Submodule.span ℤ (Set.range input.generator)
abbrev Carrier (input : Input L I H Q) := input.carrier
theorem seed_mem (input : Input L I H Q) (event : I) : input.seed event ∈ input.carrier :=
  Submodule.subset_span ⟨([],event),rfl⟩
theorem action_mem (input : Input L I H Q) (letter : L) {value : input.Ambient}
    (member : value ∈ input.carrier) : input.ambientAction letter value ∈ input.carrier := by
  refine Submodule.span_induction (p:=fun candidate _ => input.ambientAction letter candidate ∈ input.carrier) ?_ ?_ ?_ ?_ member
  · rintro _ ⟨⟨word,event⟩,rfl⟩
    apply Submodule.subset_span
    refine ⟨(word++[letter],event),?_⟩
    simp only [generator,SourceGeneratedActionWords.run_append,SourceGeneratedActionWords.run,one_mul]
    rfl
  · simp
  · intro left right _ _ hl hr; simpa using Submodule.add_mem _ hl hr
  · intro coefficient value _ hv; simpa using Submodule.smul_mem _ coefficient hv
def advance (input : Input L I H Q) (letter : L) : input.Carrier →ₗ[ℤ] input.Carrier where
  toFun := fun value => ⟨input.ambientAction letter value,input.action_mem letter value.2⟩
  map_add' := by intros; apply Subtype.ext; simp
  map_smul' := by intros; apply Subtype.ext; simp
def seedLift (input : Input L I H Q) : I →ₗ[ℤ] input.Carrier where
  toFun := fun event => ⟨input.seed event,input.seed_mem event⟩
  map_add' := by intros; apply Subtype.ext; simp
  map_smul' := by intros; apply Subtype.ext; simp
def integralFace (input : Input L I H Q) : input.Carrier →ₗ[ℤ] I where
  toFun := fun value => value.1.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
def coherentFace (input : Input L I H Q) : input.Carrier →ₗ[ℤ] H where
  toFun := fun value => value.1.2.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
def measurementFace (input : Input L I H Q) : input.Carrier →ₗ[ℤ] Q where
  toFun := fun value => value.1.2.2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
theorem integral_advance (input : Input L I H Q) (letter : L) (value : input.Carrier) :
    input.integralFace (input.advance letter value)=input.integralAction letter (input.integralFace value) := rfl
theorem coherent_advance (input : Input L I H Q) (letter : L) (value : input.Carrier) :
    input.coherentFace (input.advance letter value)=input.coherentAction letter (input.coherentFace value) := rfl
theorem measurement_advance (input : Input L I H Q) (letter : L) (value : input.Carrier) :
    input.measurementFace (input.advance letter value)=input.measurementAction letter (input.measurementFace value) := rfl
private theorem run_mem (input : Input L I H Q) (candidate : Submodule ℤ input.Ambient)
    (stable : ∀ letter value, value ∈ candidate → input.ambientAction letter value ∈ candidate)
    (word : List L) (value : input.Ambient) (member : value ∈ candidate) :
    SourceGeneratedActionWords.run input.ambientAction word value ∈ candidate := by
  induction word generalizing value with
  | nil => exact member
  | cons first rest previous => exact previous _ (stable first value member)
theorem carrier_minimal (input : Input L I H Q) (candidate : Submodule ℤ input.Ambient)
    (containsSeed : ∀ event, input.seed event ∈ candidate)
    (stable : ∀ letter value, value ∈ candidate → input.ambientAction letter value ∈ candidate) :
    input.carrier ≤ candidate := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨word,event⟩,rfl⟩
  exact run_mem input candidate stable word _ (containsSeed event)
theorem single_le (input : Input L I H Q) (letter : L) : (input.single letter).carrier ≤ input.carrier :=
  (input.single letter).carrier_minimal input.carrier (input.seed_mem) (fun _ member => input.action_mem letter member)
def singleInclusion (input : Input L I H Q) (letter : L) : (input.single letter).Carrier →ₗ[ℤ] input.Carrier :=
  Submodule.inclusion (input.single_le letter)
theorem single_seed (input : Input L I H Q) (letter : L) (event : I) :
    input.singleInclusion letter ((input.single letter).seedLift event)=input.seedLift event := rfl
theorem single_advance (input : Input L I H Q) (letter : L) (value : (input.single letter).Carrier) :
    input.singleInclusion letter ((input.single letter).omega value)=input.advance letter (input.singleInclusion letter value) := rfl
def incidence (input : Input L I H Q) (word : List L) (event : I) : input.Carrier :=
  SourceGeneratedActionWords.run input.advance word (input.seedLift event)-
    input.seedLift (SourceGeneratedActionWords.run input.integralAction word event)
theorem run_face {B : Type u} [AddCommGroup B] (input : Input L I H Q)
    (face : input.Carrier →ₗ[ℤ] B) (actions : L → B →ₗ[ℤ] B)
    (square : ∀ letter value, face (input.advance letter value)=actions letter (face value))
    (word : List L) (value : input.Carrier) :
    face (SourceGeneratedActionWords.run input.advance word value)=SourceGeneratedActionWords.run actions word (face value) := by
  induction word generalizing value with
  | nil => rfl
  | cons first rest previous => exact (previous (input.advance first value)).trans (congrArg (SourceGeneratedActionWords.run actions rest) (square first value))
theorem integral_word (input : Input L I H Q) (word : List L) (value : input.Carrier) :
    input.integralFace (SourceGeneratedActionWords.run input.advance word value)=SourceGeneratedActionWords.run input.integralAction word (input.integralFace value) :=
  run_face input input.integralFace input.integralAction input.integral_advance word value
theorem coherent_word (input : Input L I H Q) (word : List L) (value : input.Carrier) :
    input.coherentFace (SourceGeneratedActionWords.run input.advance word value)=SourceGeneratedActionWords.run input.coherentAction word (input.coherentFace value) :=
  run_face input input.coherentFace input.coherentAction input.coherent_advance word value
theorem measurement_word (input : Input L I H Q) (word : List L) (value : input.Carrier) :
    input.measurementFace (SourceGeneratedActionWords.run input.advance word value)=SourceGeneratedActionWords.run input.measurementAction word (input.measurementFace value) :=
  run_face input input.measurementFace input.measurementAction input.measurement_advance word value
theorem incidence_integral (input : Input L I H Q) (word : List L) (event : I) : input.integralFace (input.incidence word event)=0 := by
  rw [incidence,map_sub,integral_word]
  change SourceGeneratedActionWords.run input.integralAction word event-SourceGeneratedActionWords.run input.integralAction word event=0
  exact sub_self _
theorem incidence_coherent (input : Input L I H Q) (word : List L) (event : I) :
    input.coherentFace (input.incidence word event)=SourceGeneratedActionWords.run input.coherentAction word (input.coherentRead event)-input.coherentRead (SourceGeneratedActionWords.run input.integralAction word event) := by
  rw [incidence,map_sub,coherent_word]; rfl
theorem incidence_measurement (input : Input L I H Q) (word : List L) (event : I) :
    input.measurementFace (input.incidence word event)=SourceGeneratedActionWords.run input.measurementAction word (input.measurementRead event)-input.measurementRead (SourceGeneratedActionWords.run input.integralAction word event) := by
  rw [incidence,map_sub,measurement_word]; rfl
theorem single_incidence (input : Input L I H Q) (letter : L) (event : I) :
    input.singleInclusion letter ((input.single letter).incidenceResidual event)=input.incidence [letter] event := rfl
end Input
end SourceGeneratedJointActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
