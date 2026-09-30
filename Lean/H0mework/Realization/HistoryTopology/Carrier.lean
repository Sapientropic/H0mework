import H0mework.Realization.ScalarCofinal.KernelCompletion
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Topology.UniformSpace.Pi

/-! The existing module limit carries the uniformity of its discrete finite observations. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTopology

open CategoryTheory CategoryTheory.Limits SourceGeneratedScalarCofinalKernelCompletion

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {Carrier : Nat → Type u} [∀ stage, AddCommGroup (Carrier stage)]
variable [∀ stage, Module R (Carrier stage)]
variable (data : Data (R := R) (Generator := Generator) (Carrier := Carrier))
variable (compatible : data.Compatible)

abbrev Coordinates := (stage : Nat) → data.StageQuotient stage

def coordinates (value : data.Completion compatible) : Coordinates data :=
  fun stage => data.restriction compatible stage value

def Coherent (family : Coordinates data) : Prop :=
  ∀ stage, data.quotientTransition compatible stage (family (stage + 1)) = family stage

theorem coordinates_injective : Function.Injective (coordinates data compatible) := by
  intro left right equality
  apply Concrete.limit_ext (data.quotientTower compatible) left right
  intro stage
  exact congrFun equality stage.unop

theorem coordinates_source (value : Generator) :
    coordinates data compatible (data.completionMap compatible value) =
      fun stage => data.quotientMap stage value := by
  funext stage
  exact ConcreteCategory.congr_hom (data.completionMap_restriction compatible stage) value

theorem coordinates_coherent (value : data.Completion compatible) :
    Coherent data compatible (coordinates data compatible value) := by
  intro stage
  have equation := ConcreteCategory.congr_hom
    (limit.w (data.quotientTower compatible) (homOfLE (Nat.le_add_right stage 1)).op) value
  simp only [Data.quotientTower, Functor.ofOpSequence_map_homOfLE_succ] at equation
  exact equation

private def sectionsEquiv : data.Completion compatible ≃
    (data.quotientTower compatible ⋙ forget (ModuleCat R)).sections :=
  Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat R)) (limit.isLimit (data.quotientTower compatible)))

private def coherentSection (family : Coordinates data) (coherent : Coherent data compatible family) :
    (data.quotientTower compatible ⋙ forget (ModuleCat R)).sections :=
  Types.sectionOfCone
    { pt := PUnit
      π := NatTrans.ofOpSequence
        (fun stage => ↾fun _ => family stage)
        (fun stage => by
          ext point
          simp only [Functor.const_obj_map, Functor.comp_map, Data.quotientTower,
            Functor.ofOpSequence_map_homOfLE_succ]
          change family stage = data.quotientTransition compatible stage (family (stage + 1))
          exact (coherent stage).symm) } PUnit.unit

theorem range_coordinates : Set.range (coordinates data compatible) =
    {family | Coherent data compatible family} := by
  ext family
  constructor
  · rintro ⟨value, rfl⟩
    exact coordinates_coherent data compatible value
  · intro coherent
    refine ⟨(sectionsEquiv data compatible).symm
      (coherentSection data compatible family coherent), ?_⟩
    funext stage
    exact congrArg (fun sectionValue => sectionValue.val (Opposite.op stage))
      ((sectionsEquiv data compatible).apply_symm_apply
        (coherentSection data compatible family coherent))

@[instance_reducible] def stageUniform (stage : Nat) : UniformSpace (data.StageQuotient stage) := ⊥

@[instance_reducible] def coordinateUniform : UniformSpace (Coordinates data) :=
  letI : ∀ stage, UniformSpace (data.StageQuotient stage) := stageUniform data
  Pi.uniformSpace _

@[instance_reducible] def observationUniform : UniformSpace (data.Completion compatible) :=
  UniformSpace.comap (coordinates data compatible) (coordinateUniform data)

theorem coordinates_isUniformEmbedding :
    @IsUniformEmbedding _ _ (observationUniform data compatible) (coordinateUniform data)
      (coordinates data compatible) :=
  @isUniformEmbedding_comap _ _ _ (coordinateUniform data) (coordinates_injective data compatible)

theorem coordinates_isClosed :
    @IsClosed _ (coordinateUniform data).toTopologicalSpace
      (Set.range (coordinates data compatible)) := by
  let : ∀ stage, UniformSpace (data.StageQuotient stage) := stageUniform data
  change IsClosed (Set.range (coordinates data compatible))
  rw [range_coordinates]
  change IsClosed {family : Coordinates data |
    ∀ stage, data.quotientTransition compatible stage (family (stage + 1)) = family stage}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro stage
  apply isClosed_eq
  · exact continuous_of_discreteTopology.comp (continuous_apply (stage + 1))
  · exact continuous_apply stage

theorem completion_complete :
    @CompleteSpace _ (observationUniform data compatible) := by
  let : ∀ stage, UniformSpace (data.StageQuotient stage) := stageUniform data
  let : UniformSpace (data.Completion compatible) := observationUniform data compatible
  exact (coordinates_isUniformEmbedding data compatible).isUniformInducing.completeSpace
    (coordinates_isClosed data compatible).isComplete

end
end SourceGeneratedScalarCofinalTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
