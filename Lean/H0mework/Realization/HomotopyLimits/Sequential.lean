import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Root-generated sequential homotopy limits

An inverse tower of cochain complexes is not faithfully represented by its
ordinary strict limit when the actual states commute only up to homotopy.
For one shared root/tower occurrence this kernel generates the standard
mapping-cocone model

`holim F = Fib(1 - shift : ∏ F n ⟶ ∏ F n)`.

The product, shift, difference, mapping cocone and derived-zero coherence are
all calculated by the framework.  The mouth accepts no completed limit,
compatible family, homotopy, residual-zero receipt or determinant.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SequentialHomotopyLimit

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe w

attribute [local instance] HasDerivedCategory.standard

abbrev IntegralCochainComplex :=
  CochainComplex (ModuleCat.{0} ℤ) ℤ

/-- One exact root and one actual inverse tower in a shared occurrence tree. -/
structure RootGeneratedSequentialHomotopyLimitAt
    {Root : Type w}
    (dependentOccurrence : RootedAccountedUnfolding
      (Root × (ℕᵒᵖ ⥤ IntegralCochainComplex))) : Type w where
  private mk ::

namespace RootGeneratedSequentialHomotopyLimitAt

variable {Root : Type w}
variable {dependentOccurrence : RootedAccountedUnfolding
  (Root × (ℕᵒᵖ ⥤ IntegralCochainComplex))}

def generate : RootGeneratedSequentialHomotopyLimitAt
    dependentOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    RootedAccountedUnfolding Root :=
  dependentOccurrence.map Prod.fst

def actualTower
    (_face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    ℕᵒᵖ ⥤ IntegralCochainComplex :=
  dependentOccurrence.root.2

abbrev towerObject
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) : IntegralCochainComplex :=
  face.actualTower.obj (Opposite.op stage)

/-- Product of all actual stages.  This carrier is reducible so downstream
generic transport kernels see the same canonical product rather than an
opaque comparison boundary. -/
@[reducible] noncomputable def productComplex
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    IntegralCochainComplex :=
  ∏ᶜ (fun stage : Nat ↦ face.towerObject stage)

noncomputable def productProjection
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    face.productComplex ⟶ face.towerObject stage :=
  Pi.π (fun current : Nat ↦ face.towerObject current) stage

/-- Degreewise comparison between the product complex and the categorical
product of the actual degree carriers. -/
noncomputable def productXIso
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (degree : ℤ) :
    face.productComplex.X degree ≅
      ∏ᶜ (fun stage : Nat ↦ (face.towerObject stage).X degree) :=
  preservesLimitIso
    (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℤ) degree)
    (Discrete.functor fun stage : Nat ↦ face.towerObject stage) ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] theorem productXIso_inv_comp_projection
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (degree : ℤ) (stage : Nat) :
    (face.productXIso degree).inv ≫
        (face.productProjection stage).f degree =
      Pi.π (fun current : Nat ↦
        (face.towerObject current).X degree) stage := by
  let E := HomologicalComplex.eval
    (ModuleCat ℤ) (ComplexShape.up ℤ) degree
  let family := fun current : Nat ↦ face.towerObject current
  let F := Discrete.functor family
  let comparison := Discrete.compNatIsoDiscrete family E
  have first :
      (preservesLimitIso E F).inv ≫
          (Pi.π family stage).f degree =
        limit.π (F ⋙ E) (Discrete.mk stage) := by
    simpa only [E, F, family, HomologicalComplex.eval_map] using
      (preservesLimitIso_inv_π E F (Discrete.mk stage))
  dsimp only [productXIso, productProjection]
  rw [Iso.trans_inv, Category.assoc, first]
  rw [HasLimit.isoOfNatIso_inv_π]
  simp [Discrete.compNatIsoDiscrete]
  rfl

@[reassoc (attr := simp)] theorem productXIso_hom_comp_π
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (degree : ℤ) (stage : Nat) :
    (face.productXIso degree).hom ≫
        Pi.π (fun current : Nat ↦
          (face.towerObject current).X degree) stage =
      (face.productProjection stage).f degree := by
  have inverse := face.productXIso_inv_comp_projection degree stage
  calc
    _ = (face.productXIso degree).hom ≫
        ((face.productXIso degree).inv ≫
          (face.productProjection stage).f degree) :=
      congrArg (fun arrow => (face.productXIso degree).hom ≫ arrow)
        inverse.symm
    _ = _ := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Actual adjacent inverse-tower arrow. -/
noncomputable def transitionAt
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    face.towerObject (stage + 1) ⟶ face.towerObject stage :=
  face.actualTower.map (homOfLE (Nat.le_add_right stage 1)).op

noncomputable def shiftComponent
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    face.productComplex ⟶ face.towerObject stage :=
  face.productProjection (stage + 1) ≫ face.transitionAt stage

/-- Shift of compatible coordinates generated from the actual tower maps. -/
noncomputable def shift
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    face.productComplex ⟶ face.productComplex :=
  Pi.lift (face.shiftComponent)

@[reassoc (attr := simp)] theorem shift_projection
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    face.shift ≫ face.productProjection stage =
      face.shiftComponent stage :=
  Pi.lift_π _ stage

/-- The universal compatibility residual `1 - shift`. -/
noncomputable def difference
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    face.productComplex ⟶ face.productComplex :=
  𝟙 face.productComplex - face.shift

theorem difference_projection
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    face.difference ≫ face.productProjection stage =
      face.productProjection stage - face.shiftComponent stage := by
  simp [difference]

/-- Framework-generated homotopy-limit carrier. -/
@[reducible] noncomputable def homotopyLimit
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    IntegralCochainComplex :=
  CochainComplex.mappingCocone face.difference

/-- Raw stage restriction from the generated homotopy limit. -/
noncomputable def restriction
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    face.homotopyLimit ⟶ face.towerObject stage :=
  CochainComplex.mappingCocone.fst face.difference ≫
    face.productProjection stage

theorem restriction_eq
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    face.restriction stage =
      CochainComplex.mappingCocone.fst face.difference ≫
        face.productProjection stage :=
  rfl

/-- The mapping-cocone triangle in the derived category. -/
noncomputable def derivedTriangle
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    Triangle (DerivedCategory (ModuleCat.{0} ℤ)) :=
  DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle face.difference)

theorem derivedTriangle_distinguished
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    face.derivedTriangle ∈ distTriang
      (DerivedCategory (ModuleCat.{0} ℤ)) :=
  DerivedCategory.mappingCocone_triangle_distinguished face.difference

/-- Canonical derived coherence: the product restriction of the homotopy
limit has zero `1 - shift` residual. -/
theorem derivedDifference_zero
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence) :
    DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst face.difference) ≫
        DerivedCategory.Q.map face.difference = 0 := by
  change face.derivedTriangle.mor₁ ≫ face.derivedTriangle.mor₂ = 0
  exact comp_distTriang_mor_zero₁₂ face.derivedTriangle
    face.derivedTriangle_distinguished

/-- Every adjacent restriction commutes in the derived category.  Strict
equality is neither assumed nor required; it is generated by the
mapping-cocone residual. -/
theorem derivedRestriction_naturality
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    DerivedCategory.Q.map (face.restriction (stage + 1)) ≫
        DerivedCategory.Q.map (face.transitionAt stage) =
      DerivedCategory.Q.map (face.restriction stage) := by
  have zeroPost := congrArg
    (fun arrow => arrow ≫
      DerivedCategory.Q.map (face.productProjection stage))
    face.derivedDifference_zero
  simp only [zero_comp] at zeroPost
  rw [Category.assoc, ← Functor.map_comp,
    face.difference_projection] at zeroPost
  simp only [Functor.map_sub, Preadditive.comp_sub] at zeroPost
  have equality := sub_eq_zero.mp zeroPost
  change DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst face.difference) ≫
        DerivedCategory.Q.map (face.productProjection stage) =
      DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst face.difference) ≫
        DerivedCategory.Q.map
          (face.productProjection (stage + 1) ≫ face.transitionAt stage)
      at equality
  rw [Functor.map_comp] at equality
  change DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst face.difference ≫
            face.productProjection (stage + 1)) ≫
        DerivedCategory.Q.map (face.transitionAt stage) =
      DerivedCategory.Q.map
        (CochainComplex.mappingCocone.fst face.difference ≫
          face.productProjection stage)
  rw [Functor.map_comp, Functor.map_comp]
  exact (Category.assoc _ _ _).trans equality.symm

theorem preserves_shared_root_and_actual_tower
    (face : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (stage : Nat) :
    face.root = dependentOccurrence.map Prod.fst ∧
      face.root.root = dependentOccurrence.root.1 ∧
      face.actualTower = dependentOccurrence.root.2 ∧
      face.towerObject stage =
        dependentOccurrence.root.2.obj (Opposite.op stage) ∧
      face.transitionAt stage =
        dependentOccurrence.root.2.map
          (homOfLE (Nat.le_add_right stage 1)).op :=
  ⟨rfl, RootedAccountedUnfolding.root_map _ _, rfl, rfl, rfl⟩

end RootGeneratedSequentialHomotopyLimitAt

end

end SequentialHomotopyLimit
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
