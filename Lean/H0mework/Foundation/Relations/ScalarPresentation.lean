import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Scalar-polymorphic source relation presentation

For an actual `R`-module `G`, every point is a free generator.  The source
module law generates both addition relations

`[x] + [y] - [x + y]`

and scalar relations

`[r • x] - r • [x]`.

Their quotient is canonically `R`-linearly equivalent to `G`.  The scalar
relations are essential: addition relations alone would recover only the
underlying additive group and would silently privilege `ℤ`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ScalarRelationPresentation

noncomputable section

universe r u v w

variable {R : Type r} [CommRing R]
variable (G : Type u) [AddCommGroup G] [Module R G]

abbrev RelationIndex (R : Type r) [CommRing R]
    (G : Type u) [AddCommGroup G] [Module R G] :=
  (G × G) ⊕ (R × G)

/-- Evaluate the free `R`-module on the actual source carrier. -/
def freeEvaluation : (G →₀ R) →ₗ[R] G :=
  Finsupp.linearCombination R id

@[simp] theorem freeEvaluation_single (point : G) (coefficient : R) :
    freeEvaluation (R := R) G (Finsupp.single point coefficient) =
      coefficient • point := by
  simp [freeEvaluation]

def additionRelation (pair : G × G) : G →₀ R :=
  Finsupp.single pair.1 1 + Finsupp.single pair.2 1 -
    Finsupp.single (pair.1 + pair.2) 1

def scalarRelation (entry : R × G) : G →₀ R :=
  Finsupp.single (entry.1 • entry.2) 1 -
    entry.1 • Finsupp.single entry.2 1

def relation : RelationIndex R G → G →₀ R
  | .inl pair => additionRelation G pair
  | .inr entry => scalarRelation G entry

/-- The complete source-generated module-relation map. -/
def relationMap : (RelationIndex R G →₀ R) →ₗ[R] (G →₀ R) :=
  Finsupp.linearCombination R (relation (R := R) G)

@[simp] theorem relationMap_single
    (index : RelationIndex R G) (coefficient : R) :
    relationMap (R := R) G (Finsupp.single index coefficient) =
      coefficient • relation (R := R) G index := by
  simp [relationMap]

@[simp] theorem freeEvaluation_additionRelation (pair : G × G) :
    freeEvaluation (R := R) G (additionRelation (R := R) G pair) = 0 := by
  simp [freeEvaluation, additionRelation]

@[simp] theorem freeEvaluation_scalarRelation (entry : R × G) :
    freeEvaluation (R := R) G (scalarRelation (R := R) G entry) = 0 := by
  simp [freeEvaluation, scalarRelation]

@[simp] theorem freeEvaluation_relation
    (index : RelationIndex R G) :
    freeEvaluation (R := R) G (relation (R := R) G index) = 0 := by
  cases index with
  | inl pair => exact freeEvaluation_additionRelation (R := R) G pair
  | inr entry => exact freeEvaluation_scalarRelation (R := R) G entry

theorem relationRange_le_kernel :
    LinearMap.range (relationMap (R := R) G) ≤
      LinearMap.ker (freeEvaluation (R := R) G) := by
  rw [LinearMap.range_le_ker_iff]
  ext index
  simp

abbrev PresentedCarrier (R : Type r) [CommRing R]
    (G : Type u) [AddCommGroup G] [Module R G] :=
  (G →₀ R) ⧸ LinearMap.range (relationMap (R := R) G)

def presentedEvaluation : PresentedCarrier R G →ₗ[R] G :=
  Submodule.liftQ (LinearMap.range (relationMap (R := R) G))
    (freeEvaluation (R := R) G) (relationRange_le_kernel (R := R) G)

@[simp] theorem presentedEvaluation_mk (value : G →₀ R) :
    presentedEvaluation (R := R) G (Submodule.Quotient.mk value) =
      freeEvaluation (R := R) G value :=
  rfl

def presentedGenerator (point : G) : PresentedCarrier R G :=
  Submodule.Quotient.mk (Finsupp.single point 1)

@[simp] theorem presentedGenerator_add (left right : G) :
    presentedGenerator (R := R) G (left + right) =
      presentedGenerator (R := R) G left +
        presentedGenerator (R := R) G right := by
  apply (Submodule.Quotient.eq _).2
  change Finsupp.single (left + right) 1 -
      (Finsupp.single left 1 + Finsupp.single right 1) ∈
        LinearMap.range (relationMap (R := R) G)
  refine ⟨-Finsupp.single (Sum.inl (left, right)) 1, ?_⟩
  simp [relationMap, relation, additionRelation]

@[simp] theorem presentedGenerator_zero :
    presentedGenerator (R := R) G 0 = 0 := by
  have additive := presentedGenerator_add (R := R) G 0 0
  apply add_left_cancel (a := presentedGenerator (R := R) G 0)
  simpa using additive.symm

@[simp] theorem presentedGenerator_smul (scalar : R) (point : G) :
    presentedGenerator (R := R) G (scalar • point) =
      scalar • presentedGenerator (R := R) G point := by
  apply (Submodule.Quotient.eq _).2
  change Finsupp.single (scalar • point) 1 -
      scalar • Finsupp.single point 1 ∈
        LinearMap.range (relationMap (R := R) G)
  refine ⟨Finsupp.single (Sum.inr (scalar, point)) 1, ?_⟩
  simp [relationMap, relation, scalarRelation]

def presentedGeneratorMap : G →ₗ[R] PresentedCarrier R G where
  toFun := presentedGenerator (R := R) G
  map_add' := presentedGenerator_add (R := R) G
  map_smul' := presentedGenerator_smul (R := R) G

@[simp] theorem presentedEvaluation_generator (point : G) :
    presentedEvaluation (R := R) G
        (presentedGenerator (R := R) G point) = point := by
  simp [presentedGenerator]

private theorem presentedGenerator_evaluation_mk
    (representative : G →₀ R) :
    presentedGeneratorMap (R := R) G
        (presentedEvaluation (R := R) G
          (Submodule.Quotient.mk representative)) =
      Submodule.Quotient.mk representative := by
  induction representative using Finsupp.induction_linear with
  | zero => simp
  | add left right left_ih right_ih =>
      have left_ih' : presentedGeneratorMap (R := R) G
          (freeEvaluation (R := R) G left) =
          Submodule.Quotient.mk left := by
        simpa using left_ih
      have right_ih' : presentedGeneratorMap (R := R) G
          (freeEvaluation (R := R) G right) =
          Submodule.Quotient.mk right := by
        simpa using right_ih
      rw [presentedEvaluation_mk, map_add, map_add,
        Submodule.Quotient.mk_add, left_ih', right_ih']
  | single point coefficient =>
      rw [presentedEvaluation_mk, freeEvaluation_single, map_smul]
      change coefficient • Submodule.Quotient.mk
          (Finsupp.single point 1) = _
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      simp

theorem presentedGenerator_evaluation (value : PresentedCarrier R G) :
    presentedGeneratorMap (R := R) G
        (presentedEvaluation (R := R) G value) = value := by
  exact Submodule.Quotient.induction_on _ value
    (presentedGenerator_evaluation_mk (R := R) G)

/-- Canonical linear identification generated by the complete module law. -/
def presentedEquiv : PresentedCarrier R G ≃ₗ[R] G where
  toFun := presentedEvaluation (R := R) G
  invFun := presentedGeneratorMap (R := R) G
  left_inv := presentedGenerator_evaluation (R := R) G
  right_inv := presentedEvaluation_generator (R := R) G
  map_add' := map_add _
  map_smul' := map_smul _

/-! ## Naturality for actual source-linear maps -/

variable {G : Type u} {H : Type v}
variable [AddCommGroup G] [Module R G]
variable [AddCommGroup H] [Module R H]

def generatorMap (hom : G →ₗ[R] H) : (G →₀ R) →ₗ[R] (H →₀ R) :=
  Finsupp.lmapDomain R R hom

def relationIndexMap (hom : G →ₗ[R] H) :
    RelationIndex R G → RelationIndex R H
  | .inl pair => .inl (hom pair.1, hom pair.2)
  | .inr entry => .inr (entry.1, hom entry.2)

def relationGeneratorMap (hom : G →ₗ[R] H) :
    (RelationIndex R G →₀ R) →ₗ[R] (RelationIndex R H →₀ R) :=
  Finsupp.lmapDomain R R (relationIndexMap hom)

@[simp] theorem generatorMap_single
    (hom : G →ₗ[R] H) (point : G) (coefficient : R) :
    generatorMap hom (Finsupp.single point coefficient) =
      Finsupp.single (hom point) coefficient := by
  simp [generatorMap, Finsupp.lmapDomain_apply]

@[simp] theorem relationGeneratorMap_single
    (hom : G →ₗ[R] H) (index : RelationIndex R G) (coefficient : R) :
    relationGeneratorMap hom (Finsupp.single index coefficient) =
      Finsupp.single (relationIndexMap hom index) coefficient := by
  simp [relationGeneratorMap, Finsupp.lmapDomain_apply]

theorem relationMap_naturality (hom : G →ₗ[R] H) :
    (generatorMap hom).comp (relationMap G) =
      (relationMap H).comp (relationGeneratorMap hom) := by
  ext index coefficient
  cases index with
  | inl pair =>
      simp [LinearMap.comp_apply, relation, additionRelation,
        generatorMap, relationGeneratorMap, relationIndexMap,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_add,
        Finsupp.mapDomain_sub]
  | inr entry =>
      simp [LinearMap.comp_apply, relation, scalarRelation,
        generatorMap, relationGeneratorMap, relationIndexMap,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub]

theorem freeEvaluation_naturality (hom : G →ₗ[R] H) :
    (freeEvaluation (R := R) H).comp (generatorMap hom) =
      hom.comp (freeEvaluation (R := R) G) := by
  ext point
  simp

theorem relationRange_maps (hom : G →ₗ[R] H) :
    LinearMap.range (relationMap (R := R) G) ≤
      (LinearMap.range (relationMap (R := R) H)).comap (generatorMap hom) := by
  intro relationValue relation_mem
  rcases relation_mem with ⟨source, rfl⟩
  change generatorMap hom (relationMap (R := R) G source) ∈
    LinearMap.range (relationMap (R := R) H)
  rw [← LinearMap.comp_apply, relationMap_naturality,
    LinearMap.comp_apply]
  exact ⟨relationGeneratorMap hom source, rfl⟩

def presentedMap (hom : G →ₗ[R] H) :
    PresentedCarrier R G →ₗ[R] PresentedCarrier R H :=
  Submodule.mapQ (LinearMap.range (relationMap (R := R) G))
    (LinearMap.range (relationMap (R := R) H))
    (generatorMap hom) (relationRange_maps hom)

theorem presentedMap_commutes (hom : G →ₗ[R] H)
    (value : PresentedCarrier R G) :
    presentedEquiv (R := R) H (presentedMap hom value) =
      hom (presentedEquiv (R := R) G value) := by
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change freeEvaluation (R := R) H (generatorMap hom representative) =
    hom (freeEvaluation (R := R) G representative)
  exact LinearMap.congr_fun (freeEvaluation_naturality hom) representative

/-! ## Source-generated first syzygy -/

variable {K : Type*} [AddCommGroup K] [Module R K]

def zeroRelationLift (Source Target : Type*)
    [AddCommGroup Target] [Module R Target] :
    (Source →₀ R) →ₗ[R] (RelationIndex R Target →₀ R) :=
  Finsupp.lmapDomain R R (fun _ : Source => Sum.inl (0, 0))

@[simp] theorem zeroRelationLift_single
    (Source Target : Type*) [AddCommGroup Target] [Module R Target]
    (source : Source) (coefficient : R) :
    zeroRelationLift (R := R) Source Target
        (Finsupp.single source coefficient) =
      Finsupp.single (Sum.inl (0, 0)) coefficient := by
  simp [zeroRelationLift, Finsupp.lmapDomain_apply]

theorem generatorMap_comp_factorizes_through_zeroRelation
    (first : G →ₗ[R] H) (second : H →ₗ[R] K)
    (comp_zero : second.comp first = 0) :
    (generatorMap second).comp (generatorMap first) =
      (relationMap (R := R) K).comp (zeroRelationLift (R := R) G K) := by
  ext point coefficient
  have point_zero : second (first point) = 0 := by
    exact DFunLike.congr_fun comp_zero point
  simp [LinearMap.comp_apply, point_zero, relation,
    additionRelation]

/-! ## Exact-root wrapper -/

structure RootFace
    {Root : Type w} (rootOccurrence : RootedAccountedUnfolding Root) where
  private mk ::
  relationOccurrence :
    RootedAccountedUnfolding
      ((RelationIndex R G →₀ R) →ₗ[R] (G →₀ R))
  relationOccurrence_eq : relationOccurrence =
    rootOccurrence.map (fun _ => relationMap (R := R) G)

namespace RootFace

def generate {Root : Type w}
    (rootOccurrence : RootedAccountedUnfolding Root) :
    RootFace (R := R) (G := G) rootOccurrence where
  relationOccurrence := rootOccurrence.map
    (fun _ => relationMap (R := R) G)
  relationOccurrence_eq := rfl

def root {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    (_face : RootFace (R := R) (G := G) rootOccurrence) :=
  rootOccurrence

theorem relationOccurrence_is_root_map
    {Root : Type w} {rootOccurrence : RootedAccountedUnfolding Root}
    (face : RootFace (R := R) (G := G) rootOccurrence) :
    face.relationOccurrence =
      rootOccurrence.map (fun _ => relationMap (R := R) G) :=
  face.relationOccurrence_eq

abbrev cokernel {Root : Type w}
    {rootOccurrence : RootedAccountedUnfolding Root}
    (_face : RootFace (R := R) (G := G) rootOccurrence) :=
  PresentedCarrier R G

def cokernelEquiv {Root : Type w}
    {rootOccurrence : RootedAccountedUnfolding Root}
    (_face : RootFace (R := R) (G := G) rootOccurrence) :
    PresentedCarrier R G ≃ₗ[R] G :=
  presentedEquiv (R := R) G

end RootFace

end
end ScalarRelationPresentation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
