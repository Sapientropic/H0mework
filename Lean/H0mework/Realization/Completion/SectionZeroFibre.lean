import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.RingTheory.AdjoinRoot
import H0mework.Realization.Completion.PolynomialSection

/-!
# Zero fibre of a generated cofinal polynomial section

This kernel consumes an already generated global pro-section diagram.  The
zero-fibre functor sends a divisibility arrow `D' ⟶ D` to the canonical
coordinate-ring map `AdjoinRoot D' → AdjoinRoot D`; the categorical limit
and universal determinant parameter are then framework outputs.

The determinant parameter is not itself called an arithmetic component.
Reversal, a dual inclusion, and any anti-invariant difference must be
generated downstream from the same actual reversal-equivariant determinant
occurrence; this generic kernel does not invent their coordinate shape.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPolynomialSectionZeroFiber

open CategoryTheory
open CategoryTheory.Limits
open CofinalPolynomialSection
open CofinalPolynomialSection.RootGeneratedCofinalPolynomialSectionAt

noncomputable section

universe u w

variable {R : Type u} [CommRing R]

theorem sourcePolynomial_vanishes
    {source target : PolynomialSectionObjectAt R}
    (arrow : source ⟶ target) :
    source.polynomial.eval₂ (AdjoinRoot.of target.polynomial)
      (AdjoinRoot.root target.polynomial) = 0 := by
  rcases arrow.le with ⟨factor, factorization⟩
  rw [factorization, Polynomial.eval₂_mul,
    AdjoinRoot.eval₂_root, zero_mul]

def zeroFiberMap
    {source target : PolynomialSectionObjectAt R}
    (arrow : source ⟶ target) :
  AdjoinRoot source.polynomial →+* AdjoinRoot target.polynomial :=
  AdjoinRoot.lift (AdjoinRoot.of target.polynomial)
    (AdjoinRoot.root target.polynomial)
      (sourcePolynomial_vanishes arrow)

@[simp] theorem zeroFiberMap_root
    {source target : PolynomialSectionObjectAt R}
    (arrow : source ⟶ target) :
    zeroFiberMap arrow (AdjoinRoot.root source.polynomial) =
      AdjoinRoot.root target.polynomial :=
  AdjoinRoot.lift_root _

@[simp] theorem zeroFiberMap_base
    {source target : PolynomialSectionObjectAt R}
    (arrow : source ⟶ target) (coefficient : R) :
    zeroFiberMap arrow (AdjoinRoot.of source.polynomial coefficient) =
      AdjoinRoot.of target.polynomial coefficient := by
  have base := RingHom.congr_fun
    (AdjoinRoot.lift_comp_of (sourcePolynomial_vanishes arrow)) coefficient
  exact base

theorem zeroFiberMap_comp_mk
    {source target : PolynomialSectionObjectAt R}
    (arrow : source ⟶ target) :
    (zeroFiberMap arrow).comp (AdjoinRoot.mk source.polynomial) =
      AdjoinRoot.mk target.polynomial := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    exact zeroFiberMap_base arrow coefficient
  · exact zeroFiberMap_root arrow

theorem zeroFiberMap_id (object : PolynomialSectionObjectAt R) :
    zeroFiberMap (𝟙 object) = RingHom.id (AdjoinRoot object.polynomial) := by
  apply AdjoinRoot.ringHom_ext
  · apply DFunLike.ext _ _
    intro coefficient
    exact zeroFiberMap_base (𝟙 object) coefficient
  · exact zeroFiberMap_root (𝟙 object)

theorem zeroFiberMap_comp
    {first second third : PolynomialSectionObjectAt R}
    (left : first ⟶ second) (right : second ⟶ third) :
    zeroFiberMap (left ≫ right) =
      (zeroFiberMap right).comp (zeroFiberMap left) := by
  apply AdjoinRoot.ringHom_ext
  · apply DFunLike.ext _ _
    intro coefficient
    change zeroFiberMap (left ≫ right)
        (AdjoinRoot.of first.polynomial coefficient) =
      zeroFiberMap right
        (zeroFiberMap left
          (AdjoinRoot.of first.polynomial coefficient))
    rw [zeroFiberMap_base, zeroFiberMap_base, zeroFiberMap_base]
  · change zeroFiberMap (left ≫ right)
        (AdjoinRoot.root first.polynomial) =
      zeroFiberMap right
        (zeroFiberMap left (AdjoinRoot.root first.polynomial))
    rw [zeroFiberMap_root, zeroFiberMap_root, zeroFiberMap_root]

def zeroFiberFunctor :
    CategoryTheory.Functor (PolynomialSectionObjectAt R) CommRingCat where
  obj object := CommRingCat.of (AdjoinRoot object.polynomial)
  map arrow := CommRingCat.ofHom (zeroFiberMap arrow)
  map_id object := by
    apply CommRingCat.hom_ext
    exact zeroFiberMap_id object
  map_comp left right := by
    apply CommRingCat.hom_ext
    exact zeroFiberMap_comp left right

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {dependentProcessOccurrence : RootedAccountedUnfolding
  (Root × PolynomialSectionSuccessorProcessAt R)}
variable {projects : dependentProcessOccurrence.map Prod.fst = rootOccurrence}

variable (sectionFace : RootGeneratedCofinalPolynomialSectionAt
  rootOccurrence dependentProcessOccurrence projects)

def zeroFiberDiagram : CategoryTheory.Functor ℕᵒᵖ CommRingCat :=
  sectionFace.globalSectionDiagram ⋙ zeroFiberFunctor

def universalInclusionCone : Cone (zeroFiberDiagram sectionFace) where
  pt := CommRingCat.of (Polynomial R)
  π :=
    { app := fun stage => CommRingCat.ofHom
        (AdjoinRoot.mk
          (sectionFace.globalSectionDiagram.obj stage).polynomial)
      naturality := fun source target arrow => by
        simp only [Functor.const_obj_map]
        apply CommRingCat.hom_ext
        exact (zeroFiberMap_comp_mk
          (sectionFace.globalSectionDiagram.map arrow)).symm }

abbrev GlobalZeroFiberRing : CommRingCat :=
  limit (zeroFiberDiagram sectionFace)

/-- Universal inclusion into the global zero-fibre coordinate ring. -/
noncomputable def globalUniversalInclusion :
    CommRingCat.of (Polynomial R) ⟶ GlobalZeroFiberRing sectionFace :=
  limit.lift _ (universalInclusionCone sectionFace)

/-- Universal determinant parameter.  It is a scalar used to build the
arithmetic inclusion below, not the fixed component itself. -/
noncomputable def globalUniversalParameter :
    GlobalZeroFiberRing sectionFace :=
  globalUniversalInclusion sectionFace Polynomial.X

theorem globalUniversalInclusion_restriction (stage : Nat) :
    globalUniversalInclusion sectionFace ≫
        limit.π (zeroFiberDiagram sectionFace) (Opposite.op stage) =
      CommRingCat.ofHom
        (AdjoinRoot.mk
          (sectionFace.globalSectionDiagram.obj
            (Opposite.op stage)).polynomial) :=
  limit.lift_π (universalInclusionCone sectionFace) (Opposite.op stage)

theorem globalUniversalParameter_restriction (stage : Nat) :
    limit.π (zeroFiberDiagram sectionFace) (Opposite.op stage)
        (globalUniversalParameter sectionFace) =
      AdjoinRoot.root
        (sectionFace.globalSectionDiagram.obj
          (Opposite.op stage)).polynomial := by
  have restriction := ConcreteCategory.congr_hom
    (globalUniversalInclusion_restriction sectionFace stage) Polynomial.X
  have restrictionValue :
      limit.π (zeroFiberDiagram sectionFace) (Opposite.op stage)
          (globalUniversalParameter sectionFace) =
        AdjoinRoot.mk
          (sectionFace.globalSectionDiagram.obj
            (Opposite.op stage)).polynomial Polynomial.X := by
    change limit.π (zeroFiberDiagram sectionFace) (Opposite.op stage)
        (globalUniversalInclusion sectionFace Polynomial.X) =
      AdjoinRoot.mk
        (sectionFace.globalSectionDiagram.obj
          (Opposite.op stage)).polynomial Polynomial.X
    exact restriction
  exact restrictionValue.trans AdjoinRoot.mk_X

end
end CofinalPolynomialSectionZeroFiber
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
