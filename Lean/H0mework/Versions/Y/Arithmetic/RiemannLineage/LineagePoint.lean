import H0mework.Versions.Y.Arithmetic.RiemannLineage.FiniteEndpointCycle

/-!
# The source lineage of finite q-rich endpoint cycles

The successor factorial is part of the source transition.  It is retained,
not inverted: the q-rich cycle therefore forms a strictly natural family over
the actual arithmetic restrictions without inventing a backward isomorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace QRich

open CategoryTheory
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber

noncomputable section

/-- The source line whose two coordinates generate the two literal q-rich
orientations. -/
abbrev QRichLineageComplex :
    CochainComplex (ModuleCat BlockCoordinateRing) ℤ :=
  (HomologicalComplex.single (ModuleCat BlockCoordinateRing)
    (ComplexShape.up ℤ) 0).obj BlockDualBaseObject

/-- The newly appended factorial unit is the source transition itself. -/
noncomputable def qRichLineageRestriction (stage : Nat) :
    QRichLineageComplex ⟶ QRichLineageComplex :=
  (HomologicalComplex.single (ModuleCat BlockCoordinateRing)
    (ComplexShape.up ℤ) 0).map
    (ModuleCat.ofHom
      ((blockQRichSuccessorScale stage : BlockCoordinateRing) •
        LinearMap.id))

/-- The strict q-rich cycle regarded as a point generated from its source
lineage. -/
noncomputable def qRichLineagePoint (stage : Nat) :
    QRichLineageComplex ⟶ LocalWholeComplex stage :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (blockQRichEndpointVertexMap stage))
    (fun next related => by
      change 0 + 1 = next at related
      subst next
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro base
      exact blockQRichEndpointVertexMap_differential_zero stage base)

/-- The lineage point is strictly natural because the actual factorial scale
has been assigned to the source transition. -/
theorem qRichLineagePoint_successor (stage : Nat) :
    qRichLineagePoint (stage + 1) ≫
        blockDirectRestriction seedOccurrence.root stage =
      qRichLineageRestriction stage ≫ qRichLineagePoint stage := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  unfold qRichLineagePoint qRichLineageRestriction
  rw [HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.mkHomFromSingle_f]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  have restrictionZero :
      (blockDirectRestriction seedOccurrence.root stage).f 0 =
        ModuleCat.ofHom
          (blockWholeVertexRestriction seedOccurrence.root stage) := by
    simp [blockDirectRestriction]
  rw [restrictionZero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro source
  simp only [ConcreteCategory.comp_apply]
  let base : BlockDualBase :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      BlockDualBaseObject).hom.hom source
  have generated := LinearMap.congr_fun
    (blockQRichEndpointVertexMap_restriction_scale stage) base
  simpa [base, BlockDirectObject] using generated

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
