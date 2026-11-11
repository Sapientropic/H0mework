import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Factorization.LivingLawRootGeneratedScalarCochainSubfaceFactorizationKernel
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Root occurrence for cochain subface factorization

The source complex, dependent face, ambient complex, both actual arrows, and
degreewise faithfulness evidence are one occurrence payload.  The generated
face projects the existing root and calls the generic factorization/residual
classifier on that exact payload.  It creates no sibling root, caller lift,
residual-zero receipt, determinant, or domain equation.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedCochainSubfaceFactorization

open SourceGeneratedCochainSubfaceFactorization

noncomputable section

universe r m i w

variable (R : Type r) [CommRing R]
variable (Index : Type i) (shape : ComplexShape Index)

structure Data : Type (max (max r m) i + 2) where
  sourceComplex : HomologicalComplex (ModuleCat.{m} R) shape
  faceComplex : HomologicalComplex (ModuleCat.{m} R) shape
  ambientComplex : HomologicalComplex (ModuleCat.{m} R) shape
  sourceMap : sourceComplex ⟶ ambientComplex
  subfaceMap : faceComplex ⟶ ambientComplex
  subface_injective : DegreewiseInjective subfaceMap

namespace Data

variable {R Index shape}

def disposition (data : Data R Index shape) :
    SourceGeneratedCochainSubfaceFactorization.Disposition
      data.sourceMap data.subfaceMap :=
  SourceGeneratedCochainSubfaceFactorization.settle
    data.sourceMap data.subfaceMap data.subface_injective

theorem disposition_total (data : Data R Index shape) :
    Nonempty
      (SourceGeneratedCochainSubfaceFactorization.Disposition
        data.sourceMap data.subfaceMap) :=
  SourceGeneratedCochainSubfaceFactorization.settle_total
    data.sourceMap data.subfaceMap data.subface_injective

end Data

variable {R Index shape}
variable {Root : Type w}
variable {occurrence : RootedAccountedUnfolding
  (Root × Data R Index shape)}

structure Face
    (occurrence : RootedAccountedUnfolding
      (Root × Data R Index shape)) where
  private mk ::

namespace Face

def generate : Face occurrence := ⟨⟩

def root (_face : Face occurrence) : RootedAccountedUnfolding Root :=
  occurrence.map Prod.fst

def dataOccurrence (_face : Face occurrence) :
    RootedAccountedUnfolding (Data R Index shape) :=
  occurrence.map Prod.snd

def data (face : Face occurrence) : Data R Index shape :=
  face.dataOccurrence.root

def disposition (face : Face occurrence) :
    SourceGeneratedCochainSubfaceFactorization.Disposition
      face.data.sourceMap face.data.subfaceMap :=
  face.data.disposition

abbrev DispositionPayload :=
  Σ data : Data R Index shape,
    SourceGeneratedCochainSubfaceFactorization.Disposition
      data.sourceMap data.subfaceMap

def dispositionOccurrence (_face : Face occurrence) :
    RootedAccountedUnfolding (Root × DispositionPayload (R := R)
      (Index := Index) (shape := shape)) :=
  occurrence.map fun rooted =>
    (rooted.1, ⟨rooted.2, rooted.2.disposition⟩)

def forgetDisposition :
    (Root × DispositionPayload (R := R) (Index := Index) (shape := shape)) →
      (Root × Data R Index shape) :=
  fun rooted => (rooted.1, rooted.2.1)

theorem dispositionOccurrence_projects_to_source
    (face : Face occurrence) :
    face.dispositionOccurrence.map
        (forgetDisposition (R := R) (Index := Index) (shape := shape)) =
      occurrence := by
  calc
    face.dispositionOccurrence.map
        (forgetDisposition (R := R) (Index := Index) (shape := shape)) =
      occurrence.map
        ((forgetDisposition (R := R) (Index := Index) (shape := shape)) ∘
          fun rooted => (rooted.1, ⟨rooted.2, rooted.2.disposition⟩)) :=
        RootedAccountedUnfolding.map_map _ _ _
    _ = occurrence.map id := by
      congr 1
    _ = occurrence := RootedAccountedUnfolding.map_id occurrence

@[simp] theorem data_root (face : Face occurrence) :
    face.data = occurrence.root.2 := by
  simp [data, dataOccurrence]

@[simp] theorem root_value (face : Face occurrence) :
    face.root.root = occurrence.root.1 := by
  simp [root]

@[simp] theorem dispositionOccurrence_root_source
    (face : Face occurrence) :
    face.dispositionOccurrence.root.1 = occurrence.root.1 := by
  simp [dispositionOccurrence]

@[simp] theorem dispositionOccurrence_root_data
    (face : Face occurrence) :
    face.dispositionOccurrence.root.2.1 = occurrence.root.2 := by
  simp [dispositionOccurrence]

theorem preserves_root_and_data (face : Face occurrence) :
    face.root = occurrence.map Prod.fst ∧
      face.dataOccurrence = occurrence.map Prod.snd ∧
      face.data = occurrence.root.2 :=
  ⟨rfl, rfl, face.data_root⟩

end Face

end
end RootGeneratedCochainSubfaceFactorization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
