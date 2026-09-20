import H0mework.Physics.JointSources.P701

/-!
# Proposition 702: no family freedom on the four-face diagonal

P701 proves that every admissible energy / information / mathematics / physics
finite readout is the same canonical source-law output.  This file turns that
pointwise diagonal theorem into an object-level universal-form theorem:

* the diagonal subtype is equivalent to `Unit`;
* any indexed family of diagonal inhabitants is constant;
* any face-indexed output family satisfying the face laws is constant;
* every endomorphism and automorphism of the diagonal object is trivial.

This is the formal "not four tracks" statement.  The four labels may be used as
readout names, but they do not generate a parameter family.  There is one
finite diagonal object.

Boundary: this remains the finite/source-law diagonal.  Smooth Standard-Model
dynamics, the final Euler/RH adapter range, Goldbach/RH, arbitrary runtime
mechanism-faithfulness, polynomial SAT, and `P = NP` remain outside this
theorem.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open StandardModelConstraint

set_option linter.checkUnivs false

universe u v w z

/-! ## The diagonal as a unit object -/

/-- The subtype of finite outputs lying on the full four-face diagonal. -/
def EnergyInformationMathematicsPhysicsDiagonalSubtype : Type :=
  { O : SourceLawFinitePhysicalOutput //
    EnergyInformationMathematicsPhysicsDiagonalSurface O }

/-- The canonical inhabitant of the four-face diagonal subtype. -/
def canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype :
    EnergyInformationMathematicsPhysicsDiagonalSubtype :=
  ⟨canonicalSourceLawFinitePhysicalOutput,
    (energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical
      canonicalSourceLawFinitePhysicalOutput).2 rfl⟩

/-- THEOREM 1: every diagonal subtype inhabitant is canonical. -/
theorem energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical
    (X : EnergyInformationMathematicsPhysicsDiagonalSubtype) :
    X = canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype := by
  cases X with
  | mk O hO =>
      apply Subtype.ext
      exact
        (energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical
          O).1 hO

/-- THEOREM 2: the diagonal subtype is a subsingleton. -/
theorem energyInformationMathematicsPhysicsDiagonalSubtype_subsingleton :
    Subsingleton EnergyInformationMathematicsPhysicsDiagonalSubtype := by
  refine ⟨?_⟩
  intro X Y
  rw [energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical X,
    energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical Y]

/-- THEOREM 3: the four-face diagonal object is equivalent to `Unit`. -/
def energyInformationMathematicsPhysicsDiagonalSubtypeEquivUnit :
    EnergyInformationMathematicsPhysicsDiagonalSubtype ≃ Unit where
  toFun _ := ()
  invFun _ := canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype
  left_inv := by
    intro X
    exact
      (energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical X).symm
  right_inv := by
    intro u
    cases u
    rfl

/-- THEOREM 4: projecting any diagonal-subtype inhabitant recovers the
canonical finite source-law output. -/
theorem energyInformationMathematicsPhysicsDiagonalSubtype_val_eq_canonical
    (X : EnergyInformationMathematicsPhysicsDiagonalSubtype) :
    X.1 = canonicalSourceLawFinitePhysicalOutput := by
  have hX := congrArg Subtype.val
    (energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical X)
  simpa [canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype] using hX

/-! ## Indexed-family collapse -/

/-- THEOREM 5: every indexed family of diagonal inhabitants is constant. -/
theorem energyInformationMathematicsPhysicsDiagonalSubtypeFamily_eq_constant
    {ι : Type u}
    (F : ι -> EnergyInformationMathematicsPhysicsDiagonalSubtype) :
    F = fun _ => canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype := by
  funext i
  exact energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical (F i)

/-- THEOREM 6: the function space into the diagonal subtype is itself a
subsingleton for every index type. -/
theorem energyInformationMathematicsPhysicsDiagonalSubtypeFamily_subsingleton
    {ι : Type u} :
    Subsingleton
      (ι -> EnergyInformationMathematicsPhysicsDiagonalSubtype) := by
  refine ⟨?_⟩
  intro F G
  rw [energyInformationMathematicsPhysicsDiagonalSubtypeFamily_eq_constant F,
    energyInformationMathematicsPhysicsDiagonalSubtypeFamily_eq_constant G]

/-- THEOREM 7: a face-indexed output family satisfying the four face laws is
the constant canonical output family. -/
theorem faceIndexedOutputFamily_eq_constant
    (F : EnergyInformationMathematicsPhysicsFace ->
      SourceLawFinitePhysicalOutput)
    (hF : ∀ face : EnergyInformationMathematicsPhysicsFace,
      EnergyInformationMathematicsPhysicsFaceSurface face (F face)) :
    F = fun _ => canonicalSourceLawFinitePhysicalOutput := by
  funext face
  exact
    (energyInformationMathematicsPhysicsFaceSurface_iff_canonical
      face (F face)).1 (hF face)

/-- THEOREM 8: any indexed family of face/output pairs satisfying its named
face law has a constant canonical output projection. -/
theorem indexedFaceOutputFamily_output_eq_constant
    {ι : Type u}
    (F : ι ->
      EnergyInformationMathematicsPhysicsFace × SourceLawFinitePhysicalOutput)
    (hF : ∀ i : ι,
      EnergyInformationMathematicsPhysicsFaceSurface (F i).1 (F i).2) :
    (fun i => (F i).2) =
      fun _ => canonicalSourceLawFinitePhysicalOutput := by
  funext i
  exact
    (energyInformationMathematicsPhysicsFaceSurface_iff_canonical
      (F i).1 (F i).2).1 (hF i)

/-- THEOREM 9: any two indexed face/output families satisfying their named
face laws have the same output projection. -/
theorem indexedFaceOutputFamilies_outputs_eq
    {ι : Type u}
    (F G : ι ->
      EnergyInformationMathematicsPhysicsFace × SourceLawFinitePhysicalOutput)
    (hF : ∀ i : ι,
      EnergyInformationMathematicsPhysicsFaceSurface (F i).1 (F i).2)
    (hG : ∀ i : ι,
      EnergyInformationMathematicsPhysicsFaceSurface (G i).1 (G i).2) :
    (fun i => (F i).2) = (fun i => (G i).2) := by
  rw [indexedFaceOutputFamily_output_eq_constant F hF,
    indexedFaceOutputFamily_output_eq_constant G hG]

/-! ## Endomorphism and automorphism collapse -/

/-- THEOREM 10: every endomorphism of the diagonal subtype is the identity. -/
theorem energyInformationMathematicsPhysicsDiagonalEndomorphism_eq_id
    (f : EnergyInformationMathematicsPhysicsDiagonalSubtype ->
      EnergyInformationMathematicsPhysicsDiagonalSubtype) :
    f =
      (id : EnergyInformationMathematicsPhysicsDiagonalSubtype ->
        EnergyInformationMathematicsPhysicsDiagonalSubtype) := by
  funext X
  rw [energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical (f X),
    energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical X]
  rfl

/-- THEOREM 11: every automorphism of the diagonal subtype is trivial. -/
theorem energyInformationMathematicsPhysicsDiagonalAutomorphism_eq_refl
    (e : EnergyInformationMathematicsPhysicsDiagonalSubtype ≃
      EnergyInformationMathematicsPhysicsDiagonalSubtype) :
    e =
      Equiv.refl EnergyInformationMathematicsPhysicsDiagonalSubtype := by
  ext X
  have h := congrFun
    (energyInformationMathematicsPhysicsDiagonalEndomorphism_eq_id
      (fun X => e X)) X
  simpa using h

/-! ## Packaged root -/

/-- P702 certificate: the four-face diagonal is an object-level unit with no
indexed-family, endomorphism, or automorphism freedom. -/
structure EnergyInformationMathematicsPhysicsDiagonalNoFamilyFreedomCertificate
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p701_diagonal_root :
    EnergyInformationMathematicsPhysicsDiagonalCertificate.{v, w, z, u} E
  diagonal_subtype_equiv_unit :
    EnergyInformationMathematicsPhysicsDiagonalSubtype ≃ Unit
  every_diagonal_subtype_eq_canonical :
    ∀ X : EnergyInformationMathematicsPhysicsDiagonalSubtype,
      X = canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype
  every_diagonal_value_eq_canonical :
    ∀ X : EnergyInformationMathematicsPhysicsDiagonalSubtype,
      X.1 = canonicalSourceLawFinitePhysicalOutput
  diagonal_subtype_family_constant :
    ∀ {ι : Type u}
      (F : ι -> EnergyInformationMathematicsPhysicsDiagonalSubtype),
      F = fun _ => canonicalEnergyInformationMathematicsPhysicsDiagonalSubtype
  face_indexed_output_family_constant :
    ∀ (F : EnergyInformationMathematicsPhysicsFace ->
        SourceLawFinitePhysicalOutput),
      (∀ face : EnergyInformationMathematicsPhysicsFace,
        EnergyInformationMathematicsPhysicsFaceSurface face (F face)) ->
        F = fun _ => canonicalSourceLawFinitePhysicalOutput
  indexed_face_output_family_constant :
    ∀ {ι : Type u}
      (F : ι ->
        EnergyInformationMathematicsPhysicsFace × SourceLawFinitePhysicalOutput),
      (∀ i : ι,
        EnergyInformationMathematicsPhysicsFaceSurface (F i).1 (F i).2) ->
        (fun i => (F i).2) =
          fun _ => canonicalSourceLawFinitePhysicalOutput
  diagonal_endomorphism_identity :
    ∀ f : EnergyInformationMathematicsPhysicsDiagonalSubtype ->
      EnergyInformationMathematicsPhysicsDiagonalSubtype,
      f =
        (id : EnergyInformationMathematicsPhysicsDiagonalSubtype ->
          EnergyInformationMathematicsPhysicsDiagonalSubtype)
  diagonal_automorphism_trivial :
    ∀ e : EnergyInformationMathematicsPhysicsDiagonalSubtype ≃
      EnergyInformationMathematicsPhysicsDiagonalSubtype,
      e =
        Equiv.refl EnergyInformationMathematicsPhysicsDiagonalSubtype

/-- THEOREM 12: the current four-face diagonal has no indexed-family freedom. -/
def energyInformationMathematicsPhysicsDiagonalNoFamilyFreedomCertificate
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    EnergyInformationMathematicsPhysicsDiagonalNoFamilyFreedomCertificate.{u, v, w, z}
      E where
  p701_diagonal_root :=
    energyInformationMathematicsPhysicsDiagonalCertificate (E := E)
  diagonal_subtype_equiv_unit :=
    energyInformationMathematicsPhysicsDiagonalSubtypeEquivUnit
  every_diagonal_subtype_eq_canonical :=
    energyInformationMathematicsPhysicsDiagonalSubtype_eq_canonical
  every_diagonal_value_eq_canonical :=
    energyInformationMathematicsPhysicsDiagonalSubtype_val_eq_canonical
  diagonal_subtype_family_constant :=
    energyInformationMathematicsPhysicsDiagonalSubtypeFamily_eq_constant
  face_indexed_output_family_constant :=
    faceIndexedOutputFamily_eq_constant
  indexed_face_output_family_constant :=
    indexedFaceOutputFamily_output_eq_constant
  diagonal_endomorphism_identity :=
    energyInformationMathematicsPhysicsDiagonalEndomorphism_eq_id
  diagonal_automorphism_trivial :=
    energyInformationMathematicsPhysicsDiagonalAutomorphism_eq_refl

end GrandUnification
end SaturationMonoid
