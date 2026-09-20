/-
  Proposition 68: section-valued descent as an equalizer.

  Proposition 67 deliberately stopped at Prop-valued field convergence.  This
  file adds the next sheaf-shaped layer without pretending to have full
  cohomology:

    * local sections are actual objects, not only predicates;
    * overlap compatibility is equality of restricted sections;
    * a descent certificate says compatible local sections glue to a unique
      global section;
    * adding the field-descent certificate yields a unique global convergent
      section exactly when the local family is compatible and locally
      convergent.

  This is the equalizer/fiber-product shape that the memory-language slogan
  needs before any honest cochain or H¹ quotient can be built.
-/

import H0mework.Realization.Fields.SevenFieldFibre

/-! ## Section-valued indexed covers -/

/-- An indexed cover whose sections are actual objects.

`Local i` is the type of sections on open `i`; `Overlap i j` is the type of
sections on the pairwise overlap. -/
structure SectionIndexedCover
    (Index : Type*) (Global : Type*) (Local : Index -> Type*)
    (Overlap : Index -> Index -> Type*) where
  toLocal : forall i, Global -> Local i
  leftToOverlap : forall i j, Local i -> Overlap i j
  rightToOverlap : forall i j, Local j -> Overlap i j
  glue : (forall i, Local i) -> Global

/-- A family of local section objects. -/
abbrev SectionLocalFamily
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*}
    (_C : SectionIndexedCover Index Global Local Overlap) :=
  forall i, Local i

/-- Pairwise overlap equality for section-valued local families. -/
def SectionOverlapCompatible
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*}
    (C : SectionIndexedCover Index Global Local Overlap)
    (s : SectionLocalFamily C) : Prop :=
  forall i j,
    C.leftToOverlap i j (s i) = C.rightToOverlap i j (s j)

/-- A global section restricts to a chosen local family. -/
def GlobalRestrictsTo
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*}
    (C : SectionIndexedCover Index Global Local Overlap)
    (g : Global) (s : SectionLocalFamily C) : Prop :=
  forall i, C.toLocal i g = s i

/-- A section-level descent certificate.

This is the sheaf-like equalizer law at the object level:
global sections restrict compatibly; compatible local families glue back; and
the glued section is unique among globals with those restrictions. -/
structure SectionDescentCertificate
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*}
    (C : SectionIndexedCover Index Global Local Overlap) where
  globalCompatible :
    forall g, SectionOverlapCompatible C (fun i => C.toLocal i g)
  glueRestricts :
    forall s, SectionOverlapCompatible C s ->
      GlobalRestrictsTo C (C.glue s) s
  glueUnique :
    forall s, SectionOverlapCompatible C s ->
      forall g, GlobalRestrictsTo C g s -> g = C.glue s

/-- THEOREM 1: every global section restricts to a compatible local family. -/
theorem section_global_restrictions_compatible
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*}
    {C : SectionIndexedCover Index Global Local Overlap}
    (D : SectionDescentCertificate C) :
    forall g, SectionOverlapCompatible C (fun i => C.toLocal i g) := by
  exact D.globalCompatible

/-- THEOREM 2: a compatible local family glues to a global section restricting
back to that family. -/
theorem section_compatible_glues
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*}
    {C : SectionIndexedCover Index Global Local Overlap}
    (D : SectionDescentCertificate C) :
    forall s, SectionOverlapCompatible C s ->
      GlobalRestrictsTo C (C.glue s) s := by
  exact D.glueRestricts

/-- THEOREM 3: section compatibility is equivalent to existence of a unique
global section restricting to the local family. -/
theorem sectionCompatible_iff_existsUnique_global
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*}
    {C : SectionIndexedCover Index Global Local Overlap}
    (D : SectionDescentCertificate C)
    (s : SectionLocalFamily C) :
    SectionOverlapCompatible C s <->
      ∃! g, GlobalRestrictsTo C g s := by
  constructor
  · intro hcomp
    refine ⟨C.glue s, D.glueRestricts s hcomp, ?_⟩
    intro g hg
    exact D.glueUnique s hcomp g hg
  · rintro ⟨g, hg, _huniq⟩
    intro i j
    calc
      C.leftToOverlap i j (s i)
          = C.leftToOverlap i j (C.toLocal i g) := by
            rw [hg i]
      _ = C.rightToOverlap i j (C.toLocal j g) :=
            D.globalCompatible g i j
      _ = C.rightToOverlap i j (s j) := by
            rw [hg j]

/-! ## Adding field convergence to section descent -/

/-- Read a section-valued cover together with field families as an indexed
field cover. -/
def SectionIndexedCover.toIndexedFieldCover
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (C : SectionIndexedCover Index Global Local Overlap)
    (FG : FieldFamily Global Field)
    (FL : forall i, FieldFamily (Local i) Field)
    (FO : forall i j, FieldFamily (Overlap i j) Field) :
    IndexedFieldCover Index Global Local Overlap Field where
  FG := FG
  FL := FL
  FO := FO
  toLocal := C.toLocal
  leftToOverlap := C.leftToOverlap
  rightToOverlap := C.rightToOverlap
  glue := C.glue

/-- A section-valued field descent certificate combines object-level descent
with field-level restriction/descent. -/
structure SectionValuedFieldDescentCertificate
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (C : SectionIndexedCover Index Global Local Overlap)
    (FG : FieldFamily Global Field)
    (FL : forall i, FieldFamily (Local i) Field)
    (FO : forall i j, FieldFamily (Overlap i j) Field) where
  sectionCert :
    SectionDescentCertificate C
  fieldCert :
    IndexedFieldDescentCertificate
      (C.toIndexedFieldCover FG FL FO)

/-- A global section both restricts to the local family and converges in the
global field family. -/
def GlobalConvergentRestriction
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (C : SectionIndexedCover Index Global Local Overlap)
    (FG : FieldFamily Global Field)
    (g : Global) (s : SectionLocalFamily C) : Prop :=
  GlobalRestrictsTo C g s /\ FieldConvergence FG g

/-- THEOREM 4: compatible, locally convergent section families are exactly
the local data admitting a unique global convergent section. -/
theorem compatibleLocalConvergence_iff_existsUnique_globalConvergent
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    {C : SectionIndexedCover Index Global Local Overlap}
    {FG : FieldFamily Global Field}
    {FL : forall i, FieldFamily (Local i) Field}
    {FO : forall i j, FieldFamily (Overlap i j) Field}
    (D : SectionValuedFieldDescentCertificate C FG FL FO)
    (s : SectionLocalFamily C) :
    (SectionOverlapCompatible C s /\
      (forall i, FieldConvergence (FL i) (s i))) <->
      ∃! g, GlobalConvergentRestriction C FG g s := by
  constructor
  · rintro ⟨hcomp, hlocal⟩
    refine ⟨C.glue s, ?_, ?_⟩
    · exact ⟨D.sectionCert.glueRestricts s hcomp, D.fieldCert.descend s hlocal⟩
    · intro g hg
      exact D.sectionCert.glueUnique s hcomp g hg.1
  · rintro ⟨g, hg, _huniq⟩
    constructor
    · intro i j
      calc
        C.leftToOverlap i j (s i)
            = C.leftToOverlap i j (C.toLocal i g) := by
              rw [hg.1 i]
        _ = C.rightToOverlap i j (C.toLocal j g) :=
              D.sectionCert.globalCompatible g i j
        _ = C.rightToOverlap i j (s j) := by
              rw [hg.1 j]
    · intro i
      have hlocalAt :
          FieldConvergence (FL i) (C.toLocal i g) :=
        indexed_global_convergence_restricts D.fieldCert g i hg.2
      simpa [hg.1 i] using hlocalAt

/-- THEOREM 5: when section descent holds, a compatible locally convergent
family's unique underlying global section fails to converge exactly when there
is nonempty indexed boundary holonomy. -/
theorem sectionDescent_boundaryHolonomy_iff_uniqueGlobal_not_convergent
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    {Csec : SectionIndexedCover Index Global Local Overlap}
    {FG : FieldFamily Global Field}
    {FL : forall i, FieldFamily (Local i) Field}
    {FO : forall i j, FieldFamily (Overlap i j) Field}
    (_Dsec : SectionDescentCertificate Csec)
    (s : SectionLocalFamily Csec)
    (_hcomp : SectionOverlapCompatible Csec s)
    (hlocal : forall i, FieldConvergence (FL i) (s i)) :
    (exists field,
      IndexedCoverBoundaryHolonomy
        (Csec.toIndexedFieldCover FG FL FO) s field) <->
      Not (FieldConvergence FG (Csec.glue s)) := by
  exact indexedCoverBoundaryHolonomy_nonempty_iff_global_failed
    (Csec.toIndexedFieldCover FG FL FO) s hlocal

/-!
  Summary:
  - `SectionIndexedCover` is the section-valued layer missing from the earlier
    Prop-valued field geometry.
  - `sectionCompatible_iff_existsUnique_global` is the equalizer/descent law:
    compatible local sections are precisely those with a unique global gluing.
  - With field descent added, compatible locally convergent sections are
    precisely those with a unique global convergent section.
  - Without field descent, the unique underlying global can still fail field
    convergence; that failure is exactly indexed boundary holonomy.

  Remaining boundary:
  - This is still indexed-cover descent data, not a topological site.
  - It proves the equalizer/fiber-product shape, but not cochains, coboundary
    maps, `δ² = 0`, or an abelian-group H¹ quotient.
-/
