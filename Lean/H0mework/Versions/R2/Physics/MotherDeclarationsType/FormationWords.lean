import H0mework.Versions.R2.Physics.MotherDeclarationsType.FormationSource

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTypeFormation

open MotherFamilyOccurrence Stage9C.Revision

noncomputable section

abbrev Carrier (law : Law) := Generator law →₀ ℤ
abbrev TermMaterial := MemberMaterial × MotherVisit

def integerAt (parent : MotherVisit) : ℤ :=
  (StageEightDiscreteFormation.readMaterial
    (StageEightDiscreteFormation.sourceAtVisit parent)).1 (.inl 0)

theorem every_integer (value : ℤ) : ∃ parent : MotherVisit, integerAt parent = value := by
  obtain ⟨code, formed⟩ := StageEightDiscreteFormation.every_material_at_code
    (StageEightDiscreteFormation.integerAtom (.inl 0) value)
  refine ⟨SpinPair.visit (10 + code), ?_⟩
  simp only [integerAt, StageEightDiscreteFormation.sourceAtVisit,
    StageEightDiscreteFormation.full_material_recovered,
    StageEightDiscreteFormation.code_at, formed]
  simp [StageEightDiscreteFormation.integerAtom]

def readTerms (law : Law) : List TermMaterial → Option (Carrier law)
  | [] => some 0
  | term :: rest =>
      (formMember law term.1).bind fun generator =>
        (readTerms law rest).map fun word =>
          Finsupp.single generator (integerAt term.2) + word

theorem readTerms_append (law : Law) (first last : List TermMaterial) :
    readTerms law (first ++ last) =
      (readTerms law first).bind (fun left =>
        (readTerms law last).map (fun right => left + right)) := by
  induction first with
  | nil => simp [readTerms]
  | cons term rest induction =>
      simp only [List.cons_append, readTerms, induction]
      cases formMember law term.1 <;>
        cases readTerms law rest <;> cases readTerms law last <;>
        simp [add_assoc]

theorem every_terms (law : Law) (word : Carrier law) :
    ∃ terms : List TermMaterial, readTerms law terms = some word := by
  induction word using Finsupp.induction_linear with
  | zero => exact ⟨[], rfl⟩
  | add left right left_ih right_ih =>
      obtain ⟨leftTerms, leftRead⟩ := left_ih
      obtain ⟨rightTerms, rightRead⟩ := right_ih
      exact ⟨leftTerms ++ rightTerms, by rw [readTerms_append, leftRead, rightRead]; rfl⟩
  | single generator coefficient =>
      obtain ⟨memberMaterial, memberRead⟩ := every_generator law generator
      obtain ⟨coefficientMaterial, coefficientRead⟩ := every_integer coefficient
      exact ⟨[(memberMaterial, coefficientMaterial)], by
        simp [readTerms, memberRead, coefficientRead]⟩

/-- The word length comes from the same mother history, not a target word. -/
abbrev WordMaterial := Σ parent : MotherVisit,
  Fin (StageEightDiscreteFormation.codeOf parent) → TermMaterial

def formWord (law : Law) (material : WordMaterial) : Option (Carrier law) :=
  readTerms law (List.ofFn material.2)

theorem every_word (law : Law) (word : Carrier law) :
    ∃ material : WordMaterial, formWord law material = some word := by
  obtain ⟨terms, formed⟩ := every_terms law word
  let parent := SpinPair.visit (10 + terms.length)
  have lengthEq : StageEightDiscreteFormation.codeOf parent = terms.length :=
    StageEightDiscreteFormation.code_at terms.length
  let entries : Fin (StageEightDiscreteFormation.codeOf parent) → TermMaterial :=
    fun index => terms.get (Fin.cast lengthEq index)
  refine ⟨⟨parent, entries⟩, ?_⟩
  have sameList : List.ofFn entries = terms := by
    apply List.ext_get
    · simp [entries, lengthEq]
    · intro index firstBound lastBound
      simp [entries]
  simpa only [formWord, sameList] using formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTypeFormation
