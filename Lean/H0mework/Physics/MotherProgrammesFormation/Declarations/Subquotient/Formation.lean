import H0mework.Physics.MotherProgrammesFormation.Declarations.HigherLaw.Family
import H0mework.Physics.MotherProgrammesFormation.Declarations.HigherLaw.Value
import H0mework.Physics.MotherProgrammesFormation.Declarations.CommonDeclaration.Query

/-! Council probe: dependent subquotients formed by actual higher-law values.
The covered family is explicitly the subquotients of the existing complete
law carrier. This does not supply arbitrary headers or a universal ingress.
The original compiler consumer below checks equality of its entire dependent
output before descending; answer-only equality cannot merge distinct queries. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotient

open scoped Classical

noncomputable section

abbrev Base := MotherHigherLawFormation.Base
abbrev Material := MotherHigherLawFormation.Formed

def predicate (material : Material) (index value : Base) : Prop :=
  MotherHigherLawFormation.read (MotherHigherLawValue.split material).1
    (MotherHigherLawFamily.pair (index, value)) 0 = 0

def relation (material : Material) (index left right : Base) : Prop :=
  MotherHigherLawFormation.read (MotherHigherLawValue.split material).2
    (MotherHigherLawFamily.pair (index, MotherHigherLawFamily.pair (left, right))) 0 = 0

def Subquotient (keep : Base → Prop) (relate : Base → Base → Prop) : Type :=
  Quot (fun left right : { value : Base // keep value } => relate left.val right.val)

def Fiber (material : Material) (index : Base) : Type :=
  Subquotient (predicate material index) (relation material index)

def formMember (material : Material) (index value : Base) : Option (Fiber material index) :=
  if inside : predicate material index value then some (Quot.mk _ ⟨value, inside⟩) else none

theorem every_member (material : Material) (index : Base) (value : Fiber material index) :
    ∃ input : Base, formMember material index input = some value := by
  obtain ⟨input, formed⟩ := Quot.exists_rep value
  refine ⟨input.val, ?_⟩
  exact (dif_pos input.property).trans (congrArg some formed)

theorem every_family (keep : Base → Base → Prop) (relate : Base → Base → Base → Prop) :
    ∃ material : Material,
      predicate material = keep ∧ relation material = relate ∧
      ∀ index, Fiber material index = Subquotient (keep index) (relate index) := by
  obtain ⟨keepMaterial, keepRead⟩ := MotherHigherLawFormation.read_surjective
    (fun code _ => if keep (MotherHigherLawFamily.unpair code).1
      (MotherHigherLawFamily.unpair code).2 then 0 else 1)
  obtain ⟨relateMaterial, relateRead⟩ := MotherHigherLawFormation.read_surjective
    (fun code _ => if relate (MotherHigherLawFamily.unpair code).1
      (MotherHigherLawFamily.unpair (MotherHigherLawFamily.unpair code).2).1
      (MotherHigherLawFamily.unpair (MotherHigherLawFamily.unpair code).2).2 then 0 else 1)
  let material := MotherHigherLawValue.pack (keepMaterial, relateMaterial)
  have keepExact : predicate material = keep := by
    funext index value
    apply propext
    simp only [predicate, material, MotherHigherLawValue.split_pack,
      keepRead, MotherHigherLawFamily.unpair_pair]
    split_ifs <;> simp_all
  have relateExact : relation material = relate := by
    funext index left right
    apply propext
    simp only [relation, material, MotherHigherLawValue.split_pack,
      relateRead, MotherHigherLawFamily.unpair_pair]
    split_ifs <;> simp_all
  refine ⟨material, keepExact, relateExact, fun index => ?_⟩
  unfold Fiber
  rw [keepExact, relateExact]

theorem empty_fibres : ∃ material : Material, ∀ index, IsEmpty (Fiber material index) := by
  obtain ⟨material, keepExact, _, _⟩ := every_family (fun _ _ => False) (fun _ _ _ => False)
  refine ⟨material, fun index => ⟨fun value => ?_⟩⟩
  obtain ⟨input, _⟩ := Quot.exists_rep value
  exact Eq.mp (congrFun (congrFun keepExact index) input.val) input.property

open MotherFamilyOccurrence

abbrev OriginalOutput (typeLaw actionLaw : Base) (parent : MotherVisit) :=
  Σ query : MotherOriginalQueryValue.Query,
    MotherOriginalQueryValue.CompiledAt typeLaw actionLaw parent query

def compileDescends (material : Material) (index typeLaw actionLaw : Base) (parent : MotherVisit) : Prop :=
  ∀ left right : { value : Base // predicate material index value },
    relation material index left.val right.val →
    MotherOriginalQueryValue.compileRead typeLaw actionLaw parent left.val =
      MotherOriginalQueryValue.compileRead typeLaw actionLaw parent right.val

def compile (material : Material) (index typeLaw actionLaw : Base) (parent : MotherVisit) :
    Option (Fiber material index → OriginalOutput typeLaw actionLaw parent) :=
  if descends : compileDescends material index typeLaw actionLaw parent then
    some (Quot.lift (fun value =>
      MotherOriginalQueryValue.compileRead typeLaw actionLaw parent value.val) descends)
  else none

theorem compile_rep (material : Material) (index typeLaw actionLaw : Base) (parent : MotherVisit)
    (input : Base) (inside : predicate material index input)
    (compiler : Fiber material index → OriginalOutput typeLaw actionLaw parent)
    (formed : compile material index typeLaw actionLaw parent = some compiler) :
    compiler (Quot.mk _ ⟨input, inside⟩) =
      MotherOriginalQueryValue.compileRead typeLaw actionLaw parent input := by
  unfold compile at formed
  split at formed
  · exact congrFun (Option.some.inj formed).symm (Quot.mk _ ⟨input, inside⟩)
  · cases formed

theorem original_query_fibres_compile :
    ∃ material : Material,
      (∀ index, ∀ input, predicate material index input) ∧
      ∀ (typeLaw actionLaw : Base) (parent : MotherVisit) (index : Base),
        ∃ compiler : Fiber material index → OriginalOutput typeLaw actionLaw parent,
        compile material index typeLaw actionLaw parent = some compiler ∧
        ∀ query : MotherOriginalQueryValue.Query,
          ∃ value : Fiber material index, compiler value =
            ⟨query, (MotherNativePhysicalQuery.nativeInquiry typeLaw actionLaw parent).compileInquiry query⟩ := by
  obtain ⟨material, keepExact, relateExact, _⟩ := every_family (fun _ _ => True)
    (fun _ left right => MotherOriginalQueryValue.readQuery left = MotherOriginalQueryValue.readQuery right)
  have allInside : ∀ index input, predicate material index input := by
    rw [keepExact]
    exact fun _ _ => trivial
  refine ⟨material, allInside, fun typeLaw actionLaw parent index => ?_⟩
  have descends : compileDescends material index typeLaw actionLaw parent := by
    intro left right related
    have sameQuery : MotherOriginalQueryValue.readQuery left.val =
        MotherOriginalQueryValue.readQuery right.val := by
      simpa only [relateExact] using related
    exact congrArg (fun query => (⟨query,
      (MotherNativePhysicalQuery.nativeInquiry typeLaw actionLaw parent).compileInquiry query⟩ :
      OriginalOutput typeLaw actionLaw parent)) sameQuery
  let compiler : Fiber material index → OriginalOutput typeLaw actionLaw parent :=
    Quot.lift (fun value => MotherOriginalQueryValue.compileRead typeLaw actionLaw parent value.val) descends
  have formed : compile material index typeLaw actionLaw parent = some compiler := dif_pos descends
  refine ⟨compiler, formed, fun query => ?_⟩
  obtain ⟨input, inputExact⟩ := MotherOriginalQueryValue.every_original_query_compiled typeLaw actionLaw parent query
  refine ⟨Quot.mk _ ⟨input, allInside index input⟩, ?_⟩
  exact (compile_rep material index typeLaw actionLaw parent input (allInside index input) compiler formed).trans inputExact

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotient
