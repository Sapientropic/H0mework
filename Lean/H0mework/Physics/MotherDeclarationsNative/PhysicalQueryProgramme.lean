import H0mework.Physics.MotherDeclarationsJoint.CarrierFormationFactory

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery

open MotherFamilyOccurrence MotherTypeFormation Stage9C.Revision

noncomputable section

abbrev Law := MotherPhysicalLaws.Law
abbrev Term := MemberMaterial × ℕ
abbrev Word := List Term
abbrev Query := List (ℕ × Word)

def parent (code : ℕ) : MotherVisit := SpinPair.visit (10 + code)

theorem parent_code (code : ℕ) : StageEightDiscreteFormation.codeOf (parent code) = code :=
  StageEightDiscreteFormation.code_at code

def pack {Value : Type*} (values : List Value) :
    Σ parent : MotherVisit, Fin (StageEightDiscreteFormation.codeOf parent) → Value :=
  ⟨parent values.length, fun index => values.get (Fin.cast (parent_code values.length) index)⟩

theorem unpack_pack {Value : Type*} (values : List Value) : List.ofFn (pack values).2 = values := by
  apply List.ext_get
  · simp [pack, parent_code]
  · intro index firstBound lastBound
    simp [pack]

def expandTerm (term : Term) : TermMaterial := (term.1, parent term.2)
def encodeTerm (term : TermMaterial) : Term := (term.1, StageEightDiscreteFormation.codeOf term.2)

def expandWord (word : Word) : WordMaterial := pack (word.map expandTerm)
def encodeWord (word : WordMaterial) : Word := (List.ofFn word.2).map encodeTerm

def expandOrbit (orbit : ℕ × Word) : MotherJointCarrier.OrbitMaterial :=
  (parent orbit.1, expandWord orbit.2)

def encodeOrbit (orbit : MotherJointCarrier.OrbitMaterial) : ℕ × Word :=
  (StageEightDiscreteFormation.codeOf orbit.1, encodeWord orbit.2)

def expand (query : Query) : MotherJointCarrier.Material := pack (query.map expandOrbit)
def encode (material : MotherJointCarrier.Material) : Query := (MotherJointCarrier.items material).map encodeOrbit

theorem expandWord_terms (word : Word) : List.ofFn (expandWord word).2 = word.map expandTerm :=
  unpack_pack _

theorem expand_items (query : Query) : MotherJointCarrier.items (expand query) = query.map expandOrbit :=
  unpack_pack _

theorem encodeTerm_expandTerm (term : Term) : encodeTerm (expandTerm term) = term := by
  rcases term with ⟨member, address⟩
  exact congrArg (member, ·) (parent_code address)

theorem encodeWord_expandWord (word : Word) : encodeWord (expandWord word) = word := by
  rw [encodeWord, expandWord_terms, List.map_map]
  simp only [Function.comp_def, encodeTerm_expandTerm]
  exact List.map_id _

/-- All finite programme positions, complete member materials and integer addresses recover exactly. -/
theorem encode_expand (query : Query) : encode (expand query) = query := by
  rw [encode, expand_items, List.map_map]
  have one (orbit : ℕ × Word) : encodeOrbit (expandOrbit orbit) = orbit := by
    rcases orbit with ⟨stage, word⟩
    exact Prod.ext (parent_code stage) (encodeWord_expandWord word)
  simp only [Function.comp_def, one]
  exact List.map_id _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery
