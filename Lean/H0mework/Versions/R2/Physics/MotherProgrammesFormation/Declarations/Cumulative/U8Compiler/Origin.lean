import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Context
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Inputs

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherU8Revision
noncomputable section
universe u v
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {Index : Type}

structure Origin (rank : Ordinal.{0}) (state : RootInquiryStateAt N V) (label : Index → state.Query)
    (data : (index : Index) → Data (MotherNativeClause.ofState state (label index))) where
  parts : Parts rank
  rootIndices : (Unit ⊕ Index) ≃ MotherCurrentFamilies.Member parts.roots
  roots : ∀ index, MotherNativeCurrent.Restriction rank (currents state label data index)
    (MotherCurrentFamilies.atMember parts.roots (rootIndices index))
  header : MotherInquirySource.HeaderOrigin (rank := rank) state.U7 state.calculus
  header_materials : parts.header = (header.demandMaterial, header.eventMaterial, header.compilerMaterial)
  indices : Index ≃ MotherAuthorityFamilies.Member parts.indices
  operand : Operand state.root state.visit ↪ MotherArenaHigher.Base rank
  inputsAvailable : (formInputs parts.indices operand parts.inputs).isSome
  face : ∀ index, MotherInquirySource.HeaderOrigin (rank := rank) state.U7 (data index).core.frontier.face.calculus
  face_materials : ∀ index, (childAt parts.children (indices index).val).face =
    ((face index).demandMaterial, (face index).eventMaterial, (face index).compilerMaterial)
  formed : ∀ index,
    formAtContext state label data (roots (.inl ())) header index (roots (.inr index)) (face index)
      ((formInputs parts.indices operand parts.inputs).get inputsAvailable (indices index))
      (childAt parts.children (indices index).val).body = some (MotherNativeClause.ofState state (label index))

variable {rank : Ordinal.{0}} {state : RootInquiryStateAt N V} {label : Index → state.Query}
    {data : (index : Index) → Data (MotherNativeClause.ofState state (label index))}
    (origin : Origin rank state label data)

def Origin.material : MotherArenaHigher.Material rank := packParts origin.parts

theorem Origin.material_parts : unpackParts origin.material = origin.parts := unpack_packParts origin.parts

def Origin.readClause (index : Index) : MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (label index) :=
  (formAtContext state label data (origin.roots (.inl ())) origin.header index (origin.roots (.inr index)) (origin.face index)
    ((formInputs origin.parts.indices origin.operand origin.parts.inputs).get origin.inputsAvailable (origin.indices index))
    (childAt origin.parts.children (origin.indices index).val).body).get (by rw [origin.formed index]; rfl)

theorem Origin.readClause_eq (index : Index) : origin.readClause index = MotherNativeClause.ofState state (label index) :=
  Option.some.inj ((Option.some_get _).trans (origin.formed index))

/-- Read the full clause section on the actually generated index carrier,
while retaining each original query label. -/
def Origin.formedClauses (index : MotherAuthorityFamilies.Member origin.parts.indices) :
    MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (label (origin.indices.symm index)) :=
  origin.readClause (origin.indices.symm index)

private theorem dependent_congr {I : Sort u} {F : I → Sort v} (f : ∀ i, F i)
    {i j : I} (same : i = j) : HEq (f i) (f j) := by
  cases same
  rfl

theorem Origin.formedClause_at (index : Index) :
    HEq (origin.formedClauses (origin.indices index)) (MotherNativeClause.ofState state (label index)) := by
  unfold Origin.formedClauses
  exact (dependent_congr origin.readClause (origin.indices.symm_apply_apply index)).trans
    (heq_of_eq (origin.readClause_eq index))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
