import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.SubquotientInquiry.Inquiry
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Subquotient.Address

/-! Complete native inquiry nodes from higher-law material. The source code
retains the full header and every answered query; it is not a state registry
or an enumeration of an emitted orbit. -/

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeRegistry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision MotherFamilyOccurrence
open scoped Classical

noncomputable section

abbrev Base := MotherSubquotient.Base
abbrev Material := MotherSubquotient.Material
abbrev Ready := MotherSubquotientInquiry.Ready

def inputOf (material : Material) : MotherSubquotientInquiry.Input :=
  let parts := MotherHigherLawValue.split material
  let indexed := MotherHigherLawFamily.unpair (MotherHigherLawValue.readBase parts.2)
  let laws := MotherHigherLawFamily.unpair indexed.2
  ⟨parts.1, indexed.1, laws.1, laws.2⟩

theorem every_input (input : MotherSubquotientInquiry.Input) :
    ∃ material : Material, inputOf material = input := by
  obtain ⟨metadata, recovered⟩ := MotherHigherLawValue.readBase_surjective
    (MotherHigherLawFamily.pair (input.index, MotherHigherLawFamily.pair (input.typeLaw, input.actionLaw)))
  refine ⟨MotherHigherLawValue.pack (input.material, metadata), ?_⟩
  simp only [inputOf, MotherHigherLawValue.split_pack, recovered, MotherHigherLawFamily.unpair_pair]

inductive Node
  | active (ready : Ready) (depth : Nat)
  | answered (ready : Ready) (depth : Nat) (query : MotherSubquotientInquiry.Query ready.val)

def presentation (ready : Ready) (depth : Nat) : RootInquiryStatePresentation :=
  ⟨MaterialN, SpinPair.V, .create (MotherSubquotientInquiry.inquiryAt ready depth)⟩

def view : Node → RootInquiryProcessNode
  | .active ready depth => .active (presentation ready depth)
  | .answered ready depth query => .answered (presentation ready depth) query

abbrev Query (node : Node) := (view node).Query

def anchor : Base := MotherHigherLawValue.readBase (MotherHigherLawValue.scalar 0)

def formNode (material : Material) : Option Node :=
  let head := MotherHigherLawValue.split material
  let duration := MotherHigherLawValue.split head.2
  let tail := MotherHigherLawValue.split duration.2
  match MotherSubquotientInquiry.prepare (inputOf head.1) with
  | none => none
  | some ready =>
      let depth := Nat.floor (MotherHigherLawFormation.read duration.1 anchor 0)
      if MotherHigherLawFormation.read tail.1 anchor 0 = 0 then some (.active ready depth)
      else (MotherSubquotient.formMember ready.val.material ready.val.index
        (MotherHigherLawValue.readBase tail.2)).map (.answered ready depth)

theorem every_node (node : Node) : ∃ material : Material, formNode material = some node := by
  cases node with
  | active ready depth =>
      obtain ⟨head, formed⟩ := every_input ready.val
      refine ⟨MotherHigherLawValue.pack (head,
        MotherHigherLawValue.pack (MotherHigherLawValue.scalar depth,
          MotherHigherLawValue.pack (MotherHigherLawValue.scalar 0, MotherHigherLawValue.scalar 0))), ?_⟩
      simp only [formNode, MotherHigherLawValue.split_pack, formed, MotherSubquotientInquiry.prepare_recovers,
        MotherHigherLawValue.scalar_read, Nat.floor_natCast, ite_true]
  | answered ready depth query =>
      obtain ⟨head, formed⟩ := every_input ready.val
      obtain ⟨value, memberFormed⟩ := MotherSubquotient.every_member ready.val.material ready.val.index query
      obtain ⟨memberCode, memberRead⟩ := MotherHigherLawValue.readBase_surjective value
      refine ⟨MotherHigherLawValue.pack (head,
        MotherHigherLawValue.pack (MotherHigherLawValue.scalar depth,
          MotherHigherLawValue.pack (MotherHigherLawValue.scalar 1, memberCode))), ?_⟩
      simp only [formNode, MotherHigherLawValue.split_pack, formed, MotherSubquotientInquiry.prepare_recovers,
        MotherHigherLawValue.scalar_read, Nat.floor_natCast, one_ne_zero, if_false, memberRead,
        memberFormed, Option.map_some]

def queryAddress : (node : Node) → Query node → Base
  | .active ready _depth, query => MotherSubquotient.address ready.val.material ready.val.index query
  | .answered _ready _depth _prior, query => nomatch query

theorem queryAddress_injective (node : Node) : Function.Injective (queryAddress node) := by
  cases node with
  | active ready depth => exact MotherSubquotient.address_injective ready.val.material ready.val.index
  | answered ready depth prior => intro query; exact nomatch query

def Output : (node : Node) → Query node → Type 11
  | .active ready depth, query =>
      type_of% ((MotherSubquotientInquiry.inquiryAt ready depth).compileInquiry query) ×
        MotherSubquotient.OriginalOutput ready.val.typeLaw ready.val.actionLaw (MotherNativePhysicalQuery.parent depth)
  | .answered _ready _depth _prior, query => nomatch query

def compile : (node : Node) → (query : Query node) → Output node query
  | .active ready depth, query =>
      ((MotherSubquotientInquiry.inquiryAt ready depth).compileInquiry query,
        MotherSubquotientInquiry.oldCompiler ready (MotherNativePhysicalQuery.parent depth) query)
  | .answered _ready _depth _prior, query => nomatch query

theorem compile_full_objects (ready : Ready) (depth : Nat) (query : MotherSubquotientInquiry.Query ready.val) :
    compile (.active ready depth) query =
      ((MotherSubquotientInquiry.inquiryAt ready depth).compileInquiry query,
        ⟨MotherSubquotientInquiry.decode ready query,
          (MotherNativePhysicalQuery.nativeInquiry ready.val.typeLaw ready.val.actionLaw
            (MotherNativePhysicalQuery.parent depth)).compileInquiry (MotherSubquotientInquiry.decode ready query)⟩) := rfl

def nextCurrent : (node : RootInquiryProcessNode) → node.Query → AnyAuthoritativeRootCurrent
  | .active state, query => (.answered state query : RootInquiryProcessNode).erase
  | .answered _state _prior, query => nomatch query

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeRegistry
