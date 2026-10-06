import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Source
import Mathlib.Algebra.Group.Pi.Lemmas

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition
open SourceOperationEffects SourceOperationExecution
namespace P
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.SomePacket
  (step Data Index Carrier OldValue Variable environment expression raw source_seed_eq target_seed_eq)
end P
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
abbrev ChildIndex := Σ code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot,
  StepLedgerSuccessorAt (P.step root recognition code)
def childData (index : ChildIndex root recognition) := Side.generateAt root recognition index.1 (some index.2)
abbrev ChildValue (index : ChildIndex root recognition) :=
  P.Index root recognition index.1 index.2 (childData root recognition index) →
    P.Carrier root recognition index.1 index.2
abbrev ChildVar (index : ChildIndex root recognition) :=
  P.Variable root recognition index.1 index.2 (childData root recognition index) PUnit.unit
abbrev childRaw (index : ChildIndex root recognition) :=
  P.raw root recognition index.1 index.2 (childData root recognition index)
    (P.source_seed_eq root recognition index.1 index.2) (P.target_seed_eq root recognition index.1 index.2)
abbrev OldSlot := Actor.Extension.Slot (S:=Actor.Extension.Slot (S:=SourceOperationNative.Tree.Fold.Slot.{u}))
abbrev Output := Query.Output root visit recognition × (∀ index : ChildIndex root recognition, ChildValue root recognition index)
abbrev Slot := OldSlot.{u} ⊕ (ChildIndex root recognition ⊕ PUnit.{u+1})
abbrev Value : Slot root recognition → Type u
  | .inl slot => Query.Value root visit recognition slot
  | .inr (.inl index) => ChildValue root recognition index
  | .inr (.inr _) => Output root visit recognition
abbrev Variable : Slot root recognition → Type u
  | .inl slot => Query.Variable root visit recognition slot
  | .inr (.inl index) => ChildVar root recognition index
  | .inr (.inr _) => PEmpty.{u+1}
instance : ∀ slot, AddCommGroup (Value root visit recognition slot)
  | .inl _ => inferInstance
  | .inr (.inl _) => inferInstance
  | .inr (.inr _) => inferInstance
abbrev resultSlot : Slot root recognition := .inr (.inr PUnit.unit)
def environment : Env (Value root visit recognition) (Variable root visit recognition)
  | .inl slot, name => Query.environment root visit recognition slot name
  | .inr (.inl index), name => (childRaw root recognition index).environment PUnit.unit name
  | .inr (.inr _), absent => PEmpty.elim absent

def embed {slot : OldSlot.{u}} : Expr (Query.Value root visit recognition) (Query.Variable root visit recognition) slot →
    Expr (Value root visit recognition) (Variable root visit recognition) (.inl slot)
  | .var name => .var name
  | .const value => .const value
  | .add first second => .add (embed first) (embed second)
  | .linear operation argument => .linear operation (embed argument)
  | .bilinear operation first second => .bilinear operation (embed first) (embed second)

def childEmbed (index : ChildIndex root recognition) {slot : PUnit.{u+1}} :
    Expr (InventoryVector.VectorValue
      (P.Index root recognition index.1 index.2 (childData root recognition index))
      (Value:=P.OldValue root recognition index.1 index.2))
      (P.Variable root recognition index.1 index.2 (childData root recognition index)) slot →
    Expr (Value root visit recognition) (Variable root visit recognition) (.inr (.inl index))
  | .var name => .var name
  | .const value => .const value
  | .add first second => .add (childEmbed index first) (childEmbed index second)
  | .linear operation argument => .linear operation (childEmbed index argument)
  | .bilinear operation first second => .bilinear operation (childEmbed index first) (childEmbed index second)

def oldInjection : Query.Output root visit recognition →+ Output root visit recognition := (AddMonoidHom.id _).prod 0
def childInjection (index : ChildIndex root recognition) : ChildValue root recognition index →+ Output root visit recognition := by
  classical
  exact (0 : ChildValue root recognition index →+ Query.Output root visit recognition).prod
    (AddMonoidHom.single (ChildValue root recognition) index)
def outputEmbed (term : Expr (Query.Value root visit recognition) (Query.Variable root visit recognition) (.inr PUnit.unit)) :
    Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  .linear (oldInjection root visit recognition) (embed root visit recognition term)
def childOutput (index : ChildIndex root recognition)
    (term : type_of% (childRaw root recognition index).expression) :
    Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  .linear (childInjection root visit recognition index) (childEmbed root visit recognition index term)

theorem embed_eval {slot : OldSlot.{u}} (term : Expr (Query.Value root visit recognition) (Query.Variable root visit recognition) slot) :
    (embed root visit recognition term).eval (environment root visit recognition) =
      term.eval (Query.environment root visit recognition) := by
  induction term with
  | var => rfl
  | const => rfl
  | add first second one two => exact congrArg₂ (·+·) one two
  | linear operation argument previous => exact congrArg operation previous
  | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two

theorem embed_charge {slot : OldSlot.{u}} (term : Expr (Query.Value root visit recognition) (Query.Variable root visit recognition) slot) :
    remaining (embed root visit recognition term) = remaining term := by
  induction term with
  | var => rfl
  | const => rfl
  | add first second one two => simp only [embed,remaining,one,two]
  | linear operation argument previous => simp only [embed,remaining,previous]
  | bilinear operation first second one two => simp only [embed,remaining,one,two]

theorem child_embed_eval (index : ChildIndex root recognition) {slot : PUnit.{u+1}}
    (term : Expr (InventoryVector.VectorValue
      (P.Index root recognition index.1 index.2 (childData root recognition index))
      (Value:=P.OldValue root recognition index.1 index.2))
      (P.Variable root recognition index.1 index.2 (childData root recognition index)) slot) :
    (childEmbed root visit recognition index term).eval (environment root visit recognition) =
      term.eval (childRaw root recognition index).environment := by
  induction term with
  | var => rfl
  | const => rfl
  | add first second one two => exact congrArg₂ (·+·) one two
  | linear operation argument previous => exact congrArg operation previous
  | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two

theorem child_embed_charge (index : ChildIndex root recognition) {slot : PUnit.{u+1}}
    (term : Expr (InventoryVector.VectorValue
      (P.Index root recognition index.1 index.2 (childData root recognition index))
      (Value:=P.OldValue root recognition index.1 index.2))
      (P.Variable root recognition index.1 index.2 (childData root recognition index)) slot) :
    remaining (childEmbed root visit recognition index term) = remaining term := by
  induction term with
  | var => rfl
  | const => rfl
  | add first second one two => simp only [childEmbed,remaining,one,two]
  | linear operation argument previous => simp only [childEmbed,remaining,previous]
  | bilinear operation first second one two => simp only [childEmbed,remaining,one,two]
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
