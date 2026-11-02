import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeInventory
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Tensor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeBenefit
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol

/-- Explicit semantic comparison instructions; operand acquisition and the internals of
    an abstract DecidableEq instance are separate source-computation obligations. -/
inductive Event (Key : Type) where
  | source (operand : Key)
  | keyEqual (left right : Key) (answer : Bool)
  | rationalLe (left right : ℚ) (answer : Bool)
  | naturalLe (left right : Nat) (answer : Bool)
  | boolean (value : Bool)
  | branch (taken : Bool)
  | increment (before : Nat)

structure Check (Key : Type) (P : Prop) where
  private mk ::
  decision : Decidable P
  work : List (Event Key)

def Check.value {Key : Type} {P : Prop} (made : Check Key P) := @decide P made.decision

variable {Key : Type}
def transport {P Q : Prop} (same : P ↔ Q) (made : Check Key P) : Check Key Q :=
  ⟨match made.decision with
    | .isTrue yes => .isTrue (same.mp yes)
    | .isFalse no => .isFalse (fun yes => no (same.mpr yes)),made.work⟩

def conjunction {P Q : Prop} (first : Check Key P) (later : Unit → Check Key Q) : Check Key (P ∧ Q) :=
  match first.decision with
  | .isFalse no => ⟨.isFalse (fun both => no both.1),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun both => no both.2)
      | .isTrue other => .isTrue ⟨yes,other⟩,first.work ++ [.branch true] ++ second.work⟩

def implication {P Q : Prop} (first : Check Key P) (later : Unit → Check Key Q) : Check Key (P → Q) :=
  match first.decision with
  | .isFalse no => ⟨.isTrue (fun yes => False.elim (no yes)),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun accepts => no (accepts yes))
      | .isTrue other => .isTrue (fun _ => other),first.work ++ [.branch true] ++ second.work⟩

def allRows {α : Type} (P : α → Prop) (test : (item : α) → Check Key (P item)) :
    (items : List α) → Check Key (∀ item ∈ items,P item)
  | [] => ⟨.isTrue (by simp),[]⟩
  | head::tail => transport (by simp only [List.mem_cons,forall_eq_or_imp])
      (conjunction (test head) (fun _ => allRows P test tail))

def boolean (value : Bool) : Check Key (value = true) :=
  ⟨inferInstance,[.boolean value]⟩
def naturalLe (left right : Nat) : Check Key (left ≤ right) :=
  let answer := inferInstanceAs (Decidable (left ≤ right))
  ⟨answer,[.naturalLe left right (@decide _ answer)]⟩
def rationalLe (left right : ℚ) : Check Key (left ≤ right) :=
  let answer := inferInstanceAs (Decidable (left ≤ right))
  ⟨answer,[.rationalLe left right (@decide _ answer)]⟩

def equal [DecidableEq Key] (left right : Key) : Check Key (left = right) :=
  let answer := inferInstanceAs (Decidable (left = right))
  ⟨answer,[.keyEqual left right (@decide _ answer)]⟩

def Event.rekey {Other : Type} (encode : Key → Other) : Event Key → Event Other
  | .source operand => .source (encode operand)
  | .keyEqual left right answer => .keyEqual (encode left) (encode right) answer
  | .rationalLe left right answer => .rationalLe left right answer
  | .naturalLe left right answer => .naturalLe left right answer
  | .boolean value => .boolean value
  | .branch taken => .branch taken
  | .increment before => .increment before

def rekey {Other : Type} (encode : Key → Other) (_faithful : Function.Injective encode)
    {P : Prop} (made : Check Key P) : Check Other P :=
  ⟨made.decision,made.work.map (Event.rekey encode)⟩

def record {P : Prop} (work : List (Event Key)) (made : Check Key P) : Check Key P :=
  ⟨made.decision,work ++ made.work⟩

structure Counted (Key : Type) [DecidableEq Key] (key : Key) (items : List Key) where
  private mk ::
  count : Nat
  exact : count = items.count key
  work : List (Event Key)

def count [DecidableEq Key] (key : Key) : (items : List Key) → Counted Key key items
  | [] => ⟨0,rfl,[]⟩
  | head::tail =>
    if same : head = key then
      let rest := count key tail
      ⟨rest.count+1,by simp only [List.count_cons];simp [same,rest.exact],
        [.keyEqual head key true,.branch true] ++ rest.work ++ [.increment rest.count]⟩
    else
      let rest := count key tail
      ⟨rest.count,by simp only [List.count_cons];simp [same,rest.exact],
        [.keyEqual head key false,.branch false] ++ rest.work⟩

def countLe [DecidableEq Key] (key : Key) (left right : List Key) :
    Check Key (left.count key ≤ right.count key) :=
  let first := count key left
  let second := count key right
  let compared := naturalLe first.count second.count
  ⟨match compared.decision with
    | .isTrue yes => .isTrue (by simpa only [first.exact,second.exact] using yes)
    | .isFalse no => .isFalse (fun yes => no (by simpa only [first.exact,second.exact] using yes)),
    first.work ++ second.work ++ compared.work⟩

/-- Multiplicity is checked by an actual finite equality/count scan, not a Subperm oracle. -/
def subperm [DecidableEq Key] (left right : List Key) : Check Key (left.Subperm right) :=
  transport List.subperm_ext_iff.symm
    (allRows (fun key => left.count key ≤ right.count key) (fun key => countLe key left right) left)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} (cursor : Cursor seed driver)
abbrev NativeKey := Feedback.Authority.Trace.Lawful.Key Party Good Port Technology Instrument

inductive WorkKey (Party Good Port Technology Instrument : Type) where
  | identity (value : Feedback.Authority.Trace.Lawful.Key Party Good Port Technology Instrument)
  | construction (value : NativeInventory.Event Party Good Port Technology Instrument)
  deriving DecidableEq

def inventoryDue (new previous : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) :
    Check (WorkKey Party Good Port Technology Instrument)
      ((Feedback.Authority.Trace.Lawful.inventory new).due.Subperm (Feedback.Authority.Trace.Lawful.inventory previous).due) :=
  let current := NativeInventory.compile new
  let original := NativeInventory.compile previous
  record ((current.work ++ original.work).map (fun event => .source (.construction event)))
    (transport (by rw [current.exact,original.exact])
      (rekey WorkKey.identity (by intro a b h;cases h;rfl)
        (subperm current.inventory.due original.inventory.due)))

/-- The source snapshots stay indexed by the original code and economic coordinates. -/
def present (new previous : Evaluation cursor.source.val.code) :
    Check (WorkKey Party Good Port Technology Instrument)
      (evaluationBenefit cursor new previous) :=
  conjunction (implication (boolean previous.legal) (fun _ => boolean new.legal)) (fun _ =>
    conjunction (implication (boolean previous.complete) (fun _ => boolean new.complete)) (fun _ =>
      conjunction (inventoryDue new.native previous.native) (fun _ =>
        allRows (fun axis => new.value axis ≤ previous.value axis)
          (fun axis => rationalLe (new.value axis) (previous.value axis)) (Window.axes cursor.model cursor.depth))))

def future (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    Check (WorkKey Party Good Port Technology Instrument)
      (Planning.futureBenefit cursor new previous) :=
  match new,previous with
  | none,none | some _,none => ⟨.isTrue trivial,[.branch false]⟩
  | none,some _ => ⟨.isFalse id,[.branch true]⟩
  | some current,some original =>
      let evaluated := conjunction (naturalLe original.consumed current.consumed)
        (fun _ => present cursor current.evaluation original.evaluation)
      ⟨evaluated.decision,[.branch true] ++ evaluated.work⟩

theorem present_is_the_original_complete_benefit (new previous : Evaluation cursor.source.val.code) :
    (present cursor new previous).value = decide (evaluationBenefit cursor new previous) := by
  unfold Check.value
  exact Subsingleton.elim _ _ |> fun same => congrArg (fun d => @decide _ d) same

theorem future_is_the_original_complete_future_benefit
    (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (future cursor new previous).value = decide (Planning.futureBenefit cursor new previous) := by
  unfold Check.value
  exact Subsingleton.elim _ _ |> fun same => congrArg (fun d => @decide _ d) same
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeBenefit
