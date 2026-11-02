import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound.Refiner
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Meter
variable {Key : Type} [DecidableEq Key]
abbrev Number (expected : Nat) := Code Key (.number (fun value => value = expected))

def literal (value : Nat) : Number (Key := Key) value := .pure ⟨value,rfl⟩

-- Recursion stays behind the executed increment; the initial code does not build a unary spine.
def add (left : Nat) : (right : Nat) → Number (Key := Key) (left+right)
  | 0 => .pure ⟨left,rfl⟩
  | right+1 => .bind (.atom (.increment left)) fun next =>
      .bind (add next.val right) fun answer => .pure ⟨answer.val,by rw [answer.property,next.property];omega⟩

def multiply (left : Nat) : (right : Nat) → Number (Key := Key) (left*right)
  | 0 => .pure ⟨0,by simp⟩
  | right+1 => .bind (multiply left right) fun previous =>
      .bind (add previous.val left) fun answer => .pure ⟨answer.val,by rw [answer.property,previous.property];simp [Nat.mul_succ]⟩

def maximum (left right : Nat) : Number (Key := Key) (Nat.max left right) :=
  .bind (.atom (.natural left right)) fun answer => match answer with
  | .isTrue yes => .pure ⟨right,(Nat.max_eq_right yes).symm⟩
  | .isFalse no => .pure ⟨left,(Nat.max_eq_left (Nat.le_of_not_ge no)).symm⟩

def plus {a b : Nat} (first : Number (Key := Key) a) (later : Unit → Number (Key := Key) b) : Number (Key := Key) (a+b) :=
  .bind first fun left => .bind (later ()) fun right => .bind (add left.val right.val) fun answer =>
    .pure ⟨answer.val,by rw [answer.property,left.property,right.property]⟩
def pair {a b : Nat} (first : Number (Key := Key) a) (later : Unit → Number (Key := Key) b) : Number (Key := Key) (CapacityBound.pair a b) :=
  .bind (plus first later) fun total => .bind (add total.val 3) fun answer =>
    .pure ⟨answer.val,by rw [answer.property,total.property];rfl⟩
def lift {a : Nat} (body : Number (Key := Key) a) : Number (Key := Key) (CapacityBound.lift a) :=
  .bind body fun value => .bind (add value.val 2) fun answer => .pure ⟨answer.val,by rw [answer.property,value.property];rfl⟩

def length {α : Type} : (items : List α) → Number (Key := Key) items.length
  | [] => literal 0
  | _::tail => .bind (length tail) fun rest => .bind (.atom (.increment rest.val)) fun answer =>
      .pure ⟨answer.val,by rw [answer.property,rest.property];rfl⟩

def lists {α : Type} {budget : α → α → Nat} (make : (left right : α) → Number (Key := Key) (budget left right)) :
    (left right : List α) → Number (Key := Key) (CapacityBound.lists budget left right)
  | [],_ | _::_,[] => literal 1
  | left::ls,right::rs => lift (pair (make left right) (fun _ => lists make ls rs))
def rows {α : Type} {budget : α → Nat} (make : (item : α) → Number (Key := Key) (budget item)) :
    (items : List α) → Number (Key := Key) (CapacityBound.rows budget items)
  | [] => literal 1
  | head::tail => lift (pair (make head) (fun _ => rows make tail))
def count {α : Type} {budget : α → α → Nat} (make : (left right : α) → Number (Key := Key) (budget left right)) (key : α) :
    (items : List α) → Number (Key := Key) (CapacityBound.count budget key items)
  | [] => literal 1
  | head::tail => .bind (plus (make head key) (fun _ => count make key tail)) fun total =>
      .bind (add total.val 6) fun answer => .pure ⟨answer.val,by rw [answer.property,total.property];rfl⟩
def countLe {α : Type} {budget : α → α → Nat} (make : (left right : α) → Number (Key := Key) (budget left right))
    (key : α) (left right : List α) : Number (Key := Key) (CapacityBound.countLe budget key left right) :=
  .bind (plus (count make key left) (fun _ => count make key right)) fun total =>
    .bind (add total.val 6) fun answer => .pure ⟨answer.val,by rw [answer.property,total.property];rfl⟩
def subperm {α : Type} {budget : α → α → Nat} (make : (left right : α) → Number (Key := Key) (budget left right))
    (left right : List α) : Number (Key := Key) (CapacityBound.subperm budget left right) :=
  lift (rows (fun key => countLe make key left right) left)

private theorem max_append (left right : List Nat) : (left++right).foldr Nat.max 0 = Nat.max (left.foldr Nat.max 0) (right.foldr Nat.max 0) := by
  induction left with
  | nil => simp
  | cons head tail ih => simp only [List.cons_append,List.foldr_cons,ih,Nat.max_assoc]

def maxRows {α : Type} {budget : α → Nat} (make : (item : α) → Number (Key := Key) (budget item)) :
    (items : List α) → Number (Key := Key) ((items.map budget).foldr Nat.max 0)
  | [] => literal 0
  | head::tail => .bind (make head) fun first => .bind (maxRows make tail) fun later =>
      .bind (maximum first.val later.val) fun answer => .pure ⟨answer.val,by rw [answer.property,first.property,later.property];rfl⟩

def maxPairs {α : Type} {budget : α → α → Nat} (make : (left right : α) → Number (Key := Key) (budget left right)) (columns : List α) :
    (lines : List α) → Number (Key := Key) ((lines.flatMap fun line => columns.map (budget line)).foldr Nat.max 0)
  | [] => literal 0
  | head::tail => .bind (maxRows (make head) columns) fun first => .bind (maxPairs make columns tail) fun later =>
      .bind (maximum first.val later.val) fun answer => .pure ⟨answer.val,by
        rw [answer.property,first.property,later.property]
        simp only [List.flatMap_cons,max_append]⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Meter
