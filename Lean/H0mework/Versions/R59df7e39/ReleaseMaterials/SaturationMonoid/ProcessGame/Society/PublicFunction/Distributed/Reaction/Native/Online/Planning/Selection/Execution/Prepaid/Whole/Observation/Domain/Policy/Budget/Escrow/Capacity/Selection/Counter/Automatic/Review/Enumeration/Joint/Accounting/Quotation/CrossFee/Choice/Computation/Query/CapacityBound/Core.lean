import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Payment.Refiner
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound
variable {Key α : Type} [DecidableEq Key] {kind goal : Kind} {P Q : Prop}
def pair (left right : Nat) := left+right+3
def lift (value : Nat) := value+2

theorem bind_bound (body : Code Key kind) (later : Value kind → Code Key goal) {a b : Nat}
    (first : body.cost ≤ a) (rest : ∀ value,(later value).cost ≤ b) : (Code.bind body later).cost ≤ 1+a+b := by
  have := rest body.eval;dsimp only [Code.cost];omega

theorem transport_bound (same : P ↔ Q) (body : Code Key (.truth P)) {a : Nat}
    (within : body.cost ≤ a) : (Code.transport same body).cost ≤ lift a := by
  dsimp only [Code.transport,Code.cost,lift];omega

theorem negative_bound (body : Code Key (.truth P)) {a : Nat}
    (within : body.cost ≤ a) : (Code.negative body).cost ≤ lift a := by
  dsimp only [Code.negative,Code.cost,lift];omega

theorem conjunction_bound (first : Code Key (.truth P)) (later : Unit → Code Key (.truth Q)) {a b : Nat}
    (left : first.cost ≤ a) (right : (later ()).cost ≤ b) : (Code.conjunction first later).cost ≤ pair a b := by
  cases actual : first.eval <;> simp only [Code.conjunction,Code.cost,actual,pair] <;> omega

theorem implication_bound (first : Code Key (.truth P)) (later : Unit → Code Key (.truth Q)) {a b : Nat}
    (left : first.cost ≤ a) (right : (later ()).cost ≤ b) : (Code.implication first later).cost ≤ pair a b := by
  cases actual : first.eval <;> simp only [Code.implication,Code.cost,actual,pair] <;> omega

def lists (budget : α → α → Nat) : List α → List α → Nat
  | [],_ | _::_,[] => 1
  | left::ls,right::rs => lift (pair (budget left right) (lists budget ls rs))
def rows (budget : α → Nat) : List α → Nat
  | [] => 1
  | head::tail => lift (pair (budget head) (rows budget tail))
def count (budget : α → α → Nat) (key : α) : List α → Nat
  | [] => 1
  | head::tail => budget head key+count budget key tail+6
def countLe (budget : α → α → Nat) (key : α) (left right : List α) := count budget key left+count budget key right+6
def subperm (budget : α → α → Nat) (left right : List α) := lift (rows (fun key => countLe budget key left right) left)

theorem equal_bound (encode : α → Key) (faithful : Function.Injective encode) (left right : α) :
    (Source.Generic.equal encode faithful left right).cost ≤ 4 := by
  exact transport_bound _ _ (Nat.le_refl 2)

theorem lists_bound (test : (left right : α) → Code Key (.truth (left = right))) (budget : α → α → Nat)
    (within : ∀ left right,(test left right).cost ≤ budget left right) (left right : List α) :
    (Source.Generic.lists test left right).cost ≤ lists budget left right := by
  induction left generalizing right with
  | nil => cases right <;> exact Nat.le_refl 1
  | cons head tail ih => cases right with
    | nil => exact Nat.le_refl 1
    | cons other rest => exact transport_bound _ _ (conjunction_bound _ _ (within head other) (ih rest))

theorem rows_bound (claim : α → Prop) (make : (item : α) → Code Key (.truth (claim item)))
    (budget : α → Nat) (within : ∀ item,(make item).cost ≤ budget item) (items : List α) :
    (Source.Generic.rows claim make items).cost ≤ rows budget items := by
  induction items with
  | nil => exact Nat.le_refl 1
  | cons head tail ih => exact transport_bound _ _ (conjunction_bound _ _ (within head) ih)

theorem count_bound [DecidableEq α] (test : (left right : α) → Code Key (.truth (left = right))) (budget : α → α → Nat)
    (within : ∀ left right,(test left right).cost ≤ budget left right) (key : α) (items : List α) :
    (Source.Generic.count test key items).cost ≤ count budget key items := by
  induction items with
  | nil => exact Nat.le_refl 1
  | cons head tail ih =>
      apply Nat.le_trans (bind_bound (test head key) _ (within head key) (b := count budget key tail+5) ?_)
      · dsimp only [count];omega
      intro answer;cases answer with
      | isFalse different =>
          apply Nat.le_trans (bind_bound _ _ ih (b := 1) ?_)
          · omega
          intro later;exact Nat.le_refl 1
      | isTrue same =>
          apply Nat.le_trans (bind_bound _ _ ih (b := 4) ?_)
          · omega
          intro later
          refine bind_bound _ _ (a := 2) (b := 1) ?_ ?_
          · exact Nat.le_refl 2
          intro next;exact Nat.le_refl 1

theorem countLe_bound [DecidableEq α] (test : (left right : α) → Code Key (.truth (left = right))) (budget : α → α → Nat)
    (within : ∀ left right,(test left right).cost ≤ budget left right) (key : α) (left right : List α) :
    (Source.Generic.countLe test key left right).cost ≤ countLe budget key left right := by
  unfold Source.Generic.countLe
  apply Nat.le_trans (bind_bound _ _ (count_bound test budget within key left) (b := 1+count budget key right+4) ?_)
  · dsimp only [countLe];omega
  intro first
  exact bind_bound _ _ (count_bound test budget within key right) (b := 4) (fun second =>
    transport_bound _ (.atom (.natural first.val second.val) : Code Key (.truth (first.val ≤ second.val))) (Nat.le_refl 2))

theorem subperm_bound [DecidableEq α] (test : (left right : α) → Code Key (.truth (left = right))) (budget : α → α → Nat)
    (within : ∀ left right,(test left right).cost ≤ budget left right) (left right : List α) :
    (Source.Generic.subperm test left right).cost ≤ subperm budget left right :=
  transport_bound _ _ (rows_bound _ _ _ (fun key => countLe_bound test budget within key left right) left)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound
