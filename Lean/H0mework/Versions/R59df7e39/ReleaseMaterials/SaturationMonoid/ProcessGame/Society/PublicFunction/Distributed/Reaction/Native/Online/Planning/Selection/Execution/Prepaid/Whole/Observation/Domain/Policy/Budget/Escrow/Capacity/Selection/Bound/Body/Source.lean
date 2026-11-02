import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Bound
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.BodySource
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} (prepared : Prepared input)

theorem literal_units (n : Nat) : (Budget.lit (prepared := prepared) n).work.length = 1 := rfl
theorem plus_units {a b : Nat} (left : Budget.Run prepared a) (right : Budget.Run prepared b) :
    (Budget.plus left right).work.length = left.work.length+right.work.length+1 := by
  change (left.work ++ right.work ++ [_]).length = _
  simp only [List.length_append,List.length_singleton]
theorem times_units {a b : Nat} (left : Budget.Run prepared a) (right : Budget.Run prepared b) :
    (Budget.times left right).work.length = left.work.length+right.work.length+1 := by
  change (left.work ++ right.work ++ [_]).length = _
  simp only [List.length_append,List.length_singleton]
theorem largest_units {a b : Nat} (left : Budget.Run prepared a) (right : Budget.Run prepared b) :
    (Budget.largest left right).work.length = left.work.length+right.work.length+1 := by
  change (left.work ++ right.work ++ [_]).length = _
  simp only [List.length_append,List.length_singleton]
theorem mark_units {n : Nat} (tag : Budget.Tag) (made : Budget.Run prepared n) :
    (Budget.mark tag made).work.length = made.work.length+1 := by
  change (Budget.Event.branch tag :: made.work).length = _
  simp only [List.length_cons]

def mark (_tag : Budget.Tag) (cost : Nat) := cost+1

local infixl:65 " ⊞ " => fun a b : Nat => a+b+1
local infixl:70 " ⊠ " => fun a b : Nat => a+b+1

def lists {α : Type} (cost : α → α → Nat) : List α → List α → Nat
  | a::as,b::bs => cost a b + lists cost as bs + 4
  | [],[] | [],_::_ | _::_,[] => 2
def optional {α : Type} (cost : α → α → Nat) : Option α → Option α → Nat
  | some left,some right => cost left right + 3
  | none,none | none,some _ | some _,none => 2

theorem lists_exact {α : Type} (budget : α → α → Nat) (run : (left right : α) → Budget.Run prepared (budget left right))
    (cost : α → α → Nat) (same : ∀ left right,(run left right).work.length = cost left right) (left right : List α) :
    (Budget.lists budget run left right).work.length = lists cost left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a as ih =>
    cases right with
    | nil => rfl
    | cons b bs =>
      rw [Budget.lists,mark_units prepared,plus_units prepared,plus_units prepared,literal_units prepared,same,ih]
      simp only [lists];omega

theorem optional_exact {α : Type} (budget : α → α → Nat) (run : (left right : α) → Budget.Run prepared (budget left right))
    (cost : α → α → Nat) (same : ∀ left right,(run left right).work.length = cost left right) (left right : Option α) :
    (Budget.optional budget run left right).work.length = optional cost left right := by
  cases left <;> cases right
  all_goals
    dsimp only [SignatureWork.optionalBudget]
    rw [Budget.optional,mark_units prepared]
    try rw [plus_units prepared]
    rw [literal_units prepared]
    try rw [same]
  all_goals simp only [optional]
  all_goals omega

def parties (left right : List P) := lists (fun _ _ => 1) left right
def ports (left right : List O) := lists (fun _ _ => 1) left right
def bundle (left right : Bundle G) := lists (fun _ _ => 5) left right

theorem parties_exact (left right : List P) : (Budget.parties (prepared := prepared) left right).work.length = parties left right :=
  lists_exact prepared _ _ _ (fun _ _ => rfl) _ _
theorem ports_exact (left right : List O) : (Budget.ports (prepared := prepared) left right).work.length = ports left right :=
  lists_exact prepared _ _ _ (fun _ _ => rfl) _ _
theorem bundle_exact (left right : Bundle G) : (Budget.bundle (prepared := prepared) left right).work.length = bundle left right :=
  lists_exact prepared _ _ _ (fun _ _ => rfl) _ _
def operation : (left right : Institutions.Capitalism.Universal.Source.Program.Operation P G (Mandate.State P T) I) →
    Nat
  | .produce _,.produce _ => (1 ⊞ 1) + 1
  | .transfer _ _ goodsL,.transfer _ _ goodsR => mark .operation
      (1 ⊞ (1 ⊞ 1 ⊞ (1 ⊞ 1 ⊞ bundle goodsL goodsR)))
  | .use _ goodsL _,.use _ goodsR _ => mark .operation
      (1 ⊞ (1 ⊞ 1 ⊞ (bundle goodsL goodsR ⊞ 1 ⊞ 1)))
  | .issue _ _ _ _,.issue _ _ _ _ => mark .operation
      (1 ⊞ (1 ⊞ 1 ⊞ (1 ⊞ 1 ⊞ (1 ⊞ 1 ⊞ 1))))
  | .assign _ _ _ _ _,.assign _ _ _ _ _ => mark .operation
      (1 ⊞ (1 ⊞ 1 ⊞ (1 ⊞ 1 ⊞ (1 ⊞ 1 ⊞ (1 ⊞ 1 ⊞ 1)))))
  | .settle _ _ _ _,.settle _ _ _ _ => mark .operation
      (1 ⊞ (1 ⊞ 1 ⊞ (1 ⊞ 1 ⊞ (1 ⊞ 1 ⊞ 1))))
  | .revise _ _,.revise _ _ => mark .operation
      (1 ⊞ (1 ⊞ 1 ⊞ 1))
  | .produce _,.transfer _ _ _ => (1) + 1
  | .produce _,.use _ _ _ => (1) + 1
  | .produce _,.issue _ _ _ _ => (1) + 1
  | .produce _,.assign _ _ _ _ _ => (1) + 1
  | .produce _,.settle _ _ _ _ => (1) + 1
  | .produce _,.revise _ _ => (1) + 1
  | .produce _,.present => (1) + 1
  | .transfer _ _ _,.produce _ => (1) + 1
  | .transfer _ _ _,.use _ _ _ => (1) + 1
  | .transfer _ _ _,.issue _ _ _ _ => (1) + 1
  | .transfer _ _ _,.assign _ _ _ _ _ => (1) + 1
  | .transfer _ _ _,.settle _ _ _ _ => (1) + 1
  | .transfer _ _ _,.revise _ _ => (1) + 1
  | .transfer _ _ _,.present => (1) + 1
  | .use _ _ _,.produce _ => (1) + 1
  | .use _ _ _,.transfer _ _ _ => (1) + 1
  | .use _ _ _,.issue _ _ _ _ => (1) + 1
  | .use _ _ _,.assign _ _ _ _ _ => (1) + 1
  | .use _ _ _,.settle _ _ _ _ => (1) + 1
  | .use _ _ _,.revise _ _ => (1) + 1
  | .use _ _ _,.present => (1) + 1
  | .issue _ _ _ _,.produce _ => (1) + 1
  | .issue _ _ _ _,.transfer _ _ _ => (1) + 1
  | .issue _ _ _ _,.use _ _ _ => (1) + 1
  | .issue _ _ _ _,.assign _ _ _ _ _ => (1) + 1
  | .issue _ _ _ _,.settle _ _ _ _ => (1) + 1
  | .issue _ _ _ _,.revise _ _ => (1) + 1
  | .issue _ _ _ _,.present => (1) + 1
  | .assign _ _ _ _ _,.produce _ => (1) + 1
  | .assign _ _ _ _ _,.transfer _ _ _ => (1) + 1
  | .assign _ _ _ _ _,.use _ _ _ => (1) + 1
  | .assign _ _ _ _ _,.issue _ _ _ _ => (1) + 1
  | .assign _ _ _ _ _,.settle _ _ _ _ => (1) + 1
  | .assign _ _ _ _ _,.revise _ _ => (1) + 1
  | .assign _ _ _ _ _,.present => (1) + 1
  | .settle _ _ _ _,.produce _ => (1) + 1
  | .settle _ _ _ _,.transfer _ _ _ => (1) + 1
  | .settle _ _ _ _,.use _ _ _ => (1) + 1
  | .settle _ _ _ _,.issue _ _ _ _ => (1) + 1
  | .settle _ _ _ _,.assign _ _ _ _ _ => (1) + 1
  | .settle _ _ _ _,.revise _ _ => (1) + 1
  | .settle _ _ _ _,.present => (1) + 1
  | .revise _ _,.produce _ => (1) + 1
  | .revise _ _,.transfer _ _ _ => (1) + 1
  | .revise _ _,.use _ _ _ => (1) + 1
  | .revise _ _,.issue _ _ _ _ => (1) + 1
  | .revise _ _,.assign _ _ _ _ _ => (1) + 1
  | .revise _ _,.settle _ _ _ _ => (1) + 1
  | .revise _ _,.present => (1) + 1
  | .present,.produce _ => (1) + 1
  | .present,.transfer _ _ _ => (1) + 1
  | .present,.use _ _ _ => (1) + 1
  | .present,.issue _ _ _ _ => (1) + 1
  | .present,.assign _ _ _ _ _ => (1) + 1
  | .present,.settle _ _ _ _ => (1) + 1
  | .present,.revise _ _ => (1) + 1
  | .present,.present => (1) + 1
theorem operation_exact (left right : Institutions.Capitalism.Universal.Source.Program.Operation P G (Mandate.State P T) I) :
    (Budget.operation (prepared := prepared) left right).work.length = operation left right := by
  cases left <;> cases right
  all_goals
    dsimp only [ActionWork.operationBudget]
    simp only [Budget.operation,operation,mark]
    repeat' first | rw [mark_units prepared] | rw [plus_units prepared] | rw [literal_units prepared] | rw [bundle_exact prepared]
  all_goals simp only [Budget.field,Budget.read,List.length_singleton]

def request (left right : Future.Recovery.Action seed) : Nat :=
  (1 ⊞ (1 ⊞ 1 ⊞ (parties left.consents right.consents ⊞ 1 ⊞
    (1 ⊞ 1 ⊞ (ports left.gates right.gates ⊞ 1 ⊞ operation left.operation right.operation)))))+1

def word (left right : List (Future.Recovery.Action seed)) := lists request left right
def words (left right : List (List (Future.Recovery.Action seed))) := lists word left right
def invoice (left right : Option (List (Future.Recovery.Action seed))) := optional word left right
def control (left right : List (Option (List (List (Future.Recovery.Action seed))))) := lists (optional words) left right

theorem request_exact (left right : Future.Recovery.Action seed) :
    (Budget.request (prepared := prepared) left right).work.length = request left right := by
  dsimp only [ActionWork.budget]
  simp only [Budget.request,request]
  repeat' first | rw [mark_units prepared] | rw [plus_units prepared] | rw [literal_units prepared] | rw [parties_exact prepared] | rw [ports_exact prepared] | rw [operation_exact prepared]
  all_goals simp only [Budget.field,Budget.read,List.length_singleton]

theorem word_exact (left right : List (Future.Recovery.Action seed)) : (Budget.word (prepared := prepared) left right).work.length = word left right :=
  lists_exact prepared _ _ _ (request_exact prepared) _ _
theorem words_exact (left right : List (List (Future.Recovery.Action seed))) : (Budget.words (prepared := prepared) left right).work.length = words left right :=
  lists_exact prepared _ _ _ (word_exact prepared) _ _
theorem invoice_exact (left right : Option (List (Future.Recovery.Action seed))) : (Budget.invoice (prepared := prepared) left right).work.length = invoice left right :=
  optional_exact prepared _ _ _ (word_exact prepared) _ _
theorem control_exact (left right : List (Option (List (List (Future.Recovery.Action seed))))) :
    (Budget.control (prepared := prepared) left right).work.length = control left right :=
  lists_exact prepared _ _ _ (optional_exact prepared _ _ _ (words_exact prepared)) _ _
def signature : (left right : Signature (Future.Recovery.Action seed)) → Nat
  | .keep a,.keep b => (1 ⊞ word a b) + 1
  | .direct a c,.direct b d => (1 ⊞ (word a b ⊞ 1 ⊞ control c d)) + 1
  | .own a r c,.own b s d => (1 ⊞ (word a b ⊞ 1 ⊞ (word r s ⊞ 1 ⊞ control c d))) + 1
  | .invoiced a r i c,.invoiced b s j d => (1 ⊞ (word a b ⊞ 1 ⊞ (word r s ⊞ 1 ⊞ (invoice i j ⊞ 1 ⊞ control c d)))) + 1
  | .stopped a,.stopped b => (1 ⊞ invoice a b) + 1
  | .prefix a n,.prefix b m => (1 ⊞ (words a b ⊞ 1 ⊞ signature n m)) + 1
  | .keep _,.direct _ _ => (1) + 1
  | .keep _,.own _ _ _ => (1) + 1
  | .keep _,.invoiced _ _ _ _ => (1) + 1
  | .keep _,.stopped _ => (1) + 1
  | .keep _,.prefix _ _ => (1) + 1
  | .direct _ _,.keep _ => (1) + 1
  | .direct _ _,.own _ _ _ => (1) + 1
  | .direct _ _,.invoiced _ _ _ _ => (1) + 1
  | .direct _ _,.stopped _ => (1) + 1
  | .direct _ _,.prefix _ _ => (1) + 1
  | .own _ _ _,.keep _ => (1) + 1
  | .own _ _ _,.direct _ _ => (1) + 1
  | .own _ _ _,.invoiced _ _ _ _ => (1) + 1
  | .own _ _ _,.stopped _ => (1) + 1
  | .own _ _ _,.prefix _ _ => (1) + 1
  | .invoiced _ _ _ _,.keep _ => (1) + 1
  | .invoiced _ _ _ _,.direct _ _ => (1) + 1
  | .invoiced _ _ _ _,.own _ _ _ => (1) + 1
  | .invoiced _ _ _ _,.stopped _ => (1) + 1
  | .invoiced _ _ _ _,.prefix _ _ => (1) + 1
  | .stopped _,.keep _ => (1) + 1
  | .stopped _,.direct _ _ => (1) + 1
  | .stopped _,.own _ _ _ => (1) + 1
  | .stopped _,.invoiced _ _ _ _ => (1) + 1
  | .stopped _,.prefix _ _ => (1) + 1
  | .prefix _ _,.keep _ => (1) + 1
  | .prefix _ _,.direct _ _ => (1) + 1
  | .prefix _ _,.own _ _ _ => (1) + 1
  | .prefix _ _,.invoiced _ _ _ _ => (1) + 1
  | .prefix _ _,.stopped _ => (1) + 1


theorem signature_exact (left right : Signature (Future.Recovery.Action seed)) :
    (Budget.signature (prepared := prepared) left right).work.length = signature left right := by
  induction left generalizing right <;> cases right
  all_goals
    dsimp only [SignatureWork.Generic.budget]
    simp only [Budget.signature,signature]
    repeat' first | rw [mark_units prepared] | rw [plus_units prepared] | rw [literal_units prepared] | rw [word_exact prepared] | rw [words_exact prepared] | rw [invoice_exact prepared] | rw [control_exact prepared]
    all_goals simp_all only [Nat.add_assoc]


def length {α : Type} (items : List α) := 3*items.length+2
theorem length_exact {α : Type} (items : List α) : (Budget.length (prepared := prepared) items).work.length = length items := by
  induction items with
  | nil => rfl
  | cons head tail ih => rw [Budget.length,mark_units prepared,plus_units prepared,literal_units prepared,ih];simp only [length,List.length_cons];omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.BodySource
