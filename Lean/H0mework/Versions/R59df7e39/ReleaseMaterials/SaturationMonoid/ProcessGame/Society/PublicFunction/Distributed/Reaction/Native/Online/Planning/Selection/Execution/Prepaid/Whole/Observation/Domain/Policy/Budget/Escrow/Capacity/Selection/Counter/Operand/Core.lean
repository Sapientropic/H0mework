import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Expand
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} {pool : Comparison.Pool catalogue}

inductive Formula where
  | literal (value : Nat)
  | binary (opcode : Counter.Opcode) (left right : Formula)
def Formula.value : Formula → Nat
  | .literal value => value
  | .binary opcode left right => (opcode.operation left.value right.value).value
instance (n : Nat) : OfNat Formula n := ⟨.literal n⟩
instance : Add Formula := ⟨.binary .add⟩
instance : Mul Formula := ⟨.binary .multiply⟩
def Formula.render : Formula → Counter.Expression pool
  | .literal value => .literal value
  | .binary opcode left right => .binary opcode left.render right.render
theorem Formula.render_value (source : Formula) : (source.render (pool := pool)).value = source.value := by
  induction source with
  | literal => rfl
  | binary opcode left right ihL ihR => simp only [render,Counter.Expression.value,ihL,ihR,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value]
theorem add_value (left right : Formula) : (left+right).value = left.value+right.value := rfl
theorem mul_value (left right : Formula) : (left*right).value = left.value*right.value := rfl

namespace Count
local infixl:65 " ⊞ " => fun a b : Formula => a+b+1
local infixl:70 " ⊠ " => fun a b : Formula => a+b+1
def mark (_tag : Budget.Tag) (cost : Formula) := cost+1


def lists {α : Type} (cost : α → α → Formula) : List α → List α → Formula
  | a::as,b::bs => cost a b + lists cost as bs + 4
  | [],[] | [],_::_ | _::_,[] => 2

def optional {α : Type} (cost : α → α → Formula) : Option α → Option α → Formula
  | some left,some right => cost left right + 3
  | none,none | none,some _ | some _,none => 2

def parties (left right : List P) : Formula := lists (fun _ _ => 1) left right

def ports (left right : List O) : Formula := lists (fun _ _ => 1) left right

def bundle (left right : Bundle G) : Formula := lists (fun _ _ => 5) left right

def operation : (left right : Institutions.Capitalism.Universal.Source.Program.Operation P G (Mandate.State P T) I) →
    Formula
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

def request (left right : Future.Recovery.Action seed) : Formula :=
  (1 ⊞ (1 ⊞ 1 ⊞ (parties left.consents right.consents ⊞ 1 ⊞
    (1 ⊞ 1 ⊞ (ports left.gates right.gates ⊞ 1 ⊞ operation left.operation right.operation)))))+1

def word (left right : List (Future.Recovery.Action seed)) : Formula := lists request left right

def words (left right : List (List (Future.Recovery.Action seed))) : Formula := lists word left right

def invoice (left right : Option (List (Future.Recovery.Action seed))) : Formula := optional word left right

def control (left right : List (Option (List (List (Future.Recovery.Action seed))))) : Formula := lists (optional words) left right

def signature : (left right : Signature (Future.Recovery.Action seed)) → Formula
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

def length {α : Type} : List α → Formula
  | [] => 2
  | _::tail => length tail+3

theorem length_value {α : Type} (items : List α) : (length items).value = BodySource.length items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [length,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,ih,BodySource.length,List.length_cons];omega

theorem lists_value {α : Type} (cost : α → α → Formula) (left right : List α) :
    (lists cost left right).value = BodySource.lists (fun a b => (cost a b).value) left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a as ih => cases right with
    | nil => rfl
    | cons b bs => simp only [lists,BodySource.lists,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,ih]
theorem optional_value {α : Type} (cost : α → α → Formula) (left right : Option α) :
    (optional cost left right).value = BodySource.optional (fun a b => (cost a b).value) left right := by
  cases left <;> cases right <;> rfl
omit [DecidableEq P] in
theorem parties_value (left right : List P) : (parties left right).value = BodySource.parties left right := lists_value _ _ _
omit [DecidableEq O] in
theorem ports_value (left right : List O) : (ports left right).value = BodySource.ports left right := lists_value _ _ _
omit [DecidableEq G] in
theorem bundle_value (left right : Bundle G) : (bundle left right).value = BodySource.bundle left right := lists_value _ _ _
omit [DecidableEq P] [DecidableEq G] [DecidableEq T] [DecidableEq I] in
theorem operation_value (left right : Institutions.Capitalism.Universal.Source.Program.Operation P G (Mandate.State P T) I) :
    (operation left right).value = BodySource.operation left right := by
  cases left <;> cases right
  all_goals simp only [operation,BodySource.operation,mark,BodySource.mark,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,bundle_value]
theorem request_value (left right : Future.Recovery.Action seed) : (request left right).value = BodySource.request left right := by
  simp only [request,BodySource.request,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,parties_value,ports_value,operation_value]
theorem word_value (left right : List (Future.Recovery.Action seed)) : (word left right).value = BodySource.word left right := by
  simp only [word,BodySource.word,lists_value,request_value]
theorem words_value (left right : List (List (Future.Recovery.Action seed))) : (words left right).value = BodySource.words left right := by
  simp only [words,BodySource.words,lists_value,word_value]
theorem invoice_value (left right : Option (List (Future.Recovery.Action seed))) : (invoice left right).value = BodySource.invoice left right := by
  simp only [invoice,BodySource.invoice,optional_value,word_value]
theorem control_value (left right : List (Option (List (List (Future.Recovery.Action seed))))) :
    (control left right).value = BodySource.control left right := by
  simp only [control,BodySource.control,lists_value,optional_value,words_value]
theorem signature_value (left right : Signature (Future.Recovery.Action seed)) :
    (signature left right).value = BodySource.signature left right := by
  induction left generalizing right <;> cases right
  all_goals simp_all only [signature,BodySource.signature,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,word_value,words_value,invoice_value,control_value]
end Count

namespace Amount
def lists {α : Type} (cost : α → α → Formula) : List α → List α → Formula
  | a::as,b::bs => cost a b+1+lists cost as bs
  | [],[] | [],_::_ | _::_,[] => 1
def optional {α : Type} (cost : α → α → Formula) : Option α → Option α → Formula
  | some left,some right => 1+cost left right
  | none,none | none,some _ | some _,none => 1
def parties (left right : List P) := lists (fun _ _ => 1) left right
def ports (left right : List O) := lists (fun _ _ => 1) left right
def bundle (left right : Bundle G) := lists (fun _ _ => 3) left right
def operation : (_left _right : Institutions.Capitalism.Universal.Source.Program.Operation P G (Mandate.State P T) I) →
    Formula
  | .produce _left,.produce _right => id (Formula.literal 1 + (1 : Formula))
  | .transfer _a _b goodsL,.transfer _c _d goodsR => id
      (Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + bundle goodsL goodsR)))
  | .use _a goodsL _u,.use _b goodsR _v => id
      (Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + (bundle goodsL goodsR + Formula.literal 1 + (1 : Formula))))
  | .issue _i _a _b _q,.issue _j _c _d _r => id
      (Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + (1 : Formula)))))
  | .assign _i _a _b _c _q,.assign _j _d _e _f _r => id
      (Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + (1 : Formula))))))
  | .settle _i _a _b _q,.settle _j _c _d _r => id
      (Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + (1 : Formula)))))
  | .revise _a _t,.revise _b _u => id
      (Formula.literal 1 + ((1 : Formula) + Formula.literal 1 + (1 : Formula)))
  | .produce _,.transfer _ _ _ => id (Formula.literal 1)
  | .produce _,.use _ _ _ => id (Formula.literal 1)
  | .produce _,.issue _ _ _ _ => id (Formula.literal 1)
  | .produce _,.assign _ _ _ _ _ => id (Formula.literal 1)
  | .produce _,.settle _ _ _ _ => id (Formula.literal 1)
  | .produce _,.revise _ _ => id (Formula.literal 1)
  | .produce _,.present => id (Formula.literal 1)
  | .transfer _ _ _,.produce _ => id (Formula.literal 1)
  | .transfer _ _ _,.use _ _ _ => id (Formula.literal 1)
  | .transfer _ _ _,.issue _ _ _ _ => id (Formula.literal 1)
  | .transfer _ _ _,.assign _ _ _ _ _ => id (Formula.literal 1)
  | .transfer _ _ _,.settle _ _ _ _ => id (Formula.literal 1)
  | .transfer _ _ _,.revise _ _ => id (Formula.literal 1)
  | .transfer _ _ _,.present => id (Formula.literal 1)
  | .use _ _ _,.produce _ => id (Formula.literal 1)
  | .use _ _ _,.transfer _ _ _ => id (Formula.literal 1)
  | .use _ _ _,.issue _ _ _ _ => id (Formula.literal 1)
  | .use _ _ _,.assign _ _ _ _ _ => id (Formula.literal 1)
  | .use _ _ _,.settle _ _ _ _ => id (Formula.literal 1)
  | .use _ _ _,.revise _ _ => id (Formula.literal 1)
  | .use _ _ _,.present => id (Formula.literal 1)
  | .issue _ _ _ _,.produce _ => id (Formula.literal 1)
  | .issue _ _ _ _,.transfer _ _ _ => id (Formula.literal 1)
  | .issue _ _ _ _,.use _ _ _ => id (Formula.literal 1)
  | .issue _ _ _ _,.assign _ _ _ _ _ => id (Formula.literal 1)
  | .issue _ _ _ _,.settle _ _ _ _ => id (Formula.literal 1)
  | .issue _ _ _ _,.revise _ _ => id (Formula.literal 1)
  | .issue _ _ _ _,.present => id (Formula.literal 1)
  | .assign _ _ _ _ _,.produce _ => id (Formula.literal 1)
  | .assign _ _ _ _ _,.transfer _ _ _ => id (Formula.literal 1)
  | .assign _ _ _ _ _,.use _ _ _ => id (Formula.literal 1)
  | .assign _ _ _ _ _,.issue _ _ _ _ => id (Formula.literal 1)
  | .assign _ _ _ _ _,.settle _ _ _ _ => id (Formula.literal 1)
  | .assign _ _ _ _ _,.revise _ _ => id (Formula.literal 1)
  | .assign _ _ _ _ _,.present => id (Formula.literal 1)
  | .settle _ _ _ _,.produce _ => id (Formula.literal 1)
  | .settle _ _ _ _,.transfer _ _ _ => id (Formula.literal 1)
  | .settle _ _ _ _,.use _ _ _ => id (Formula.literal 1)
  | .settle _ _ _ _,.issue _ _ _ _ => id (Formula.literal 1)
  | .settle _ _ _ _,.assign _ _ _ _ _ => id (Formula.literal 1)
  | .settle _ _ _ _,.revise _ _ => id (Formula.literal 1)
  | .settle _ _ _ _,.present => id (Formula.literal 1)
  | .revise _ _,.produce _ => id (Formula.literal 1)
  | .revise _ _,.transfer _ _ _ => id (Formula.literal 1)
  | .revise _ _,.use _ _ _ => id (Formula.literal 1)
  | .revise _ _,.issue _ _ _ _ => id (Formula.literal 1)
  | .revise _ _,.assign _ _ _ _ _ => id (Formula.literal 1)
  | .revise _ _,.settle _ _ _ _ => id (Formula.literal 1)
  | .revise _ _,.present => id (Formula.literal 1)
  | .present,.produce _ => id (Formula.literal 1)
  | .present,.transfer _ _ _ => id (Formula.literal 1)
  | .present,.use _ _ _ => id (Formula.literal 1)
  | .present,.issue _ _ _ _ => id (Formula.literal 1)
  | .present,.assign _ _ _ _ _ => id (Formula.literal 1)
  | .present,.settle _ _ _ _ => id (Formula.literal 1)
  | .present,.revise _ _ => id (Formula.literal 1)
  | .present,.present => id (Formula.literal 1)

def request (left right : Future.Recovery.Action seed) : Formula :=
  id (Formula.literal 1 + ((1 : Formula) + Formula.literal 1 +
    (parties left.consents right.consents + Formula.literal 1 + ((1 : Formula) + Formula.literal 1 +
      (ports left.gates right.gates + Formula.literal 1 + operation left.operation right.operation)))))

def word (left right : List (Future.Recovery.Action seed)) := lists request left right
def words (left right : List (List (Future.Recovery.Action seed))) := lists word left right
def invoice (left right : Option (List (Future.Recovery.Action seed))) := optional word left right
def control (left right : List (Option (List (List (Future.Recovery.Action seed))))) := lists (optional words) left right
def signature : (left right : Signature (Future.Recovery.Action seed)) → Formula
  | .keep a,.keep b => id (Formula.literal 1 + word a b)
  | .direct a c,.direct b d => id (Formula.literal 1 + (word a b + Formula.literal 1 + control c d))
  | .own a r c,.own b s d => id (Formula.literal 1 + (word a b + Formula.literal 1 + (word r s + Formula.literal 1 + control c d)))
  | .invoiced a r i c,.invoiced b s j d => id (Formula.literal 1 + (word a b + Formula.literal 1 + (word r s + Formula.literal 1 + (invoice i j + Formula.literal 1 + control c d))))
  | .stopped a,.stopped b => id (Formula.literal 1 + invoice a b)
  | .prefix a n,.prefix b m => id (Formula.literal 1 + (words a b + Formula.literal 1 + signature n m))
  | .keep _,.direct _ _ => id (Formula.literal 1)
  | .keep _,.own _ _ _ => id (Formula.literal 1)
  | .keep _,.invoiced _ _ _ _ => id (Formula.literal 1)
  | .keep _,.stopped _ => id (Formula.literal 1)
  | .keep _,.prefix _ _ => id (Formula.literal 1)
  | .direct _ _,.keep _ => id (Formula.literal 1)
  | .direct _ _,.own _ _ _ => id (Formula.literal 1)
  | .direct _ _,.invoiced _ _ _ _ => id (Formula.literal 1)
  | .direct _ _,.stopped _ => id (Formula.literal 1)
  | .direct _ _,.prefix _ _ => id (Formula.literal 1)
  | .own _ _ _,.keep _ => id (Formula.literal 1)
  | .own _ _ _,.direct _ _ => id (Formula.literal 1)
  | .own _ _ _,.invoiced _ _ _ _ => id (Formula.literal 1)
  | .own _ _ _,.stopped _ => id (Formula.literal 1)
  | .own _ _ _,.prefix _ _ => id (Formula.literal 1)
  | .invoiced _ _ _ _,.keep _ => id (Formula.literal 1)
  | .invoiced _ _ _ _,.direct _ _ => id (Formula.literal 1)
  | .invoiced _ _ _ _,.own _ _ _ => id (Formula.literal 1)
  | .invoiced _ _ _ _,.stopped _ => id (Formula.literal 1)
  | .invoiced _ _ _ _,.prefix _ _ => id (Formula.literal 1)
  | .stopped _,.keep _ => id (Formula.literal 1)
  | .stopped _,.direct _ _ => id (Formula.literal 1)
  | .stopped _,.own _ _ _ => id (Formula.literal 1)
  | .stopped _,.invoiced _ _ _ _ => id (Formula.literal 1)
  | .stopped _,.prefix _ _ => id (Formula.literal 1)
  | .prefix _ _,.keep _ => id (Formula.literal 1)
  | .prefix _ _,.direct _ _ => id (Formula.literal 1)
  | .prefix _ _,.own _ _ _ => id (Formula.literal 1)
  | .prefix _ _,.invoiced _ _ _ _ => id (Formula.literal 1)
  | .prefix _ _,.stopped _ => id (Formula.literal 1)


theorem lists_value {α : Type} (cost : α → α → Formula) (left right : List α) :
    (lists cost left right).value = NativeAdmission.listsBudget (fun a b => (cost a b).value) left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a as ih => cases right with
    | nil => rfl
    | cons b bs => simp only [lists,NativeAdmission.listsBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,ih]
theorem optional_value {α : Type} (cost : α → α → Formula) (left right : Option α) :
    (optional cost left right).value = SignatureWork.optionalBudget (fun a b => (cost a b).value) left right := by
  cases left <;> cases right <;> rfl
omit [DecidableEq P] in
theorem parties_value (left right : List P) : (parties left right).value = ActionWork.partiesBudget left right := lists_value _ _ _
omit [DecidableEq O] in
theorem ports_value (left right : List O) : (ports left right).value = ActionWork.portsBudget left right := lists_value _ _ _
omit [DecidableEq G] in
theorem bundle_value (left right : Bundle G) : (bundle left right).value = ActionWork.bundleBudget left right := lists_value _ _ _
omit [DecidableEq P] [DecidableEq G] [DecidableEq T] [DecidableEq I] in
theorem operation_value (left right : Institutions.Capitalism.Universal.Source.Program.Operation P G (Mandate.State P T) I) :
    (operation left right).value = ActionWork.operationBudget left right := by
  cases left <;> cases right
  all_goals simp only [operation,ActionWork.operationBudget,id_eq,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,parties_value,ports_value,bundle_value]
theorem request_value (left right : Future.Recovery.Action seed) : (request left right).value = ActionWork.budget left right := by
  simp only [request,ActionWork.budget,id_eq,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,parties_value,ports_value,operation_value]
theorem word_value (left right : List (Future.Recovery.Action seed)) : (word left right).value = SignatureWork.Generic.wordBudget ActionWork.budget left right := by
  simp only [word,SignatureWork.Generic.wordBudget,lists_value,request_value]
theorem words_value (left right : List (List (Future.Recovery.Action seed))) : (words left right).value = SignatureWork.Generic.wordsBudget ActionWork.budget left right := by
  simp only [words,SignatureWork.Generic.wordsBudget,lists_value,word_value]
theorem invoice_value (left right : Option (List (Future.Recovery.Action seed))) : (invoice left right).value = SignatureWork.Generic.invoiceBudget ActionWork.budget left right := by
  simp only [invoice,SignatureWork.Generic.invoiceBudget,optional_value,word_value]
theorem control_value (left right : List (Option (List (List (Future.Recovery.Action seed))))) :
    (control left right).value = SignatureWork.Generic.controlBudget ActionWork.budget left right := by
  simp only [control,SignatureWork.Generic.controlBudget,lists_value,optional_value,words_value]
theorem signature_value (left right : Signature (Future.Recovery.Action seed)) :
    (signature left right).value = SignatureWork.Generic.budget ActionWork.budget left right := by
  induction left generalizing right <;> cases right
  all_goals simp_all only [signature,SignatureWork.Generic.budget,id_eq,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,word_value,words_value,invoice_value,control_value]
end Amount
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Expand
