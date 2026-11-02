import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Operand.Native
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

def presentAmount (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :=
  Amount.Source.evaluation (Whole.Materialization.bound scope input.span intent rival)
    (initial input prepared.saved[index].point).depth (Whole.extent scope input.span intent)
def presentCount (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :=
  Count.Source.evaluation (Whole.Materialization.bound scope input.span intent rival)
    (initial input prepared.saved[index].point).depth (Whole.extent scope input.span intent)
theorem presentAmount_value (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :
    (presentAmount index scope intent rival).value = Whole.Materialization.presentBudget scope input.span intent rival :=
  Amount.Source.evaluation_value _ _ _
theorem presentCount_value (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :
    (presentCount index scope intent rival).value = Body.present index scope intent rival :=
  Count.Source.evaluation_value _ _ _

structure FutureParts (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code)
    (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model)) where
  private mk ::
  value : Option (Future.Recovery.Assessment.Report (initial input prepared.saved[index].point).model)
  amount : Formula
  count : Formula
  value_exact : value = (Whole.Materialization.future scope input.span intent rival word).value
  amount_exact : amount.value = Whole.Materialization.futureBudget scope input.span intent rival word
  count_exact : count.value = Body.future index scope intent rival word

-- One original produce branch supplies both the actual Report and both source formulas.
def future (index : Index prepared) (scope : Bound.CellScope index) (intent : Whole.Intent scope)
    (rival : Opponent (initial input prepared.saved[index].point).source.val.code)
    (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model)) :
    FutureParts index scope intent rival word :=
  let target := Whole.target scope input.span intent rival
  match same : Future.produce (initial input prepared.saved[index].point).model
      (initial input prepared.saved[index].point).depth (Whole.target scope input.span intent rival).indexed (Whole.count scope input.span intent) word with
  | .inl _ => ⟨none,0,2,by simp only [Whole.Materialization.future,same],
      by simp only [Whole.Materialization.futureBudget,same];rfl,by simp only [Body.future,same];rfl⟩
  | .inr receipt =>
    let restored := Future.Recovery.produceWith (old := (initial input prepared.saved[index].point).model) input.pricing receipt
    let emitted := NativeTensor.report restored (initial input prepared.saved[index].point).depth target.property
    let amount := Amount.Source.evaluation restored.bound (initial input prepared.saved[index].point).depth
      (restored.walk.finish.depth-(initial input prepared.saved[index].point).depth)
    let count := Count.Source.evaluation restored.bound (initial input prepared.saved[index].point).depth
      (restored.walk.finish.depth-(initial input prepared.saved[index].point).depth)+1
    ⟨some emitted.value,amount,count,by simp only [Whole.Materialization.future,same];rfl,
      by simp only [Whole.Materialization.futureBudget,same,NativeTensor.reportBudget];exact Amount.Source.evaluation_value _ _ _,
      by simp only [Body.future,same];dsimp only [count];rw [add_value,Count.Source.evaluation_value];rfl⟩

local infixl:65 " ⊞ " => fun a b : Formula => a+b+1

def body (query : Work.Query pool) : Formula := 1+(match query with
  | .admission policy row => match row with
    | .coherence first second => 1 ⊞ Count.signature
        (Policy.Work.cachedShape (.ready (read pool policy first).scope) (read pool policy first).intent)
        (Policy.Work.cachedShape (.ready (read pool policy second).scope) (read pool policy second).intent)
    | .native index coordinate => match coordinate with
      | .present table =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := Whole.Materialization.present branch.scope input.span branch.intent rival
        let original := Whole.Materialization.present branch.scope input.span .keep rival
        presentAmount index branch.scope branch.intent rival+presentAmount index branch.scope .keep rival+
          (1 ⊞ presentCount index branch.scope branch.intent rival ⊞ presentCount index branch.scope .keep rival ⊞
            Count.Present.present (initial input prepared.saved[index].point) current.value original.value)
      | .future table word =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := future index branch.scope branch.intent rival word
        let original := future index branch.scope .keep rival word
        current.amount+original.amount+(1 ⊞ current.count ⊞ original.count ⊞
          Count.FutureShape.comparison (initial input prepared.saved[index].point) current.value original.value)
      | .funding .. | .release | .coverage | .deployment => 1
    | .informed | .uniform .. => 1
  | .present new previous index table =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := Whole.Materialization.present left.scope input.span left.intent rival
    let original := Whole.Materialization.present right.scope input.span right.intent rival
    presentAmount index left.scope left.intent rival+presentAmount index right.scope right.intent rival+
      (1 ⊞ presentCount index left.scope left.intent rival ⊞ presentCount index right.scope right.intent rival ⊞
        Count.BenefitShape.present (initial input prepared.saved[index].point) current.value original.value)
  | .future new previous index table word =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := future index left.scope left.intent rival word
    let original := future index right.scope right.intent rival word
    current.amount+original.amount+(1 ⊞ current.count ⊞ original.count ⊞
      Count.BenefitShape.future (initial input prepared.saved[index].point) current.value original.value)
  | .funding .. => 1)

theorem body_value (query : Work.Query pool) : (body query).value = Body.atom query := by
  cases query with
  | admission policy row => cases row with
    | informed | uniform => rfl
    | coherence first second => simp only [body,Body.atom,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.signature_value]
    | native index coordinate => cases coordinate with
      | release | coverage | deployment | funding => rfl
      | present table => simp only [body,Body.atom,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,presentAmount_value,presentCount_value,Count.Present.present_value]
      | future table word => simp only [body,Body.atom,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,FutureParts.amount_exact,FutureParts.count_exact,Count.FutureShape.comparison_value,FutureParts.value_exact]
  | present new previous index table => simp only [body,Body.atom,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,presentAmount_value,presentCount_value,Count.BenefitShape.present_value]
  | future new previous index table word => simp only [body,Body.atom,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,FutureParts.amount_exact,FutureParts.count_exact,Count.BenefitShape.future_value,FutureParts.value_exact]
  | funding => rfl

def selection (query : Work.Query pool) : Formula := match query with
  | .admission policy row => match row with
    | .coherence first second => 1+Amount.signature
        (Policy.Work.cachedShape (.ready (read pool policy first).scope) (read pool policy first).intent)
        (Policy.Work.cachedShape (.ready (read pool policy second).scope) (read pool policy second).intent)
    | .native index coordinate => match coordinate with
      | .present table =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := Whole.Materialization.present branch.scope input.span branch.intent rival
        let original := Whole.Materialization.present branch.scope input.span .keep rival
        1+presentAmount index branch.scope branch.intent rival+presentAmount index branch.scope .keep rival+
          Amount.Present.present (initial input prepared.saved[index].point) current.value original.value
      | .future table word =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := future index branch.scope branch.intent rival word
        let original := future index branch.scope .keep rival word
        1+current.amount+original.amount+Amount.FutureShape.comparison (initial input prepared.saved[index].point) current.value original.value
      | .funding .. => 4
      | .release | .coverage | .deployment => 1
    | .informed | .uniform .. => 1
  | .present new previous index table =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := Whole.Materialization.present left.scope input.span left.intent rival
    let original := Whole.Materialization.present right.scope input.span right.intent rival
    1+presentAmount index left.scope left.intent rival+presentAmount index right.scope right.intent rival+
      Amount.BenefitShape.present (initial input prepared.saved[index].point) current.value original.value
  | .future new previous index table word =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := future index left.scope left.intent rival word
    let original := future index right.scope right.intent rival word
    1+current.amount+original.amount+Amount.BenefitShape.future (initial input prepared.saved[index].point) current.value original.value
  | .funding .. => 4

theorem selection_value (query : Work.Query pool) : (selection query).value = Work.atomBudget pool query := by
  cases query with
  | admission policy row => cases row with
    | informed | uniform => rfl
    | coherence first second => simp only [selection,Work.atomBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Amount.signature_value]
    | native index coordinate => cases coordinate with
      | release | coverage | deployment | funding => rfl
      | present table => simp only [selection,Work.atomBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,presentAmount_value,Amount.Present.present_value]
      | future table word => simp only [selection,Work.atomBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,FutureParts.amount_exact,Amount.FutureShape.comparison_value,FutureParts.value_exact]
  | present new previous index table => simp only [selection,Work.atomBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,presentAmount_value,Amount.BenefitShape.present_value]
  | future new previous index table word => simp only [selection,Work.atomBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,FutureParts.amount_exact,Amount.BenefitShape.future_value,FutureParts.value_exact]
  | funding => rfl

def resolve : Counter.Operand pool → Formula
  | .body query => body query
  | .selection query => selection query
theorem resolve_value (field : Counter.Operand pool) : (resolve field).value = field.value pool := by
  cases field with
  | body query => exact body_value query
  | selection query => exact selection_value query
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Expand
