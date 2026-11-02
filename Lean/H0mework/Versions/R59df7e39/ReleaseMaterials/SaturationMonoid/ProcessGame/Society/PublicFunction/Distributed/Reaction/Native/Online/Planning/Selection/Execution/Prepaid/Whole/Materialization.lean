import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Selection
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeTensor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Materialization
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} {cursor : Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)}
  {n : Nat} {baseReference : Term cursor} {actor : Party} {position : Nat}
  (scope : Scope cursor pricing n baseReference actor position) (span : Nat)

structure Emission (α Party Good Port Technology Instrument : Type) where
  private mk ::
  value : α
  work : List (NativeTensor.Event Party Good Port Technology Instrument)
local notation "Produced" => Emission

def bound (intent : Intent scope) (rival : Opponent cursor.source.val.code) :
    Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument) :=
  let source := target scope span intent rival
  ⟨seed.base,seed.scope,source.val,source.indexed.property.1,source.indexed.property.2⟩

def present (intent : Intent scope) (rival : Opponent cursor.source.val.code) :
    Produced (Evaluation cursor.source.val.code) Party Good Port Technology Instrument :=
  let made := NativeTensor.evaluation (bound scope span intent rival) cursor.depth (extent scope span intent)
  ⟨(target scope span intent rival).property ▸ made.value,made.work⟩

theorem present_exact (intent : Intent scope) (rival : Opponent cursor.source.val.code) :
    (present scope span intent rival).value = (tensor scope span intent rival).present := by
  dsimp only [present]
  rw [NativeTensor.evaluation_exact]
  rfl

def presentBudget (intent : Intent scope) (rival : Opponent cursor.source.val.code) :=
  NativeTensor.evaluationBudget (bound scope span intent rival) cursor.depth (extent scope span intent)
theorem present_work_bound (intent : Intent scope) (rival : Opponent cursor.source.val.code) :
    (present scope span intent rival).work.length ≤ presentBudget scope span intent rival :=
  NativeTensor.evaluation_work_bound _ _ _

def future (intent : Intent scope) (rival : Opponent cursor.source.val.code)
    (word : List (Future.Recovery.Action cursor.model)) :
    Produced (Option (Future.Recovery.Assessment.Report cursor.model)) Party Good Port Technology Instrument :=
  let source := target scope span intent rival
  match Future.produce cursor.model cursor.depth source.indexed (count scope span intent) word with
  | .inl _ => ⟨none,[]⟩
  | .inr receipt =>
    let made := Future.Recovery.produceWith pricing receipt
    let emitted := NativeTensor.report made cursor.depth source.property
    ⟨some emitted.value,emitted.work⟩

def futureBudget (intent : Intent scope) (rival : Opponent cursor.source.val.code)
    (word : List (Future.Recovery.Action cursor.model)) : Nat :=
  match Future.produce cursor.model cursor.depth (target scope span intent rival).indexed (count scope span intent) word with
  | .inl _ => 0
  | .inr receipt => NativeTensor.reportBudget (Future.Recovery.produceWith pricing receipt) cursor.depth

theorem future_exact (intent : Intent scope) (rival : Opponent cursor.source.val.code)
    (word : List (Future.Recovery.Action cursor.model)) :
    (future scope span intent rival word).value = (tensor scope span intent rival).future cursor word := by
  unfold future tensor Tensor.future restoration
  dsimp only
  generalize same : Future.produce cursor.model cursor.depth (target scope span intent rival).indexed (count scope span intent) word = actual
  cases actual with
  | inl _ => rfl
  | inr receipt => exact congrArg some (NativeTensor.report_exact (Future.Recovery.produceWith pricing receipt) cursor.depth (target scope span intent rival).property)

theorem future_work_bound (intent : Intent scope) (rival : Opponent cursor.source.val.code)
    (word : List (Future.Recovery.Action cursor.model)) :
    (future scope span intent rival word).work.length ≤ futureBudget scope span intent rival word := by
  unfold future futureBudget
  dsimp only
  generalize same : Future.produce cursor.model cursor.depth (target scope span intent rival).indexed (count scope span intent) word = actual
  cases actual with
  | inl _ => exact Nat.le_refl _
  | inr receipt => exact NativeTensor.report_work_bound (Future.Recovery.produceWith pricing receipt) cursor.depth (target scope span intent rival).property
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Materialization
