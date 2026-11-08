import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Cut
import Mathlib.Data.Fintype.Sigma

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

abbrev Slot (ids : Finset TaskId) (task : TaskId → Task) :=
  Σ id : { id // id ∈ ids }, Fin (task id.val).slots.length

def Slot.spec {ids : Finset TaskId} {task : TaskId → Task} (slot : Slot ids task) : ServiceSlot Party Good :=
  (task slot.1.val).slots.get slot.2

def Slot.goods {ids : Finset TaskId} {task : TaskId → Task} (slot : Slot ids task) : Finset Good :=
  (slot.spec.goods.map Prod.fst).toFinset

abbrev Need (ids : Finset TaskId) (task : TaskId → Task) :=
  Σ slot : Slot ids task, { good // good ∈ slot.goods }

def goods (ids : Finset TaskId) (task : TaskId → Task) : Finset Good :=
  (Finset.univ : Finset (Slot ids task)).biUnion fun slot => slot.goods

abbrev Ordinal (source : C) (script : Script) := Fin (Execution.inventory source script).length

abbrev Supply (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task) :=
  Ordinal source script × { good // good ∈ goods ids task }

/-- Signed original use capacity. Rejected instructions, internal transfers
and unsigned material have no service capacity. -/
def paidAmount (law : RawLaw Party Good Port Technology Instrument) (item : Item) (good : Good) : ℚ :=
  match item.request.operation with
  | .use bearer _ _ => flowAt (law.actualDebit item.before item.request) bearer good
  | _ => 0

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem paidAmount_nonnegative (law : RawLaw Party Good Port Technology Instrument) (item : Item) (good : Good) :
    0 ≤ paidAmount law item good := by
  cases operation : item.request.operation with
  | use bearer bundle purpose =>
    simp only [paidAmount, operation, RawLaw.actualDebit]
    split
    · rename_i accepted
      exact amount_nonnegative _ accepted.2.2.2.1 _
    · rfl
  | _ => simp [paidAmount, operation]

def useFor (item : Item) (slot : ServiceSlot Party Good) : Prop :=
  match item.request.operation with
  | .use bearer _ purpose => bearer = slot.bearer ∧ purpose = slot.purpose
  | _ => False

instance (item : Item) (slot : ServiceSlot Party Good) : Decidable (useFor item slot) := by
  unfold useFor
  cases item.request.operation <;> infer_instance

def accepts (source : C) (script : Script) {ids : Finset TaskId} {task : TaskId → Task}
    (reserved : Finset (Ordinal source script)) (line : Need ids task) (receipt : Supply source script ids task) : Prop :=
  let timed := Execution.timedAt source script receipt.1
  let slot := line.1.spec
  let originalTask := task line.1.1.val
  receipt.1 ∉ reserved ∧ line.2.val = receipt.2.val ∧ originalTask.earliest ≤ timed.1.before.clock ∧
    timed.2 ≤ originalTask.deadline ∧ source.native.handlerFace.rootRead.Valid timed.1.before timed.1.request ∧
    useFor timed.1 slot

instance (source : C) (script : Script) {ids : Finset TaskId} {task : TaskId → Task}
    (reserved : Finset (Ordinal source script)) (line : Need ids task) (receipt : Supply source script ids task) :
    Decidable (accepts source script reserved line receipt) := by
  let timed := Execution.timedAt source script receipt.1
  letI : Decidable (receipt.1 ∉ reserved) := inferInstance
  letI : Decidable (line.2.val = receipt.2.val) := inferInstance
  letI : Decidable ((task line.1.1.val).earliest ≤ timed.1.before.clock) := inferInstance
  letI : Decidable (timed.2 ≤ (task line.1.1.val).deadline) := inferInstance
  letI : Decidable (source.native.handlerFace.rootRead.Valid timed.1.before timed.1.request) :=
    RawLaw.instDecidableValid source.native.handlerFace.rootRead timed.1.before timed.1.request
  letI : Decidable (useFor timed.1 line.1.spec) := inferInstance
  dsimp only [accepts]
  infer_instance

/-- Fragmentation uses the quantity of one original good per receipt and
retains the original task and slot on every row. A whole-use reservation
removes its ordinal from every good's capacity. -/
def network (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task)
    (reserved : Finset (Ordinal source script)) : Network (Need ids task) (Supply source script ids task) where
  need := fun line => max 0 (amount Good line.1.spec.goods line.2.val)
  capacity := fun receipt =>
    if receipt.1 ∈ reserved then 0 else
      paidAmount source.native.handlerFace.rootRead (Execution.timedAt source script receipt.1).1 receipt.2.val
  allows := fun line receipt => decide (accepts source script reserved line receipt)
  need_nonnegative := fun _ => le_max_left _ _
  capacity_nonnegative := by
    intro receipt
    split
    · exact le_rfl
    · exact paidAmount_nonnegative _ _ _

@[simp] theorem network_allows_iff (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task)
    (reserved : Finset (Ordinal source script)) (line : Need ids task) (receipt : Supply source script ids task) :
    (network source script ids task reserved).allows line receipt = true ↔
      accepts source script reserved line receipt := by
  simp [network]

theorem network_reads_nonnegative_original_need (source : C) (script : Script)
    (ids : Finset TaskId) (task : TaskId → Task) (reserved : Finset (Ordinal source script))
    (line : Need ids task) (valid : NonnegativeBundle Good line.1.spec.goods) :
    (network source script ids task reserved).need line = amount Good line.1.spec.goods line.2.val :=
  max_eq_right (amount_nonnegative _ valid _)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
