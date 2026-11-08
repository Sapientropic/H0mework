import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Run
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Carry
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "Request" => Source.Program.Request Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source past)}

local notation "Rows" => Service.Need ordered.toFinset task
local notation "Receipt" => Network.Certificate (Service.network source past ordered.toFinset task reserved)

def residualRows (receipt : Receipt) (dueBy : ℚ) : List Rows :=
  (Service.needList ordered.toFinset task ordered rfl).dedup.filter fun line =>
    decide ((task line.1.1.val).deadline ≤ dueBy ∧ 0 < Service.remaining receipt line)

theorem original_due_and_unpaid_iff_listed (receipt : Receipt) (dueBy : ℚ) (line : Rows) :
    line ∈ residualRows receipt dueBy ↔
      (task line.1.1.val).deadline ≤ dueBy ∧ 0 < Service.remaining receipt line := by
  simp only [residualRows, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
  exact ⟨And.right, fun listed => ⟨Service.needList_covers _ _ _ _ line, listed⟩⟩

/-- Keep the original bearer, good and use. Only the unpaid original
quantity enters the next native proposal. The owning interpreter checks
the proposed signature. -/
def residualUse (receipt : Receipt) (line : Rows) (signed : Request) : Request :=
  { signed with
    consents := []
    operation := .use line.1.spec.bearer [(line.2.val, Service.remaining receipt line)] line.1.spec.purpose }

def residualWord (receipt : Receipt) (dueBy : ℚ) (sign : Rows → Request) : Word :=
  (residualRows receipt dueBy).map fun line => residualUse receipt line (sign line)

theorem the_residual_word_contains_the_exact_original_unpaid_material
    (receipt : Receipt) (dueBy : ℚ) (sign : Rows → Request) (line : Rows)
    (due : (task line.1.1.val).deadline ≤ dueBy) (remaining : 0 < Service.remaining receipt line)
    (original : Service.OriginalDemands ordered.toFinset task) :
    residualUse receipt line (sign line) ∈ residualWord receipt dueBy sign ∧
      Network.rowTotal receipt.allocation line + Service.remaining receipt line =
        amount Good line.1.spec.goods line.2.val :=
  ⟨List.mem_map.mpr ⟨line, (original_due_and_unpaid_iff_listed receipt dueBy line).mpr ⟨due, remaining⟩, rfl⟩,
    (Service.allocated_and_remaining_are_the_original_quantity receipt line original).2⟩

theorem residual_word_is_service (receipt : Receipt) (dueBy : ℚ) (sign : Rows → Request) :
    ∀ request ∈ residualWord receipt dueBy sign, IsService request := by
  intro request listed
  obtain ⟨line, original, rfl⟩ := List.mem_map.mp listed
  refine ⟨_, _, _, rfl, ?_⟩
  intro lot inside
  rw [List.mem_singleton.mp inside]
  exact ((original_due_and_unpaid_iff_listed receipt dueBy line).mp original).2.le

theorem residual_word_has_no_old_controller_consents (receipt : Receipt) (dueBy : ℚ)
    (sign : Rows → Request) : ∀ request ∈ residualWord receipt dueBy sign, request.consents = [] := by
  intro request listed
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp listed
  rfl

def InWindow (time : ℚ) (line : Rows) : Prop :=
  (task line.1.1.val).earliest ≤ time ∧ time ≤ (task line.1.1.val).deadline

instance (time : ℚ) (line : Rows) : Decidable (InWindow time line) := by
  unfold InWindow
  infer_instance

inductive Continuation (receipt : Receipt) (dueBy : ℚ) (sign : Rows → Request) (held : Word)
  | window (line : Rows) (original : line ∈ residualRows receipt dueBy)
      (unavailable : ¬ InWindow (Execution.endAt source past).raw.clock line)
  | checked (timely : ∀ line ∈ residualRows receipt dueBy,
      InWindow (Execution.endAt source past).raw.clock line)
      (outcome : NativeDecision (Execution.endAt source past) (residualWord receipt dueBy sign) held)

def prepare (receipt : Receipt) (dueBy : ℚ) (sign : Rows → Request) (held : Word)
    (reserve : ∀ request ∈ held, IsService request)
    (opening : ∀ party good, 0 ≤ (Execution.endAt source past).raw.stock party good)
    (ready : Ready (Execution.endAt source past)) (review : ReviewAvailable (Execution.endAt source past)) :
    Continuation receipt dueBy sign held :=
  match Abolition.Material.inspectList (InWindow (Execution.endAt source past).raw.clock)
      (residualRows receipt dueBy) with
  | .failure row original blocked => .window row original blocked
  | .clear timely => .checked timely (run _ (residualWord receipt dueBy sign) held
      (residual_word_is_service receipt dueBy sign) reserve
      (residual_word_has_no_old_controller_consents receipt dueBy sign) opening ready review)


end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
