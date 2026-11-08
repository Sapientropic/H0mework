import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Service
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Stock
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.NativeAssignment
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Decision
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.ProdSigma

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Quantities
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (word : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)

local notation "Row" => Due.Service.Need ordered.toFinset task
local notation "Lot" => Due.Service.Supply source word ordered.toFinset task
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Address" => Party × Good

def rows : List Row := Due.Service.needList ordered.toFinset task ordered rfl
def lots : List Lot := Due.Service.supplyList source word ordered.toFinset task ordered rfl

def edgeList : List (Row × Lot) := ((rows ordered task).product (lots source word ordered task)).dedup

def index : Row × Lot ≃ Fin (edgeList source word ordered task).length :=
  (List.Nodup.getEquivOfForallMemList _ (List.nodup_dedup _) fun pair =>
    List.mem_dedup.mpr (List.mem_product.mpr ⟨Due.Service.needList_covers _ _ _ rfl pair.1,
      Due.Service.supplyList_covers _ _ _ _ _ rfl pair.2⟩)).symm

variable (reserved : Finset (Due.Service.Ordinal source word))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ)

def watched := Due.Settlement.watched source word ordered task
def due (row : Row) : Bool := decide (Due.Settlement.deadline row ≤ Due.Settlement.finish source word)
def heldRows : List Row := ((rows ordered task).filter (· ∈ held)).dedup
def opening (key : Address) : ℚ := min (budget key) (source.raw.stock key.1 key.2)

local notation "network" => Due.Service.network source word ordered.toFinset task reserved
local notation "Index" => Fin (List.length (edgeList source word ordered task))

def paymentAt (position : ℕ) (row : Row) : Affine (edgeList source word ordered task).length :=
  if valid : position < (Execution.inventory source word).length then
    edge (index source word ordered task) row (⟨position, valid⟩, Due.Settlement.originalUnit row)
  else Affine.literal 0

theorem paymentAt_exact (values : Index → ℚ) (position : ℕ) (row : Row) :
    (paymentAt source word ordered task position row).eval values =
      Reserve.assignedAt (Due.Settlement.paidAt (decode (index source word ordered task) values)) row position := by
  unfold paymentAt Reserve.assignedAt
  split <;> simp_all [Due.Settlement.paidAt]

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem paidSteps_readSteps {n : ℕ} (law : RawLaw Party Good Port Technology Instrument)
    (pay : ℕ → Row → Affine n) (values : Fin n → ℚ) (items : List (Item × ℚ)) (offset : ℕ) :
    paidSteps (Reserve.readSteps law (fun _ _ => 0) items offset)
      (fun item row => pay item.1 row) values =
      Reserve.readSteps law (fun row position => (pay position row).eval values) items offset := by
  induction items generalizing offset with
  | nil => rfl
  | cons first rest ih =>
    simp only [Reserve.readSteps, paidSteps, List.map_cons]
    rw [← ih (offset + 1)]
    rfl

theorem paidSteps_exact (values : Index → ℚ) :
    paidSteps (Reserve.originalSteps source word (fun _ _ => 0))
      (fun item row => paymentAt source word ordered task item.1 row) values =
    Reserve.originalSteps source word
      (Reserve.assignedAt (Due.Settlement.paidAt (decode (index source word ordered task) values))) := by
  unfold Reserve.originalSteps
  let law := source.native.handlerFace.rootRead
  let items := Execution.timedInventory source word
  refine (paidSteps_readSteps ordered task law (paymentAt source word ordered task) values items 0).trans ?_
  exact congrArg (fun paid => Reserve.readSteps law paid items 0)
    (funext fun row => funext fun position => paymentAt_exact source word ordered task values position row)

def view (allocation : Row → Lot → ℚ) :=
  Due.Settlement.profile source word ordered.toFinset task reserved allocation

def Fits (allocation : Row → Lot → ℚ) : Prop :=
  Covers network (due source word ordered task) allocation ∧
    ∀ key ∈ watched source word ordered task,
      let profile := view source word ordered task reserved allocation
      Reserve.Protects (heldRows ordered task held) profile.address key
        (Reserve.originalSteps source word (Reserve.assignedAt profile.paid)) profile.required
        (opening source budget key)

def constraints : List (Inequality (edgeList source word ordered task).length) :=
  serviceConstraints network (due source word ordered task) (index source word ordered task)
      (rows ordered task) (lots source word ordered task) ++
    (watched source word ordered task).flatMap fun key =>
      stockConstraints (heldRows ordered task held) Due.Settlement.address key
        (fun item row => paymentAt source word ordered task item.1 row)
        (Reserve.originalSteps source word (fun _ _ => 0))
        (fun row => Affine.literal ((network).need row)) (opening source budget key)

theorem constraints_exact (values : Index → ℚ) :
    Feasible (constraints source word ordered task reserved held budget) values ↔
      Fits source word ordered task reserved held budget (decode (index source word ordered task) values) := by
  unfold constraints Fits
  rw [feasible_append]
  refine and_congr (serviceConstraints_exact (network) (due source word ordered task) (index source word ordered task)
    (rows ordered task) (lots source word ordered task)
    (Due.Service.needList_covers _ _ _ rfl) (Due.Service.supplyList_covers _ _ _ _ _ rfl) values) ?_
  simp only [feasible_flatMap, stockConstraints_exact, paidSteps_exact, Affine.eval_literal]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation
