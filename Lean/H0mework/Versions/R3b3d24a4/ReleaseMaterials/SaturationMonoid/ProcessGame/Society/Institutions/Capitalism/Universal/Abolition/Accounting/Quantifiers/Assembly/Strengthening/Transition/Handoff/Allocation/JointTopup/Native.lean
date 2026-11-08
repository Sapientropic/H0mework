import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Limits
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Service
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Stock
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Quantities
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
open Diagnostics

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (word : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
  (reserved : Finset (Due.Service.Ordinal source word))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ)
  (limits : Limits Party Good)

local notation "Row" => Due.Service.Need ordered.toFinset task
local notation "Lot" => Due.Service.Supply source word ordered.toFinset task
local notation "Material" => ℕ × ExecutionItem Party Good Port Technology Instrument
local notation "Address" => Party × Good
local notation "Network" => Due.Service.network source word ordered.toFinset task reserved
local notation "Keys" => watched source word ordered task
local notation "Width" => List.length (edgeList source word ordered task)
local notation "Total" => Width + List.length Keys

theorem watched_distinct : List.Nodup Keys := List.nodup_dedup _

inductive Site (P G Need Supply Entry : Type*) where
  | service (site : ServiceSite Need Supply)
  | stock (site : StockSite (P × G) Entry)
  | limit (site : LimitSite P G)

local notation "JointSite" => Site Party Good Row Lot Material

def readExtra (values : Fin Total → ℚ) : Address → ℚ :=
  extraAt Keys (watched_distinct source word ordered task) values

def readAllocation (values : Fin Total → ℚ) : Row → Lot → ℚ :=
  decode (index source word ordered task) (serviceValues values)

def encodeJoint (extra : Address → ℚ) (allocation : Row → Lot → ℚ) : Fin Total → ℚ :=
  join Keys (watched_distinct source word ordered task) (encode (index source word ordered task) allocation) extra

private def servicePart : List (Tagged JointSite Total) :=
  (serviceTagged (Network) (due source word ordered task) (index source word ordered task)
    (rows ordered task) (lots source word ordered task)).map fun row =>
      ⟨.service row.label, extendRow row.inequality (List.length Keys)⟩

private theorem servicePart_exact (values : Fin Total → ℚ) :
    Feasible (numeric (servicePart source word ordered task reserved)) values ↔
      Covers (Network) (due source word ordered task) (readAllocation source word ordered task values) := by
  have lifted : numeric (servicePart source word ordered task reserved) =
      (numeric (serviceTagged (Network) (due source word ordered task) (index source word ordered task)
        (rows ordered task) (lots source word ordered task))).map
          (fun row => extendRow row (List.length Keys)) := by
    simp only [servicePart, numeric, List.map_map, Function.comp_def]
  rw [lifted, serviceTagged_exact, feasible_map]
  simp only [extendRow_exact]
  exact serviceConstraints_exact _ _ _ _ _
    (Due.Service.needList_covers _ _ _ rfl) (Due.Service.supplyList_covers _ _ _ _ _ rfl) _

private def stockPart (key : Address) : List (Tagged JointSite Total) :=
  let stock := (Affine.literal (opening source budget key)).add
    (extraForm Keys (watched_distinct source word ordered task) Width key)
  let steps := Reserve.originalSteps source word (fun _ _ => 0)
  let tags := stockLabels key (Execution.inventory source word).length (Due.Settlement.finish source word) steps
  (attach tags (stockConstraintsFor (heldRows ordered task held) Due.Settlement.address key
    (fun item row => addCoordinates (paymentAt source word ordered task item.1 row) (List.length Keys))
    steps (fun row => Affine.literal ((Network).need row)) stock)).map (Tagged.mapLabel Site.stock)

def KeepsStock (extra : Address → ℚ) (allocation : Row → Lot → ℚ) (key : Address) : Prop :=
  let profile := view source word ordered task reserved allocation
  Reserve.Protects (heldRows ordered task held) profile.address key
    (Reserve.originalSteps source word (Reserve.assignedAt profile.paid)) profile.required
    (opening source budget key + extra key)

private theorem stockPart_exact (key : Address) (values : Fin Total → ℚ) :
    Feasible (numeric (stockPart source word ordered task reserved held budget key)) values ↔
      KeepsStock source word ordered task reserved held budget (readExtra source word ordered task values)
        (readAllocation source word ordered task values) key := by
  unfold stockPart KeepsStock
  rw [numeric_mapLabel, attach_exact _ _ (stockLabels_aligned _ _ _ _ _ _ _ _ _), stockConstraintsFor_exact]
  have exactPaid := paidSteps_exact source word ordered task (serviceValues values)
  simp only [paidSteps] at exactPaid
  simp only [paidSteps, eval_addCoordinates, Affine.eval_literal, Affine.eval_add, extraForm_exact]
  rw [exactPaid]
  rfl

/-- One numerical word, one service assignment, and one vector of proposed
physical additions. Shared pool constraints follow the kept prefixes. -/
def system : List (Tagged JointSite Total) :=
  (servicePart source word ordered task reserved ++
    List.flatMap (stockPart source word ordered task reserved held budget) Keys) ++
    (limitTags limits Keys (watched_distinct source word ordered task) Width).map (Tagged.mapLabel Site.limit)

def FitsJoint (extra : Address → ℚ) (allocation : Row → Lot → ℚ) : Prop :=
  (∀ key ∉ Keys, extra key = 0) ∧
    limits.Fits Keys extra ∧ Covers (Network) (due source word ordered task) allocation ∧
    ∀ key ∈ Keys, KeepsStock source word ordered task reserved held budget extra allocation key

theorem system_exact (values : Fin Total → ℚ) :
    Feasible (numeric (system source word ordered task reserved held budget limits)) values ↔
      FitsJoint source word ordered task reserved held budget limits
        (readExtra source word ordered task values) (readAllocation source word ordered task values) := by
  simp only [system, numeric_append, feasible_append, servicePart_exact, numeric_flatMap, feasible_flatMap,
    stockPart_exact, numeric_mapLabel, limitTags_exact, FitsJoint]
  constructor
  · rintro ⟨⟨service, kept⟩, capped⟩
    exact ⟨extraAt_unlisted _ _ _, capped, service, kept⟩
  · rintro ⟨_, capped, service, kept⟩
    exact ⟨⟨service, kept⟩, capped⟩

theorem original_candidate_enters_system (extra : Address → ℚ) (allocation : Row → Lot → ℚ)
    (admitted : FitsJoint source word ordered task reserved held budget limits extra allocation) :
    Feasible (numeric (system source word ordered task reserved held budget limits))
      (encodeJoint source word ordered task extra allocation) := by
  apply (system_exact source word ordered task reserved held budget limits _).mpr
  simpa only [encodeJoint, readExtra, readAllocation, serviceValues_join, extraAt_join _ _ _ _ admitted.1,
    decode_encode] using admitted

theorem zero_matches_the_existing_original_assignment (allocation : Row → Lot → ℚ) :
    FitsJoint source word ordered task reserved held budget limits (fun _ => 0) allocation ↔
      limits.Fits Keys (fun _ => 0) ∧ Fits source word ordered task reserved held budget allocation := by
  unfold FitsJoint Fits KeepsStock
  simp only [add_zero]
  exact ⟨And.right, fun original => ⟨by simp, original⟩⟩

theorem shared_cap_conflict_names_the_original_pool
    (conflict : Conflict (system source word ordered task reserved held budget limits))
    {good : Good} {cap : ℚ} (named : conflict.label = .limit (.sharedCap good cap)) :
    good ∈ List.map Prod.snd Keys ∧ limits.shared good = some cap := by
  have listed := conflict.failed_is_original
  unfold system at listed
  rcases List.mem_append.mp listed with original | caps
  · rcases List.mem_append.mp original with service | stock
    · obtain ⟨line, _, read⟩ := List.mem_map.mp service
      have wrong : Site.service line.label = Site.limit (.sharedCap good cap) :=
        (congrArg Tagged.label read).trans named
      cases wrong
    · obtain ⟨key, _, group⟩ := List.mem_flatMap.mp stock
      unfold stockPart at group
      obtain ⟨line, _, read⟩ := List.mem_map.mp group
      have wrong : Site.stock line.label = Site.limit (.sharedCap good cap) :=
        (congrArg Tagged.label read).trans named
      cases wrong
  · obtain ⟨line, original, read⟩ := List.mem_map.mp caps
    have same : line.label = .sharedCap good cap :=
      Site.limit.inj ((congrArg Tagged.label read).trans named)
    exact shared_cap_is_original limits Keys (watched_distinct source word ordered task) original same

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup
