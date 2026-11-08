import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Native
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Minimum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation

open Abolition.Root Abolition.Root.Registered PublicFunction Quantities
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

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

local notation "Row" => Due.Service.Need ordered.toFinset task
local notation "Lot" => Due.Service.Supply source word ordered.toFinset task
local notation "network" => Due.Service.network source word ordered.toFinset task reserved
local notation "width" => List.length (edgeList source word ordered task)

def stockAt (target : Party × Good) (openingAmount : ℚ) (key : Party × Good) : ℚ :=
  if key = target then openingAmount else opening source budget key

def FitsAt (target : Party × Good) (openingAmount : ℚ) (allocation : Row → Lot → ℚ) : Prop :=
  0 ≤ openingAmount ∧ Covers (network) (due source word ordered task) allocation ∧
    ∀ key ∈ watched source word ordered task,
      let profile := view source word ordered task reserved allocation
      Reserve.Protects (heldRows ordered task held) profile.address key
        (Reserve.originalSteps source word (Reserve.assignedAt profile.paid)) profile.required
        (stockAt source budget target openingAmount key)

def objective (target : Party × Good) : List (Inequality (width + 1)) :=
  let openingAmount : Affine (width + 1) := Affine.variableAt (Fin.last width)
  Affine.le (Affine.literal 0) openingAmount ::
    ((serviceConstraints (network) (due source word ordered task) (index source word ordered task)
        (rows ordered task) (lots source word ordered task)).map liftInequality ++
      (watched source word ordered task).flatMap fun key =>
        stockConstraintsFor (heldRows ordered task held) Due.Settlement.address key
          (fun item row => (paymentAt source word ordered task item.1 row).lift)
          (Reserve.originalSteps source word (fun _ _ => 0))
          (fun row => Affine.literal ((network).need row))
          (if key = target then openingAmount else Affine.literal (opening source budget key)))

theorem objective_exact (target : Party × Good) (values : Fin (width + 1) → ℚ) :
    Feasible (objective source word ordered task reserved held budget target) values ↔
      FitsAt source word ordered task reserved held budget target (values (Fin.last width))
        (decode (index source word ordered task) (Fin.init values)) := by
  unfold objective FitsAt
  simp only [feasible_cons, feasible_append, Affine.holds_le, Affine.eval_literal, Affine.eval_variableAt,
    feasible_map, liftInequality_exact]
  apply and_congr_right
  intro _
  refine and_congr (serviceConstraints_exact (network) (due source word ordered task) (index source word ordered task)
    (rows ordered task) (lots source word ordered task)
    (Due.Service.needList_covers _ _ _ rfl) (Due.Service.supplyList_covers _ _ _ _ _ rfl) (Fin.init values)) ?_
  simp only [feasible_flatMap, stockConstraintsFor_exact, Affine.eval_literal]
  apply forall_congr'
  intro key
  apply imp_congr_right
  intro _
  have actual := paidSteps_exact source word ordered task (Fin.init values)
  simp only [paidSteps, Affine.eval_lift] at actual ⊢
  rw [actual]
  by_cases selected : key = target <;>
    simp [selected, stockAt, view, Due.Settlement.profile, Due.Liquidity.profile]

inductive AddressMinimum (target : Party × Good)
  | blocked (impossible : ¬ ∃ amount allocation,
      FitsAt source word ordered task reserved held budget target amount allocation)
  | attained (amount : ℚ) (allocation : Row → Lot → ℚ)
      (paid : FitsAt source word ordered task reserved held budget target amount allocation)
      (least : ∀ other otherAllocation,
        FitsAt source word ordered task reserved held budget target other otherAllocation → amount ≤ other)

def leastOpeningAt (target : Party × Good) : AddressMinimum source word ordered task reserved held budget target :=
  let original := objective source word ordered task reserved held budget target
  match minimumLast original with
  | .empty impossible => .blocked (by
      rintro ⟨amount, allocation, fit⟩
      let values : Fin (width + 1) → ℚ := Fin.snoc (encode (index source word ordered task) allocation) amount
      exact impossible ⟨values, (objective_exact source word ordered task reserved held budget target values).mpr
        (by simpa only [values, Fin.snoc_last, Fin.init_snoc, decode_encode] using fit)⟩)
  | .unboundedBelow below =>
    let infeasible := below 0
    False.elim (not_lt_of_ge ((objective_exact source word ordered task reserved held budget target
      infeasible.val).mp infeasible.property.1).1 infeasible.property.2)
  | .attained values fit minimal =>
    .attained (values (Fin.last width)) (decode (index source word ordered task) (Fin.init values))
      ((objective_exact source word ordered task reserved held budget target values).mp fit)
      (fun amount allocation checked => by
        let other : Fin (width + 1) → ℚ := Fin.snoc (encode (index source word ordered task) allocation) amount
        have otherFits := (objective_exact source word ordered task reserved held budget target other).mpr
          (by simpa only [other, Fin.snoc_last, Fin.init_snoc, decode_encode] using checked)
        exact (minimal other otherFits).trans_eq (Fin.snoc_last _ _))

theorem with_available_stock_at_the_target_uses_the_same_joint_contract
    (target : Party × Good) (allocation : Row → Lot → ℚ) :
    FitsAt source word ordered task reserved held budget target (opening source budget target) allocation ↔
      Fits source word ordered task reserved held budget allocation ∧ 0 ≤ opening source budget target := by
  unfold FitsAt Fits
  have same (key : Party × Good) :
      stockAt source budget target (opening source budget target) key = opening source budget key := by
    by_cases h : key = target <;> simp [stockAt, h]
  simp only [same]
  exact and_comm

theorem fitsAt_increases_with_real_stock (target : Party × Good) (first later : ℚ)
    (allocation : Row → Lot → ℚ)
    (checked : FitsAt source word ordered task reserved held budget target first allocation)
    (provided : first ≤ later) :
    FitsAt source word ordered task reserved held budget target later allocation := by
  refine ⟨checked.1.trans provided, checked.2.1, fun key listed => ?_⟩
  let profile := view source word ordered task reserved allocation
  let steps := Reserve.originalSteps source word (Reserve.assignedAt profile.paid)
  have before := (Reserve.openingNeed_fits_iff (heldRows ordered task held) profile.address key steps
    profile.required (stockAt source budget target first key)).mpr (checked.2.2 key listed)
  have enough : stockAt source budget target first key ≤ stockAt source budget target later key := by
    by_cases chosen : key = target <;> simp [stockAt, chosen, provided]
  exact (Reserve.openingNeed_fits_iff _ _ _ _ _ _).mp (before.trans enough)

theorem the_attained_opening_is_the_exact_required_stock (target : Party × Good)
    {amount : ℚ} {allocation : Row → Lot → ℚ}
    (paid : FitsAt source word ordered task reserved held budget target amount allocation)
    (least : ∀ other otherAllocation,
      FitsAt source word ordered task reserved held budget target other otherAllocation → amount ≤ other)
    (stock : ℚ) :
    (∃ assignment, FitsAt source word ordered task reserved held budget target stock assignment) ↔ amount ≤ stock :=
  ⟨fun ⟨assignment, fits⟩ => least stock assignment fits,
    fun enough => ⟨allocation, fitsAt_increases_with_real_stock source word ordered task reserved held budget
      target amount stock allocation paid enough⟩⟩

theorem the_tight_topup_keeps_every_other_address_fixed (target : Party × Good)
    {amount : ℚ} {allocation : Row → Lot → ℚ}
    (paid : FitsAt source word ordered task reserved held budget target amount allocation)
    (least : ∀ other otherAllocation,
      FitsAt source word ordered task reserved held budget target other otherAllocation → amount ≤ other)
    (extra : ℚ) (nonnegative : 0 ≤ extra) :
    (∃ assignment, FitsAt source word ordered task reserved held budget target
      (opening source budget target + extra) assignment) ↔
      max 0 (amount - opening source budget target) ≤ extra := by
  rw [the_attained_opening_is_the_exact_required_stock source word ordered task reserved held budget target paid least,
    max_le_iff]
  exact ⟨fun enough => ⟨nonnegative, sub_le_iff_le_add.mpr (by linarith only [enough])⟩,
    fun enough => by linarith only [enough.2]⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation
