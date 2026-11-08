import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Deadline.Restriction
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Residual
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Deadline.Capacity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

/-- Two disjoint service modes on the original task roster. -/
structure Agenda (Party Good : Type) (TaskId : Type*) [DecidableEq Party] [DecidableEq Good] [DecidableEq TaskId] where
  task : TaskId → PublicTaskSpec Party Good
  atomic : List TaskId
  fragments : List TaskId
  disjoint : Disjoint atomic.toFinset fragments.toFinset
  original : OriginalDemands fragments.toFinset task

variable (agenda : Agenda Party Good TaskId)

def atomicAt (time : ℚ) : List TaskId :=
  agenda.atomic.filter fun id => decide ((agenda.task id).deadline ≤ time)

def dueLine (line : Need agenda.fragments.toFinset agenda.task) : ℚ :=
  (agenda.task line.1.1.val).deadline

abbrev keepAt (time : ℚ) : Need agenda.fragments.toFinset agenda.task → Bool :=
  Due.Deadline.dueBy (dueLine agenda) time

def cuts : Finset ℚ := ((agenda.atomic ++ agenda.fragments).map fun id => (agenda.task id).deadline).toFinset

abbrev base (source : C) (script : Script) (reserved : Finset (Ordinal source script)) :=
  network source script agenda.fragments.toFinset agenda.task reserved

abbrev ChoiceAt (source : C) (script : Script) (time : ℚ) :=
  WholeChoice source script (atomicAt agenda time).toFinset agenda.task

abbrev networkAt (source : C) (script : Script) (time : ℚ) (choice : ChoiceAt agenda source script time) :=
  (base agenda source script choice.reserved).restrict (keepAt agenda time)

def ServedThrough (source : C) (script : Script) (time : ℚ) : Prop :=
  ∃ choice : ChoiceAt agenda source script time,
    (base agenda source script choice.reserved).PaysWhere (keepAt agenda time)

theorem earlier_atomic_rows_are_original (earlier later : ℚ) (time : earlier ≤ later) :
    (atomicAt agenda earlier).toFinset ⊆ (atomicAt agenda later).toFinset := by
  intro id included
  obtain ⟨present, due⟩ := List.mem_filter.mp (List.mem_toFinset.mp included)
  exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨present, decide_eq_true ((of_decide_eq_true due).trans time)⟩)

theorem served_through_is_downward (source : C) (script : Script) {earlier later : ℚ} (order : earlier ≤ later) :
    ServedThrough agenda source script later → ServedThrough agenda source script earlier := by
  rintro ⟨whole, allocation, admitted, paid⟩
  let included := earlier_atomic_rows_are_original agenda earlier later order
  let shorter := restrictWhole included whole
  have subsets := restriction_releases_only_unneeded_whole_reservations included whole
  exact ⟨shorter, allocation, released_reservations_preserve_original_allocation subsets admitted,
    fun line due => paid line (decide_eq_true ((of_decide_eq_true due).trans order))⟩

/-- At each maturity cut, try all original whole assignments and solve each
rational residual on the same actual receipt ordinals. -/
def inspectAt (source : C) (script : Script) (time : ℚ) :
    ResidualSearch (networkAt agenda source script time) :=
  searchResidual (networkAt agenda source script time)
    (wholeChoices source script (atomicAt agenda time).toFinset agenda.task (atomicAt agenda time) rfl)
    (wholeChoices_contains_every_original_assignment source script _ agenda.task _ rfl)
    (fun choice => (networkAt agenda source script time choice).solveListed
      (needList agenda.fragments.toFinset agenda.task agenda.fragments rfl)
      (supplyList source script agenda.fragments.toFinset agenda.task agenda.fragments rfl)
      (needList_covers _ _ _ rfl) (supplyList_covers _ _ _ _ _ rfl))

theorem inspectAt_pays_exactly_the_original_due_prefix (source : C) (script : Script) (time : ℚ) :
    (inspectAt agenda source script time).hasAllocation = true ↔ ServedThrough agenda source script time := by
  rw [residual_search_passes_iff_some_assignment_fits]
  constructor
  · rintro ⟨choice, allocation, paid⟩
    exact ⟨choice, ((base agenda source script choice.reserved).restriction_is_exact_for_the_original_due_rows
      (keepAt agenda time)).mp ⟨allocation, paid⟩⟩
  · rintro ⟨choice, paid⟩
    obtain ⟨allocation, complete⟩ :=
      ((base agenda source script choice.reserved).restriction_is_exact_for_the_original_due_rows
        (keepAt agenda time)).mpr paid
    exact ⟨choice, allocation, complete⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
