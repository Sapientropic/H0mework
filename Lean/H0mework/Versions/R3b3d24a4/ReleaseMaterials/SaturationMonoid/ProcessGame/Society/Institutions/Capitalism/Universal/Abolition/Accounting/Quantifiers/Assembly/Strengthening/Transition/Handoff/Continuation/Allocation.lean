import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Native
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.CarryJoin.Incidence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Quantities
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (past future : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)

local notation "Row" => Due.Service.Need ordered.toFinset task
local notation "OldLot" => Due.Service.Supply source past ordered.toFinset task
local notation "Lot" => Due.Service.Supply source (past ++ future) ordered.toFinset task
local notation "Site" => ServiceSite Row Lot ⊕ StockSite (Party × Good)
  (ℕ × ExecutionItem Party Good Port Technology Instrument)
local notation "Width" => List.length (edgeList source (past ++ future) ordered task)
local notation "LinearFits" => SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Feasible

def reservations (prior : Finset (Due.Service.Ordinal source past))
    (later : Finset (Due.Service.Ordinal (Execution.endAt source past) future)) :
    Finset (Due.Service.Ordinal source (past ++ future)) :=
  Due.Service.carryReservations source past future prior ∪
    later.image (Due.Service.laterOrdinal source past future)

def priorSupply (lot : OldLot) : Lot :=
  (Due.Service.priorOrdinal source past future lot.1, lot.2)

def Keeps (prior : Row → OldLot → ℚ) (combined : Row → Lot → ℚ) : Prop :=
  ∀ row lot, combined row (priorSupply source past future ordered task lot) = prior row lot

private def pinValue {Label : Type} {width : ℕ} (label : Label)
    (coordinate : Affine width) (paid : ℚ) : List (Tagged Label width) :=
  [⟨label, Affine.le coordinate (Affine.literal paid)⟩,
    ⟨label, Affine.le (Affine.literal paid) coordinate⟩]

private def pin (prior : Row → OldLot → ℚ) (key : Row × OldLot) : List (Tagged (Row × OldLot) Width) :=
  pinValue key
    (edge (index source (past ++ future) ordered task) key.1 (priorSupply source past future ordered task key.2))
    (prior key.1 key.2)

variable (prior : Due.Service.Need ordered.toFinset task → Due.Service.Supply source past ordered.toFinset task → ℚ)

private theorem pin_exact (key : Row × OldLot) (values : Fin Width → ℚ) :
    LinearFits (numeric (pin source past future ordered task prior key)) values ↔
      decode (index source (past ++ future) ordered task) values key.1
        (priorSupply source past future ordered task key.2) = prior key.1 key.2 := by
  simp only [pin, pinValue, numeric, List.map_cons, List.map_nil, feasible_cons, feasible_nil, and_true,
    Affine.holds_le, Affine.eval_literal, edge_eval]
  exact le_antisymm_iff.symm

private theorem all_prior_edges_are_pinned (row : Row) (lot : OldLot) :
    (row, lot) ∈ edgeList source past ordered task := by
  apply List.mem_dedup.mpr
  exact List.mem_product.mpr ⟨Due.Service.needList_covers _ _ _ rfl row,
    Due.Service.supplyList_covers _ _ _ _ _ rfl lot⟩

private theorem pins_exact (values : Fin Width → ℚ) :
    LinearFits (numeric ((edgeList source past ordered task).flatMap (pin source past future ordered task prior)))
      values ↔ Keeps source past future ordered task prior
        (decode (index source (past ++ future) ordered task) values) := by
  rw [numeric_flatMap, feasible_flatMap]
  constructor
  · intro checked row lot
    exact (pin_exact source past future ordered task prior (row, lot) values).mp
      (checked (row, lot) (all_prior_edges_are_pinned source past ordered task row lot))
  · rintro kept ⟨row, lot⟩ _
    exact (pin_exact source past future ordered task prior (row, lot) values).mpr (kept row lot)

variable
  (oldReserved : Finset (Due.Service.Ordinal source past))
  (newReserved : Finset (Due.Service.Ordinal (Execution.endAt source past) future))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ)

local notation "Booked" => reservations source past future oldReserved newReserved

/-- Old paid coordinates are fixed before the service and chronological
stock constraints for the longer original word are examined. -/
def taggedSystem (prior : Row → OldLot → ℚ)
    (oldReserved : Finset (Due.Service.Ordinal source past))
    (newReserved : Finset (Due.Service.Ordinal (Execution.endAt source past) future))
    (held : Finset Row) (budget : Party × Good → ℚ) :
    List (Tagged ((Row × OldLot) ⊕ Site) Width) :=
  let locked := (edgeList source past ordered task).flatMap (pin source past future ordered task prior)
  let conditions : List (Tagged Site Width) :=
    taggedConstraints source (past ++ future) ordered task
      (reservations source past future oldReserved newReserved) held budget
  locked.map (Tagged.mapLabel Sum.inl) ++ conditions.map (Tagged.mapLabel Sum.inr)

theorem taggedSystem_exact (values : Fin Width → ℚ) :
    LinearFits (numeric (taggedSystem source past future ordered task prior oldReserved newReserved held budget))
      values ↔ Keeps source past future ordered task prior
        (decode (index source (past ++ future) ordered task) values) ∧
        Allocation.Fits source (past ++ future) ordered task Booked held budget
          (decode (index source (past ++ future) ordered task) values) := by
  rw [taggedSystem, numeric_append, numeric_mapLabel, numeric_mapLabel, feasible_append,
    pins_exact, taggedConstraints_exact, constraints_exact]

inductive AllocationResult where
  | paid (combined : Row → Lot → ℚ)
      (kept : Keeps source past future ordered task prior combined)
      (fits : Allocation.Fits source (past ++ future) ordered task Booked held budget combined)
  | blocked (reason : Conflict (taggedSystem source past future ordered task prior
      oldReserved newReserved held budget))

def allocate : AllocationResult source past future ordered task prior oldReserved newReserved held budget :=
  match diagnose (taggedSystem source past future ordered task prior oldReserved newReserved held budget) with
  | .feasible values checked =>
    let exactFit := (taggedSystem_exact source past future ordered task prior
      oldReserved newReserved held budget values).mp checked
    .paid (decode (index source (past ++ future) ordered task) values) exactFit.1 exactFit.2
  | .blocked failure => .blocked failure

theorem conflict_refutes_every_extension
    (reason : Conflict (taggedSystem source past future ordered task prior oldReserved newReserved held budget)) :
    ¬ ∃ combined, Keeps source past future ordered task prior combined ∧
      Allocation.Fits source (past ++ future) ordered task Booked held budget combined := by
  rintro ⟨combined, kept, fits⟩
  let values := encode (index source (past ++ future) ordered task) combined
  refine reason.refutes ⟨values, (taggedSystem_exact source past future ordered task prior
    oldReserved newReserved held budget values).mpr ?_⟩
  simpa only [values, decode_encode] using And.intro kept fits

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation
