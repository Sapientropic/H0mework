import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Service
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Stock
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Quantities
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
local notation "Material" => ℕ × ExecutionItem Party Good Port Technology Instrument
local notation "Address" => Party × Good
local notation "Site" => ServiceSite Row Lot ⊕ StockSite Address Material
local notation "Network" => Due.Service.network source word ordered.toFinset task reserved
local notation "Width" => List.length (edgeList source word ordered task)

def originalStock (key : Address) : List (Tagged (StockSite Address Material) Width) :=
  stockTagged (heldRows ordered task held) Due.Settlement.address key
    (Execution.inventory source word).length (Due.Settlement.finish source word)
    (fun item row => paymentAt source word ordered task item.1 row)
    (Reserve.originalSteps source word (fun _ _ => 0))
    (fun row => Affine.literal ((Network).need row)) (opening source budget key)

def serviceTags : List (Tagged Site Width) :=
  (serviceTagged (Network) (due source word ordered task) (index source word ordered task)
    (rows ordered task) (lots source word ordered task)).map (Tagged.mapLabel Sum.inl)

def bridgeTags : List (Tagged Site Width) :=
  (watched source word ordered task).flatMap fun key =>
    (originalStock source word ordered task reserved held budget key).map (Tagged.mapLabel Sum.inr)

/-- Labels decorate the same original list of inequalities. Their order
starts with service incidence and uses literal material order within an address. -/
def taggedConstraints : List (Tagged Site Width) :=
  serviceTags source word ordered task reserved ++ bridgeTags source word ordered task reserved held budget

theorem taggedConstraints_exact :
    numeric (taggedConstraints source word ordered task reserved held budget) =
      constraints source word ordered task reserved held budget := by
  unfold taggedConstraints constraints serviceTags bridgeTags originalStock
  simp only [numeric_append, numeric_mapLabel, serviceTagged_exact, numeric_flatMap, stockTagged_exact]

def diagnoseAllocation : Diagnosis (taggedConstraints source word ordered task reserved held budget) :=
  diagnose (taggedConstraints source word ordered task reserved held budget)

def jointConflictOfInfeasible
    (impossible : ¬ ∃ allocation, Fits source word ordered task reserved held budget allocation) :
    Conflict (taggedConstraints source word ordered task reserved held budget) :=
  conflictOfInfeasible _ (by
    rintro ⟨values, checked⟩
    apply impossible
    refine ⟨decode (index source word ordered task) values, ?_⟩
    exact (constraints_exact source word ordered task reserved held budget values).mp
      (taggedConstraints_exact source word ordered task reserved held budget ▸ checked))

theorem jointConflict_refutes
    (failure : Conflict (taggedConstraints source word ordered task reserved held budget)) :
    ¬ ∃ allocation, Fits source word ordered task reserved held budget allocation := by
  rintro ⟨allocation, fits⟩
  apply failure.refutes
  refine ⟨encode (index source word ordered task) allocation, ?_⟩
  rw [taggedConstraints_exact]
  apply (constraints_exact source word ordered task reserved held budget _).mpr
  simpa only [decode_encode] using fits

theorem stock_conflict_names_its_actual_cut
    (failure : Conflict (taggedConstraints source word ordered task reserved held budget))
    (site : StockSite Address Material) (named : failure.label = .inr site) :
    site.address ∈ watched source word ordered task ∧
      (site.cut = .terminal (Execution.inventory source word).length (Due.Settlement.finish source word) ∨
        ∃ step ∈ Reserve.originalSteps source word (fun _ _ => 0 : Row → ℕ → ℚ),
          site.cut = .material step.item step.clock) := by
  have original := failure.failed_is_original
  unfold taggedConstraints at original
  rcases List.mem_append.mp original with service | stock
  · obtain ⟨line, _, same⟩ := List.mem_map.mp service
    have mismatch : Sum.inl line.label = Sum.inr site := (congrArg Tagged.label same).trans named
    cases mismatch
  · obtain ⟨key, monitored, localRow⟩ := List.mem_flatMap.mp stock
    obtain ⟨line, listed, same⟩ := List.mem_map.mp localRow
    have read : line.label = site := Sum.inr.inj ((congrArg Tagged.label same).trans named)
    have here : site ∈ stockLabels key (Execution.inventory source word).length
        (Due.Settlement.finish source word) (Reserve.originalSteps source word (fun _ _ => 0 : Row → ℕ → ℚ)) := by
      have labels := stockTagged_labels (heldRows ordered task held) Due.Settlement.address key
        (Execution.inventory source word).length (Due.Settlement.finish source word)
        (fun item row => paymentAt source word ordered task item.1 row)
        (Reserve.originalSteps source word (fun _ _ => 0))
        (fun row => Affine.literal ((Network).need row)) (opening source budget key)
      rw [← labels]
      exact List.mem_map.mpr ⟨line, listed, read⟩
    obtain ⟨address, cut⟩ := stockLabels_original here
    exact ⟨address ▸ monitored, cut⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics
