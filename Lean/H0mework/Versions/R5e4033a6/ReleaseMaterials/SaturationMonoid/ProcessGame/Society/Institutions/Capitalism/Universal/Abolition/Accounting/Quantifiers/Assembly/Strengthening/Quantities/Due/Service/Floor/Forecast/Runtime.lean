import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.FloorGuard
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Funding
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Stock
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Use

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Runtime

open Source.Program Abolition.Root Abolition.Root.Registered

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Reading" => Cell (Party := Party) (Good := Good) × ℚ

/-- The scan reads finite numeric fields. The proofs bind each reading to
the literal source cut. -/
structure Snapshot (source : C) (past : Script) where
  current : Raw
  rows : List Reading
  current_exact : current = (Execution.endAt source past).raw
  rows_exact : rows.Perm ((roster source).map fun row =>
    (row.val, Demand.delivered source past row.val.1 row.val.2.1 row.val.2.2.1))

private def address (entry : Reading) : Party × Good := (entry.1.1, entry.1.2.2.1)

private def forecastAt (word : Word) (key : Party × Good) (entry : Reading) : ℚ :=
  let cell := entry.1
  if address entry = key then
    max 0 (cell.2.2.2 - (entry.2 + forecastUse word cell.1 cell.2.1 cell.2.2.1))
  else 0

def forecastRows (rows : List Reading) (word : Word) (key : Party × Good) : ℚ :=
  (rows.map (forecastAt word key)).sum

def chargeRows (rows : List Reading) (word : Word) (key : Party × Good) : ℚ :=
  Production.required word key.1 key.2 + forecastRows rows word key

def supportRows (rows : List Reading) (word : Word) : List (Party × Good) :=
  Production.addresses word ++ (rows.map address).dedup

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem chargeRows_zero_off_support (rows : List Reading) (word : Word) (key : Party × Good)
    (absent : key ∉ supportRows rows word) : chargeRows rows word key = 0 := by
  unfold chargeRows
  rw [Production.required_is_zero_at_an_unmentioned_address _ _ _
    (fun member => absent (List.mem_append_left _ member)), zero_add]
  unfold forecastRows
  apply List.sum_eq_zero
  intro quantity included
  obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp included
  unfold forecastAt
  apply if_neg
  intro same
  apply absent
  exact List.mem_append_right _ (List.mem_dedup.mpr (List.mem_map.mpr ⟨entry, listed, same⟩))

/-- Execute the existing stock checker on finite, exact rational data. -/
def inspectRows (current : Raw) (rows : List Reading) (word : Word)
    (opening : ∀ party good, 0 ≤ current.stock party good) :
    Production.StockDecision current (chargeRows rows word) (supportRows rows word) :=
  Production.inspectStock current (chargeRows rows word) (supportRows rows word)
    (chargeRows_zero_off_support rows word) opening

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

abbrev Snapshot.forecast (snapshot : Snapshot source past) (word : Word) := forecastRows snapshot.rows word

abbrev Snapshot.charge (snapshot : Snapshot source past) (word : Word) := chargeRows snapshot.rows word

abbrev Snapshot.support (snapshot : Snapshot source past) (word : Word) := supportRows snapshot.rows word

def Snapshot.extraStock (snapshot : Snapshot source past) (word : Word) (key : Party × Good) : ℚ :=
  max 0 (snapshot.charge word key - snapshot.current.stock key.1 key.2)

theorem Snapshot.forecast_exact (snapshot : Snapshot source past) (word : Word) (key : Party × Good) :
    snapshot.forecast word key = forecastHolding source past word key := by
  unfold Snapshot.forecast forecastRows forecastHolding
  rw [(snapshot.rows_exact.map (forecastAt word key)).sum_eq, List.map_map]
  rfl

theorem Snapshot.charge_exact (snapshot : Snapshot source past) (word : Word) (key : Party × Good) :
    snapshot.charge word key = Production.floorCharge source past word key := by
  unfold Snapshot.charge chargeRows Production.floorCharge
  exact congrArg (Production.required word key.1 key.2 + ·) (snapshot.forecast_exact word key)

theorem Snapshot.support_exact (snapshot : Snapshot source past) (word : Word) (key : Party × Good) :
    key ∈ snapshot.support word ↔ key ∈ Production.floorSupport source word := by
  unfold Snapshot.support supportRows Production.floorSupport holdingAddresses
  simp only [List.mem_append, List.mem_dedup]
  apply or_congr Iff.rfl
  have same := (snapshot.rows_exact.map address).mem_iff (a := key)
  rw [List.map_map] at same
  exact same

theorem Snapshot.extraStock_exact (snapshot : Snapshot source past) (word : Word) (key : Party × Good) :
    snapshot.extraStock word key = Production.extraForOriginalFloor source past word key := by
  unfold Snapshot.extraStock Production.extraForOriginalFloor
  rw [snapshot.charge_exact, snapshot.current_exact]

def Snapshot.inspect (snapshot : Snapshot source past) (word : Word)
    (opening : ∀ party good, 0 ≤ snapshot.current.stock party good) :
    Production.StockDecision snapshot.current (snapshot.charge word) (snapshot.support word) :=
  inspectRows snapshot.current snapshot.rows word opening

def Snapshot.inspectOriginal (snapshot : Snapshot source past) (word : Word)
    (opening : ∀ party good, 0 ≤ snapshot.current.stock party good) :
    Production.StockDecision (Execution.endAt source past).raw
      (Production.floorCharge source past word) (Production.floorSupport source word) :=
  match snapshot.inspect word opening with
  | .funded all => .funded fun key => by
    rw [← snapshot.charge_exact, ← snapshot.current_exact]
    exact all key
  | .short issue =>
    .short ⟨issue.address, (snapshot.support_exact word issue.address).mp issue.original, by
      rw [← snapshot.charge_exact, ← snapshot.current_exact]
      exact issue.short⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Runtime
