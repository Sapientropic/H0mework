import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Carry
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (past future : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
  (ids : Finset TaskId) (task : TaskId → PublicTaskSpec Party Good)

def carriedSupply :
    (Supply source past ids task ⊕ Supply (endAt source past) future ids task) ≃
      Supply source (past ++ future) ids task :=
  (Equiv.sumProdDistrib _ _ _).symm.trans
    (Equiv.prodCongr (finSumFinEquiv.trans (finCongr (by rw [inventory_append, List.length_append]))) (Equiv.refl _))

@[simp] theorem carriedSupply_left (item : Supply source past ids task) :
    carriedSupply source past future ids task (.inl item) = (priorOrdinal source past future item.1, item.2) := by
  exact Prod.ext (Fin.ext rfl) rfl

@[simp] theorem carriedSupply_right (item : Supply (endAt source past) future ids task) :
    carriedSupply source past future ids task (.inr item) = (laterOrdinal source past future item.1, item.2) := by
  exact Prod.ext (Fin.ext rfl) rfl

def carryReservations (booked : Finset (Ordinal source past)) : Finset (Ordinal source (past ++ future)) :=
  booked.image (priorOrdinal source past future)

private theorem old_booking (booked : Finset (Ordinal source past)) (item : Ordinal source past) :
    priorOrdinal source past future item ∈ carryReservations source past future booked ↔ item ∈ booked := by
  constructor
  · intro reserved
    obtain ⟨old, listed, exactOrdinal⟩ := Finset.mem_image.mp reserved
    have equal : old = item := Fin.ext (congrArg (fun (i : Ordinal source (past ++ future)) => i.val) exactOrdinal)
    exact equal ▸ listed
  · intro listed
    exact Finset.mem_image.mpr ⟨item, listed, rfl⟩

private theorem new_not_booked (booked : Finset (Ordinal source past))
    (item : Ordinal (endAt source past) future) :
    laterOrdinal source past future item ∉ carryReservations source past future booked := by
  intro reserved
  obtain ⟨old, _, exactOrdinal⟩ := Finset.mem_image.mp reserved
  exact prior_and_later_service_ordinals_are_disjoint source past future old item exactOrdinal

private theorem old_law_is_still_original :
    (endAt source past).native.handlerFace.rootRead = source.native.handlerFace.rootRead := by
  change Physical.Public.interpreter (endAt source past).native.input = Physical.Public.interpreter source.native.input
  rw [Execution.endAt_input]

theorem carried_left_capacity (booked : Finset (Ordinal source past)) (item : Supply source past ids task) :
    (network source (past ++ future) ids task (carryReservations source past future booked)).capacity
      (carriedSupply source past future ids task (.inl item)) =
    (network source past ids task booked).capacity item := by
  have time := prior_ordinal_keeps_its_exact_original_receipt_and_clock source past future item.1
  simp [network, time, old_booking]

theorem carried_right_capacity (booked : Finset (Ordinal source past))
    (item : Supply (endAt source past) future ids task) :
    (network source (past ++ future) ids task (carryReservations source past future booked)).capacity
      (carriedSupply source past future ids task (.inr item)) =
    (network (endAt source past) future ids task ∅).capacity item := by
  have time := later_ordinal_keeps_its_exact_original_receipt_and_clock source past future item.1
  simp [network, time, new_not_booked, old_law_is_still_original]

theorem carried_left_incidence (booked : Finset (Ordinal source past))
    (line : Need ids task) (item : Supply source past ids task) :
    let combined := network source (past ++ future) ids task (carryReservations source past future booked)
    let old := network source past ids task booked
    let used := carriedSupply source past future ids task (.inl item)
    combined.allows line used = old.allows line item ∧ combined.capacity used = old.capacity item := by
  have time := prior_ordinal_keeps_its_exact_original_receipt_and_clock source past future item.1
  dsimp only
  constructor
  · apply Bool.eq_iff_iff.mpr
    rw [network_allows_iff, network_allows_iff, carriedSupply_left]
    simp [accepts, time, old_booking]
  · exact carried_left_capacity source past future ids task booked item

theorem carried_right_incidence (booked : Finset (Ordinal source past))
    (line : Need ids task) (item : Supply (endAt source past) future ids task) :
    let combined := network source (past ++ future) ids task (carryReservations source past future booked)
    let fresh := network (endAt source past) future ids task ∅
    let used := carriedSupply source past future ids task (.inr item)
    combined.allows line used = fresh.allows line item ∧ combined.capacity used = fresh.capacity item := by
  have time := later_ordinal_keeps_its_exact_original_receipt_and_clock source past future item.1
  dsimp only
  constructor
  · apply Bool.eq_iff_iff.mpr
    rw [network_allows_iff, network_allows_iff, carriedSupply_right]
    simp [accepts, time, new_not_booked, old_law_is_still_original]
  · exact carried_right_capacity source past future ids task booked item

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
