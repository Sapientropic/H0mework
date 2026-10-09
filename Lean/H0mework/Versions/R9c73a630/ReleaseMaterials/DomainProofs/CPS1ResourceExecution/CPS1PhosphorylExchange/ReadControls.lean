import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Native

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction

-- This reader recomputes both bond weights from the actual fields and positions.
def readBondChange (source before after : List Body.Node)
    (initial occupied : Coefficients source) (channel : Channel) : Option (ℝ × ℝ) := do
  let first ← electronicBond source before initial channel
  let last ← electronicBond source after occupied channel
  pure (last.1-first.1,last.2-first.2)

theorem actual_bond_change {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
    {source : Common before step raw} (current : NativeCurrent source) :
    ∃ leaving attacking : ℝ,
      readBondChange source.nodes source.nodes current.nodes
        current.initialOccupied current.occupied current.channel = some (leaving,attacking) ∧
      leaving < 0 ∧ 0 < attacking := by
  refine ⟨current.response.afterLeaving-current.response.beforeLeaving,
    current.response.afterAttacking-current.response.beforeAttacking,?_,?_,?_⟩
  · simp only [readBondChange,current.responseActual.1,current.responseActual.2,
      Bind.bind,Option.bind,Pure.pure]
  · exact sub_neg.mpr current.exchanging.1
  · exact sub_pos.mpr current.exchanging.2

def readRemainingSlots {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (chainSlot : Fin (LiveStock cursor).length) :
    List (CPS1ReactiveField.LiveMaterial frame × Nat) :=
  (LiveStock cursor).zipIdx.filter (fun entry =>
    !(entry.2 = chainSlot.val ∨ entry.2 = source.ammonia.slot.val))

theorem remaining_slot_exact {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (chainSlot : Fin (LiveStock cursor).length)
    (material : CPS1ReactiveField.LiveMaterial frame) (slot : Nat) :
    (material,slot) ∈ readRemainingSlots source chainSlot ↔
      (LiveStock cursor)[slot]? = some material ∧
      slot ≠ chainSlot.val ∧ slot ≠ source.ammonia.slot.val := by
  simp [readRemainingSlots,List.mk_mem_zipIdx_iff_getElem?]

theorem remaining_materials_exact {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (chainSlot : Fin (LiveStock cursor).length) :
    (readRemainingSlots source chainSlot).map Prod.fst = unspentLive source chainSlot := by
  unfold readRemainingSlots unspentLive
  induction (LiveStock cursor).zipIdx with
  | nil => rfl
  | cons entry rest ih =>
    by_cases consumed : entry.2 = chainSlot.val ∨ entry.2 = source.ammonia.slot.val
    · have test : (!decide (entry.2 = chainSlot.val ∨ entry.2 = source.ammonia.slot.val)) = false := by
        simp [consumed]
      simp only [List.filter_cons,test,Bool.false_eq_true,if_false,List.filterMap_cons,if_pos consumed,ih]
    · have test : (!decide (entry.2 = chainSlot.val ∨ entry.2 = source.ammonia.slot.val)) = true := by
        simp [consumed]
      simp only [List.filter_cons,test,if_true,List.map_cons,List.filterMap_cons,if_neg consumed,ih]

theorem actual_inventory_read {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
    {source : Common before step raw} (current : NativeCurrent source) :
    inventory current = StockItem.evolved current ::
      ((readRemainingSlots before.packet.source current.chainSlot).map Prod.fst).map
        (StockItem.remaining (source := source)) := by
  rw [remaining_materials_exact,← current.remainingActual]
  rfl

theorem missing_atp_is_retained {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) (raw : Raw)
    (missing : (raw.fuel.filter (· == .atp)).length < 2) :
    admit before step raw = .error .missingATP := by
  unfold admit
  rw [dif_pos missing]

theorem missing_bicarbonate_is_retained {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) (raw : Raw)
    (atp : 2 ≤ (raw.fuel.filter (· == .atp)).length)
    (missing : .bicarbonate ∉ raw.fuel) :
    admit before step raw = .error .missingBicarbonate := by
  unfold admit
  rw [dif_neg (Nat.not_lt.mpr atp),dif_pos missing]

theorem success_requires_positive_time {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
    (source : Common before step raw) (next : NativeCurrent source)
    (_actual : firstElectronicExchange source = .ok next) : 0 < raw.time :=
  next.elapsed

theorem nonpositive_time_cannot_fire {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
    (source : Common before step raw) (time : raw.time ≤ 0) :
    ∀ next, firstElectronicExchange source ≠ .ok next := by
  intro next actual
  exact (not_lt.mpr time) (success_requires_positive_time source next actual)

theorem zero_coordinate_work_cannot_fire {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
    (source : Common before step raw) (channel : Channel)
    (selected : channel? source.atoms raw.fuel = some channel)
    (zero : ∀ occupied : Coefficients source.nodes,
      directionalChainWork source.atoms source.nodes source.electronInertia occupied channel = 0) :
    ∀ next, firstElectronicExchange source ≠ .ok next := by
  intro next _actual
  have same := Option.some.inj (next.channelActual.symm.trans selected)
  have absent : next.chainWork = 0 := by
    rw [next.chainWorkActual,same]
    exact zero next.halfOccupied
  exact next.acted absent

theorem absent_chain_has_zero_coordinate_work {frame : CPS1Recycling.Frame}
    {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (fuel : List FuelKind) (nodes : List Body.Node)
    (mass : ℝ) (occupied : Coefficients nodes) (channel : Channel)
    (selected : channel? atoms fuel = some channel)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup)
    (ready : Body.ready nodes) (absent : chainNuclei atoms nodes = []) :
    directionalChainWork atoms nodes mass occupied channel = 0 := by
  rw [directional_chain_work_nuclear atoms fuel nodes mass occupied channel selected unique ready,absent]
  simp [Body.force]

end
end CPS1PhosphorylExchange
