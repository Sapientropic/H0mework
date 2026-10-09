import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalPositive
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicDynamics Filter
open scoped Topology
variable {frame : CPS1Recycling.Frame}

def measurementPacket {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (empty : source.owned.chainRows = []) (reserve time : ℝ) :
    Packet cursor (source.measurementRaw reserve time) :=
  ⟨source,source.measurementNodes,by simp [rowCompatible,empty],by
    simpa only [empty,List.nil_append] using whole_source_measurement_gather source reserve time⟩

theorem measurement_packet_actual {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (selected : sourceAt cursor = .ok source)
    (empty : source.owned.chainRows = []) (reserve time : ℝ) :
    packet cursor (source.measurementRaw reserve time) = .ok (measurementPacket source empty reserve time) := by
  unfold packet
  rw [selected]
  simp only [Bind.bind,Except.bind]
  have compatible : rowCompatible source.owned.chainRows (source.measurementRaw reserve time).rows = .ok () := by
    simp [rowCompatible,empty]
  have gathered : Body.gather (source.particles.map Particle.readout)
      (source.owned.chainRows ++ (source.measurementRaw reserve time).rows) = .ok source.measurementNodes := by
    simpa only [empty,List.nil_append] using whole_source_measurement_gather source reserve time
  split
  · rename_i failure admitted
    have impossible := admitted.symm.trans compatible
    cases impossible
  · rename_i unitValue admitted
    cases unitValue
    split
    · rename_i failure actual
      have impossible := actual.symm.trans gathered
      cases impossible
    · rename_i nodes actual
      have same := Except.ok.inj (actual.symm.trans gathered)
      subst nodes
      rfl

def measurementCurrent {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (empty : source.owned.chainRows = []) (reserve time : ℝ) :=
  start (measurementPacket source empty reserve time)

private theorem measurement_raw_time {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (reserve time : ℝ) : (source.measurementRaw reserve time).time = time := rfl

private theorem native_step_of_laws {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) (elapsed : 0 < time) (nonnegative : 0 ≤ before.reserve)
    (ready : Body.ready before.nodes) (acted : SourceActs before.packet.source before.nodes)
    (nextReady : Body.ready (before.nodes.map (fun node => Body.kick node before.nodes time)))
    (budget : Body.energy (before.nodes.map (fun node => Body.kick node before.nodes time))-before.energy ≤ before.reserve) :
    ∃ step, nativeStep before time = .ok step := by
  unfold nativeStep
  simp only [dif_pos elapsed,dif_pos nonnegative,dif_pos ready,dif_pos acted,dif_pos nextReady,dif_pos budget]
  exact ⟨_,rfl⟩

theorem measured_successful_time {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (empty : source.owned.chainRows = []) :
    ∃ index : Nat, ∃ step, nativeStep (measurementCurrent source empty 1 0) ((1/2 : ℝ)^index) = .ok step := by
  have events := source_success_eventually (measurementCurrent source empty 1 0)
    (whole_source_measurement_separated source) (by norm_num [measurementCurrent,start,Source.measurementRaw]) (measured_source_acts source)
  have powers : Tendsto (fun index : Nat => (1/2 : ℝ)^index) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,selected⟩ := (powers.eventually events).exists
  exact ⟨index,selected (pow_pos (by norm_num : (0 : ℝ) < 1/2) index)⟩

theorem measured_public_responded {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (selected : sourceAt cursor = .ok source)
    (empty : source.owned.chainRows = []) :
    ∃ index : Nat,
      ∃ step : NativeStep (measurementCurrent source empty 1 ((1/2 : ℝ)^index)) ((1/2 : ℝ)^index),
        fromCursor cursor (source.measurementRaw 1 ((1/2 : ℝ)^index)) =
          .responded (measurementCurrent source empty 1 ((1/2 : ℝ)^index)) step := by
  obtain ⟨index,prior,actual⟩ := measured_successful_time source empty
  let time : ℝ := (1/2 : ℝ)^index
  have elapsed : 0 < time := pow_pos (by norm_num) index
  have ready : Body.ready source.measurementNodes := whole_source_measurement_separated source
  have acted : SourceActs source source.measurementNodes := measured_source_acts source
  have nextReady : Body.ready (source.measurementNodes.map (fun node => Body.kick node source.measurementNodes time)) := by
    have ready := prior.nextReady
    rw [prior.nodes] at ready
    exact ready
  have budget : Body.energy (source.measurementNodes.map (fun node => Body.kick node source.measurementNodes time)) -
      Body.energy source.measurementNodes ≤ 1 := by
    have paid := prior.positiveReserve
    rw [prior.reserve] at paid
    change 0 ≤ 1-(prior.next.energy-Body.energy source.measurementNodes) at paid
    unfold Current.energy at paid
    rw [prior.nodes] at paid
    exact sub_nonneg.mp paid
  have success : ∃ step, nativeStep (measurementCurrent source empty 1 time) time = .ok step := by
    exact native_step_of_laws (measurementCurrent source empty 1 time) time elapsed
      (by norm_num [measurementCurrent,start,Source.measurementRaw]) ready acted nextReady budget
  obtain ⟨step,actualNext⟩ := success
  refine ⟨index,step,?_⟩
  unfold fromCursor
  rw [measurement_packet_actual source selected empty 1 time]
  simp only [measurement_raw_time]
  simp only [measurementCurrent,time] at actualNext ⊢
  simp only [actualNext]

end
end CPS1SameEventFunction.Classical
