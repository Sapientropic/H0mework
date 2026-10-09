import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalDynamics
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicDynamics
variable {frame : CPS1Recycling.Frame}

def line (coordinate : ℝ) : Body.Point := WithLp.toLp 2 (fun axis => if axis = 0 then coordinate else 0)

theorem line_first (coordinate : ℝ) : line coordinate (0 : Fin 3) = coordinate := by simp [line]

def coordinate (target : Charged.Address) (row : Charged.Particle × Nat) : ℝ :=
  if row.1.address = target then 0 else
    if 0 < row.1.charge then (row.2 : ℝ)+1 else -((row.2 : ℝ)+1)

def measuredNode (target : Charged.Address) (row : Charged.Particle × Nat) : Body.Node :=
  ⟨row.1,⟨line (coordinate target row),0,1⟩⟩

def measuredNodes (particles : List Charged.Particle) (target : Charged.Address) :=
  particles.zipIdx.map (measuredNode target)

theorem measured_particles (particles : List Charged.Particle) (target : Charged.Address) :
    (measuredNodes particles target).map Body.Node.particle = particles := by
  simp only [measuredNodes,List.map_map,Function.comp_def,measuredNode]
  exact List.zipIdx_map_fst 0 _

theorem measured_gather (particles : List Charged.Particle) (target : Charged.Address)
    (unique : (particles.map Charged.Particle.address).Nodup) :
    Body.gather particles ((measuredNodes particles target).map (fun node => (node.particle.address,node.row))) =
      .ok (measuredNodes particles target) := by
  have addresses : ((measuredNodes particles target).map (fun node => node.particle.address)).Nodup := by
    change ((measuredNodes particles target).map (Charged.Particle.address ∘ Body.Node.particle)).Nodup
    rw [← List.map_map,measured_particles]
    exact unique
  apply Body.gather_exact _ _ (measured_particles particles target)
  · exact fun node held => Body.row_at_source _ addresses node held
  · intro node held
    rcases List.mem_map.mp held with ⟨row,_,rfl⟩
    norm_num [measuredNode]

private theorem coordinate_separated (target : Charged.Address) (first second : Charged.Particle × Nat)
    (differentAddress : first.1.address ≠ second.1.address) (differentOrdinal : first.2 ≠ second.2) :
    coordinate target first ≠ coordinate target second := by
  have positiveFirst : 0 < (first.2 : ℝ)+1 := by positivity
  have positiveSecond : 0 < (second.2 : ℝ)+1 := by positivity
  by_cases firstTarget : first.1.address = target
  · by_cases secondTarget : second.1.address = target
    · exact False.elim (differentAddress (firstTarget.trans secondTarget.symm))
    · by_cases secondPositive : 0 < second.1.charge <;>
        simp only [coordinate,firstTarget,secondTarget,secondPositive,if_true,if_false] <;> linarith
  · by_cases secondTarget : second.1.address = target
    · by_cases firstPositive : 0 < first.1.charge <;>
        simp only [coordinate,firstTarget,secondTarget,firstPositive,if_true,if_false] <;> linarith
    · by_cases firstPositive : 0 < first.1.charge <;> by_cases secondPositive : 0 < second.1.charge <;>
        simp only [coordinate,firstTarget,secondTarget,firstPositive,secondPositive,if_true,if_false]
      · intro equal
        apply differentOrdinal
        exact_mod_cast (by linarith : (first.2 : ℝ) = (second.2 : ℝ))
      · linarith
      · linarith
      · intro equal
        apply differentOrdinal
        exact_mod_cast (by linarith : (first.2 : ℝ) = (second.2 : ℝ))

theorem measured_ready (particles : List Charged.Particle) (target : Charged.Address)
    (unique : (particles.map Charged.Particle.address).Nodup) : Body.ready (measuredNodes particles target) := by
  have addresses : (particles.zipIdx.map (fun row => row.1.address)).Nodup := by
    change (particles.zipIdx.map (Charged.Particle.address ∘ Prod.fst)).Nodup
    rw [← List.map_map,List.zipIdx_map_fst]
    exact unique
  have ordinals : (particles.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have distinct := (List.pairwise_map.mp addresses).and (List.pairwise_map.mp ordinals)
  apply List.pairwise_map.mpr
  apply distinct.imp
  intro first second separate equal
  have read := congrArg (fun point : Body.Point => point (0 : Fin 3)) equal
  simp only [measuredNode,line_first] at read
  exact coordinate_separated target first second separate.1 separate.2 read

def Source.targetAddress {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) : Charged.Address :=
  .nucleus source.graph.atoms.length

def Source.measurementNodes {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :=
  measuredNodes (source.particles.map Particle.readout) source.targetAddress

def Source.measurementRaw {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (reserve time : ℝ) : Raw :=
  ⟨source.measurementNodes.map (fun node => (node.particle.address,node.row)),reserve,time⟩

theorem whole_source_measurement_gather {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (reserve time : ℝ) :
    Body.gather (source.particles.map Particle.readout) (source.measurementRaw reserve time).rows =
      .ok source.measurementNodes := by
  apply measured_gather
  simpa only [List.map_map,Function.comp_def] using source_global_addresses_unique source

theorem whole_source_measurement_separated {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :
    Body.ready source.measurementNodes := by
  apply measured_ready
  simpa only [List.map_map,Function.comp_def] using source_global_addresses_unique source

end
end CPS1SameEventFunction.Classical
