import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Dynamics

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicDynamics
variable {frame : CPS1Recycling.Frame}

def isAmmoniaNode {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (node : Body.Node) : Bool :=
  (source.originAt? node.particle.address).any AtomOrigin.isAmmonia

def ammoniaNodes {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (nodes : List Body.Node) := nodes.filter (isAmmoniaNode source)

def chainForce {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (nodes : List Body.Node) (node : Body.Node) : Body.Point :=
  Body.force node nodes-Body.force node (ammoniaNodes source nodes)

def SourceActs {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (nodes : List Body.Node) : Prop :=
  ∃ node ∈ nodes, isAmmoniaNode source node = true ∧
    chainForce source nodes node ≠ 0 ∧ Body.force node nodes ≠ 0

structure Stage where
  before : List Body.Node
  after : List Body.Node
  time : ℝ
  beforeReserve : ℝ
  afterReserve : ℝ

structure Current (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw) where
  packet : Packet cursor raw
  nodes : List Body.Node
  reserve : ℝ
  stages : List Stage

def start {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (packet : Packet cursor raw) : Current cursor raw := ⟨packet,packet.nodes,raw.reserve,[]⟩

def Current.energy {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) : ℝ := Body.energy current.nodes

def Current.account {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) : ℝ := current.energy+current.reserve

structure NativeStep {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) where
  next : Current cursor raw
  source : next.packet = before.packet
  nodes : next.nodes = before.nodes.map (fun node => Body.kick node before.nodes time)
  reserve : next.reserve = before.reserve-(next.energy-before.energy)
  history : next.stages = before.stages ++ [⟨before.nodes,next.nodes,time,before.reserve,next.reserve⟩]
  elapsed : 0 < time
  acted : SourceActs before.packet.source before.nodes
  ready : Body.ready before.nodes
  nextReady : Body.ready next.nodes
  positiveReserve : 0 ≤ next.reserve

def nativeStep {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) : Except MechanicalFailure (NativeStep before time) := by
  classical
  exact if elapsed : 0 < time then
    if nonnegative : 0 ≤ before.reserve then
      if ready : Body.ready before.nodes then
        if acted : SourceActs before.packet.source before.nodes then
          let nodes := before.nodes.map (fun node => Body.kick node before.nodes time)
          if nextReady : Body.ready nodes then
            let difference := Body.energy nodes-before.energy
            if budget : difference ≤ before.reserve then
              let returned := before.reserve-difference
              let next : Current cursor raw :=
                ⟨before.packet,nodes,returned,before.stages ++ [⟨before.nodes,nodes,time,before.reserve,returned⟩]⟩
              .ok ⟨next,rfl,rfl,rfl,rfl,elapsed,acted,ready,nextReady,sub_nonneg.mpr budget⟩
            else .error .energyShortage
          else .error .collision
        else .error .noSourceResponse
      else .error .collision
    else .error .negativeReserve
  else .error .nonpositiveTime

inductive Disposition (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw)
  | sourceResidual (failure : AdmissionFailure)
  | mechanicalResidual (current : Current cursor raw) (failure : MechanicalFailure)
  | responded (before : Current cursor raw) (step : NativeStep before raw.time)

def fromCursor (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw) : Disposition cursor raw :=
  match packet cursor raw with
  | .error failure => .sourceResidual failure
  | .ok source =>
    let current := start source
    match nativeStep current raw.time with
    | .error failure => .mechanicalResidual current failure
    | .ok step => .responded current step

structure ResponseRow (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  origin : Option (AtomOrigin cursor)
  source : Charged.Particle
  total : Body.Point
  chain : Body.Point

def readResponse {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (before after : List Body.Node) (time : ℝ) : List (ResponseRow cursor) :=
  (before.zip after).map (fun row =>
    let total := row.2.row.momentum-row.1.row.momentum
    ⟨source.originAt? row.1.particle.address,row.1.particle,total,
      total-time • Body.force row.1 (ammoniaNodes source before)⟩)

theorem native_chain_response {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (nodes : List Body.Node) (node : Body.Node) (time : ℝ) :
    (Body.kick node nodes time).row.momentum-node.row.momentum-
      time • Body.force node (ammoniaNodes source nodes) = time • chainForce source nodes node := by
  simp only [Body.kick,chainForce,smul_sub]
  abel

theorem next_source_accounted {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) (time : ℝ) (step : NativeStep current time) :
    step.next.account = current.account ∧ step.next.packet = current.packet ∧
      step.next.nodes.map Body.Node.particle = current.nodes.map Body.Node.particle := by
  refine ⟨?_,step.source,?_⟩
  · unfold Current.account
    rw [step.reserve]
    ring
  · rw [step.nodes]
    simp only [List.map_map,Function.comp_def,Body.kick]

end
end CPS1SameEventFunction.Classical
