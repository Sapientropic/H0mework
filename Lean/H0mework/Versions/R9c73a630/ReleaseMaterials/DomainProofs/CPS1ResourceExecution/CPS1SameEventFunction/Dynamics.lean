import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ChainInteraction

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ReactiveField.Carried CPS1AtomicDynamics
variable {frame : CPS1Recycling.Frame}

structure MechanicalStage where
  before : List Body.Node
  after : List Body.Node
  time : ℝ
  beforeReserve : ℝ
  afterReserve : ℝ

-- The old cursor is retained as source history, not as a second spendable stock.
-- One NH3 token is represented by the bound packet; every unspent token and every
-- old full-E coefficient, origin, pending action and physical cut stays present.
structure Current (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw) where
  packet : Packet cursor raw
  nodes : List Body.Node
  reserve : ℝ
  stages : List MechanicalStage

def start {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (source : Packet cursor raw) : Current cursor raw :=
  ⟨source,source.nodes,source.source.active.fields.reserve+raw.reserve,[]⟩

def Current.energy {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) : ℝ :=
  materialEnergy current.packet.source.active.fields current.nodes

def Current.account {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) : ℝ := current.energy+current.reserve

def Current.unspent {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) := current.packet.source.ammonia.unspent

def Current.boundMaterial {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) := current.packet.source.ammonia.material

inductive MechanicalFailure
  | nonpositiveTime | negativeReserve | collision | noSourceResponse | energyShortage
  deriving DecidableEq

def SourceActs {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : CPS1ReactiveNuclear.Germ root state) (nodes : List Body.Node) : Prop :=
  ∃ node ∈ nodes, chainForce germ node ≠ 0 ∧ externalForce state node ≠ 0 ∧ sourceForce state nodes node ≠ 0

structure NativeStep {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) where
  next : Current cursor raw
  source : next.packet = before.packet
  nodes : next.nodes = sourceNext before.packet.source.active.fields before.nodes time
  reserve : next.reserve = before.reserve - (next.energy-before.energy)
  history : next.stages = before.stages ++ [⟨before.nodes,next.nodes,time,before.reserve,next.reserve⟩]
  elapsed : 0 < time
  acted : SourceActs before.packet.source.germ before.nodes
  currentReady : Body.ready (before.packet.source.active.fields.nuclei ++ before.nodes)
  nextReady : Body.ready (next.packet.source.active.fields.nuclei ++ next.nodes)
  positiveReserve : 0 ≤ next.reserve

-- Source energy and the actual generated trajectory select every disposition.
-- There is no caller-supplied force, target response or success certificate.
def nativeStep {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) : Except MechanicalFailure (NativeStep before time) := by
  classical
  exact if elapsed : 0 < time then
    if nonnegative : 0 ≤ before.reserve then
      if ready : Body.ready (before.packet.source.active.fields.nuclei ++ before.nodes) then
        if acted : SourceActs before.packet.source.germ before.nodes then
          let nodes := sourceNext before.packet.source.active.fields before.nodes time
          if nextReady : Body.ready (before.packet.source.active.fields.nuclei ++ nodes) then
            let difference := materialEnergy before.packet.source.active.fields nodes-before.energy
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

inductive FunctionDisposition (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw)
  | sourceResidual (failure : SourceFailure)
  | mechanicalResidual (current : Current cursor raw) (failure : MechanicalFailure)
  | responded (before : Current cursor raw) (step : NativeStep before raw.time)

-- This public producer starts at the actual returned cursor exactly once.
def fromCursor (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw) : FunctionDisposition cursor raw :=
  match packet cursor raw with
  | .error failure => .sourceResidual failure
  | .ok source =>
    let current := start source
    match nativeStep current raw.time with
    | .error failure => .mechanicalResidual current failure
    | .ok step => .responded current step

theorem actual_accounted_update {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) (step : NativeStep before time) :
    step.next.account = before.account ∧ step.next.packet = before.packet ∧
    step.next.unspent = before.unspent ∧ step.next.boundMaterial = before.boundMaterial ∧
    step.next.packet.source.active.fields = before.packet.source.active.fields ∧
    step.next.stages = before.stages ++
      [⟨before.nodes,step.next.nodes,time,before.reserve,step.next.reserve⟩] := by
  refine ⟨?_,step.source,?_,?_,?_,step.history⟩
  · unfold Current.account
    rw [step.reserve]
    ring
  · unfold Current.unspent
    rw [step.source]
  · unfold Current.boundMaterial
    rw [step.source]
  · rw [step.source]

theorem actual_next_response {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) (step : NativeStep before time) :
    ∃ node ∈ before.nodes,
      independentChainImpulse before.packet.source.germ node
        (sourceKick before.packet.source.active.fields before.nodes time node) before.nodes time ≠ 0 ∧
      independentImpulse node (sourceKick before.packet.source.active.fields before.nodes time node)
        before.nodes time ≠ 0 ∧
      (sourceKick before.packet.source.active.fields before.nodes time node).row.momentum ≠ node.row.momentum ∧
      sourceKick before.packet.source.active.fields before.nodes time node ∈ step.next.nodes := by
  rcases step.acted with ⟨node,held,chain,full,net⟩
  refine ⟨node,held,chain_response_nonzero _ _ _ _ (ne_of_gt step.elapsed) chain,
    independent_response_nonzero _ _ _ _ (ne_of_gt step.elapsed) full,?_,?_⟩
  · have delta : (sourceKick before.packet.source.active.fields before.nodes time node).row.momentum-
        node.row.momentum = time • sourceForce before.packet.source.active.fields before.nodes node := by
      simp only [sourceKick,Coulomb.nextP]
      abel
    apply sub_ne_zero.mp
    rw [delta]
    exact smul_ne_zero (ne_of_gt step.elapsed) net
  · rw [step.nodes]
    exact List.mem_map_of_mem held

theorem source_full_stock_partition {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) :
    (current.boundMaterial :: current.unspent).Perm (LiveStock cursor) := by
  simpa only [Current.boundMaterial,Current.unspent,AmmoniaAt.material,AmmoniaAt.unspent,
    List.get_eq_getElem] using List.getElem_cons_eraseIdx_perm current.packet.source.ammonia.slot.isLt

end
end CPS1SameEventFunction
