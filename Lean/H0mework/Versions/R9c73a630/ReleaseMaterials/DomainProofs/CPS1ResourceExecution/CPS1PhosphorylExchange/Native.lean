import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Variation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Derivatives

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction CPS1BiologicalUpdate
open Filter
open scoped BigOperators InnerProductSpace Matrix
open scoped Topology

def sourceKick (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source)
    (time : ℝ) (node : Body.Node) : Body.Node :=
  match node.particle.address with
  | .electron .. => node
  | .nucleus _ =>
    let force := energyForce source pose mass occupied node
    {node with row := {node.row with
      position := node.row.position+(time/node.row.inertia) • node.row.momentum+
        (time^2/(2*node.row.inertia)) • force
      momentum := node.row.momentum+time • force}}

structure ElectronicBond {frame : CPS1Recycling.Frame}
    (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  first : AtomOrigin cursor
  second : AtomOrigin cursor
  weight : ℝ

-- All pairs, including newly formed cross-occurrence incidence, are generated
-- from the updated density. The input graph survives as source provenance.
def electronicBonds {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (source pose : List Body.Node) (occupied : Coefficients source) :
    List (ElectronicBond cursor) :=
  (atoms.zipIdx).flatMap (fun first => (atoms.zipIdx).filterMap (fun second =>
    if first.2 < second.2 then do
      let left ← nodeAt? pose (.nucleus first.2)
      let right ← nodeAt? pose (.nucleus second.2)
      pure ⟨first.1.origin,second.1.origin,
        Complex.normSq (densityKernelAt source occupied left.row.position right.row.position)⟩
    else none))

def electronicBond (source pose : List Body.Node) (occupied : Coefficients source) (channel : Channel) : Option (ℝ × ℝ) := do
  let p ← nodeAt? pose channel.phosphorus
  let leave ← nodeAt? pose channel.leavingOxygen
  let attack ← nodeAt? pose channel.attackingOxygen
  pure (Complex.normSq (densityKernelAt source occupied p.row.position leave.row.position),
    Complex.normSq (densityKernelAt source occupied p.row.position attack.row.position))

structure BondResponse where
  beforeLeaving : ℝ
  afterLeaving : ℝ
  beforeAttacking : ℝ
  afterAttacking : ℝ
  time : ℝ

def BondResponse.exchanging (response : BondResponse) : Prop :=
  response.afterLeaving < response.beforeLeaving ∧ response.beforeAttacking < response.afterAttacking

-- The actual paid chain slot is selected from the same current inventory,
-- rather than duplicated beside a replacement molecular token.
def chainSlot? {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) : Option (Fin (LiveStock cursor).length) := by
  classical
  exact (List.finRange (LiveStock cursor).length).find? (fun slot =>
    decide (Classical.ownedLive? ((LiveStock cursor).get slot) = some source.owned))

def unspentLive {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (chainSlot : Fin (LiveStock cursor).length) :=
  (LiveStock cursor).zipIdx.filterMap (fun entry =>
    if entry.2 = chainSlot.val ∨ entry.2 = source.ammonia.slot.val then none else some entry.1)

structure NativeCurrent {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw) where
  nodes : List Body.Node
  occupied : Coefficients source.nodes
  reserve : ℝ
  channel : Channel
  channelActual : channel? source.atoms raw.fuel = some channel
  response : BondResponse
  bonds : List (ElectronicBond cursor)
  chainSlot : Fin (LiveStock cursor).length
  chainSlotActual : Classical.ownedLive? ((LiveStock cursor).get chainSlot) = some before.packet.source.owned
  parentsDistinct : chainSlot ≠ before.packet.source.ammonia.slot
  remaining : List (CPS1ReactiveField.LiveMaterial frame)
  remainingActual : remaining = unspentLive before.packet.source chainSlot
  materializedRaw : List (FuelKind × Nat)
  rawActual : materializedRaw = raw.fuel.zipIdx
  atomsActual : nodes.map Body.Node.particle = source.nodes.map Body.Node.particle
  ready : Body.ready nodes
  positiveReserve : 0 ≤ reserve
  initialOccupied : Coefficients source.nodes
  initialActual : initialOccupied = initialOccupation source.nodes
  initialGram : initialOccupied.conjTranspose * initialOccupied = 1
  initialBond : ∃ point : Body.Point, 0 < bondWeight source.nodes initialOccupied point point
  halfOccupied : Coefficients source.nodes
  halfActual : halfOccupied = occupiedNextAt source.nodes source.nodes source.electronInertia raw.time initialOccupied
  halfGram : halfOccupied.conjTranspose * halfOccupied = 1
  elapsed : 0 < raw.time
  smooth : energySmooth source.nodes source.nodes source.electronInertia halfOccupied
  nodesActual : nodes = source.nodes.map (sourceKick source.nodes source.nodes source.electronInertia halfOccupied raw.time)
  occupiedActual : occupied = occupiedNextAt source.nodes nodes source.electronInertia raw.time halfOccupied
  occupiedGram : occupied.conjTranspose * occupied = 1
  electronNumber : Matrix.trace (density occupied) = (electronCount source.nodes : ℂ)
  chainWork : ℝ
  chainWorkActual : chainWork = directionalChainWork source.atoms source.nodes source.electronInertia halfOccupied channel
  acted : chainWork ≠ 0
  exchanging : response.exchanging
  responseActual : electronicBond source.nodes source.nodes initialOccupied channel =
      some (response.beforeLeaving,response.beforeAttacking) ∧
    electronicBond source.nodes nodes occupied channel =
      some (response.afterLeaving,response.afterAttacking)
  bondsActual : bonds = electronicBonds source.atoms source.nodes nodes occupied
  account : wholeEnergyAt source.nodes nodes source.electronInertia occupied+reserve =
    Body.energy source.nodes+step.next.reserve+raw.reserve

-- This inventory genuinely replaces the selected native materials with their
-- atomized electronic/bond successor. Original tokens remain only as parents.
inductive StockItem {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw)
  | remaining (material : CPS1ReactiveField.LiveMaterial frame)
  | evolved (current : NativeCurrent source)

def inventory {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
    {source : Common before step raw} (current : NativeCurrent source) : List (StockItem source) :=
  .evolved current :: current.remaining.map StockItem.remaining

theorem source_kick_particles (nodes : List Body.Node) (mass : ℝ) (occupied : Coefficients nodes) (time : ℝ) :
    (nodes.map (sourceKick nodes nodes mass occupied time)).map Body.Node.particle = nodes.map Body.Node.particle := by
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro node _
  cases selected : node.particle.address <;> simp only [sourceKick,selected]

def firstElectronicExchange {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
    (source : Common before step raw) : Except Failure (NativeCurrent source) := by
  classical
  exact match channelSelected : channel? source.atoms raw.fuel with
  | none => .error .noExchangeCoordinate
  | some channel => match chainSlot? before.packet.source with
    | none => .error .noPaidChainSlot
    | some slot =>
      if paid : Classical.ownedLive? ((LiveStock cursor).get slot) = some before.packet.source.owned then
        if distinct : slot ≠ before.packet.source.ammonia.slot then
          match captured : capture source.nodes source.electronInertia (step.next.reserve+raw.reserve) with
          | .error failure => .error failure
          | .ok electrons =>
            if elapsed : 0 < raw.time then
              let half := occupiedNextAt source.nodes source.nodes source.electronInertia raw.time electrons.occupied
              let smooth := energy_smooth_of_ready source.nodes source.nodes source.electronInertia half source.ready
              let work := directionalChainWork source.atoms source.nodes source.electronInertia half channel
              if acted : work ≠ 0 then
                let nodes := source.nodes.map (sourceKick source.nodes source.nodes source.electronInertia half raw.time)
                if ready : Body.ready nodes then
                  let occupied := occupiedNextAt source.nodes nodes source.electronInertia raw.time half
                  let price := wholeEnergyAt source.nodes nodes source.electronInertia occupied-
                    wholeEnergyAt source.nodes source.nodes source.electronInertia electrons.occupied
                  if budget : price ≤ electrons.reserve then
                    match firstActual : electronicBond source.nodes source.nodes electrons.occupied channel with
                    | none => .error .noExchangeCoordinate
                    | some first => match afterActual : electronicBond source.nodes nodes occupied channel with
                      | none => .error .noExchangeCoordinate
                      | some after =>
                        let response : BondResponse := ⟨first.1,after.1,first.2,after.2,raw.time⟩
                        if exchanged : response.exchanging then
                          have accounting : wholeEnergyAt source.nodes nodes source.electronInertia occupied+
                              (electrons.reserve-price) = Body.energy source.nodes+step.next.reserve+raw.reserve := by
                            have paidCapture := (captured_account source.nodes source.electronInertia
                              (step.next.reserve+raw.reserve) electrons captured).2
                            rw [← whole_energy_at_self] at paidCapture
                            dsimp only [price]
                            linarith
                          have initialActual := (captured_account source.nodes source.electronInertia
                            (step.next.reserve+raw.reserve) electrons captured).1
                          have initialGram : electrons.occupied.conjTranspose * electrons.occupied = 1 := by
                            rw [initialActual]
                            exact initial_occupation_gram source.nodes
                          have initialBond : ∃ point : Body.Point, 0 < bondWeight source.nodes electrons.occupied point point := by
                            rw [initialActual]
                            exact initial_bond_nonempty source.nodes (common_positive_electrons source).1
                          have halfGram : half.conjTranspose * half = 1 :=
                            (occupied_next_gram source.nodes source.nodes source.electronInertia raw.time electrons.occupied).trans initialGram
                          have occupiedGram : occupied.conjTranspose * occupied = 1 :=
                            (occupied_next_gram source.nodes nodes source.electronInertia raw.time half).trans halfGram
                          .ok {
                            nodes := nodes, occupied := occupied, reserve := electrons.reserve-price
                            channel := channel, channelActual := channelSelected, response := response
                            bonds := electronicBonds source.atoms source.nodes nodes occupied
                            chainSlot := slot, chainSlotActual := paid, parentsDistinct := distinct
                            remaining := unspentLive before.packet.source slot, remainingActual := rfl
                            materializedRaw := raw.fuel.zipIdx, rawActual := rfl
                            atomsActual := source_kick_particles source.nodes source.electronInertia half raw.time
                            ready := ready, positiveReserve := sub_nonneg.mpr budget
                            initialOccupied := electrons.occupied, initialActual := initialActual, initialGram := initialGram, initialBond := initialBond
                            halfOccupied := half, halfActual := rfl, halfGram := halfGram
                            elapsed := elapsed, smooth := smooth, nodesActual := rfl, occupiedActual := rfl, occupiedGram := occupiedGram
                            electronNumber := electron_number source.nodes occupied occupiedGram
                            chainWork := work, chainWorkActual := rfl, acted := acted, exchanging := exchanged
                            responseActual := ⟨firstActual,afterActual⟩, bondsActual := rfl, account := accounting }
                        else .error .wrongExchangeDirection
                  else .error .energyShortage
                else .error .collision
              else .error .zeroCoordinateWork
            else .error .nonpositiveTime
        else .error .noPaidChainSlot
      else .error .noPaidChainSlot

inductive Disposition {body : Body} (priorRaw : WholeRaw) (raw : Raw) :
    (repair : LocalRepairDisposition body) → WholeResponse repair priorRaw → Type 1
  | retained {repair : LocalRepairDisposition body} (whole : WholeResponse repair priorRaw) (failure : Failure) :
      Disposition priorRaw raw repair whole
  | responded {receipt : LocalRepairReceipt body} (whole : WholeResponse (.repaired receipt) priorRaw)
      (before : Classical.Current receipt.nextBody.current.2 priorRaw.particles)
      (step : Classical.NativeStep before priorRaw.particles.time)
      (actualParticles : whole.particles = Classical.Disposition.responded before step)
      (source : Common before step raw) (next : NativeCurrent source) :
      Disposition priorRaw raw (.repaired receipt) whole

-- Root consumers pass their already stored response. This method never runs the
-- old classical producer or either 1500-step biological construction again.
def fromWhole {body : Body} (repair : LocalRepairDisposition body) {priorRaw : WholeRaw}
    (whole : WholeResponse repair priorRaw) (raw : Raw) : Disposition priorRaw raw repair whole := by
  classical
  cases repair with
  | residual event failed => exact .retained whole .priorResponse
  | repaired receipt =>
    exact match actual : whole.particles with
    | .sourceResidual _ => .retained whole .priorResponse
    | .mechanicalResidual _ _ => .retained whole .priorResponse
    | .responded before step =>
      match admitted : admit before step raw with
      | .error failure => .retained whole failure
      | .ok source => match firstElectronicExchange source with
        | .error failure => .retained whole failure
        | .ok next => .responded whole before step actual source next

end
end CPS1PhosphorylExchange
