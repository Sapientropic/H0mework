import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Response
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Positive
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Data.Rat.Encodable

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1AtomicDynamics CPS1PhosphorylExchange CPS1SameEventFunction
open scoped Topology BigOperators

def rationalCoordinate (index : Nat) : ℝ := ((Encodable.decode (α := ℚ) index).getD 0 : ℚ)
def dyadicHeight (index : Nat) : ℝ := 1/((1/2 : ℝ)^index)

private theorem rational_axis_available (nodes : List Body.Node) (electrons : 0 < electronCount nodes) :
    ∃ index : Nat, 0 < bondWeight nodes (initialOccupation nodes)
      (transversePoint (rationalCoordinate index) 0 0) (transversePoint (rationalCoordinate index) 0 0) := by
  have pointContinuous : Continuous (fun x : ℝ => transversePoint x 0 0) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    fun_prop
  have continuous : Continuous (fun x : ℝ => bondWeight nodes (initialOccupation nodes)
      (transversePoint x 0 0) (transversePoint x 0 0)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact bond_weight_continuous nodes (fun _ : ℝ => initialOccupation nodes)
      (fun x => transversePoint x 0 0) (fun x => transversePoint x 0 0) x
      continuousAt_const pointContinuous.continuousAt pointContinuous.continuousAt
  obtain ⟨x,positive⟩ := initial_axis_bond_nonempty nodes electrons
  obtain ⟨q,present⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_mem_open
    (isOpen_lt continuous_const continuous) ⟨x,positive⟩
  refine ⟨Encodable.encode q,?_⟩
  simpa only [rationalCoordinate,Encodable.encodek,Option.getD_some,Set.mem_ofPred_eq] using present

abbrev indexedBaseRaw {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (coordinate height : Nat) : CPS1PhosphorylExchange.Raw :=
  baseRaw before.packet.source (rationalCoordinate coordinate) (dyadicHeight height)

abbrev indexedBaseNodes {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) (coordinate height : Nat) :=
  baseNodes before step (rationalCoordinate coordinate) (dyadicHeight height)

structure SourceBaseParameters {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) : Type where
  coordinate : Nat
  height : Nat
  high : 1 < dyadicHeight height
  margin : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3)+4 < dyadicHeight height
  axis : 0 < bondWeight (indexedBaseNodes before step coordinate height)
    (initialOccupation (indexedBaseNodes before step coordinate height))
    (transversePoint (rationalCoordinate coordinate) 0 0) (transversePoint (rationalCoordinate coordinate) 0 0)
  work : ∀ occupied : Coefficients (indexedBaseNodes before step coordinate height),
    0 < directionalChainWork (commonAtoms before.packet.source firstFuel)
      (indexedBaseNodes before step coordinate height) 1 occupied (firstChannel before.packet.source)
  admitted : ∃ source : Common before step (indexedBaseRaw before coordinate height),
    admit before step (indexedBaseRaw before coordinate height) = .ok source ∧
    source.nodes = indexedBaseNodes before step coordinate height ∧ source.electronInertia = 1

noncomputable def source_base_parameters {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (oldUnit : ∀ node ∈ step.next.nodes, node.row.inertia = 1) : SourceBaseParameters before step := by
  classical
  let firstHeight := oldHeight step.next.nodes
  have firstAbove : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3) < firstHeight := by
    intro node held
    have bounded := old_below_height step.next.nodes node held
    dsimp only [firstHeight]
    linarith
  have electrons : 0 < electronCount (baseNodes before step 0 firstHeight) := by
    obtain ⟨source,_,nodes,_⟩ := base_admitted before step actual 0 firstHeight oldUnit firstAbove
    have generated := (common_positive_electrons source).1
    rwa [nodes] at generated
  let coordinate := Nat.find (rational_axis_available (baseNodes before step 0 firstHeight) electrons)
  let x := rationalCoordinate coordinate
  have axisInitial : 0 < bondWeight (baseNodes before step 0 firstHeight)
      (initialOccupation (baseNodes before step 0 firstHeight)) (transversePoint x 0 0) (transversePoint x 0 0) :=
    Nat.find_spec (rational_axis_available (baseNodes before step 0 firstHeight) electrons)
  have charge : 0 < ((postChain before.packet.source step.next.nodes).map
      (fun node => (node.particle.charge : ℝ))).sum := by
    obtain ⟨source,_,nodes,_⟩ := base_admitted before step actual 0 firstHeight oldUnit firstAbove
    have generated := common_chain_charge_positive source
    rw [source.atomSource,nodes] at generated
    change 0 < ((chainNuclei (commonAtoms before.packet.source firstFuel)
      (baseNodes before step 0 firstHeight)).map (fun node => (node.particle.charge : ℝ))).sum at generated
    rw [base_chain_nuclei_exact before step actual 0 firstHeight] at generated
    exact generated
  have boundPositive : 0 < firstHeight := lt_trans (by norm_num) (old_height_positive step.next.nodes)
  let height := Nat.find (finite_high_coordinate (postChain before.packet.source step.next.nodes) x firstHeight charge boundPositive)
  have generated := Nat.find_spec (finite_high_coordinate (postChain before.packet.source step.next.nodes) x firstHeight charge boundPositive)
  have heightBound : firstHeight < dyadicHeight height := generated.1
  have workPositive : 0 < verticalExchangeWork (postChain before.packet.source step.next.nodes) x ((1/2 : ℝ)^height) := generated.2
  have margin : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3)+4 < dyadicHeight height := by
    intro node held
    exact lt_trans (old_below_height step.next.nodes node held) heightBound
  have above : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3) < dyadicHeight height := by
    intro node held
    have bounded := margin node held
    linarith
  refine ⟨coordinate,height,?_,margin,?_,?_,?_⟩
  · have lower := old_height_positive step.next.nodes
    dsimp only [firstHeight] at heightBound
    linarith
  · have count : electronCount (baseNodes before step 0 firstHeight) =
        electronCount (baseNodes before step x (dyadicHeight height)) := by
      rw [base_electron_count before step actual 0 firstHeight,
        base_electron_count before step actual x (dyadicHeight height)]
    rwa [initial_bond_count _ _ count] at axisInitial
  · intro occupied
    change 0 < directionalChainWork (commonAtoms before.packet.source firstFuel)
      (baseNodes before step x (1/((1/2 : ℝ)^height))) 1 occupied (firstChannel before.packet.source)
    rw [first_base_chain_work before step actual x ((1/2 : ℝ)^height) 1
      (base_ready before step x (dyadicHeight height) above) occupied]
    exact workPositive
  · exact base_admitted before step actual x (dyadicHeight height) oldUnit above

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
