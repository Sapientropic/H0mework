import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Roles

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction Filter
open scoped Topology BigOperators InnerProductSpace
variable {frame : CPS1Recycling.Frame}

def postChain {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (nodes : List Body.Node) : List Body.Node :=
  chainNuclei (source.atoms.map (fun atom => ⟨.prior atom,atom.descriptor⟩)) nodes

private theorem inner_vertical (point : Body.Point) (scale : ℝ) :
    inner ℝ point (transversePoint 0 scale 0) = scale*point (1 : Fin 3) := by
  simp [PiLp.inner_apply,transversePoint,Fin.sum_univ_three]

private theorem force_vertical (node : Body.Node) (nodes : List Body.Node) (charge x offset parameter : ℝ)
    (actualCharge : (node.particle.charge : ℝ) = charge)
    (actualPosition : node.row.position = transversePoint x (1/parameter+offset) 0)
    (different : ∀ old ∈ nodes, old.particle.address ≠ node.particle.address) :
    Body.force node nodes (1 : Fin 3) = verticalChainForce charge nodes x offset parameter := by
  induction nodes with
  | nil => simp [Body.force,verticalChainForce]
  | cons old rest ih =>
    have selected := different old List.mem_cons_self
    have next := ih (fun other held => different other (List.mem_cons_of_mem _ held))
    simp only [Body.force,verticalChainForce,List.map_cons,List.sum_cons,PiLp.add_apply,
      if_neg selected,actualCharge,actualPosition] at *
    rw [next]

theorem first_base_chain_work {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x parameter mass : ℝ)
    (ready : Body.ready (baseNodes before step x (1/parameter)))
    (occupied : Coefficients (baseNodes before step x (1/parameter))) :
    directionalChainWork (commonAtoms before.packet.source firstFuel)
      (baseNodes before step x (1/parameter)) mass occupied (firstChannel before.packet.source) =
      verticalExchangeWork (postChain before.packet.source step.next.nodes) x parameter := by
  let source := before.packet.source
  let height : ℝ := 1/parameter
  let nodes := baseNodes before step x height
  let chain := postChain source step.next.nodes
  have selected := first_channel_selected source
  have unique := base_addresses_unique before step actual x height
  have fresh := first_fresh_nuclei_present source x height
  have pHeld : phosphorusNode source x height ∈ nucleusNodes nodes :=
    List.mem_filter.mpr ⟨List.mem_append_right _ fresh.1,rfl⟩
  have leaveHeld : leavingNode source x height ∈ nucleusNodes nodes :=
    List.mem_filter.mpr ⟨List.mem_append_right _ fresh.2.1,rfl⟩
  have attackHeld : attackingNode source x height ∈ nucleusNodes nodes :=
    List.mem_filter.mpr ⟨List.mem_append_right _ fresh.2.2,rfl⟩
  have found := first_base_nuclei_found before step actual x height
  have outside (node : Body.Node) (held : node ∈ chain) (offset : Nat) :
      node.particle.address ≠ .nucleus (source.atoms.length+offset) := by
    have oldHeld := (List.mem_filter.mp (List.mem_filter.mp held).1).1
    have bound := post_atom_slot_lt before step actual node oldHeld
    change node.particle.address.slot < source.atoms.length at bound
    intro same
    rw [same,Charged.Address.slot] at bound
    omega
  have pForce := force_vertical (phosphorusNode source x height) chain 15 x 0 parameter
    (by norm_num [phosphorusNode]) (by simp [phosphorusNode,height])
    (fun node held => outside node held 28)
  have leaveForce := force_vertical (leavingNode source x height) chain 8 x 1 parameter
    (by norm_num [leavingNode]) rfl (fun node held => outside node held 25)
  have attackForce := force_vertical (attackingNode source x height) chain 8 x 2 parameter
    (by norm_num [attackingNode]) rfl (fun node held => outside node held 88)
  rw [directional_chain_work_nuclear _ firstFuel _ mass occupied _ selected unique ready,
    base_chain_nuclei_exact before step actual x height]
  change ((nucleusNodes nodes).map (fun node => inner ℝ (Body.force node chain)
    (coordinateDirection nodes (firstChannel source) node))).sum = verticalExchangeWork chain x parameter
  rw [coordinate_work_three nodes chain (firstChannel source) _ _ _ unique pHeld leaveHeld attackHeld
    found.1 found.2.1 found.2.2 (first_channel_distinct source)]
  have pDirection : 2 • ((attackingNode source x height).row.position-
      (leavingNode source x height).row.position) = transversePoint 0 2 0 := by
    ext axis; fin_cases axis <;> simp [attackingNode,leavingNode,transversePoint]
    all_goals ring
  have leaveDirection : (-2 : ℝ) • ((phosphorusNode source x height).row.position-
      (leavingNode source x height).row.position) = transversePoint 0 2 0 := by
    ext axis; fin_cases axis <;> simp [phosphorusNode,leavingNode,transversePoint]
  have attackDirection : 2 • ((phosphorusNode source x height).row.position-
      (attackingNode source x height).row.position) = transversePoint 0 (-4) 0 := by
    ext axis; fin_cases axis <;> simp [phosphorusNode,attackingNode,transversePoint]
    all_goals ring
  rw [pDirection,leaveDirection,attackDirection,inner_vertical,inner_vertical,inner_vertical,pForce,leaveForce,attackForce]
  unfold verticalExchangeWork
  ring

theorem finite_high_coordinate (nodes : List Body.Node) (x bound : ℝ)
    (charge : 0 < (nodes.map (fun node => (node.particle.charge : ℝ))).sum) (above : 0 < bound) :
    ∃ index : Nat, bound < 1/((1/2 : ℝ)^index) ∧
      0 < verticalExchangeWork nodes x ((1/2 : ℝ)^index) := by
  have powers : Tendsto (fun index : Nat => (1/2 : ℝ)^index) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have small : ∀ᶠ parameter in 𝓝 (0 : ℝ), parameter < 1/bound :=
    continuousAt_id.eventually_lt continuousAt_const (by positivity)
  obtain ⟨index,short,strict⟩ := (powers.eventually (small.and (source_coordinate_work_positive nodes x charge))).exists
  have positive : 0 < (1/2 : ℝ)^index := pow_pos (by norm_num) index
  have height : bound < 1/((1/2 : ℝ)^index) := by
    apply (lt_div_iff₀ positive).mpr
    have product := (lt_div_iff₀ above).mp short
    nlinarith
  have generated := (div_eq_iff (pow_ne_zero 2 (ne_of_gt positive))).mp
    (vertical_exchange_work_normalized nodes x ((1/2 : ℝ)^index) positive)
  refine ⟨index,height,?_⟩
  rw [generated]
  exact mul_pos strict (pow_pos positive 2)

theorem generated_base_nonempty {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (oldUnit : ∀ node ∈ step.next.nodes, node.row.inertia = 1) :
    ∃ x height : ℝ, ∃ source : Common before step (baseRaw before.packet.source x height),
      admit before step (baseRaw before.packet.source x height) = .ok source ∧
      source.nodes = baseNodes before step x height ∧ source.electronInertia = 1 ∧
      1 < height ∧ (∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3)+4 < height) ∧
      0 < bondWeight source.nodes (initialOccupation source.nodes)
        (transversePoint x 0 0) (transversePoint x 0 0) ∧
      (∀ occupied : Coefficients (baseNodes before step x height),
        0 < directionalChainWork (commonAtoms before.packet.source firstFuel)
          (baseNodes before step x height) 1 occupied (firstChannel before.packet.source)) := by
  let firstHeight := oldHeight step.next.nodes
  have firstAbove : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3) < firstHeight := by
    intro node held
    have original := old_below_height step.next.nodes node held
    dsimp only [firstHeight]
    linarith
  obtain ⟨initial,initialAdmitted,initialNodes,initialMass⟩ := base_admitted before step actual 0 firstHeight oldUnit firstAbove
  obtain ⟨x,axisPositive⟩ := initial_axis_bond_nonempty initial.nodes (common_positive_electrons initial).1
  have charge : 0 < ((postChain before.packet.source step.next.nodes).map
      (fun node => (node.particle.charge : ℝ))).sum := by
    have generated := common_chain_charge_positive initial
    rw [initial.atomSource,initialNodes] at generated
    change 0 < ((chainNuclei (commonAtoms before.packet.source firstFuel)
      (baseNodes before step 0 firstHeight)).map (fun node => (node.particle.charge : ℝ))).sum at generated
    rw [base_chain_nuclei_exact before step actual 0 firstHeight] at generated
    exact generated
  have boundPositive : 0 < firstHeight := lt_trans (by norm_num) (old_height_positive step.next.nodes)
  obtain ⟨index,heightBound,workPositive⟩ := finite_high_coordinate
    (postChain before.packet.source step.next.nodes) x firstHeight charge boundPositive
  let parameter : ℝ := (1/2 : ℝ)^index
  let height : ℝ := 1/parameter
  have margin : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3)+4 < height := by
    intro node held
    exact lt_trans (old_below_height step.next.nodes node held) heightBound
  have above : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3) < height := by
    intro node held
    have high := margin node held
    linarith
  obtain ⟨source,admitted,nodes,mass⟩ := base_admitted before step actual x height oldUnit above
  have count : electronCount initial.nodes = electronCount source.nodes := by
    rw [initialNodes,nodes,base_electron_count before step actual 0 firstHeight,
      base_electron_count before step actual x height]
  have axis : 0 < bondWeight source.nodes (initialOccupation source.nodes)
      (transversePoint x 0 0) (transversePoint x 0 0) := by
    rwa [initial_bond_count initial.nodes source.nodes count] at axisPositive
  refine ⟨x,height,source,admitted,nodes,mass,?_,margin,axis,?_⟩
  · have original := old_height_positive step.next.nodes
    linarith
  · intro occupied
    rw [first_base_chain_work before step actual x parameter 1
      (base_ready before step x height above) occupied]
    exact workPositive

end
end CPS1PhosphorylExchange
