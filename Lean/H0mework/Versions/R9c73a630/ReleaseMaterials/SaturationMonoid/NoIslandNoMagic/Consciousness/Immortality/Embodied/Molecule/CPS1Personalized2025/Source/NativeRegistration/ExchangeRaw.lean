import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.ExchangeBase

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1PhosphorylExchange CPS1SameEventFunction Filter
open scoped Topology BigOperators InnerProductSpace Matrix

noncomputable def normalReserve (source : List Body.Node) (mass amplitude : ℝ) (channel : Channel) (time : ℝ) : ℝ :=
  let nodes := normalEntry source channel amplitude time
  let initial := initialOccupation nodes
  let half := normalHalf nodes mass time
  let after := rowPose source (normalEndRows source mass amplitude (coordinateDirection source channel) time)
  let occupied := occupiedNextAt nodes after mass time half
  |wholeEnergy nodes mass initial-Body.energy nodes| +
    |wholeEnergyAt nodes after mass occupied-wholeEnergyAt nodes nodes mass initial|+1

noncomputable def normalRawAt {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) (channel : Channel) (index : Nat) : CPS1PhosphorylExchange.Raw :=
  let amplitude := normalAmplitude source.atoms source.nodes source.electronInertia channel
  let time : ℝ := (1/2)^index
  momentumRaw raw (normalChange source.nodes channel amplitude time)
    (normalReserve source.nodes source.electronInertia amplitude channel time) time

private theorem normal_source_index {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) (channel : Channel) (p leaving attacking : Body.Node) (x height : ℝ)
    (selected : channel? source.atoms raw.fuel = some channel)
    (inertia : ∀ node ∈ source.nodes, node.row.inertia = 1)
    (pHeld : p ∈ nucleusNodes source.nodes) (leaveHeld : leaving ∈ nucleusNodes source.nodes) (attackHeld : attacking ∈ nucleusNodes source.nodes)
    (pFound : nodeAt? source.nodes channel.phosphorus = some p) (leaveFound : nodeAt? source.nodes channel.leavingOxygen = some leaving)
    (attackFound : nodeAt? source.nodes channel.attackingOxygen = some attacking)
    (different : channel.phosphorus ≠ channel.leavingOxygen ∧ channel.phosphorus ≠ channel.attackingOxygen ∧
      channel.leavingOxygen ≠ channel.attackingOxygen)
    (pPosition : p.row.position = transversePoint x height 0)
    (leavePosition : leaving.row.position = transversePoint x (height+1) 0)
    (attackPosition : attacking.row.position = transversePoint x (height+2) 0)
    (positive : 0 < bondWeight source.nodes (initialOccupation source.nodes) (transversePoint x 0 0) (transversePoint x 0 0))
    (above : 1 < height)
    (workPositive : 0 < directionalChainWork source.atoms source.nodes source.electronInertia (initialOccupation source.nodes) channel)
    (oldZero : ∀ node ∈ step.next.nodes, coordinateDirection source.nodes channel node = 0)
    (limitReady : ∀ amplitude, 0 < amplitude → amplitude ≤ 1/16 →
      Body.ready (rowPose source.nodes (normalEndRows source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) 0))) :
    let amplitude := normalAmplitude source.atoms source.nodes source.electronInertia channel
    ∃ index : Nat,
      ∃ next : NativeCurrent (momentumCommon source (normalChange source.nodes channel amplitude ((1/2 : ℝ)^index)) (normalReserve source.nodes source.electronInertia amplitude channel ((1/2 : ℝ)^index)) ((1/2 : ℝ)^index)
        (by intro node held; simp only [normalChange,address_coordinate,oldZero node held,smul_zero])),
      firstElectronicExchange (momentumCommon source (normalChange source.nodes channel amplitude ((1/2 : ℝ)^index)) (normalReserve source.nodes source.electronInertia amplitude channel ((1/2 : ℝ)^index)) ((1/2 : ℝ)^index)
        (by intro node held; simp only [normalChange,address_coordinate,oldZero node held,smul_zero])) = .ok next := by
  let amplitude := normalAmplitude source.atoms source.nodes source.electronInertia channel
  let work := directionalChainWork source.atoms source.nodes source.electronInertia (initialOccupation source.nodes) channel
  have denominator : 0 < 16*(1+work) := by dsimp only [work]; positivity
  have forward : 0 < amplitude := div_pos workPositive denominator
  have small : amplitude ≤ 1/16 := by
    apply (div_le_iff₀ denominator).mpr
    linarith
  have unique := (common_measured_whole source).2.1
  have exchanges := normal_mode_exchange_eventually source.nodes source.electronInertia amplitude x height channel p leaving attacking
    unique source.ready pHeld leaveHeld attackHeld pFound leaveFound attackFound different pPosition leavePosition attackPosition positive above forward small
  have ready := normal_end_ready_eventually source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel)
    unique source.ready (limitReady amplitude forward small)
  have powers : Tendsto (fun index : Nat => (1/2 : ℝ)^index) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,exchanged,nextReady⟩ := (powers.eventually (exchanges.and ready)).exists
  let time : ℝ := (1/2 : ℝ)^index
  have elapsed : 0 < time := pow_pos (by norm_num) index
  let change := normalChange source.nodes channel amplitude time
  have priorZero : ∀ node ∈ step.next.nodes, change node.particle.address = 0 := by
    intro node held
    simp only [change,normalChange,address_coordinate,oldZero node held,smul_zero]
  let nodes := normalEntry source.nodes channel amplitude time
  let initial := initialOccupation nodes
  let half := normalHalf nodes source.electronInertia time
  let after := rowPose source.nodes (normalEndRows source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) time)
  let occupied := occupiedNextAt nodes after source.electronInertia time half
  let capturePrice := wholeEnergy nodes source.electronInertia initial-Body.energy nodes
  let pulsePrice := wholeEnergyAt nodes after source.electronInertia occupied-wholeEnergyAt nodes nodes source.electronInertia initial
  let reserve := |capturePrice|+|pulsePrice|+1
  let target := momentumCommon source change reserve time priorZero
  have captureNonnegative : ¬ step.next.reserve+reserve < 0 := by
    dsimp only [reserve]
    linarith [step.positiveReserve,abs_nonneg capturePrice,abs_nonneg pulsePrice]
  have captureEnough : ¬ step.next.reserve+reserve < capturePrice := by
    dsimp only [reserve]
    linarith [step.positiveReserve,le_abs_self capturePrice,abs_nonneg pulsePrice]
  have captured : capture nodes source.electronInertia (step.next.reserve+reserve) =
      .ok (⟨initial,step.next.reserve+reserve-capturePrice⟩ : ElectronicState nodes) := by
    simp only [capture]
    change (if _ : step.next.reserve+reserve < 0 then _ else if _ : step.next.reserve+reserve < capturePrice then _ else _) = _
    rw [dif_neg captureNonnegative,dif_neg captureEnough]
  have affordable : pulsePrice ≤ step.next.reserve+reserve-capturePrice := by
    dsimp only [reserve]
    linarith [step.positiveReserve,le_abs_self capturePrice,le_abs_self pulsePrice]
  have acted : directionalChainWork target.atoms target.nodes target.electronInertia half channel ≠ 0 := by
    have identity := directional_chain_work_momentum source.atoms raw.fuel source.nodes change source.electronInertia half
      (initialOccupation source.nodes) channel selected unique source.ready
    exact ne_of_gt (identity ▸ workPositive)
  have actualNodes : nodes.map (sourceKick nodes nodes source.electronInertia half time) = after :=
    normal_entry_nodes source.nodes channel source.electronInertia amplitude time unique source.ready elapsed inertia
  let first := (bondWeight source.nodes (initialOccupation source.nodes) p.row.position leaving.row.position,
    bondWeight source.nodes (initialOccupation source.nodes) p.row.position attacking.row.position)
  let final := (bondWeight source.nodes (normalOccupied source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) time)
      (normalEndRows source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) time p).position
      (normalEndRows source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) time leaving).position,
    bondWeight source.nodes (normalOccupied source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) time)
      (normalEndRows source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) time p).position
      (normalEndRows source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) time attacking).position)
  have firstActual : electronicBond nodes nodes initial channel = some first := by
    dsimp only [initial]
    rw [← initial_occupation_count source.nodes nodes (momentum_pose_count source.nodes change),electronic_bond_source_count,
      electronic_bond_momentum_pose]
    simp only [electronicBond,pFound,leaveFound,attackFound,Bind.bind,Option.bind_some,Pure.pure]
    rfl
  have finalActual : electronicBond nodes after occupied channel = some final := by
    dsimp only [occupied,after,half,nodes]
    rw [normal_entry_occupied,electronic_bond_source_count]
    exact electronic_bond_row_pose source.nodes source.nodes _ _ channel p leaving attacking pFound leaveFound attackFound
  obtain ⟨slot,slotActual,paid⟩ := paid_chain_slot_exists before.packet.source
  have distinct := paid_chain_slot_distinct before.packet.source slot paid
  have targetSelected : channel? target.atoms (momentumRaw raw change reserve time).fuel = some channel := selected
  have responseExchanged : (⟨first.1,final.1,first.2,final.2,time⟩ : BondResponse).exchanging := exchanged
  have readyActual : Body.ready (nodes.map (sourceKick nodes nodes source.electronInertia half time)) := by
    rw [actualNodes]
    exact nextReady
  have budgetActual :
      wholeEnergyAt nodes (nodes.map (sourceKick nodes nodes source.electronInertia half time)) source.electronInertia
        (occupiedNextAt nodes (nodes.map (sourceKick nodes nodes source.electronInertia half time)) source.electronInertia time half)-
      wholeEnergyAt nodes nodes source.electronInertia initial ≤ step.next.reserve+reserve-capturePrice := by
    rw [actualNodes]
    exact affordable
  have bondActual :
      electronicBond nodes (nodes.map (sourceKick nodes nodes source.electronInertia half time))
        (occupiedNextAt nodes (nodes.map (sourceKick nodes nodes source.electronInertia half time)) source.electronInertia time half) channel = some final := by
    rw [actualNodes]
    exact finalActual
  refine ⟨index,?_⟩
  change ∃ next : NativeCurrent target, firstElectronicExchange target = .ok next
  unfold firstElectronicExchange
  split
  · rename_i found
    have impossible := found.symm.trans targetSelected
    cases impossible
  · rename_i actualChannel found
    have same := Option.some.inj (found.symm.trans targetSelected)
    subst actualChannel
    split
    · rename_i found
      have impossible := found.symm.trans slotActual
      cases impossible
    · rename_i actualSlot found
      have same := Option.some.inj (found.symm.trans slotActual)
      subst actualSlot
      simp only [dif_pos paid,dif_pos distinct]
      split
      · rename_i failure found
        have impossible := found.symm.trans captured
        cases impossible
      · rename_i electrons found
        have same := Except.ok.inj (found.symm.trans captured)
        subst electrons
        split
        ·
          split
          ·
            split
            ·
              split
              ·
                split
                · rename_i found
                  have impossible := found.symm.trans firstActual
                  cases impossible
                · rename_i actualFirst found
                  have same := Option.some.inj (found.symm.trans firstActual)
                  subst actualFirst
                  split
                  · rename_i found
                    have impossible := found.symm.trans bondActual
                    cases impossible
                  · rename_i actualFinal found
                    have same := Option.some.inj (found.symm.trans bondActual)
                    subst actualFinal
                    simp only [dif_pos responseExchanged]
                    exact ⟨_,rfl⟩
              · rename_i denied
                exact False.elim (denied budgetActual)
            · rename_i denied
              exact False.elim (denied readyActual)
          · rename_i denied
            exact False.elim (denied acted)
        · rename_i denied
          exact False.elim (denied elapsed)

private theorem base_normal_index {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (oldUnit : ∀ node ∈ step.next.nodes, node.row.inertia = 1)
    (parameters : SourceBaseParameters before step)
    (source : Common before step (indexedBaseRaw before parameters.coordinate parameters.height))
    (admitted : admit before step (indexedBaseRaw before parameters.coordinate parameters.height) = .ok source) :
    ∃ index : Nat, ∃ nextSource : Common before step (normalRawAt source (firstChannel before.packet.source) index),
      admit before step (normalRawAt source (firstChannel before.packet.source) index) = .ok nextSource ∧
      ∃ next : NativeCurrent nextSource, firstElectronicExchange nextSource = .ok next := by
  let x := rationalCoordinate parameters.coordinate
  let height := dyadicHeight parameters.height
  have sourceFacts : source.nodes = baseNodes before step x height ∧ source.electronInertia = 1 := by
    obtain ⟨expected,expectedActual,nodes,mass⟩ := parameters.admitted
    have same : source = expected := Except.ok.inj (admitted.symm.trans expectedActual)
    exact ⟨(congrArg (fun value : Common before step (indexedBaseRaw before parameters.coordinate parameters.height) => value.nodes) same).trans nodes,
      (congrArg (fun value : Common before step (indexedBaseRaw before parameters.coordinate parameters.height) => value.electronInertia) same).trans mass⟩
  have nodes := sourceFacts.1
  have mass := sourceFacts.2
  have above : 1 < height := parameters.high
  have margin : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3)+4 < height := parameters.margin
  have axis : 0 < bondWeight source.nodes (initialOccupation source.nodes)
      (transversePoint x 0 0) (transversePoint x 0 0) := by
    rw [nodes]
    exact parameters.axis
  have work : ∀ occupied : Coefficients (baseNodes before step x height),
      0 < directionalChainWork (commonAtoms before.packet.source firstFuel)
        (baseNodes before step x height) 1 occupied (firstChannel before.packet.source) := parameters.work
  let channel := firstChannel before.packet.source
  let p := phosphorusNode before.packet.source x height
  let leaving := leavingNode before.packet.source x height
  let attacking := attackingNode before.packet.source x height
  have selected : channel? source.atoms (baseRaw before.packet.source x height).fuel = some channel := by
    rw [source.atomSource]
    exact first_channel_selected before.packet.source
  have held := first_fresh_nuclei_present before.packet.source x height
  have pHeld : p ∈ nucleusNodes source.nodes := by
    rw [nodes]
    exact List.mem_filter.mpr ⟨List.mem_append_right _ held.1,rfl⟩
  have leaveHeld : leaving ∈ nucleusNodes source.nodes := by
    rw [nodes]
    exact List.mem_filter.mpr ⟨List.mem_append_right _ held.2.1,rfl⟩
  have attackHeld : attacking ∈ nucleusNodes source.nodes := by
    rw [nodes]
    exact List.mem_filter.mpr ⟨List.mem_append_right _ held.2.2,rfl⟩
  have found := first_base_nuclei_found before step actual x height
  have sourceUnit : ∀ node ∈ source.nodes, node.row.inertia = 1 := by
    intro node member
    rw [nodes] at member
    rcases List.mem_append.mp member with old | fresh
    · exact oldUnit node old
    · exact fresh_unit_inertia _ _ _ node fresh
  have sourceWork : 0 < directionalChainWork source.atoms source.nodes source.electronInertia
      (initialOccupation source.nodes) channel := by
    rw [source.atomSource,mass,nodes]
    exact work _
  have oldZero : ∀ node ∈ step.next.nodes, coordinateDirection source.nodes channel node = 0 := by
    intro node member
    rw [nodes,base_coordinate_direction before step actual x height]
    exact post_first_direction_zero before step actual node member
  have limitReady (amplitude : ℝ) (forward : 0 < amplitude) (small : amplitude ≤ 1/16) :
      Body.ready (rowPose source.nodes (normalEndRows source.nodes source.electronInertia amplitude
        (coordinateDirection source.nodes channel) 0)) := by
    have positions (node : Body.Node) (member : node ∈ source.nodes) :
        (normalEndRows source.nodes source.electronInertia amplitude (coordinateDirection source.nodes channel) 0 node).position =
          firstShiftedPosition before.packet.source amplitude node := by
      cases address : node.particle.address with
      | nucleus slot =>
        rw [normal_end_position_zero _ _ _ _ node (List.mem_filter.mpr ⟨member,by rw [address]⟩),nodes,
          base_coordinate_direction before step actual x height]
        rfl
      | electron slot orbital =>
        simp only [normalEndRows,address]
        simp only [firstShiftedPosition,firstDirection,firstChannel,address]
        simp
    have initialReady := base_first_shift_ready before step actual x height amplitude
      (fun node member => by have high := margin node member; linarith) forward.le small
    simp only [Body.ready,rowPose,List.pairwise_map]
    have sourceReady : source.nodes.Pairwise (fun first second => firstShiftedPosition before.packet.source amplitude first ≠
        firstShiftedPosition before.packet.source amplitude second) := by
      simpa only [nodes,Body.ready,List.pairwise_map,firstShiftedNode] using initialReady
    exact sourceReady.imp_of_mem (fun {first second} firstHeld secondHeld separate => by
      rwa [positions first firstHeld,positions second secondHeld])
  obtain ⟨index,next,actualExchange⟩ := normal_source_index source channel p leaving attacking x height selected sourceUnit
    pHeld leaveHeld attackHeld (by rw [nodes]; exact found.1) (by rw [nodes]; exact found.2.1)
    (by rw [nodes]; exact found.2.2) (first_channel_distinct _) rfl rfl rfl axis above sourceWork oldZero limitReady
  let amplitude := normalAmplitude source.atoms source.nodes source.electronInertia channel
  let time : ℝ := (1/2 : ℝ)^index
  let reserve := normalReserve source.nodes source.electronInertia amplitude channel time
  let change := normalChange source.nodes channel amplitude time
  have priorZero : ∀ node ∈ step.next.nodes, change node.particle.address = 0 := by
    intro node member
    simp only [change,normalChange,address_coordinate,oldZero node member,smul_zero]
  let nextSource := momentumCommon source change reserve time priorZero
  have compatible := base_rows_compatible before step actual x height
  have transformed := compatible_momentum _ _ change
    (by intro entry member; obtain ⟨node,held,same⟩ := List.mem_map.mp member; subst entry; exact priorZero node held) compatible
  exact ⟨index,nextSource,admit_common nextSource transformed,next,actualExchange⟩

noncomputable def source_exchange_raw {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (oldUnit : ∀ node ∈ step.next.nodes, node.row.inertia = 1) : CPS1PhosphorylExchange.Raw := by
  classical
  let parameters := source_base_parameters before step actual oldUnit
  exact match admitted : admit before step (indexedBaseRaw before parameters.coordinate parameters.height) with
    | .error _ => indexedBaseRaw before parameters.coordinate parameters.height
    | .ok source => normalRawAt source (firstChannel before.packet.source)
        (Nat.find (base_normal_index before step actual oldUnit parameters source admitted))

theorem source_exchange_actual {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (oldUnit : ∀ node ∈ step.next.nodes, node.row.inertia = 1) :
    ∃ source : Common before step (source_exchange_raw before step actual oldUnit),
      admit before step (source_exchange_raw before step actual oldUnit) = .ok source ∧
      ∃ next : NativeCurrent source, firstElectronicExchange source = .ok next := by
  classical
  unfold source_exchange_raw
  dsimp only
  split
  · rename_i failure cut
    obtain ⟨expected,found,_⟩ := (source_base_parameters before step actual oldUnit).admitted
    have impossible := found.symm.trans cut
    cases impossible
  · rename_i source admitted
    exact Nat.find_spec (base_normal_index before step actual oldUnit
      (source_base_parameters before step actual oldUnit) source admitted)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
