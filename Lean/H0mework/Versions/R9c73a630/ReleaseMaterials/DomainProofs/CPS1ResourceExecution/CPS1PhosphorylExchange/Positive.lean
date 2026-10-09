import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.SelectedBase

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction CPS1ElectronicSource
open Filter
open scoped BigOperators InnerProductSpace Matrix Topology

def rowPose (nodes : List Body.Node) (rows : Body.Node → Body.Row) : List Body.Node :=
  nodes.map (fun node => ⟨node.particle,rows node⟩)

theorem nuclei_row_pose (nodes : List Body.Node) (rows : Body.Node → Body.Row) :
    nucleusNodes (rowPose nodes rows) = rowPose (nucleusNodes nodes) rows := by
  unfold nucleusNodes rowPose
  rw [List.filter_map]
  rfl

theorem electrons_row_pose (nodes : List Body.Node) (rows : Body.Node → Body.Row) :
    electronCount (rowPose nodes rows) = electronCount nodes := by
  unfold electronCount rowPose
  rw [List.filter_map,List.length_map]
  rfl

private theorem sum_continuous_at {X K I : Type} [TopologicalSpace X]
    [NormedAddCommGroup K] (items : List I) (f : I → X → K) (point : X)
    (paid : ∀ item ∈ items, ContinuousAt (f item) point) :
    ContinuousAt (fun value => (items.map (fun item => f item value)).sum) point := by
  induction items with
  | nil => exact continuousAt_const
  | cons item rest ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      (paid item List.mem_cons_self).add (ih (fun other held => paid other (List.mem_cons_of_mem _ held)))

theorem attraction_row_pose_continuous {X : Type} [TopologicalSpace X] (source pose : List Body.Node)
    (rows : X → Body.Node → Body.Row) (point : X) (i j : Spatial source)
    (positions : ∀ node ∈ nucleusNodes pose, ContinuousAt (fun value axis => (rows value node).position axis) point) :
    ContinuousAt (fun value => attractionAt source (rowPose pose (rows value)) i j) point := by
  simp only [attractionAt]
  simp only [nuclei_row_pose]
  simp only [rowPose,List.map_map,Function.comp_def]
  apply sum_continuous_at
  intro node held
  exact ((nuclear_integral_differentiable (electronCount source+1) i j
    (fun axis => (rows point node).position axis)).continuousAt.comp (positions node held)).const_mul _

theorem fock_row_pose_continuous {X : Type} [TopologicalSpace X] (source pose : List Body.Node) (mass : ℝ)
    (rows : X → Body.Node → Body.Row) (occupied : X → Coefficients source) (point : X)
    (positions : ∀ node ∈ nucleusNodes pose, ContinuousAt (fun value axis => (rows value node).position axis) point)
    (occupation : ContinuousAt occupied point) :
    ContinuousAt (fun value => fockAt source (rowPose pose (rows value)) mass (occupied value)) point := by
  have rho : ContinuousAt (fun value => density (occupied value)) point :=
    CPS1PositivePulse.matrix_mul_continuousAt _ _ point occupation
      (continuous_id.matrix_conjTranspose.continuousAt.comp occupation)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  have coreContinuous : ContinuousAt (fun value => coreAt source (rowPose pose (rows value)) mass i k) point := by
    by_cases same : i.2 = k.2
    · simp only [coreAt,if_pos same]
      exact continuousAt_const.add (attraction_row_pose_continuous source pose rows point i.1 k.1 positions)
    · simp only [coreAt,if_neg same]
      exact continuousAt_const
  unfold fockAt
  apply coreContinuous.add
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro l _
  exact (continuousAt_pi.mp (continuousAt_pi.mp rho l) j).mul_const _

theorem occupied_next_row_pose_continuous {X : Type} [TopologicalSpace X] (source pose : List Body.Node) (mass : ℝ)
    (rows : X → Body.Node → Body.Row) (time : X → ℝ) (occupied : X → Coefficients source) (point : X)
    (positions : ∀ node ∈ nucleusNodes pose, ContinuousAt (fun value axis => (rows value node).position axis) point)
    (elapsed : ContinuousAt time point) (occupation : ContinuousAt occupied point) :
    ContinuousAt (fun value => occupiedNextAt source (rowPose pose (rows value)) mass (time value) (occupied value)) point :=
  CPS1PositivePulse.occupied_update_continuousAt
    (fun value => fockAt source (rowPose pose (rows value)) mass (occupied value))
    (fun value => time value/2) occupied point
    (fock_row_pose_continuous source pose mass rows occupied point positions occupation)
    (elapsed.div_const 2) occupation
    (fock_at_hermitian source (rowPose pose (rows point)) mass (occupied point))

theorem core_axis_differentiable (source pose : List Body.Node) (mass : ℝ)
    (address : Charged.Address) (axis : Fin 3) (i j : Spin source) :
    DifferentiableAt ℝ (fun amount => coreAt source (displaced pose address axis amount) mass i j) 0 := by
  by_cases same : i.2 = j.2
  · simp only [coreAt,if_pos same]
    apply DifferentiableAt.add (differentiableAt_const _)
    simp only [attractionAt,nucleus_nodes_displaced,List.map_map,Function.comp_def]
    have paid (nodes : List Body.Node) : DifferentiableAt ℝ
        (fun amount => (nodes.map (fun node => -(node.particle.charge : ℂ)*
          nuclearIntegral 0 (electronCount source+1) i.1 j.1
            (fun index => (Field.perturb (axisDirection address axis) amount node).row.position index))).sum) 0 := by
      induction nodes with
      | nil => exact differentiableAt_const _
      | cons node rest ih =>
        have kernel := CPS1QuantumNuclear.normalized_nuclear_line 0 (electronCount source+1) i.1 j.1
          (fun index => node.row.position index)
          (fun index => axisDirection address axis node.particle.address index)
        simpa only [List.map_cons,List.sum_cons,Field.perturb,PiLp.add_apply,PiLp.smul_apply,
          Pi.add_apply,Pi.smul_apply] using! kernel.differentiableAt.const_mul _ |>.add ih
    exact paid (nucleusNodes pose)
  · simp only [coreAt,if_neg same]
    exact differentiableAt_const _

def coreAxis (source pose : List Body.Node) (mass : ℝ) (address : Charged.Address) (axis : Fin 3) :
    Matrix (Spin source) (Spin source) ℂ :=
  fun i j => deriv (fun amount => coreAt source (displaced pose address axis amount) mass i j) 0

theorem electronic_axis_derivative (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source)
    (address : Charged.Address) (axis : Fin 3) :
    deriv (fun amount => electronicPoseEnergy source (displaced pose address axis amount) mass occupied) 0 =
      (Matrix.trace (coreAxis source pose mass address axis*density occupied)).re := by
  have derivative : HasDerivAt
      (fun amount => Matrix.trace (coreAt source (displaced pose address axis amount) mass*density occupied))
      (Matrix.trace (coreAxis source pose mass address axis*density occupied)) 0 := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact (core_axis_differentiable source pose mass address axis i j).hasDerivAt.mul_const _
  have realDerivative := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 derivative
  have actual := realDerivative.add_const
    ((1/2)*(∑ i, ∑ j, ∑ k, ∑ l, density occupied k i*density occupied l j*
      (twoBody source i j k l-twoBody source i j l k)).re)
  exact actual.deriv

theorem energy_force_occupation_continuous {X : Type} [TopologicalSpace X] (source pose : List Body.Node)
    (mass : ℝ) (occupied : X → Coefficients source) (point : X)
    (unique : ((nucleusNodes pose).map (fun node => node.particle.address)).Nodup)
    (ready : Body.ready (nucleusNodes pose)) (node : Body.Node) (held : node ∈ nucleusNodes pose)
    (occupation : ContinuousAt occupied point) :
    ContinuousAt (fun value => energyForce source pose mass (occupied value) node) point := by
  have rho : ContinuousAt (fun value => density (occupied value)) point :=
    CPS1PositivePulse.matrix_mul_continuousAt _ _ point occupation
      (continuous_id.matrix_conjTranspose.continuousAt.comp occupation)
  change ContinuousAt (fun value => WithLp.toLp 2 (fun axis => energyForce source pose mass (occupied value) node axis)) point
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.comp
  apply continuousAt_pi.mpr
  intro axis
  have electronic : ContinuousAt (fun value =>
      (Matrix.trace (coreAxis source pose mass node.particle.address axis*density (occupied value))).re) point := by
    apply Complex.continuous_re.continuousAt.comp
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (continuousAt_pi.mp (continuousAt_pi.mp rho j) i).const_mul _
  have equality (value : X) : energyForce source pose mass (occupied value) node axis =
      Body.force node (nucleusNodes pose) axis-
        (Matrix.trace (coreAxis source pose mass node.particle.address axis*density (occupied value))).re := by
    rw [energy_force_partition source pose mass (occupied value) unique ready node held axis,electronic_axis_derivative]
  simpa only [equality] using! continuousAt_const.sub electronic

theorem normal_mode_bond_limits (nodes : List Body.Node) (x height amplitude : ℝ)
    (positive : 0 < bondWeight nodes (initialOccupation nodes) (transversePoint x 0 0) (transversePoint x 0 0))
    (above : 1 < height) (forward : 0 < amplitude) (small : amplitude ≤ 1/16) :
    bondWeight nodes (initialOccupation nodes) (transversePoint x (height+2*amplitude) 0)
        (transversePoint x (height+1+2*amplitude) 0) <
      bondWeight nodes (initialOccupation nodes) (transversePoint x height 0) (transversePoint x (height+1) 0) ∧
    bondWeight nodes (initialOccupation nodes) (transversePoint x height 0) (transversePoint x (height+2) 0) <
      bondWeight nodes (initialOccupation nodes) (transversePoint x (height+2*amplitude) 0)
        (transversePoint x (height+2-4*amplitude) 0) := by
  have leaveExponent : -((height+2*amplitude)^2)-((height+1+2*amplitude)^2) < -(height^2)-((height+1)^2) := by
    nlinarith [sq_nonneg amplitude]
  have attackExponent : -(height^2)-((height+2)^2) <
      -((height+2*amplitude)^2)-((height+2-4*amplitude)^2) := by
    have product : 0 < amplitude*(height+4-5*amplitude) := by
      apply mul_pos forward
      linarith
    nlinarith
  constructor
  · rw [bond_weight_transverse nodes (initialOccupation nodes) x (height+2*amplitude) 0 x (height+1+2*amplitude) 0,
      bond_weight_transverse nodes (initialOccupation nodes) x height 0 x (height+1) 0]
    norm_num
    rw [← Real.exp_add,← Real.exp_add]
    apply mul_lt_mul_of_pos_right _ positive
    apply (sq_lt_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr
    exact Real.exp_lt_exp.mpr (by simpa only [sub_eq_add_neg] using leaveExponent)
  · rw [bond_weight_transverse nodes (initialOccupation nodes) x height 0 x (height+2) 0,
      bond_weight_transverse nodes (initialOccupation nodes) x (height+2*amplitude) 0 x (height+2-4*amplitude) 0]
    norm_num
    rw [← Real.exp_add,← Real.exp_add]
    apply mul_lt_mul_of_pos_right _ positive
    apply (sq_lt_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr
    exact Real.exp_lt_exp.mpr (by simpa only [sub_eq_add_neg] using attackExponent)

def normalHalf (nodes : List Body.Node) (mass time : ℝ) : Coefficients nodes :=
  occupiedNextAt nodes nodes mass time (initialOccupation nodes)

-- The zero-parameter extension only exposes the limit of positive measured
-- pulses. Actual returned pulses retain both occupied updates and their force.
def normalEndRows (nodes : List Body.Node) (mass amplitude : ℝ) (direction : Body.Node → Body.Point)
    (time : ℝ) (node : Body.Node) : Body.Row :=
  match node.particle.address with
  | .electron .. => node.row
  | .nucleus _ =>
    let force := energyForce nodes nodes mass (normalHalf nodes mass time) node
    {node.row with
      position := node.row.position+amplitude • direction node+(time/node.row.inertia) • node.row.momentum+
        (time^2/(2*node.row.inertia)) • force
      momentum := node.row.momentum+(node.row.inertia*amplitude/time) • direction node+time • force}

def normalOccupied (nodes : List Body.Node) (mass amplitude : ℝ) (direction : Body.Node → Body.Point)
    (time : ℝ) : Coefficients nodes :=
  occupiedNextAt nodes (rowPose nodes (normalEndRows nodes mass amplitude direction time)) mass time
    (normalHalf nodes mass time)

theorem normal_half_continuous (nodes : List Body.Node) (mass : ℝ) :
    ContinuousAt (normalHalf nodes mass) 0 :=
  occupied_next_continuous nodes nodes mass id (fun _ => initialOccupation nodes) 0
    continuousAt_id continuousAt_const

theorem normal_half_zero (nodes : List Body.Node) (mass : ℝ) :
    normalHalf nodes mass 0 = initialOccupation nodes := occupied_next_zero nodes nodes mass _

theorem normal_end_position_continuous (nodes : List Body.Node) (mass amplitude : ℝ)
    (direction : Body.Node → Body.Point)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup) (ready : Body.ready nodes)
    (node : Body.Node) (held : node ∈ nodes) :
    ContinuousAt (fun time => (normalEndRows nodes mass amplitude direction time node).position) 0 := by
  have nuclearUnique : ((nucleusNodes nodes).map (fun node => node.particle.address)).Nodup :=
    List.pairwise_map.mpr ((List.pairwise_map.mp unique).filter _)
  cases address : node.particle.address with
  | electron slot orbital => simp only [normalEndRows,address]; exact continuousAt_const
  | nucleus slot =>
    have nuclearHeld : node ∈ nucleusNodes nodes := List.mem_filter.mpr ⟨held,by rw [address]⟩
    have force := energy_force_occupation_continuous nodes nodes mass (normalHalf nodes mass) 0
      nuclearUnique (ready.filter _) node nuclearHeld (normal_half_continuous nodes mass)
    simp only [normalEndRows,address]
    exact (continuousAt_const.add ((continuousAt_id.div_const _).smul continuousAt_const)).add
      (((continuousAt_id.pow 2).div_const _).smul force)

theorem normal_occupied_continuous (nodes : List Body.Node) (mass amplitude : ℝ)
    (direction : Body.Node → Body.Point)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup) (ready : Body.ready nodes) :
    ContinuousAt (normalOccupied nodes mass amplitude direction) 0 := by
  apply occupied_next_row_pose_continuous nodes nodes mass
    (normalEndRows nodes mass amplitude direction) id (normalHalf nodes mass) 0
  · intro node held
    apply continuousAt_pi.mpr
    intro axis
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) axis).continuousAt.comp
      (normal_end_position_continuous nodes mass amplitude direction unique ready node (List.mem_filter.mp held).1)
  · exact continuousAt_id
  · exact normal_half_continuous nodes mass

theorem normal_occupied_zero (nodes : List Body.Node) (mass amplitude : ℝ)
    (direction : Body.Node → Body.Point) :
    normalOccupied nodes mass amplitude direction 0 = initialOccupation nodes := by
  rw [normalOccupied,occupied_next_zero,normal_half_zero]

theorem normal_end_position_zero (nodes : List Body.Node) (mass amplitude : ℝ)
    (direction : Body.Node → Body.Point) (node : Body.Node) (held : node ∈ nucleusNodes nodes) :
    (normalEndRows nodes mass amplitude direction 0 node).position = node.row.position+amplitude • direction node := by
  have nuclear := (List.mem_filter.mp held).2
  cases address : node.particle.address with
  | electron slot orbital => simp only [address,Bool.false_eq_true] at nuclear
  | nucleus slot => simp [normalEndRows,address]

theorem node_at_address (nodes : List Body.Node) (address : Charged.Address) (node : Body.Node)
    (actual : nodeAt? nodes address = some node) : node.particle.address = address := by
  unfold nodeAt? at actual
  simpa only [beq_iff_eq] using List.find?_some actual

theorem node_at_row_pose (nodes : List Body.Node) (rows : Body.Node → Body.Row) (address : Charged.Address) :
    nodeAt? (rowPose nodes rows) address = (nodeAt? nodes address).map (fun node => ⟨node.particle,rows node⟩) := by
  unfold nodeAt? rowPose
  rw [List.find?_map]
  rfl

theorem normal_coordinate_positions (nodes : List Body.Node) (mass amplitude x height : ℝ) (channel : Channel)
    (p leaving attacking : Body.Node)
    (pHeld : p ∈ nucleusNodes nodes) (leaveHeld : leaving ∈ nucleusNodes nodes) (attackHeld : attacking ∈ nucleusNodes nodes)
    (pFound : nodeAt? nodes channel.phosphorus = some p) (leaveFound : nodeAt? nodes channel.leavingOxygen = some leaving)
    (attackFound : nodeAt? nodes channel.attackingOxygen = some attacking)
    (different : channel.phosphorus ≠ channel.leavingOxygen ∧ channel.phosphorus ≠ channel.attackingOxygen ∧
      channel.leavingOxygen ≠ channel.attackingOxygen)
    (pPosition : p.row.position = transversePoint x height 0)
    (leavePosition : leaving.row.position = transversePoint x (height+1) 0)
    (attackPosition : attacking.row.position = transversePoint x (height+2) 0) :
    (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) 0 p).position =
        transversePoint x (height+2*amplitude) 0 ∧
    (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) 0 leaving).position =
        transversePoint x (height+1+2*amplitude) 0 ∧
    (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) 0 attacking).position =
        transversePoint x (height+2-4*amplitude) 0 := by
  have pAddress := node_at_address nodes channel.phosphorus p pFound
  have leaveAddress := node_at_address nodes channel.leavingOxygen leaving leaveFound
  have attackAddress := node_at_address nodes channel.attackingOxygen attacking attackFound
  rw [normal_end_position_zero nodes mass amplitude _ p pHeld,
    normal_end_position_zero nodes mass amplitude _ leaving leaveHeld,
    normal_end_position_zero nodes mass amplitude _ attacking attackHeld]
  simp only [coordinateDirection,pFound,leaveFound,attackFound,pAddress,leaveAddress,attackAddress,
    if_neg (Ne.symm different.1),if_neg (Ne.symm different.2.1),if_neg (Ne.symm different.2.2),
    pPosition,leavePosition,attackPosition]
  constructor
  · ext axis; fin_cases axis <;> simp [transversePoint]; ring
  · constructor
    · ext axis; fin_cases axis <;> simp [transversePoint]; ring
    · ext axis; fin_cases axis <;> simp [transversePoint]; ring

theorem normal_mode_exchange_eventually (nodes : List Body.Node) (mass amplitude x height : ℝ) (channel : Channel)
    (p leaving attacking : Body.Node)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup) (ready : Body.ready nodes)
    (pHeld : p ∈ nucleusNodes nodes) (leaveHeld : leaving ∈ nucleusNodes nodes) (attackHeld : attacking ∈ nucleusNodes nodes)
    (pFound : nodeAt? nodes channel.phosphorus = some p) (leaveFound : nodeAt? nodes channel.leavingOxygen = some leaving)
    (attackFound : nodeAt? nodes channel.attackingOxygen = some attacking)
    (different : channel.phosphorus ≠ channel.leavingOxygen ∧ channel.phosphorus ≠ channel.attackingOxygen ∧
      channel.leavingOxygen ≠ channel.attackingOxygen)
    (pPosition : p.row.position = transversePoint x height 0)
    (leavePosition : leaving.row.position = transversePoint x (height+1) 0)
    (attackPosition : attacking.row.position = transversePoint x (height+2) 0)
    (positive : 0 < bondWeight nodes (initialOccupation nodes) (transversePoint x 0 0) (transversePoint x 0 0))
    (above : 1 < height) (forward : 0 < amplitude) (small : amplitude ≤ 1/16) :
    ∀ᶠ time in 𝓝 (0 : ℝ),
      bondWeight nodes (normalOccupied nodes mass amplitude (coordinateDirection nodes channel) time)
        (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) time p).position
        (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) time leaving).position <
          bondWeight nodes (initialOccupation nodes) p.row.position leaving.row.position ∧
      bondWeight nodes (initialOccupation nodes) p.row.position attacking.row.position <
        bondWeight nodes (normalOccupied nodes mass amplitude (coordinateDirection nodes channel) time)
          (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) time p).position
          (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) time attacking).position := by
  let occupied := normalOccupied nodes mass amplitude (coordinateDirection nodes channel)
  let rows := normalEndRows nodes mass amplitude (coordinateDirection nodes channel)
  have occupation := normal_occupied_continuous nodes mass amplitude (coordinateDirection nodes channel) unique ready
  have position (node : Body.Node) (held : node ∈ nucleusNodes nodes) : ContinuousAt (fun time => (rows time node).position) 0 :=
    normal_end_position_continuous nodes mass amplitude (coordinateDirection nodes channel) unique ready node (List.mem_filter.mp held).1
  have leavingContinuous := bond_weight_continuous nodes occupied (fun time => (rows time p).position)
    (fun time => (rows time leaving).position) 0 occupation (position p pHeld) (position leaving leaveHeld)
  have attackingContinuous := bond_weight_continuous nodes occupied (fun time => (rows time p).position)
    (fun time => (rows time attacking).position) 0 occupation (position p pHeld) (position attacking attackHeld)
  have limits := normal_coordinate_positions nodes mass amplitude x height channel p leaving attacking
    pHeld leaveHeld attackHeld pFound leaveFound attackFound different pPosition leavePosition attackPosition
  have strict := normal_mode_bond_limits nodes x height amplitude positive above forward small
  have leavingStrict : bondWeight nodes (occupied 0) (rows 0 p).position (rows 0 leaving).position <
      bondWeight nodes (initialOccupation nodes) p.row.position leaving.row.position := by
    simpa only [occupied,rows,normal_occupied_zero,limits.1,limits.2.1,pPosition,leavePosition] using strict.1
  have attackingStrict : bondWeight nodes (initialOccupation nodes) p.row.position attacking.row.position <
      bondWeight nodes (occupied 0) (rows 0 p).position (rows 0 attacking).position := by
    simpa only [occupied,rows,normal_occupied_zero,limits.1,limits.2.2,pPosition,attackPosition] using strict.2
  exact (leavingContinuous.eventually_lt continuousAt_const leavingStrict).and
    (continuousAt_const.eventually_lt attackingContinuous attackingStrict)

abbrev CountOccupation (count : Nat) := Matrix (Fin (count+1) × Bool) (Fin count) ℂ

private def countedInitial (count : Nat) : CountOccupation count :=
  fun index electron => if index = (⟨electron.val/2,by omega⟩,decide (electron.val%2=1)) then 1 else 0

private def countedCore (count : Nat) (pose : List Body.Node) (mass : ℝ) :
    Matrix (Fin (count+1) × Bool) (Fin (count+1) × Bool) ℂ := fun i j =>
  if i.2 = j.2 then
    ((1/(2*mass) : ℝ) : ℂ)*(∑ axis : Fin 3,
      inner ℂ (spatialField 0 (count+1) i.1 (Pi.single axis 1)) (spatialField 0 (count+1) j.1 (Pi.single axis 1)))+
    ((nucleusNodes pose).map (fun node => -(node.particle.charge : ℂ)*
      nuclearIntegral 0 (count+1) i.1 j.1 (fun axis => node.row.position axis))).sum
  else 0

private def countedTwoBody (count : Nat) (i j k l : Fin (count+1) × Bool) : ℂ :=
  if i.2 = k.2 ∧ j.2 = l.2 then pairIntegral 0 (count+1) i.1 k.1 j.1 l.1 else 0

private def countedDensity {count : Nat} (occupied : CountOccupation count) :
    Matrix (Fin (count+1) × Bool) (Fin (count+1) × Bool) ℂ := occupied*occupied.conjTranspose

private def countedNext (count : Nat) (pose : List Body.Node) (mass time : ℝ) (occupied : CountOccupation count) :
    CountOccupation count := CPS1ElectronicEvolution.occupiedUpdate
      (fun i k => countedCore count pose mass i k+∑ j, ∑ l,
        countedDensity occupied l j*(countedTwoBody count i j k l-countedTwoBody count i j l k))
      (time/2) occupied

private def countedBond (count : Nat) (occupied : CountOccupation count) (first second : Body.Point) : ℝ :=
  Complex.normSq (∑ spin : Bool, ∑ i : Fin (count+1), ∑ j : Fin (count+1),
    star (spatialValue 0 (count+1) i 0 (fun axis => first axis))*countedDensity occupied (i,spin) (j,spin)*
      spatialValue 0 (count+1) j 0 (fun axis => second axis))

private def countedEnergy (count : Nat) (pose : List Body.Node) (mass : ℝ) (occupied : CountOccupation count) : ℝ :=
  Body.energy (nucleusNodes pose)+(Matrix.trace (countedCore count pose mass*countedDensity occupied)).re+
    (1/2)*(∑ i, ∑ j, ∑ k, ∑ l, countedDensity occupied k i*countedDensity occupied l j*
      (countedTwoBody count i j k l-countedTwoBody count i j l k)).re

private def countedForce (count : Nat) (pose : List Body.Node) (mass : ℝ) (occupied : CountOccupation count)
    (node : Body.Node) : Body.Point :=
  match node.particle.address with
  | .electron .. => 0
  | .nucleus _ => WithLp.toLp 2 (fun axis => -deriv
      (fun amount => countedEnergy count (displaced pose node.particle.address axis amount) mass occupied) 0)

def transferOccupation {first second : Nat} (same : first = second) (occupied : CountOccupation first) :
    CountOccupation second := same ▸ occupied

theorem initial_occupation_count (source target : List Body.Node) (same : electronCount source = electronCount target) :
    transferOccupation same (initialOccupation source) = initialOccupation target := by
  have transport {first second : Nat} (equal : first = second) :
      transferOccupation equal (countedInitial first) = countedInitial second := by cases equal; rfl
  exact transport same

theorem occupied_next_source_count (source target pose : List Body.Node) (same : electronCount source = electronCount target)
    (mass time : ℝ) (occupied : Coefficients source) :
    transferOccupation same (occupiedNextAt source pose mass time occupied) =
      occupiedNextAt target pose mass time (transferOccupation same occupied) := by
  have transport {first second : Nat} (equal : first = second) (field : CountOccupation first) :
      transferOccupation equal (countedNext first pose mass time field) =
        countedNext second pose mass time (transferOccupation equal field) := by cases equal; rfl
  exact transport same occupied

theorem bond_weight_source_count (source target : List Body.Node) (same : electronCount source = electronCount target)
    (occupied : Coefficients source) (first second : Body.Point) :
    bondWeight target (transferOccupation same occupied) first second = bondWeight source occupied first second := by
  have transport {old next : Nat} (equal : old = next) (field : CountOccupation old) :
      countedBond next (transferOccupation equal field) first second = countedBond old field first second := by
    cases equal; rfl
  exact transport same occupied

theorem energy_force_source_count (source target pose : List Body.Node) (same : electronCount source = electronCount target)
    (mass : ℝ) (occupied : Coefficients source) (node : Body.Node) :
    energyForce target pose mass (transferOccupation same occupied) node = energyForce source pose mass occupied node := by
  have transport {old next : Nat} (equal : old = next) (field : CountOccupation old) :
      countedForce next pose mass (transferOccupation equal field) node = countedForce old pose mass field node := by
    cases equal; rfl
  exact transport same occupied

def momentumNode (change : Charged.Address → Body.Point) (node : Body.Node) : Body.Node :=
  match node.particle.address with
  | .electron .. => node
  | .nucleus _ => {node with row := {node.row with momentum := node.row.momentum+change node.particle.address}}

abbrev momentumPose (nodes : List Body.Node) (change : Charged.Address → Body.Point) : List Body.Node :=
  nodes.map (momentumNode change)

@[simp] theorem momentum_node_particle (change : Charged.Address → Body.Point) (node : Body.Node) :
    (momentumNode change node).particle = node.particle := by
  cases address : node.particle.address <;> simp only [momentumNode,address]

@[simp] theorem momentum_node_position (change : Charged.Address → Body.Point) (node : Body.Node) :
    (momentumNode change node).row.position = node.row.position := by
  cases address : node.particle.address <;> simp only [momentumNode,address]

theorem momentum_pose_nuclei (nodes : List Body.Node) (change : Charged.Address → Body.Point) :
    nucleusNodes (momentumPose nodes change) = momentumPose (nucleusNodes nodes) change := by
  unfold nucleusNodes momentumPose
  rw [List.filter_map]
  simp only [momentum_node_particle,Function.comp_def]

theorem momentum_pose_count (nodes : List Body.Node) (change : Charged.Address → Body.Point) :
    electronCount nodes = electronCount (momentumPose nodes change) := by
  unfold electronCount momentumPose
  rw [List.filter_map,List.length_map]
  simp only [Function.comp_def,momentum_node_particle]

theorem attraction_pose_momentum (source pose : List Body.Node) (change : Charged.Address → Body.Point)
    (i j : Spatial source) : attractionAt source (momentumPose pose change) i j = attractionAt source pose i j := by
  unfold attractionAt
  rw [momentum_pose_nuclei]
  simp only [momentumPose,List.map_map,Function.comp_def,momentum_node_particle,momentum_node_position]

theorem core_pose_momentum (source pose : List Body.Node) (change : Charged.Address → Body.Point) (mass : ℝ) :
    coreAt source (momentumPose pose change) mass = coreAt source pose mass := by
  ext i j
  simp only [coreAt,attraction_pose_momentum]

theorem occupied_next_pose_momentum (source pose : List Body.Node) (change : Charged.Address → Body.Point)
    (mass time : ℝ) (occupied : Coefficients source) :
    occupiedNextAt source (momentumPose pose change) mass time occupied = occupiedNextAt source pose mass time occupied := by
  unfold occupiedNextAt fockAt
  rw [core_pose_momentum]

theorem displaced_momentum_pose (pose : List Body.Node) (change : Charged.Address → Body.Point)
    (address : Charged.Address) (axis : Fin 3) (amount : ℝ) :
    displaced (momentumPose pose change) address axis amount = momentumPose (displaced pose address axis amount) change := by
  simp only [displaced,momentumPose,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro node _
  cases selected : node.particle.address <;> simp only [Field.perturb,momentumNode,selected]

theorem force_pose_momentum (node : Body.Node) (pose : List Body.Node) (change : Charged.Address → Body.Point) :
    Body.force (momentumNode change node) (momentumPose pose change) = Body.force node pose := by
  simp only [Body.force,momentumPose,List.map_map,Function.comp_def,momentum_node_particle,momentum_node_position]

theorem energy_force_pose_momentum (source pose : List Body.Node) (change : Charged.Address → Body.Point)
    (mass : ℝ) (occupied : Coefficients source)
    (unique : ((nucleusNodes pose).map (fun node => node.particle.address)).Nodup)
    (ready : Body.ready (nucleusNodes pose)) (node : Body.Node) (held : node ∈ nucleusNodes pose) :
    energyForce source (momentumPose pose change) mass occupied (momentumNode change node) =
      energyForce source pose mass occupied node := by
  have nextUnique : ((nucleusNodes (momentumPose pose change)).map (fun node => node.particle.address)).Nodup := by
    rw [momentum_pose_nuclei]
    simpa only [momentumPose,List.map_map,Function.comp_def,momentum_node_particle] using unique
  have nextReady : Body.ready (nucleusNodes (momentumPose pose change)) := by
    rw [momentum_pose_nuclei]
    simpa only [Body.ready,momentumPose,List.pairwise_map,momentum_node_position] using ready
  have nextHeld : momentumNode change node ∈ nucleusNodes (momentumPose pose change) := by
    rw [momentum_pose_nuclei]
    exact List.mem_map_of_mem held
  have derivative : coreAxis source (momentumPose pose change) mass node.particle.address =
      coreAxis source pose mass node.particle.address := by
    ext axis i j
    unfold coreAxis
    simp only [displaced_momentum_pose,core_pose_momentum]
  ext axis
  rw [energy_force_partition source (momentumPose pose change) mass occupied nextUnique nextReady _ nextHeld axis,
    energy_force_partition source pose mass occupied unique ready node held axis]
  rw [momentum_node_particle,electronic_axis_derivative,electronic_axis_derivative,
    momentum_pose_nuclei,force_pose_momentum,derivative]

def addressCoordinate (nodes : List Body.Node) (channel : Channel) (address : Charged.Address) : Body.Point :=
  match nodeAt? nodes channel.phosphorus,nodeAt? nodes channel.leavingOxygen,nodeAt? nodes channel.attackingOxygen with
  | some p,some leaving,some attacking =>
    if address = channel.phosphorus then 2 • (attacking.row.position-leaving.row.position)
    else if address = channel.leavingOxygen then (-2 : ℝ) • (p.row.position-leaving.row.position)
    else if address = channel.attackingOxygen then 2 • (p.row.position-attacking.row.position)
    else 0
  | _,_,_ => 0

theorem address_coordinate (nodes : List Body.Node) (channel : Channel) (node : Body.Node) :
    addressCoordinate nodes channel node.particle.address = coordinateDirection nodes channel node := rfl

def normalChange (nodes : List Body.Node) (channel : Channel) (amplitude time : ℝ) (address : Charged.Address) : Body.Point :=
  (amplitude/time) • addressCoordinate nodes channel address

abbrev normalEntry (nodes : List Body.Node) (channel : Channel) (amplitude time : ℝ) : List Body.Node :=
  momentumPose nodes (normalChange nodes channel amplitude time)

theorem normal_entry_half (nodes : List Body.Node) (channel : Channel) (mass amplitude time : ℝ) :
    normalHalf (normalEntry nodes channel amplitude time) mass time =
      transferOccupation (momentum_pose_count nodes (normalChange nodes channel amplitude time))
        (normalHalf nodes mass time) := by
  unfold normalHalf normalEntry
  rw [← initial_occupation_count nodes (momentumPose nodes (normalChange nodes channel amplitude time))
    (momentum_pose_count nodes (normalChange nodes channel amplitude time))]
  rw [← occupied_next_source_count,occupied_next_pose_momentum]

theorem normal_end_ready_eventually (nodes : List Body.Node) (mass amplitude : ℝ)
    (direction : Body.Node → Body.Point)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup) (ready : Body.ready nodes)
    (limitReady : Body.ready (rowPose nodes (normalEndRows nodes mass amplitude direction 0))) :
    ∀ᶠ time in 𝓝 (0 : ℝ), Body.ready (rowPose nodes (normalEndRows nodes mass amplitude direction time)) := by
  have separated := CPS1PositivePulse.pairwise_positions_eventually nodes
    (fun time node => (normalEndRows nodes mass amplitude direction time node).position)
    (normal_end_position_continuous nodes mass amplitude direction unique ready)
    (by simpa only [Body.ready,rowPose,List.pairwise_map] using limitReady)
  simpa only [Body.ready,rowPose,List.pairwise_map] using separated

theorem normal_entry_kick (nodes : List Body.Node) (channel : Channel) (mass amplitude time : ℝ)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup) (ready : Body.ready nodes)
    (elapsed : 0 < time) (node : Body.Node) (held : node ∈ nodes) (inertia : node.row.inertia = 1) :
    sourceKick (normalEntry nodes channel amplitude time) (normalEntry nodes channel amplitude time) mass
        (normalHalf (normalEntry nodes channel amplitude time) mass time) time
        (momentumNode (normalChange nodes channel amplitude time) node) =
      ⟨node.particle,normalEndRows nodes mass amplitude (coordinateDirection nodes channel) time node⟩ := by
  let change := normalChange nodes channel amplitude time
  have nuclearUnique : ((nucleusNodes nodes).map (fun node => node.particle.address)).Nodup :=
    List.pairwise_map.mpr ((List.pairwise_map.mp unique).filter _)
  cases address : node.particle.address with
  | electron slot orbital => simp only [momentumNode,address,sourceKick,normalEndRows]
  | nucleus slot =>
    have nuclearHeld : node ∈ nucleusNodes nodes := List.mem_filter.mpr ⟨held,by rw [address]⟩
    have force : energyForce (normalEntry nodes channel amplitude time) (normalEntry nodes channel amplitude time) mass
        (normalHalf (normalEntry nodes channel amplitude time) mass time) (momentumNode change node) =
        energyForce nodes nodes mass (normalHalf nodes mass time) node := by
      rw [normal_entry_half,energy_force_source_count]
      exact energy_force_pose_momentum nodes nodes change mass (normalHalf nodes mass time)
        nuclearUnique (ready.filter _) node nuclearHeld
    have scalar : time*(amplitude/time) = amplitude := by field_simp
    have direction : addressCoordinate nodes channel (.nucleus slot) = coordinateDirection nodes channel node := by
      rw [← address,address_coordinate]
    simp only [sourceKick,momentum_node_particle,address]
    rw [force]
    simp only [momentumNode,address,normalEndRows,Body.Node.mk.injEq,Body.Row.mk.injEq,true_and,and_true]
    constructor
    · simp only [normalChange,direction,inertia,div_one,smul_add,smul_smul,scalar]
      abel
    · simp only [normalChange,direction,inertia,one_mul]

theorem normal_entry_nodes (nodes : List Body.Node) (channel : Channel) (mass amplitude time : ℝ)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup) (ready : Body.ready nodes)
    (elapsed : 0 < time) (inertia : ∀ node ∈ nodes, node.row.inertia = 1) :
    (normalEntry nodes channel amplitude time).map
        (sourceKick (normalEntry nodes channel amplitude time) (normalEntry nodes channel amplitude time) mass
          (normalHalf (normalEntry nodes channel amplitude time) mass time) time) =
      rowPose nodes (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) time) := by
  unfold normalEntry momentumPose rowPose
  rw [List.map_map]
  apply List.map_congr_left
  intro node held
  exact normal_entry_kick nodes channel mass amplitude time unique ready elapsed node held (inertia node held)

theorem normal_entry_occupied (nodes : List Body.Node) (channel : Channel) (mass amplitude time : ℝ) :
    occupiedNextAt (normalEntry nodes channel amplitude time)
        (rowPose nodes (normalEndRows nodes mass amplitude (coordinateDirection nodes channel) time)) mass time
        (normalHalf (normalEntry nodes channel amplitude time) mass time) =
      transferOccupation (momentum_pose_count nodes (normalChange nodes channel amplitude time))
        (normalOccupied nodes mass amplitude (coordinateDirection nodes channel) time) := by
  rw [normal_entry_half,← occupied_next_source_count]
  rfl

theorem electronic_bond_source_count (source target pose : List Body.Node) (same : electronCount source = electronCount target)
    (occupied : Coefficients source) (channel : Channel) :
    electronicBond target pose (transferOccupation same occupied) channel = electronicBond source pose occupied channel := by
  unfold electronicBond
  cases p : nodeAt? pose channel.phosphorus <;>
    cases leaving : nodeAt? pose channel.leavingOxygen <;>
      cases attacking : nodeAt? pose channel.attackingOxygen <;> simp
  exact ⟨bond_weight_source_count source target same occupied _ _,
    bond_weight_source_count source target same occupied _ _⟩

theorem electronic_bond_momentum_pose (source pose : List Body.Node) (change : Charged.Address → Body.Point)
    (occupied : Coefficients source) (channel : Channel) :
    electronicBond source (momentumPose pose change) occupied channel = electronicBond source pose occupied channel := by
  have selector (address : Charged.Address) : nodeAt? (momentumPose pose change) address =
      (nodeAt? pose address).map (momentumNode change) := by
    unfold nodeAt? momentumPose
    rw [List.find?_map]
    simp only [Function.comp_def,momentum_node_particle]
  simp only [electronicBond,selector]
  cases p : nodeAt? pose channel.phosphorus <;>
    cases leaving : nodeAt? pose channel.leavingOxygen <;>
      cases attacking : nodeAt? pose channel.attackingOxygen <;>
        simp

theorem electronic_bond_row_pose (source pose : List Body.Node) (rows : Body.Node → Body.Row)
    (occupied : Coefficients source) (channel : Channel) (p leaving attacking : Body.Node)
    (pFound : nodeAt? pose channel.phosphorus = some p) (leaveFound : nodeAt? pose channel.leavingOxygen = some leaving)
    (attackFound : nodeAt? pose channel.attackingOxygen = some attacking) :
    electronicBond source (rowPose pose rows) occupied channel =
      some (bondWeight source occupied (rows p).position (rows leaving).position,
        bondWeight source occupied (rows p).position (rows attacking).position) := by
  simp only [electronicBond,node_at_row_pose,pFound,leaveFound,attackFound,Option.map_some,
    Bind.bind,Option.bind_some,Pure.pure]
  rfl

def momentumRow (change : Charged.Address → Body.Point) (address : Charged.Address) (row : Body.Row) : Body.Row :=
  match address with
  | .electron .. => row
  | .nucleus _ => {row with momentum := row.momentum+change address}

def momentumRows (rows : List (Charged.Address × Body.Row)) (change : Charged.Address → Body.Point) :
    List (Charged.Address × Body.Row) :=
  rows.map (fun entry => (entry.1,momentumRow change entry.1 entry.2))

theorem momentum_node_row (change : Charged.Address → Body.Point) (node : Body.Node) :
    (momentumNode change node).row = momentumRow change node.particle.address node.row := by
  cases address : node.particle.address <;> simp only [momentumNode,momentumRow,address]

theorem momentum_node_inertia (change : Charged.Address → Body.Point) (node : Body.Node) :
    (momentumNode change node).row.inertia = node.row.inertia := by
  cases address : node.particle.address <;> simp only [momentumNode,address]

theorem momentum_row_zero (change : Charged.Address → Body.Point) (address : Charged.Address) (row : Body.Row)
    (zero : change address = 0) : momentumRow change address row = row := by
  cases address <;> simp [momentumRow,zero]

theorem momentum_row_at (rows : List (Charged.Address × Body.Row)) (change : Charged.Address → Body.Point)
    (address : Charged.Address) :
    Body.row? (momentumRows rows change) address = (Body.row? rows address).map (momentumRow change address) := by
  unfold Body.row? momentumRows
  rw [List.find?_map]
  simp only [Function.comp_def]
  cases actual : rows.find? (fun entry => decide (entry.1 = address)) with
  | none => rfl
  | some entry =>
    have selected : entry.1 = address := of_decide_eq_true
      (List.find?_some (p := fun item : Charged.Address × Body.Row => decide (item.1 = address)) actual)
    simp only [Option.map_some,selected]

theorem gathered_momentum (particles : List Charged.Particle) (rows : List (Charged.Address × Body.Row))
    (nodes : List Body.Node) (change : Charged.Address → Body.Point) (actual : Body.gather particles rows = .ok nodes) :
    Body.gather particles (momentumRows rows change) = .ok (momentumPose nodes change) := by
  have source := Body.gather_source particles rows nodes actual
  have particlesActual : (momentumPose nodes change).map Body.Node.particle = particles := by
    simpa only [momentumPose,List.map_map,Function.comp_def,momentum_node_particle] using source.1
  apply Body.gather_exact particles (momentumPose nodes change) particlesActual
  · intro node held
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp held
    rw [momentum_node_particle,momentum_node_row,momentum_row_at,(source.2 old member).2]
    rfl
  · intro node held
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp held
    rw [momentum_node_inertia]
    exact (source.2 old member).1

abbrev momentumRaw (raw : Raw) (change : Charged.Address → Body.Point) (reserve time : ℝ) : Raw :=
  ⟨raw.fuel,momentumRows raw.rows change,reserve,time⟩

theorem momentum_prior_rows (nodes : List Body.Node) (change : Charged.Address → Body.Point)
    (zero : ∀ node ∈ nodes, change node.particle.address = 0) :
    momentumRows (nodes.map (fun node => (node.particle.address,node.row))) change =
      nodes.map (fun node => (node.particle.address,node.row)) := by
  unfold momentumRows
  rw [List.map_map]
  apply List.map_congr_left
  intro node held
  dsimp only [Function.comp_def]
  rw [momentum_row_zero change node.particle.address node.row (zero node held)]

abbrev momentumCommon {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
    (source : Common before step raw) (change : Charged.Address → Body.Point) (reserve time : ℝ)
    (zero : ∀ node ∈ step.next.nodes, change node.particle.address = 0) :
    Common before step (momentumRaw raw change reserve time) where
  atoms := source.atoms
  atomSource := source.atomSource
  bonds := source.bonds
  bondSource := source.bondSource
  atpFuel := source.atpFuel
  bicarbonateFuel := source.bicarbonateFuel
  nodes := momentumPose source.nodes change
  measured := by
    have actual := gathered_momentum _ _ _ change source.measured
    unfold momentumRows at actual
    rw [List.map_append] at actual
    change Body.gather _
      (momentumRows (step.next.nodes.map (fun node => (node.particle.address,node.row))) change ++
        momentumRows raw.rows change) = _ at actual
    rw [momentum_prior_rows step.next.nodes change zero] at actual
    exact actual
  electronInertia := source.electronInertia
  uniformElectrons := by
    intro node held
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp held
    rw [momentum_node_particle]
    cases address : old.particle.address with
    | nucleus slot => trivial
    | electron slot orbital =>
      have uniform := source.uniformElectrons old member
      rw [address] at uniform
      rw [momentum_node_inertia]
      exact uniform
  ready := by
    simpa only [Body.ready,momentumPose,List.pairwise_map,momentum_node_position] using source.ready

theorem coordinate_direction_momentum (nodes : List Body.Node) (change : Charged.Address → Body.Point)
    (channel : Channel) (node : Body.Node) :
    coordinateDirection (momentumPose nodes change) channel (momentumNode change node) = coordinateDirection nodes channel node := by
  have selector (address : Charged.Address) : nodeAt? (momentumPose nodes change) address =
      (nodeAt? nodes address).map (momentumNode change) := by
    unfold nodeAt? momentumPose
    rw [List.find?_map]
    simp only [Function.comp_def,momentum_node_particle]
  simp only [coordinateDirection,selector,momentum_node_particle]
  cases p : nodeAt? nodes channel.phosphorus <;>
    cases leaving : nodeAt? nodes channel.leavingOxygen <;>
      cases attacking : nodeAt? nodes channel.attackingOxygen <;> simp

theorem chain_nuclei_momentum {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (nodes : List Body.Node) (change : Charged.Address → Body.Point) :
    chainNuclei atoms (momentumPose nodes change) = momentumPose (chainNuclei atoms nodes) change := by
  unfold chainNuclei
  rw [momentum_pose_nuclei]
  unfold momentumPose
  rw [List.filter_map]
  simp only [Function.comp_def,isChainNode,originAt?,momentum_node_particle]
  rfl

theorem directional_chain_work_momentum {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (fuel : List FuelKind) (nodes : List Body.Node) (change : Charged.Address → Body.Point)
    (mass : ℝ) (next : Coefficients (momentumPose nodes change)) (before : Coefficients nodes) (channel : Channel)
    (selected : channel? atoms fuel = some channel)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup) (ready : Body.ready nodes) :
    directionalChainWork atoms (momentumPose nodes change) mass next channel =
      directionalChainWork atoms nodes mass before channel := by
  have nextUnique : ((momentumPose nodes change).map (fun node => node.particle.address)).Nodup := by
    simpa only [momentumPose,List.map_map,Function.comp_def,momentum_node_particle] using unique
  have nextReady : Body.ready (momentumPose nodes change) := by
    simpa only [Body.ready,momentumPose,List.pairwise_map,momentum_node_position] using ready
  rw [directional_chain_work_nuclear atoms fuel (momentumPose nodes change) mass next channel selected nextUnique nextReady,
    directional_chain_work_nuclear atoms fuel nodes mass before channel selected unique ready,
    momentum_pose_nuclei,chain_nuclei_momentum]
  simp only [momentumPose,List.map_map,Function.comp_def]
  have each (node : Body.Node) :
      inner ℝ (Body.force (momentumNode change node) (momentumPose (chainNuclei atoms nodes) change))
          (coordinateDirection (momentumPose nodes change) channel (momentumNode change node)) =
        inner ℝ (Body.force node (chainNuclei atoms nodes)) (coordinateDirection nodes channel node) := by
    rw [force_pose_momentum,coordinate_direction_momentum]
  simp only [each]

def measuredElectronMass (nodes : List Body.Node) : ℝ :=
  ((nodes.find? (fun node => match node.particle.address with | .electron .. => true | _ => false)).map
    (fun node => node.row.inertia)).getD 1

theorem common_measured_electron_mass {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw) :
    measuredElectronMass source.nodes = source.electronInertia := by
  obtain ⟨node,held,slot,orbital,address⟩ := common_electron_present source
  let electron := fun node : Body.Node => match node.particle.address with | .electron .. => true | _ => false
  have present : (source.nodes.find? electron).isSome :=
    List.find?_isSome.mpr ⟨node,held,by simp only [electron,address]⟩
  cases actual : source.nodes.find? electron with
  | none => rw [actual] at present; cases present
  | some selected =>
    have member := List.mem_of_find?_eq_some actual
    have role := List.find?_some actual
    have uniform := source.uniformElectrons selected member
    cases selectedAddress : selected.particle.address with
    | nucleus index => simp only [electron,selectedAddress,Bool.false_eq_true] at role
    | electron index number =>
      rw [selectedAddress] at uniform
      unfold measuredElectronMass
      change ((source.nodes.find? electron).map (fun node => node.row.inertia)).getD 1 = _
      rw [actual]
      exact uniform

theorem admit_common {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw)
    (compatible : Classical.rowCompatible (step.next.nodes.map (fun node => (node.particle.address,node.row))) raw.rows = .ok ()) :
    admit before step raw = .ok source := by
  classical
  have enough := not_lt_of_ge source.atpFuel
  have bicarbonate : ¬ .bicarbonate ∉ raw.fuel := not_not.mpr source.bicarbonateFuel
  unfold admit
  simp only [dif_neg enough,dif_neg bicarbonate]
  split
  · rename_i failure found
    have impossible := found.symm.trans compatible
    cases impossible
  · rename_i unitValue found
    cases unitValue
    split
    · rename_i failure found
      have impossible := found.symm.trans source.measured
      cases impossible
    · rename_i nodes found
      have same := Except.ok.inj (found.symm.trans source.measured)
      subst nodes
      split
      · have uniform : ∀ node ∈ source.nodes, match node.particle.address with
          | .nucleus _ => True | .electron .. => node.row.inertia = measuredElectronMass source.nodes := by
          rw [common_measured_electron_mass source]
          exact source.uniformElectrons
        split
        · have mass := common_measured_electron_mass source
          rcases source with ⟨atoms,atomSource,bonds,bondSource,atpFuel,bicarbonateFuel,nodes,measured,inertia,uniformSource,ready⟩
          dsimp only at mass atomSource bondSource ⊢
          subst atoms
          subst bonds
          subst inertia
          rfl
        · rename_i denied
          exact False.elim (denied uniform)
      · rename_i denied
        exact False.elim (denied source.ready)

theorem compatible_momentum (known rows : List (Charged.Address × Body.Row)) (change : Charged.Address → Body.Point)
    (zero : ∀ entry ∈ known, change entry.1 = 0)
    (compatible : Classical.rowCompatible known rows = .ok ()) :
    Classical.rowCompatible known (momentumRows rows change) = .ok () := by
  unfold Classical.rowCompatible at compatible ⊢
  split at compatible
  · rename_i original
    split
    · rfl
    · rename_i entry generated
      have held := List.mem_of_find?_eq_some generated
      have checked := List.find?_some generated
      have absent := List.find?_eq_none.mp original entry held
      rw [momentum_row_at] at checked
      cases old : Body.row? rows entry.1 with
      | none => simp only [old,Option.map_none,Bool.false_eq_true] at checked
      | some row =>
        simp only [old,Option.map_some,momentum_row_zero change entry.1 row (zero entry held)] at checked
        rw [old] at absent
        exact False.elim (absent checked)
  · cases compatible

def normalAmplitude {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (nodes : List Body.Node) (mass : ℝ) (channel : Channel) : ℝ :=
  let work := directionalChainWork atoms nodes mass (initialOccupation nodes) channel
  work/(16*(1+work))

private theorem normal_mode_first_exchange {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw}
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
    ∃ index : Nat, ∃ reserve : ℝ,
      ∃ next : NativeCurrent (momentumCommon source (normalChange source.nodes channel amplitude ((1/2 : ℝ)^index)) reserve ((1/2 : ℝ)^index)
        (by intro node held; simp only [normalChange,address_coordinate,oldZero node held,smul_zero])),
      firstElectronicExchange (momentumCommon source (normalChange source.nodes channel amplitude ((1/2 : ℝ)^index)) reserve ((1/2 : ℝ)^index)
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
  refine ⟨index,reserve,?_⟩
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

theorem generated_exchange_nonempty {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw) (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (oldUnit : ∀ node ∈ step.next.nodes, node.row.inertia = 1) :
    ∃ raw : Raw, ∃ source : Common before step raw,
      admit before step raw = .ok source ∧ ∃ next : NativeCurrent source, firstElectronicExchange source = .ok next := by
  obtain ⟨x,height,source,admitted,nodes,mass,above,margin,axis,work⟩ := generated_base_nonempty before step actual oldUnit
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
  obtain ⟨index,reserve,next,actualExchange⟩ := normal_mode_first_exchange source channel p leaving attacking x height selected sourceUnit
    pHeld leaveHeld attackHeld (by rw [nodes]; exact found.1) (by rw [nodes]; exact found.2.1)
    (by rw [nodes]; exact found.2.2) (first_channel_distinct _) rfl rfl rfl axis above sourceWork oldZero limitReady
  let amplitude := normalAmplitude source.atoms source.nodes source.electronInertia channel
  let time : ℝ := (1/2 : ℝ)^index
  let change := normalChange source.nodes channel amplitude time
  have priorZero : ∀ node ∈ step.next.nodes, change node.particle.address = 0 := by
    intro node member
    simp only [change,normalChange,address_coordinate,oldZero node member,smul_zero]
  let nextSource := momentumCommon source change reserve time priorZero
  have compatible := base_rows_compatible before step actual x height
  have transformed := compatible_momentum _ _ change
    (by intro entry member; obtain ⟨node,held,same⟩ := List.mem_map.mp member; subst entry; exact priorZero node held) compatible
  exact ⟨momentumRaw (baseRaw before.packet.source x height) change reserve time,nextSource,
    admit_common nextSource transformed,next,actualExchange⟩

def StoredUnitPost {body : CPS1BiologicalUpdate.Body} {receipt : CPS1BiologicalUpdate.LocalRepairReceipt body}
    {priorRaw : WholeRaw} (whole : WholeResponse (.repaired receipt) priorRaw) : Prop :=
  match whole.particles with
  | .responded _ step => ∀ node ∈ step.next.nodes, node.row.inertia = 1
  | _ => False

theorem stored_exchange_nonempty {body : CPS1BiologicalUpdate.Body}
    (receipt : CPS1BiologicalUpdate.LocalRepairReceipt body) {priorRaw : WholeRaw}
    (whole : WholeResponse (.repaired receipt) priorRaw) (unitPost : StoredUnitPost whole) :
    ∃ raw : Raw,
      ∃ before : Classical.Current receipt.nextBody.current.2 priorRaw.particles,
      ∃ step : Classical.NativeStep before priorRaw.particles.time,
      ∃ actual : whole.particles = .responded before step,
      ∃ source : Common before step raw, ∃ next : NativeCurrent source,
        fromWhole (.repaired receipt) whole raw = .responded whole before step actual source next := by
  have past : ∃ before : Classical.Current receipt.nextBody.current.2 priorRaw.particles,
      ∃ step : Classical.NativeStep before priorRaw.particles.time,
      whole.particles = .responded before step ∧ (∀ node ∈ step.next.nodes, node.row.inertia = 1) := by
    cases actual : whole.particles with
    | sourceResidual failure => simp only [StoredUnitPost,actual] at unitPost
    | mechanicalResidual before failure => simp only [StoredUnitPost,actual] at unitPost
    | responded before step =>
      exact ⟨before,step,rfl,by simpa only [StoredUnitPost,actual] using unitPost⟩
  obtain ⟨before,step,actual,oldUnit⟩ := past
  have oldActual : Classical.fromCursor receipt.nextBody.current.2 priorRaw.particles = .responded before step :=
    whole.particlesActual.symm.trans actual
  obtain ⟨raw,source,admitted,next,exchanged⟩ := generated_exchange_nonempty before step oldActual oldUnit
  refine ⟨raw,before,step,actual,source,next,?_⟩
  unfold fromWhole
  dsimp only
  split
  · rename_i failure found
    have impossible := found.symm.trans actual
    cases impossible
  · rename_i other failure found
    have impossible := found.symm.trans actual
    cases impossible
  · rename_i actualBefore actualStep found
    have same := Classical.Disposition.responded.inj (found.symm.trans actual)
    rcases same with ⟨beforeSame,stepSame⟩
    subst actualBefore
    cases stepSame
    split
    · rename_i failure found
      have impossible := found.symm.trans admitted
      cases impossible
    · rename_i actualSource found
      have same := Except.ok.inj (found.symm.trans admitted)
      subst actualSource
      split
      · rename_i failure found
        have impossible := found.symm.trans exchanged
        cases impossible
      · rename_i actualNext found
        have same := Except.ok.inj (found.symm.trans exchanged)
        subst actualNext
        rfl

end
end CPS1PhosphorylExchange
