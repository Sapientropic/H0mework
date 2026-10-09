import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeFullSmooth
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Positive

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace CPS1MaterialIncidence.NativeBodyFunctionProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange NativeAmmoniaDynamics
open CPS1ElectronicSource NativeResumableProbe Filter
open scoped BigOperators Matrix Topology

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw}

def fullCoreAxis (current : NativeCurrent source) (pose : List Body.Node)
    (address : Charged.Address) (axis : Fin 3) : Matrix (RawIndex current) (RawIndex current) ℂ :=
  fun i j => deriv (fun amount => rawCore current (displaced pose address axis amount) i j) 0

theorem full_trace_axis (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ)
    (address : Charged.Address) (axis : Fin 3) :
    HasDerivAt (fun amount => (Matrix.trace
      (rawCore current (displaced pose address axis amount)*rawDensity current occupied)).re)
      (Matrix.trace (fullCoreAxis current pose address axis*rawDensity current occupied)).re 0 := by
  have complex : HasDerivAt (fun amount => Matrix.trace
      (rawCore current (displaced pose address axis amount)*rawDensity current occupied))
      (Matrix.trace (fullCoreAxis current pose address axis*rawDensity current occupied)) 0 := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact (full_raw_core_differentiable current pose address axis i j).hasDerivAt.mul_const _
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 complex

private theorem source_nuclear_axis (current : NativeCurrent source) (pose : List Body.Node)
    (ready : Body.ready pose) (address : Charged.Address) (axis : Fin 3) :
    DifferentiableAt ℝ (fun amount => Body.energy (nucleusNodes (displaced pose address axis amount))) 0 := by
  have source := full_raw_energy_differentiable current pose
    (0 : Matrix (RawIndex current) (Electron source.nodes) ℂ) ready address axis
  simpa only [rawEnergy,rawDensity,Matrix.conjTranspose_zero,Matrix.zero_mul,Matrix.mul_zero,
    Matrix.trace_zero,Matrix.zero_apply,Complex.zero_re,zero_mul,mul_zero,Finset.sum_const_zero,add_zero] using! source

theorem full_energy_axis (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ)
    (ready : Body.ready pose) (address : Charged.Address) (axis : Fin 3) :
    deriv (fun amount => rawEnergy current (displaced pose address axis amount) occupied) 0 =
      deriv (fun amount => Body.energy (nucleusNodes (displaced pose address axis amount))) 0 +
      (Matrix.trace (fullCoreAxis current pose address axis*rawDensity current occupied)).re := by
  have nuclear := (source_nuclear_axis current pose ready address axis).hasDerivAt
  have electronic := full_trace_axis current pose occupied address axis
  have complete := (nuclear.add electronic).add_const
    ((1/2)*(∑ i, ∑ j, ∑ k, ∑ l, rawDensity current occupied k i*rawDensity current occupied l j*
      (rawTwoBody current i j k l-rawTwoBody current i j l k)).re)
  simpa only [rawEnergy] using! complete.deriv

def halfAt {current : NativeCurrent source} (state : PostState current) (time : ℝ) :=
  CPS1ElectronicEvolution.occupiedUpdate (fullFockAt current state.pose state.occupied) (time/2) state.occupied

def forceAt {current : NativeCurrent source} (state : PostState current) (time : ℝ) (node : Body.Node) : Body.Point :=
  match node.particle.address with
  | .electron .. => 0
  | .nucleus _ => WithLp.toLp 2 (fun axis => -deriv (fun amount => rawEnergy current
      (displaced state.pose node.particle.address axis amount) (rawIncrement current (halfAt state time))) 0)

theorem half_at_zero {current : NativeCurrent source} (state : PostState current) : halfAt state 0 = state.occupied := by
  simp only [halfAt,zero_div,CPS1ElectronicEvolution.occupiedUpdate,CPS1ElectronicEvolution.zero_time,Matrix.one_mul]

theorem half_at_actual {current : NativeCurrent source} (state : PostState current) :
    halfAt state state.time = halfCoordinates state := rfl

theorem half_at_continuous {current : NativeCurrent source} (state : PostState current) : ContinuousAt (halfAt state) 0 :=
  CPS1PositivePulse.occupied_update_continuousAt
    (fun _ : ℝ => fullFockAt current state.pose state.occupied) (fun time : ℝ => time/2)
    (fun _ : ℝ => state.occupied) 0 continuousAt_const (continuousAt_id.div_const 2) continuousAt_const
    (full_fock_hermitian current state.pose state.occupied)

theorem force_at_actual {current : NativeCurrent source} (state : PostState current) (node : Body.Node) :
    forceAt state state.time node = fullForce state node := rfl

theorem force_at_continuous {current : NativeCurrent source} (state : PostState current) (node : Body.Node) :
    ContinuousAt (fun time => forceAt state time node) 0 := by
  cases address : node.particle.address with
  | electron slot orbital => simp only [forceAt,address]; exact continuousAt_const
  | nucleus slot =>
    have rawContinuous : ContinuousAt (fun time => rawIncrement current (halfAt state time)) 0 := by
      unfold rawIncrement
      exact continuousAt_const.add
        (CPS1PositivePulse.matrix_mul_continuousAt _ _ 0 continuousAt_const
          ((half_at_continuous state).sub continuousAt_const))
    have densityContinuous : ContinuousAt
        (fun time => rawDensity current (rawIncrement current (halfAt state time))) 0 :=
      CPS1PositivePulse.matrix_mul_continuousAt _ _ 0 rawContinuous
        (continuous_id.matrix_conjTranspose.continuousAt.comp rawContinuous)
    simp only [forceAt,address]
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.comp
    apply continuousAt_pi.mpr
    intro axis
    have electronic : ContinuousAt (fun time =>
        (Matrix.trace (fullCoreAxis current state.pose node.particle.address axis *
          rawDensity current (rawIncrement current (halfAt state time)))).re) 0 := by
      apply Complex.continuous_re.continuousAt.comp
      simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro j _
      exact (continuousAt_pi.mp (continuousAt_pi.mp densityContinuous j) i).const_mul _
    simpa only [full_energy_axis current state.pose _ state.ready (Charged.Address.nucleus slot) axis,address] using!
      ((continuousAt_const : ContinuousAt (fun _ : ℝ => deriv (fun amount =>
        Body.energy (nucleusNodes (displaced state.pose node.particle.address axis amount))) 0) 0).add electronic).neg

def endRowsAt {current : NativeCurrent source} (state : PostState current) (time : ℝ)
    (node : Body.Node) : Body.Row :=
  match node.particle.address with
  | .electron .. => node.row
  | .nucleus _ => {node.row with
      position := node.row.position+(time/node.row.inertia) • node.row.momentum+
        (time^2/(2*node.row.inertia)) • forceAt state time node
      momentum := node.row.momentum+time • forceAt state time node}

def poseAt {current : NativeCurrent source} (state : PostState current) (time : ℝ) : List Body.Node :=
  rowPose state.pose (endRowsAt state time)

theorem end_rows_at_zero {current : NativeCurrent source} (state : PostState current) (node : Body.Node) :
    endRowsAt state 0 node = node.row := by
  cases address : node.particle.address <;>
    simp only [endRowsAt,address,zero_div,zero_pow (by decide : 2 ≠ 0),zero_smul,add_zero]

theorem pose_at_zero {current : NativeCurrent source} (state : PostState current) : poseAt state 0 = state.pose := by
  simp only [poseAt,rowPose,end_rows_at_zero]
  change (List.map fun node : Body.Node => node) state.pose = state.pose
  simp only [List.map_id_fun',id_eq]

theorem pose_at_actual {current : NativeCurrent source} (state : PostState current) :
    poseAt state state.time = endPose state := by
  unfold poseAt rowPose endPose
  congr 1
  funext node
  cases address : node.particle.address <;> simp only [endRowsAt,fullKick,address,force_at_actual]

theorem end_position_at_continuous {current : NativeCurrent source} (state : PostState current) (node : Body.Node) :
    ContinuousAt (fun time => (endRowsAt state time node).position) 0 := by
  cases address : node.particle.address with
  | electron slot orbital => simp only [endRowsAt,address]; exact continuousAt_const
  | nucleus slot =>
    simpa only [endRowsAt,address] using!
      (continuousAt_const.add ((continuousAt_id.div_const node.row.inertia).smul continuousAt_const)).add
        (((continuousAt_id.pow 2).div_const (2*node.row.inertia)).smul (force_at_continuous state node))

theorem end_momentum_at_continuous {current : NativeCurrent source} (state : PostState current) (node : Body.Node) :
    ContinuousAt (fun time => (endRowsAt state time node).momentum) 0 := by
  cases address : node.particle.address with
  | electron slot orbital => simp only [endRowsAt,address]; exact continuousAt_const
  | nucleus slot =>
    simpa only [endRowsAt,address] using!
      continuousAt_const.add (continuousAt_id.smul (force_at_continuous state node))

theorem end_inertia_at {current : NativeCurrent source} (state : PostState current) (time : ℝ) (node : Body.Node) :
    (endRowsAt state time node).inertia = node.row.inertia := by
  cases address : node.particle.address <;> simp only [endRowsAt,address]

private theorem sum_at_continuous {K I : Type} [NormedAddCommGroup K]
    (items : List I) (f : I → ℝ → K) (paid : ∀ item ∈ items, ContinuousAt (f item) 0) :
    ContinuousAt (fun time => (items.map (fun item => f item time)).sum) 0 := by
  induction items with
  | nil => exact continuousAt_const
  | cons item rest ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      (paid item List.mem_cons_self).add (ih (fun other held => paid other (List.mem_cons_of_mem _ held)))

theorem core_at_continuous {current : NativeCurrent source} (state : PostState current) :
    ContinuousAt (fun time => rawCore current (poseAt state time)) 0 := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  simp only [rawCore,poseAt]
  simp only [nuclei_row_pose]
  simp only [rowPose,List.map_map,Function.comp_def]
  apply ContinuousAt.add continuousAt_const
  apply sum_at_continuous
  intro node _
  apply ContinuousAt.const_mul
  apply tendsto_finsetSum
  intro spin _
  apply (full_raw_nuclear_differentiable current i j spin _).continuousAt.comp
  apply continuousAt_pi.mpr
  intro axis
  exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) axis).continuousAt.comp (end_position_at_continuous state node)

theorem fock_at_continuous {current : NativeCurrent source} (state : PostState current) :
    ContinuousAt (fun time => fullFockAt current (poseAt state time) (halfAt state time)) 0 := by
  have rawContinuous : ContinuousAt (fun time => rawIncrement current (halfAt state time)) 0 := by
    unfold rawIncrement
    exact continuousAt_const.add (CPS1PositivePulse.matrix_mul_continuousAt _ _ 0 continuousAt_const
      ((half_at_continuous state).sub continuousAt_const))
  have densityContinuous : ContinuousAt (fun time => rawDensity current (rawIncrement current (halfAt state time))) 0 :=
    CPS1PositivePulse.matrix_mul_continuousAt _ _ 0 rawContinuous
      (continuous_id.matrix_conjTranspose.continuousAt.comp rawContinuous)
  have fockContinuous : ContinuousAt
      (fun time => rawFock current (poseAt state time) (rawIncrement current (halfAt state time))) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro k
    unfold rawFock
    apply ((continuousAt_pi.mp (continuousAt_pi.mp (core_at_continuous state) i) k)).add
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro l _
    exact (continuousAt_pi.mp (continuousAt_pi.mp densityContinuous l) j).mul_const _
  exact CPS1PositivePulse.matrix_mul_continuousAt _ _ 0
    (CPS1PositivePulse.matrix_mul_continuousAt _ _ 0 continuousAt_const fockContinuous) continuousAt_const

def occupiedAt {current : NativeCurrent source} (state : PostState current) (time : ℝ) :=
  CPS1ElectronicEvolution.occupiedUpdate (fullFockAt current (poseAt state time) (halfAt state time))
    (time/2) (halfAt state time)

theorem occupied_at_zero {current : NativeCurrent source} (state : PostState current) :
    occupiedAt state 0 = state.occupied := by
  simp only [occupiedAt,zero_div,CPS1ElectronicEvolution.occupiedUpdate,CPS1ElectronicEvolution.zero_time,
    Matrix.one_mul,half_at_zero]

theorem occupied_at_actual {current : NativeCurrent source} (state : PostState current) :
    occupiedAt state state.time = endCoordinates state := by
  simp only [occupiedAt,pose_at_actual,half_at_actual,endCoordinates]

theorem occupied_at_continuous {current : NativeCurrent source} (state : PostState current) :
    ContinuousAt (occupiedAt state) 0 :=
  CPS1PositivePulse.occupied_update_continuousAt
    (fun time => fullFockAt current (poseAt state time) (halfAt state time)) (fun time : ℝ => time/2)
    (halfAt state) 0 (fock_at_continuous state) (continuousAt_id.div_const 2) (half_at_continuous state)
    (full_fock_hermitian current _ _)

private theorem potential_at_continuous {current : NativeCurrent source} (state : PostState current)
    (nodes : List Body.Node) (ready : Body.ready nodes) :
    ContinuousAt (fun time => Body.potential (rowPose nodes (endRowsAt state time))) 0 := by
  induction nodes with
  | nil => exact continuousAt_const
  | cons first rest ih =>
    have separated := List.pairwise_cons.mp ready
    have head := sum_at_continuous rest
      (fun second time => Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
        (endRowsAt state time first).position (endRowsAt state time second).position)
      (fun second held => by
        have relative := (end_position_at_continuous state first).sub (end_position_at_continuous state second)
        have nonzero : ‖(endRowsAt state 0 first).position-(endRowsAt state 0 second).position‖ ≠ 0 := by
          rw [end_rows_at_zero,end_rows_at_zero]
          exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (separated.1 second held))
        exact continuousAt_const.div relative.norm nonzero)
    simpa only [rowPose,List.map_cons,Body.potential,List.map_map,Function.comp_def] using!
      head.add (ih separated.2)

theorem nuclear_energy_at_continuous {current : NativeCurrent source} (state : PostState current) :
    ContinuousAt (fun time => Body.energy (nucleusNodes (poseAt state time))) 0 := by
  have kinetic := sum_at_continuous (nucleusNodes state.pose)
    (fun node time => Coulomb.kinetic node.row.inertia (endRowsAt state time node).momentum)
    (fun node _ => ((end_momentum_at_continuous state node).norm.pow 2).div_const (2*node.row.inertia))
  have potential := potential_at_continuous state (nucleusNodes state.pose) (state.ready.filter _)
  simp only [poseAt]
  simp only [nuclei_row_pose]
  simpa only [Body.energy,Body.kinetic,rowPose,List.map_map,Function.comp_def,end_inertia_at] using! kinetic.add potential

theorem energy_at_continuous {current : NativeCurrent source} (state : PostState current) :
    ContinuousAt (fun time => rawEnergy current (poseAt state time) (rawIncrement current (occupiedAt state time))) 0 := by
  have rawContinuous : ContinuousAt (fun time => rawIncrement current (occupiedAt state time)) 0 := by
    unfold rawIncrement
    exact continuousAt_const.add (CPS1PositivePulse.matrix_mul_continuousAt _ _ 0 continuousAt_const
      ((occupied_at_continuous state).sub continuousAt_const))
  have densityContinuous : ContinuousAt (fun time => rawDensity current (rawIncrement current (occupiedAt state time))) 0 :=
    CPS1PositivePulse.matrix_mul_continuousAt _ _ 0 rawContinuous
      (continuous_id.matrix_conjTranspose.continuousAt.comp rawContinuous)
  have electronic : ContinuousAt (fun time => (Matrix.trace
      (rawCore current (poseAt state time)*rawDensity current (rawIncrement current (occupiedAt state time)))).re) 0 := by
    apply Complex.continuous_re.continuousAt.comp
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (continuousAt_pi.mp (continuousAt_pi.mp (core_at_continuous state) i) j).mul
      (continuousAt_pi.mp (continuousAt_pi.mp densityContinuous j) i)
  have interaction : ContinuousAt (fun time =>
      (1/2)*(∑ i, ∑ j, ∑ k, ∑ l, rawDensity current (rawIncrement current (occupiedAt state time)) k i *
        rawDensity current (rawIncrement current (occupiedAt state time)) l j *
        (rawTwoBody current i j k l-rawTwoBody current i j l k)).re) 0 := by
    apply ContinuousAt.const_mul
    apply Complex.continuous_re.continuousAt.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k _
    apply tendsto_finsetSum
    intro l _
    exact ((continuousAt_pi.mp (continuousAt_pi.mp densityContinuous k) i).mul
      (continuousAt_pi.mp (continuousAt_pi.mp densityContinuous l) j)).mul_const _
  simpa only [rawEnergy] using! ((nuclear_energy_at_continuous state).add electronic).add interaction

def priceAt {current : NativeCurrent source} (state : PostState current) (time : ℝ) : ℝ :=
  rawEnergy current (poseAt state time) (rawIncrement current (occupiedAt state time))-state.energy

theorem price_at_zero {current : NativeCurrent source} (state : PostState current) : priceAt state 0 = 0 := by
  simp only [priceAt,pose_at_zero,occupied_at_zero,PostState.energy,PostState.rawC,sub_self]

theorem price_at_actual {current : NativeCurrent source} (state : PostState current) :
    priceAt state state.time = energyPrice state := by
  simp only [priceAt,pose_at_actual,occupied_at_actual,energyPrice]

theorem price_at_continuous {current : NativeCurrent source} (state : PostState current) :
    ContinuousAt (priceAt state) 0 := (energy_at_continuous state).sub continuousAt_const

theorem pose_at_ready_eventually {current : NativeCurrent source} (state : PostState current) :
    ∀ᶠ time in 𝓝 (0 : ℝ), Body.ready (poseAt state time) := by
  have separated := CPS1PositivePulse.pairwise_positions_eventually state.pose
    (fun time node => (endRowsAt state time node).position)
    (fun node _ => end_position_at_continuous state node)
    (by simpa only [end_rows_at_zero,Body.ready] using state.ready)
  simpa only [poseAt,Body.ready,rowPose,List.pairwise_map] using separated

def refinedAt {current : NativeCurrent source} (state : PostState current) (index : Nat) : PostState current :=
  {state with index := state.index+index}

theorem refined_at_time {current : NativeCurrent source} (state : PostState current) (index : Nat) :
    (refinedAt state index).time = state.time*(1/2 : ℝ)^index := by
  simp only [refinedAt,PostState.time,CPS1ReactiveFieldDynamics.dyadicTime,pow_add,mul_assoc]

theorem refined_pose_actual {current : NativeCurrent source} (state : PostState current) (index : Nat) :
    poseAt state (refinedAt state index).time = endPose (refinedAt state index) := by
  exact pose_at_actual (refinedAt state index)

theorem refined_price_actual {current : NativeCurrent source} (state : PostState current) (index : Nat) :
    priceAt state (refinedAt state index).time = energyPrice (refinedAt state index) := by
  exact price_at_actual (refinedAt state index)

theorem positive_reserve_paid_refinement {current : NativeCurrent source} (state : PostState current)
    (positive : 0 < state.reserve) :
    ∃ index, Body.ready (endPose (refinedAt state index)) ∧
      energyPrice (refinedAt state index) < (refinedAt state index).reserve := by
  have budget : ∀ᶠ time in 𝓝 (0 : ℝ), priceAt state time < state.reserve :=
    (price_at_continuous state).eventually_lt continuousAt_const (by
      rw [price_at_zero]
      exact positive)
  have powers : Tendsto (fun index : Nat => state.time*(1/2 : ℝ)^index) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using! (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)))
  obtain ⟨index,ready,affordable⟩ := (powers.eventually ((pose_at_ready_eventually state).and budget)).exists
  rw [← refined_at_time state index,refined_pose_actual] at ready
  rw [← refined_at_time state index,refined_price_actual] at affordable
  exact ⟨index,ready,affordable⟩

theorem ready_refinement_exists {current : NativeCurrent source} (state : PostState current) :
    ∃ index, Body.ready (endPose (refinedAt state index)) := by
  have powers : Tendsto (fun index : Nat => state.time*(1/2 : ℝ)^index) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using! (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)))
  obtain ⟨index,ready⟩ := (powers.eventually (pose_at_ready_eventually state)).exists
  rw [← refined_at_time state index,refined_pose_actual] at ready
  exact ⟨index,ready⟩

def RefinementPaidGuard {current : NativeCurrent source} (state : PostState current) (index : Nat) : Prop :=
  Body.ready (endPose (refinedAt state index)) ∧
    energyPrice (refinedAt state index) ≤ (refinedAt state index).reserve

/-- The ordinal is generated from the original checker. Every earlier
literal event is unpaid; a zero source account is tested at its first ready pose. -/
inductive PaidSourceDisposition {current : NativeCurrent source} (state : PostState current) : Type
  | paid (index : Nat) (event : PaidStep (refinedAt state index))
      (earlierUnpaid : ∀ earlier < index, ¬ RefinementPaidGuard state earlier)
  | energyShortage (index : Nat) (zero : state.reserve = 0)
      (ready : Body.ready (endPose (refinedAt state index)))
      (shortage : ¬ energyPrice (refinedAt state index) ≤ (refinedAt state index).reserve)
      (earlierUnpaid : ∀ earlier < index, ¬ RefinementPaidGuard state earlier)

def source_generated_paid_disposition {current : NativeCurrent source} (state : PostState current) :
    PaidSourceDisposition state := by
  classical
  by_cases positive : 0 < state.reserve
  · have existsPaid : ∃ index, RefinementPaidGuard state index := by
      obtain ⟨index,ready,budget⟩ := positive_reserve_paid_refinement state positive
      exact ⟨index,ready,budget.le⟩
    let index := Nat.find existsPaid
    have selected := Nat.find_spec existsPaid
    exact .paid index ⟨post_full_smooth _,selected.1,selected.2⟩
      (fun earlier smaller => Nat.find_min existsPaid smaller)
  · have zero : state.reserve = 0 := le_antisymm (le_of_not_gt positive) state.nonnegative
    let existsReady := ready_refinement_exists state
    let index := Nat.find existsReady
    have ready : Body.ready (endPose (refinedAt state index)) := Nat.find_spec existsReady
    have earlierUnpaid : ∀ earlier < index, ¬ RefinementPaidGuard state earlier := by
      intro earlier smaller earlierPaid
      exact Nat.find_min existsReady smaller earlierPaid.1
    by_cases budget : energyPrice (refinedAt state index) ≤ (refinedAt state index).reserve
    · exact .paid index ⟨post_full_smooth _,ready,budget⟩ earlierUnpaid
    · exact .energyShortage index zero ready budget earlierUnpaid

def PaidSourceDisposition.index {current : NativeCurrent source} {state : PostState current}
    (generated : PaidSourceDisposition state) : Nat :=
  match generated with
  | .paid index .. => index
  | .energyShortage index .. => index

def PaidSourceDisposition.result {current : NativeCurrent source} {state : PostState current}
    (generated : PaidSourceDisposition state) : NativePhysicalResult (refinedAt state generated.index) :=
  match generated with
  | .paid _ event _ => .paid event
  | .energyShortage _ _ ready shortage _ => .energyShortage (post_full_smooth _) ready shortage

def PaidSourceDisposition.next {current : NativeCurrent source} {state : PostState current}
    (generated : PaidSourceDisposition state) : PostState current := generated.result.next

theorem PaidSourceDisposition.actual {current : NativeCurrent source} {state : PostState current}
    (generated : PaidSourceDisposition state) :
    advanceNative (refinedAt state generated.index) = generated.result := by
  cases generated with
  | paid index event earlierUnpaid => exact advance_native_paid _ event.smooth event.ready event.budget
  | energyShortage index zero ready shortage earlierUnpaid => exact advance_native_energy_shortage _ (post_full_smooth _) ready shortage

theorem PaidSourceDisposition.unpaid_prefix {current : NativeCurrent source} {state : PostState current}
    (generated : PaidSourceDisposition state) :
    ∀ earlier < generated.index, ¬ RefinementPaidGuard state earlier := by
  cases generated with
  | paid index event earlierUnpaid => exact earlierUnpaid
  | energyShortage index zero ready shortage earlierUnpaid => exact earlierUnpaid

theorem PaidSourceDisposition.complete_next {current : NativeCurrent source} {state : PostState current}
    (generated : PaidSourceDisposition state) :
    generated.next.energy+generated.next.reserve = state.energy+state.reserve ∧
    Matrix.trace (generated.next.occupied*generated.next.occupied.conjTranspose) = (electronCount source.nodes : ℂ) ∧
    generated.next.pose.map (fun node => node.particle) = state.pose.map (fun node => node.particle) ∧
    CPS1ElectronicEvolution.fields (rawField current) generated.next.rawC =
      CPS1ElectronicEvolution.fields (basis current) generated.next.occupied :=
  ⟨native_result_account generated.result,native_result_ne generated.result,
    native_result_particles generated.result,native_result_fields generated.result⟩

theorem paid_source_refinement_cannot_pay_clock {current : NativeCurrent source} (state : PostState current)
    (index : Nat) (event : PaidStep (refinedAt state index)) :
    event.after ≠ refineState (refinedAt state index) := by
  intro equal
  have elapsed := congrArg PostState.elapsed equal
  have clock := paid_clock event
  simp only [refineState] at elapsed
  exact (ne_of_gt clock) elapsed

theorem zero_source_shortage_cannot_pay {current : NativeCurrent source} (state : PostState current)
    (index : Nat) (zero : state.reserve = 0)
    (positive : 0 < energyPrice (refinedAt state index))
    (event : PaidStep (refinedAt state index)) : False := by
  have budget := event.budget
  change energyPrice (refinedAt state index) ≤ state.reserve at budget
  rw [zero] at budget
  exact (not_le_of_gt positive) budget

end
end CPS1MaterialIncidence.NativeBodyFunctionProbe
