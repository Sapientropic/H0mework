import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRawRegularity
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeBodyFunction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace CPS1MaterialIncidence.NativeBodyFunctionProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange NativeAmmoniaDynamics CPS1ElectronicSource
open NativeResumableProbe NativeBodyProbe NativePrepareNextProbe NativePrepareBinding
open NativePaidEvent NativeCPContinuationProbe NativeAdoptionProbe
open scoped BigOperators Matrix Topology

private theorem finite_list_differentiable {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {I : Type} (items : List I) (f : I → ℝ → K)
    (smooth : ∀ item ∈ items, DifferentiableAt ℝ (f item) 0) :
    DifferentiableAt ℝ (fun amount => (items.map (fun item => f item amount)).sum) 0 := by
  induction items with
  | nil => exact differentiableAt_const 0
  | cons item rest ih =>
      simpa only [List.map_cons,List.sum_cons] using!
        (smooth item List.mem_cons_self).add (ih (fun other held => smooth other (List.mem_cons_of_mem _ held)))

private theorem potential_displaced_differentiable (nodes : List Body.Node) (ready : Body.ready nodes)
    (direction : Charged.Address → Body.Point) :
    DifferentiableAt ℝ (fun amount => Body.potential (nodes.map (Field.perturb direction amount))) 0 := by
  induction nodes with
  | nil => exact differentiableAt_const 0
  | cons first rest ih =>
      have separated := List.pairwise_cons.mp ready
      have pairs := finite_list_differentiable rest
        (fun second amount => Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
          (Field.perturb direction amount first).row.position (Field.perturb direction amount second).row.position)
        (fun second held => (Field.pair_line_derivative first second direction (separated.1 second held)).differentiableAt)
      simpa only [List.map_cons,Field.potential_cons,List.map_map,Function.comp_def,Field.perturb] using!
        pairs.add (ih separated.2)

private theorem nuclear_energy_differentiable (pose : List Body.Node) (ready : Body.ready pose)
    (address : Charged.Address) (axis : Fin 3) :
    DifferentiableAt ℝ (fun amount => Body.energy (nucleusNodes (displaced pose address axis amount))) 0 := by
  have kinetic : ∀ amount, Body.kinetic ((nucleusNodes pose).map (Field.perturb (axisDirection address axis) amount)) =
      Body.kinetic (nucleusNodes pose) := by
    intro amount
    simp only [Body.kinetic,List.map_map,Function.comp_def,Field.perturb]
  have potential := potential_displaced_differentiable (nucleusNodes pose) (ready.filter _) (axisDirection address axis)
  simpa only [nucleus_nodes_displaced,Body.energy,kinetic] using!
    (differentiableAt_const (Body.kinetic (nucleusNodes pose))).add potential

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw}

/-- Every raw matrix entry includes both stored and source-local orbitals.
Only the nuclear argument moves; the admitted full raw field stays fixed. -/
theorem full_raw_core_differentiable (current : NativeCurrent source) (pose : List Body.Node)
    (address : Charged.Address) (axis : Fin 3) (i j : RawIndex current) :
    DifferentiableAt ℝ (fun amount => rawCore current (displaced pose address axis amount) i j) 0 := by
  simp only [rawCore,nucleus_nodes_displaced,List.map_map,Function.comp_def]
  apply DifferentiableAt.add (differentiableAt_const _)
  apply finite_list_differentiable
  intro node _
  change DifferentiableAt ℝ (fun amount => -(node.particle.charge : ℂ) *
    ∑ spin : Bool, rawNuclearIntegral current i j spin
      (Geometry.nucleusPosition (Field.perturb (axisDirection address axis) amount node))) 0
  have selection : DifferentiableAt ℝ
      (fun amount => Geometry.nucleusPosition (Field.perturb (axisDirection address axis) amount node)) 0 := by
    apply differentiableAt_pi.mpr
    intro coordinate
    simpa only [Geometry.nucleusPosition,Field.perturb,PiLp.add_apply,PiLp.smul_apply] using!
      (differentiableAt_const (node.row.position coordinate)).add
        ((differentiableAt_id (𝕜 := ℝ) (x := (0 : ℝ))).mul_const ((axisDirection address axis) node.particle.address coordinate))
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro spin _
  exact (full_raw_nuclear_differentiable current i j spin _).comp 0 selection

theorem full_raw_trace_differentiable (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ)
    (address : Charged.Address) (axis : Fin 3) :
    DifferentiableAt ℝ (fun amount =>
      (Matrix.trace (rawCore current (displaced pose address axis amount) * rawDensity current occupied)).re) 0 := by
  apply Complex.reCLM.differentiableAt.comp 0
  unfold Matrix.trace Matrix.diag
  apply DifferentiableAt.fun_sum
  intro i _
  simp only [Matrix.mul_apply]
  apply DifferentiableAt.fun_sum
  intro j _
  exact (full_raw_core_differentiable current pose address axis i j).mul_const _

theorem full_raw_energy_differentiable (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ)
    (ready : Body.ready pose) (address : Charged.Address) (axis : Fin 3) :
    DifferentiableAt ℝ (fun amount => rawEnergy current (displaced pose address axis amount) occupied) 0 := by
  have nuclear := nuclear_energy_differentiable pose ready address axis
  have electronic := full_raw_trace_differentiable current pose occupied address axis
  simpa only [rawEnergy] using! (nuclear.add electronic).add (differentiableAt_const _)

theorem post_full_smooth {current : NativeCurrent source} (state : PostState current) : FullSmooth state := by
  intro node _ axis
  exact full_raw_energy_differentiable current state.pose (rawIncrement current (halfCoordinates state))
    state.ready node.particle.address axis

theorem post_nondifferentiable_impossible {current : NativeCurrent source} (state : PostState current)
    (failed : ¬ FullSmooth state) : False := failed (post_full_smooth state)

section Body
variable {oldBody : CPS1BiologicalUpdate.Body} {receipt : CPS1BiologicalUpdate.LocalRepairReceipt oldBody}
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  {returned : NativePrepareNext paid continuation} {germ : NativeOriginGerm returned.occurrence}

theorem native_body_full_smooth (body : NativeBody receipt returned germ) : FullSmooth body.current.state :=
  post_full_smooth body.current.state

theorem body_function_nondifferentiable_impossible (body : NativeBody receipt returned germ)
    (failed : ¬ FullSmooth body.current.state) : False := failed (native_body_full_smooth body)

end Body
end
end CPS1MaterialIncidence.NativeBodyFunctionProbe
