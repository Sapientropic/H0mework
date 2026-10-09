import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Fields
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Coulomb

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource ContinuousLinearMap
open scoped BigOperators InnerProductSpace
variable {frame : CPS1Recycling.Frame}

def pointLinear : Point →ₗ[ℝ] CPS1AtomicDynamics.Body.Point where
  toFun := euclideanPoint
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar point; rfl

def pointDifferential : Point →L[ℝ] CPS1AtomicDynamics.Body.Point :=
  pointLinear.toContinuousLinearMap

theorem point_differential_apply (point : Point) : pointDifferential point = euclideanPoint point := rfl

def nuclearPositionMap (source : CPS1ElectronicSource.State frame)
    (index : CPS1MolecularFrame.NuclearIndex source) :
    NuclearConfiguration source →L[ℝ] CPS1AtomicDynamics.Body.Point :=
  pointDifferential.comp (ContinuousLinearMap.proj index)

theorem nuclear_position_map_apply (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (index : CPS1MolecularFrame.NuclearIndex source) :
    nuclearPositionMap source index positions = euclideanPoint (positions index) := rfl

def nuclearNodeAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (index : CPS1MolecularFrame.NuclearIndex source) : CPS1AtomicDynamics.Body.Node :=
  {CPS1MolecularFrame.nucleus source index with row :=
    {(CPS1MolecularFrame.nucleus source index).row with position := euclideanPoint (positions index)}}

def nuclearNodesAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :
    List CPS1AtomicDynamics.Body.Node := List.ofFn (nuclearNodeAt source positions)

def energySourceMomenta (source : CPS1ElectronicSource.State frame) : NuclearConfiguration source :=
  fun index axis => CPS1MolecularFrame.momentum source index axis

theorem energy_source_momenta_euclidean (source : CPS1ElectronicSource.State frame)
    (index : CPS1MolecularFrame.NuclearIndex source) :
    euclideanPoint (energySourceMomenta source index) = CPS1MolecularFrame.momentum source index := by
  ext axis
  rfl

def nuclearKineticAt (source : CPS1ElectronicSource.State frame) (momenta : NuclearConfiguration source) : ℝ :=
  ((List.finRange source.geometry.nuclei.length).map (fun index =>
    CPS1AtomicDynamics.Coulomb.kinetic (CPS1MolecularFrame.inertia source index)
      (euclideanPoint (momenta index)))).sum

def nuclearEnergyAt (source : CPS1ElectronicSource.State frame)
    (positions momenta : NuclearConfiguration source) : ℝ :=
  nuclearKineticAt source momenta + CPS1AtomicDynamics.Body.potential (nuclearNodesAt source positions)

theorem nuclear_node_source (source : CPS1ElectronicSource.State frame)
    (index : CPS1MolecularFrame.NuclearIndex source) :
    nuclearNodeAt source (sourcePositions source) index = CPS1MolecularFrame.nucleus source index := rfl

theorem nuclear_nodes_source (source : CPS1ElectronicSource.State frame) :
    nuclearNodesAt source (sourcePositions source) = source.geometry.nuclei := by
  change List.ofFn (CPS1MolecularFrame.nucleus source) = source.geometry.nuclei
  exact CPS1MolecularFrame.actual_nuclei_complete source

theorem nuclear_kinetic_source (source : CPS1ElectronicSource.State frame) :
    nuclearKineticAt source (energySourceMomenta source) = CPS1AtomicDynamics.Body.kinetic source.geometry.nuclei := by
  have same := congrArg CPS1AtomicDynamics.Body.kinetic (CPS1MolecularFrame.actual_nuclei_complete source)
  simpa only [CPS1AtomicDynamics.Body.kinetic,List.ofFn_eq_map,List.map_map,Function.comp_def,
    nuclearKineticAt,CPS1MolecularFrame.inertia,energy_source_momenta_euclidean,CPS1MolecularFrame.momentum] using same

theorem nuclear_energy_source (source : CPS1ElectronicSource.State frame) :
    nuclearEnergyAt source (sourcePositions source) (energySourceMomenta source) = source.geometry.nuclearEnergy := by
  rw [nuclearEnergyAt,nuclear_kinetic_source,nuclear_nodes_source]
  rfl

theorem nuclear_node_whole (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (index : CPS1MolecularFrame.NuclearIndex source) :
    (nuclearNodeAt source positions index).particle = (CPS1MolecularFrame.nucleus source index).particle ∧
      (nuclearNodeAt source positions index).row.inertia = CPS1MolecularFrame.inertia source index ∧
      (nuclearNodeAt source positions index).row.momentum = CPS1MolecularFrame.momentum source index :=
  ⟨rfl,rfl,rfl⟩

theorem differentiable_list_sum {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} (indices : List ι) (fields : ι → X → ℝ) (current : X)
    (generated : ∀ index ∈ indices, DifferentiableAt ℝ (fields index) current) :
    DifferentiableAt ℝ (fun next => (indices.map (fun index => fields index next)).sum) current := by
  induction indices with
  | nil => exact differentiableAt_const 0
  | cons index rest ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (generated index (List.mem_cons_self)).add (ih (fun other member => generated other (List.mem_cons_of_mem _ member)))

def nuclearPairDifferential (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first second : CPS1MolecularFrame.NuclearIndex source) : NuclearConfiguration source →L[ℝ] ℝ :=
  (-(innerSL ℝ (CPS1AtomicDynamics.Coulomb.pairForce
    ((CPS1MolecularFrame.nucleus source first).particle.charge : ℝ)
    ((CPS1MolecularFrame.nucleus source second).particle.charge : ℝ)
    (nuclearPositionMap source first positions - nuclearPositionMap source second positions) 0))).comp
      (nuclearPositionMap source first - nuclearPositionMap source second)

theorem nuclear_pair_hasFDerivAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first second : CPS1MolecularFrame.NuclearIndex source)
    (distinct : (nuclearNodeAt source positions first).row.position ≠
      (nuclearNodeAt source positions second).row.position) :
    HasFDerivAt (fun next => CPS1AtomicDynamics.Coulomb.pairEnergy
      ((CPS1MolecularFrame.nucleus source first).particle.charge : ℝ)
      ((CPS1MolecularFrame.nucleus source second).particle.charge : ℝ)
      (euclideanPoint (next first)) (euclideanPoint (next second)))
      (nuclearPairDifferential source positions first second) positions := by
  have separated : nuclearPositionMap source first positions - nuclearPositionMap source second positions ≠ 0 :=
    sub_ne_zero.mpr distinct
  have generated := (CPS1AtomicDynamics.Coulomb.pair_energy_derivative
    ((CPS1MolecularFrame.nucleus source first).particle.charge : ℝ)
    ((CPS1MolecularFrame.nucleus source second).particle.charge : ℝ)
    (nuclearPositionMap source first positions - nuclearPositionMap source second positions) 0 separated).comp
    positions (nuclearPositionMap source first - nuclearPositionMap source second).hasFDerivAt
  simpa only [Function.comp_def,CPS1AtomicDynamics.Coulomb.pairEnergy,sub_zero,sub_apply,
    nuclear_position_map_apply,nuclearPairDifferential] using! generated

theorem nuclear_potential_indices_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (indices : List (CPS1MolecularFrame.NuclearIndex source))
    (separated : (indices.map (nuclearNodeAt source positions)).Pairwise
      (fun first second => first.row.position ≠ second.row.position)) :
    DifferentiableAt ℝ (fun next => CPS1AtomicDynamics.Body.potential
      (indices.map (nuclearNodeAt source next))) positions := by
  induction indices with
  | nil => exact differentiableAt_const 0
  | cons first rest ih =>
    have pairwise := List.pairwise_cons.mp separated
    have head : ∀ second ∈ rest, (nuclearNodeAt source positions first).row.position ≠
        (nuclearNodeAt source positions second).row.position := by
      intro second member
      exact pairwise.1 _ (List.mem_map_of_mem member)
    have firstPart := differentiable_list_sum rest
      (fun second (next : NuclearConfiguration source) => CPS1AtomicDynamics.Coulomb.pairEnergy
        ((CPS1MolecularFrame.nucleus source first).particle.charge : ℝ)
        ((CPS1MolecularFrame.nucleus source second).particle.charge : ℝ)
        (euclideanPoint (next first)) (euclideanPoint (next second))) positions
      (fun second member => (nuclear_pair_hasFDerivAt source positions first second (head second member)).differentiableAt)
    have restPart := ih pairwise.2
    simpa only [List.map_cons,CPS1AtomicDynamics.Body.potential,List.map_map,
      Function.comp_def,nuclearNodeAt] using! firstPart.add restPart

theorem nuclear_potential_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source positions)) :
    DifferentiableAt ℝ (fun next => CPS1AtomicDynamics.Body.potential (nuclearNodesAt source next)) positions := by
  have generated := nuclear_potential_indices_differentiable source positions (List.finRange source.geometry.nuclei.length)
  have separated : (List.map (nuclearNodeAt source positions) (List.finRange source.geometry.nuclei.length)).Pairwise
      (fun first second => first.row.position ≠ second.row.position) := by
    simpa only [nuclearNodesAt,List.ofFn_eq_map,CPS1AtomicDynamics.Body.ready] using ready
  simpa only [nuclearNodesAt,List.ofFn_eq_map] using generated separated

theorem nuclear_kinetic_differentiable (source : CPS1ElectronicSource.State frame)
    (momenta : NuclearConfiguration source) : DifferentiableAt ℝ (nuclearKineticAt source) momenta := by
  apply differentiable_list_sum
  intro index _
  have generated := ((nuclearPositionMap source index).hasFDerivAt (x := momenta)).norm_sq
  have squared : DifferentiableAt ℝ (fun next : NuclearConfiguration source =>
      ‖nuclearPositionMap source index next‖^2) momenta := generated.differentiableAt
  have divided := squared.const_smul ((2 * CPS1MolecularFrame.inertia source index)⁻¹)
  simpa only [CPS1AtomicDynamics.Coulomb.kinetic,nuclear_position_map_apply,div_eq_mul_inv,
    smul_eq_mul,mul_comm] using! divided

def nuclearEnergyDifferential (source : CPS1ElectronicSource.State frame)
    (positions momenta : NuclearConfiguration source) :
    (NuclearConfiguration source × NuclearConfiguration source) →L[ℝ] ℝ :=
  fderiv ℝ (fun point => nuclearEnergyAt source point.1 point.2) (positions,momenta)

theorem nuclear_energy_hasFDerivAt (source : CPS1ElectronicSource.State frame)
    (positions momenta : NuclearConfiguration source) (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source positions)) :
    HasFDerivAt (fun point : NuclearConfiguration source × NuclearConfiguration source =>
      nuclearEnergyAt source point.1 point.2) (nuclearEnergyDifferential source positions momenta) (positions,momenta) := by
  have kinetic := (nuclear_kinetic_differentiable source momenta).comp (positions,momenta)
    (differentiableAt_snd : DifferentiableAt ℝ (Prod.snd :
      NuclearConfiguration source × NuclearConfiguration source → NuclearConfiguration source) (positions,momenta))
  have potential := (nuclear_potential_differentiable source positions ready).comp (positions,momenta)
    (differentiableAt_fst : DifferentiableAt ℝ (Prod.fst :
      NuclearConfiguration source × NuclearConfiguration source → NuclearConfiguration source) (positions,momenta))
  exact (kinetic.add potential).hasFDerivAt

end
end CPS1Deformation
