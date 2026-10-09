import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveNuclear.Germ
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Energy

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveNuclear
noncomputable section
open CPS1ElectronicSource
open CPS1ReactiveField CPS1ReactiveField.Carried
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.Elementwise
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
variable {frame : CPS1Recycling.Frame}
variable {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}

/-- Every centre selector is a projection from this germ's generated physical Id. -/
def selectedNuclearPositions (germ : Germ root state) (p q : state.PrimitiveIndex) (id : germ.Id) :
    germ.Configuration →L[ℝ] (Fin 3 → Point) :=
  ContinuousLinearMap.pi ![
    (ContinuousLinearMap.proj (germ.primitiveId p) : germ.Configuration →L[ℝ] Point),
    (ContinuousLinearMap.proj (germ.primitiveId q) : germ.Configuration →L[ℝ] Point),
    (ContinuousLinearMap.proj id : germ.Configuration →L[ℝ] Point)]

def selectedPairPositions (germ : Germ root state) (p q r s : state.PrimitiveIndex) :
    germ.Configuration →L[ℝ] (Fin 4 → Point) :=
  ContinuousLinearMap.pi ![
    (ContinuousLinearMap.proj (germ.primitiveId p) : germ.Configuration →L[ℝ] Point),
    (ContinuousLinearMap.proj (germ.primitiveId q) : germ.Configuration →L[ℝ] Point),
    (ContinuousLinearMap.proj (germ.primitiveId r) : germ.Configuration →L[ℝ] Point),
    (ContinuousLinearMap.proj (germ.primitiveId s) : germ.Configuration →L[ℝ] Point)]

def primitiveJetAt (germ : Germ root state) (positions : germ.Configuration)
    (index : state.PrimitiveIndex) (jet : Fin 3 → Nat) : SpinSpace :=
  (germ.primitiveAt positions index).jet jet

def primitiveJetDifferential (germ : Germ root state) (positions : germ.Configuration)
    (index : state.PrimitiveIndex) (jet : Fin 3 → Nat) : germ.Configuration →L[ℝ] SpinSpace :=
  (CPS1Following.spinInjection (state.primitive index).spin).comp
    ((CPS1Deformation.orbitalJetFDeriv (state.primitive index).mode jet
      (positions (germ.primitiveId index))).comp (ContinuousLinearMap.proj (germ.primitiveId index)))

theorem primitive_jet_hasFDerivAt (germ : Germ root state) (positions : germ.Configuration)
    (index : state.PrimitiveIndex) (jet : Fin 3 → Nat) :
    HasFDerivAt (fun next => primitiveJetAt germ next index jet)
      (primitiveJetDifferential germ positions index jet) positions := by
  have projection := (ContinuousLinearMap.proj (germ.primitiveId index) :
    germ.Configuration →L[ℝ] Point).hasFDerivAt (x := positions)
  have orbital := (CPS1Deformation.orbital_jet_hasFDerivAt (state.primitive index).mode jet
    (positions (germ.primitiveId index))).comp positions projection
  have spin := (CPS1Following.spinInjection (state.primitive index).spin).hasFDerivAt.comp positions orbital
  simpa only [Function.comp_def,primitiveJetAt,Germ.primitiveAt,Primitive.jet,
    primitiveJetDifferential,CPS1Following.spin_injection_apply] using! spin

def occupiedJetAt (germ : Germ root state) (positions : germ.Configuration)
    (electron : state.ElectronIndex) (jet : Fin 3 → Nat) : SpinSpace :=
  ∑ primitive, state.occupied primitive electron • primitiveJetAt germ positions primitive jet

def occupiedJetDifferential (germ : Germ root state) (positions : germ.Configuration)
    (electron : state.ElectronIndex) (jet : Fin 3 → Nat) : germ.Configuration →L[ℝ] SpinSpace :=
  ∑ primitive, state.occupied primitive electron • primitiveJetDifferential germ positions primitive jet

theorem occupied_jet_hasFDerivAt (germ : Germ root state) (positions : germ.Configuration)
    (electron : state.ElectronIndex) (jet : Fin 3 → Nat) :
    HasFDerivAt (fun next => occupiedJetAt germ next electron jet)
      (occupiedJetDifferential germ positions electron jet) positions := by
  exact HasFDerivAt.fun_sum (u := Finset.univ) (fun primitive _ =>
    (primitive_jet_hasFDerivAt germ positions primitive jet).const_smul
      (state.occupied primitive electron))

def rawNuclearAt (germ : Germ root state) (positions : germ.Configuration)
    (p q : state.PrimitiveIndex) (spin : Bool) (id : germ.Id) : ℂ :=
  if (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin then
    CPS1MolecularFrame.primitiveNuclearIntegral (positions (germ.primitiveId p))
      (positions (germ.primitiveId q)) (state.primitive p).mode (state.primitive q).mode (positions id) 0 0
  else 0

def rawPairAt (germ : Germ root state) (positions : germ.Configuration)
    (p q r s : state.PrimitiveIndex) (spin secondSpin : Bool) : ℂ :=
  if (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin ∧
      (state.primitive r).spin = secondSpin ∧ (state.primitive s).spin = secondSpin then
    CPS1MolecularFrame.primitivePairIntegral (positions (germ.primitiveId p))
      (positions (germ.primitiveId q)) (positions (germ.primitiveId r)) (positions (germ.primitiveId s))
      (state.primitive p).mode (state.primitive q).mode (state.primitive r).mode (state.primitive s).mode 0 0 0 0
  else 0

theorem raw_nuclear_differentiable (germ : Germ root state) (positions : germ.Configuration)
    (p q : state.PrimitiveIndex) (spin : Bool) (id : germ.Id) :
    DifferentiableAt ℝ (fun next => rawNuclearAt germ next p q spin id) positions := by
  by_cases matching : (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin
  · simp only [rawNuclearAt,if_pos matching]
    have generated := (CPS1Deformation.multicentre_nuclear_hasFDerivAt
      (state.primitive p).mode (state.primitive q).mode 0 0
      (selectedNuclearPositions germ p q id positions)).comp positions
        (selectedNuclearPositions germ p q id).hasFDerivAt
    exact generated.differentiableAt
  · simp only [rawNuclearAt,if_neg matching]
    exact differentiableAt_const 0

theorem raw_pair_differentiable (germ : Germ root state) (positions : germ.Configuration)
    (p q r s : state.PrimitiveIndex) (spin secondSpin : Bool) :
    DifferentiableAt ℝ (fun next => rawPairAt germ next p q r s spin secondSpin) positions := by
  by_cases matching : (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin ∧
      (state.primitive r).spin = secondSpin ∧ (state.primitive s).spin = secondSpin
  · simp only [rawPairAt,if_pos matching]
    have generated := (CPS1Deformation.multicentre_pair_hasFDerivAt
      ![(state.primitive p).mode,(state.primitive q).mode,(state.primitive r).mode,(state.primitive s).mode]
      (fun _ => 0) (selectedPairPositions germ p q r s positions)).comp positions
        (selectedPairPositions germ p q r s).hasFDerivAt
    exact generated.differentiableAt
  · simp only [rawPairAt,if_neg matching]
    exact differentiableAt_const 0

def fieldKineticAt (germ : Germ root state) (positions : germ.Configuration)
    (i j : state.ElectronIndex) : ℂ :=
  ((1/(2*state.electronInertia) : ℝ) : ℂ)*∑ axis : Fin 3,
    inner ℂ (occupiedJetAt germ positions i (raise 0 axis)) (occupiedJetAt germ positions j (raise 0 axis))

def fieldAttractionAt (germ : Germ root state) (positions : germ.Configuration)
    (i j : state.ElectronIndex) : ℂ :=
  (List.ofFn (fun slot : Fin state.nuclei.length =>
    -((state.nuclei.get slot).particle.charge : ℂ)*
      (∑ spin : Bool, ∑ p, ∑ q, star (state.occupied p i)*state.occupied q j*
        rawNuclearAt germ positions p q spin (germ.nuclearId slot)))).sum

def fieldTwoBodyAt (germ : Germ root state) (positions : germ.Configuration)
    (i j k l : state.ElectronIndex) : ℂ :=
  ∑ spin : Bool, ∑ secondSpin : Bool, ∑ p, ∑ q, ∑ r, ∑ s,
    (star (state.occupied p i)*state.occupied q k*star (state.occupied r j)*state.occupied s l)*
      rawPairAt germ positions p q r s spin secondSpin

def fieldEnergyAt (germ : Germ root state) (positions : germ.Configuration) : ℝ :=
  (∑ i, (fieldKineticAt germ positions i i+fieldAttractionAt germ positions i i)).re+
    (1/2)*(∑ i, ∑ j, (fieldTwoBodyAt germ positions i j i j-fieldTwoBodyAt germ positions i j j i)).re

private theorem complex_list_differentiable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type*} (indices : List I) (values : I → X → ℂ) (current : X)
    (each : ∀ index ∈ indices, DifferentiableAt ℝ (values index) current) :
    DifferentiableAt ℝ (fun next => (indices.map (fun index => values index next)).sum) current := by
  induction indices with
  | nil => exact differentiableAt_const 0
  | cons index rest ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (each index List.mem_cons_self).add (ih (fun other member => each other (List.mem_cons_of_mem _ member)))

theorem field_kinetic_differentiable (germ : Germ root state) (positions : germ.Configuration)
    (i j : state.ElectronIndex) :
    DifferentiableAt ℝ (fun next => fieldKineticAt germ next i j) positions := by
  exact (DifferentiableAt.fun_sum (u := Finset.univ) (fun axis _ =>
    ((occupied_jet_hasFDerivAt germ positions i (raise 0 axis)).inner ℂ
      (occupied_jet_hasFDerivAt germ positions j (raise 0 axis))).differentiableAt)).const_mul
        ((1/(2*state.electronInertia) : ℝ) : ℂ)

theorem field_attraction_differentiable (germ : Germ root state) (positions : germ.Configuration)
    (i j : state.ElectronIndex) :
    DifferentiableAt ℝ (fun next => fieldAttractionAt germ next i j) positions := by
  have each (slot : Fin state.nuclei.length) :=
    (DifferentiableAt.fun_sum (u := Finset.univ) (fun spin _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ =>
        DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ =>
          (raw_nuclear_differentiable germ positions p q spin (germ.nuclearId slot)).const_mul
            (star (state.occupied p i)*state.occupied q j))))).const_mul
              (-((state.nuclei.get slot).particle.charge : ℂ))
  have generated := complex_list_differentiable (List.finRange state.nuclei.length)
    (fun slot next => -((state.nuclei.get slot).particle.charge : ℂ)*
      (∑ spin : Bool, ∑ p, ∑ q, star (state.occupied p i)*state.occupied q j*
        rawNuclearAt germ next p q spin (germ.nuclearId slot))) positions (fun slot _ => each slot)
  simpa only [fieldAttractionAt,List.ofFn_eq_map] using generated

theorem field_two_body_differentiable (germ : Germ root state) (positions : germ.Configuration)
    (i j k l : state.ElectronIndex) :
    DifferentiableAt ℝ (fun next => fieldTwoBodyAt germ next i j k l) positions := by
  exact DifferentiableAt.fun_sum (u := Finset.univ) (fun spin _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun secondSpin _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ =>
        DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ =>
          DifferentiableAt.fun_sum (u := Finset.univ) (fun r _ =>
            DifferentiableAt.fun_sum (u := Finset.univ) (fun s _ =>
              (raw_pair_differentiable germ positions p q r s spin secondSpin).const_mul
                (star (state.occupied p i)*state.occupied q k*star (state.occupied r j)*state.occupied s l)))))))

theorem field_energy_differentiable (germ : Germ root state) (positions : germ.Configuration) :
    DifferentiableAt ℝ (fieldEnergyAt germ) positions := by
  have core := DifferentiableAt.fun_sum (u := Finset.univ) (fun i _ =>
    (field_kinetic_differentiable germ positions i i).add (field_attraction_differentiable germ positions i i))
  have pair := DifferentiableAt.fun_sum (u := Finset.univ) (fun i _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ =>
      (field_two_body_differentiable germ positions i j i j).sub
        (field_two_body_differentiable germ positions i j j i)))
  exact (Complex.reCLM.differentiableAt.comp positions core).add
    ((Complex.reCLM.differentiableAt.comp positions pair).const_smul (1/2 : ℝ))

def nuclearPointMap (germ : Germ root state) (slot : Fin state.nuclei.length) :
    germ.Configuration →L[ℝ] CPS1AtomicDynamics.Body.Point :=
  CPS1Deformation.pointDifferential.comp (ContinuousLinearMap.proj (germ.nuclearId slot))

private theorem nuclear_pair_differentiable (germ : Germ root state) (positions : germ.Configuration)
    (first second : Fin state.nuclei.length)
    (distinct : (germ.nodeAt positions germ.momenta first).row.position ≠
      (germ.nodeAt positions germ.momenta second).row.position) :
    DifferentiableAt ℝ (fun next => CPS1AtomicDynamics.Coulomb.pairEnergy
      ((state.nuclei.get first).particle.charge : ℝ) ((state.nuclei.get second).particle.charge : ℝ)
      (euclideanPoint (next (germ.nuclearId first))) (euclideanPoint (next (germ.nuclearId second)))) positions := by
  let relative := nuclearPointMap germ first-nuclearPointMap germ second
  have nonzero : relative positions ≠ 0 := sub_ne_zero.mpr distinct
  have generated := (CPS1AtomicDynamics.Coulomb.pair_energy_derivative
    ((state.nuclei.get first).particle.charge : ℝ) ((state.nuclei.get second).particle.charge : ℝ)
    (relative positions) 0 nonzero).comp positions relative.hasFDerivAt
  simpa only [Function.comp_def,relative,nuclearPointMap,CPS1Deformation.point_differential_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,CPS1AtomicDynamics.Coulomb.pairEnergy,
    sub_zero,sub_apply] using! generated.differentiableAt

private theorem nuclear_potential_indices_differentiable (germ : Germ root state)
    (positions : germ.Configuration) (indices : List (Fin state.nuclei.length))
    (separated : (indices.map (germ.nodeAt positions germ.momenta)).Pairwise
      (fun first second => first.row.position ≠ second.row.position)) :
    DifferentiableAt ℝ (fun next => CPS1AtomicDynamics.Body.potential
      (indices.map (germ.nodeAt next germ.momenta))) positions := by
  induction indices with
  | nil => exact differentiableAt_const 0
  | cons first rest ih =>
    have pairwise := List.pairwise_cons.mp separated
    have firstPart := CPS1Deformation.differentiable_list_sum rest
      (fun second (next : germ.Configuration) => CPS1AtomicDynamics.Coulomb.pairEnergy
        ((state.nuclei.get first).particle.charge : ℝ) ((state.nuclei.get second).particle.charge : ℝ)
        (euclideanPoint (next (germ.nuclearId first))) (euclideanPoint (next (germ.nuclearId second)))) positions
      (fun second member => nuclear_pair_differentiable germ positions first second
        (pairwise.1 _ (List.mem_map_of_mem member)))
    simpa only [List.map_cons,CPS1AtomicDynamics.Body.potential,List.map_map,Function.comp_def,Germ.nodeAt]
      using! firstPart.add (ih pairwise.2)

private theorem nuclear_potential_current_differentiable (germ : Germ root state) :
    DifferentiableAt ℝ (fun next => CPS1AtomicDynamics.Body.potential
      (List.ofFn (germ.nodeAt next germ.momenta))) germ.positions := by
  have separated : ((List.finRange state.nuclei.length).map
      (germ.nodeAt germ.positions germ.momenta)).Pairwise
      (fun first second => first.row.position ≠ second.row.position) := by
    rw [show germ.nodeAt germ.positions germ.momenta = state.nuclei.get from funext germ.node_current]
    rw [← List.ofFn_eq_map,List.ofFn_get]
    exact germ.ready
  simpa only [List.ofFn_eq_map] using
    nuclear_potential_indices_differentiable germ germ.positions (List.finRange state.nuclei.length) separated

private theorem nuclear_kinetic_differentiable (germ : Germ root state) (momenta : germ.Configuration) :
    DifferentiableAt ℝ (fun next => CPS1AtomicDynamics.Body.kinetic
      (List.ofFn (germ.nodeAt germ.positions next))) momenta := by
  have generated := CPS1Deformation.differentiable_list_sum (List.finRange state.nuclei.length)
    (fun slot (next : germ.Configuration) => CPS1AtomicDynamics.Coulomb.kinetic
      (state.nuclei.get slot).row.inertia (euclideanPoint (next (germ.nuclearId slot)))) momenta
      (fun slot _ => by
        have squared := ((nuclearPointMap germ slot).hasFDerivAt (x := momenta)).norm_sq
        simpa only [CPS1AtomicDynamics.Coulomb.kinetic,nuclearPointMap,CPS1Deformation.point_differential_apply,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,div_eq_mul_inv,smul_eq_mul,mul_comm]
          using! squared.differentiableAt.const_smul ((2*(state.nuclei.get slot).row.inertia)⁻¹))
  simpa only [CPS1AtomicDynamics.Body.kinetic,List.ofFn_eq_map,List.map_map,Function.comp_def,Germ.nodeAt]
    using generated

abbrev NuclearPhase (germ : Germ root state) := germ.Configuration × germ.Configuration

def fullNuclearEnergy (germ : Germ root state) (phase : NuclearPhase germ) : ℝ :=
  germ.energy (phase,state.occupied)

private theorem snapshot_kinetic_at (germ : Germ root state) (phase : NuclearPhase germ)
    (i j : state.ElectronIndex) :
    (germ.snapshotAt (phase,state.occupied)).kinetic i j = fieldKineticAt germ phase.1 i j := rfl

private theorem snapshot_attraction_at (germ : Germ root state) (phase : NuclearPhase germ)
    (i j : state.ElectronIndex) :
    (germ.snapshotAt (phase,state.occupied)).attraction i j = fieldAttractionAt germ phase.1 i j := by
  unfold Snapshot.attraction
  change ((List.ofFn (germ.nodeAt phase.1 phase.2)).map (fun node =>
    -(node.particle.charge : ℂ)*(∑ spin : Bool, ∑ p, ∑ q,
      star (state.occupied p i)*state.occupied q j*
      (germ.snapshotAt (phase,state.occupied)).nuclearIntegral p q spin
        (Geometry.nucleusPosition node)))).sum = fieldAttractionAt germ phase.1 i j
  rw [List.map_ofFn]
  rfl

private theorem snapshot_two_body_at (germ : Germ root state) (phase : NuclearPhase germ)
    (i j k l : state.ElectronIndex) :
    (germ.snapshotAt (phase,state.occupied)).twoBody i j k l = fieldTwoBodyAt germ phase.1 i j k l := rfl

theorem full_nuclear_energy_eq (germ : Germ root state) (phase : NuclearPhase germ) :
    fullNuclearEnergy germ phase = germ.nuclearEnergy phase.1 phase.2+fieldEnergyAt germ phase.1 := by
  have core : (∑ i : state.ElectronIndex,
      ((germ.snapshotAt (phase,state.occupied)).kinetic i i+
      (germ.snapshotAt (phase,state.occupied)).attraction i i)) =
      ∑ i, (fieldKineticAt germ phase.1 i i+fieldAttractionAt germ phase.1 i i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [snapshot_kinetic_at,snapshot_attraction_at]
  have pairs : (∑ i : state.ElectronIndex, ∑ j : state.ElectronIndex,
      ((germ.snapshotAt (phase,state.occupied)).twoBody i j i j-
      (germ.snapshotAt (phase,state.occupied)).twoBody i j j i)) =
      ∑ i, ∑ j, (fieldTwoBodyAt germ phase.1 i j i j-fieldTwoBodyAt germ phase.1 i j j i) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [snapshot_two_body_at,snapshot_two_body_at]
  calc
    fullNuclearEnergy germ phase =
      CPS1AtomicDynamics.Body.energy (List.ofFn (germ.nodeAt phase.1 phase.2))+
        (∑ i : state.ElectronIndex,
          ((germ.snapshotAt (phase,state.occupied)).kinetic i i+
          (germ.snapshotAt (phase,state.occupied)).attraction i i)).re+
        (1/2)*(∑ i : state.ElectronIndex, ∑ j : state.ElectronIndex,
          ((germ.snapshotAt (phase,state.occupied)).twoBody i j i j-
          (germ.snapshotAt (phase,state.occupied)).twoBody i j j i)).re := rfl
    _ = CPS1AtomicDynamics.Body.energy (List.ofFn (germ.nodeAt phase.1 phase.2))+
        (∑ i, (fieldKineticAt germ phase.1 i i+fieldAttractionAt germ phase.1 i i)).re+
        (1/2)*(∑ i, ∑ j,
          (fieldTwoBodyAt germ phase.1 i j i j-fieldTwoBodyAt germ phase.1 i j j i)).re :=
      congrArg₂ (fun core pair : ℂ =>
        CPS1AtomicDynamics.Body.energy (List.ofFn (germ.nodeAt phase.1 phase.2))+
        core.re+(1/2)*pair.re) core pairs
    _ = germ.nuclearEnergy phase.1 phase.2+fieldEnergyAt germ phase.1 := by
      unfold Germ.nuclearEnergy fieldEnergyAt
      ring

private theorem nuclear_kinetic_other_position (germ : Germ root state) (phase : NuclearPhase germ) :
    CPS1AtomicDynamics.Body.kinetic (List.ofFn (germ.nodeAt phase.1 phase.2)) =
      CPS1AtomicDynamics.Body.kinetic (List.ofFn (germ.nodeAt germ.positions phase.2)) := by
  unfold CPS1AtomicDynamics.Body.kinetic
  rw [List.map_ofFn,List.map_ofFn]
  rfl

private theorem nuclear_potential_other_momentum_indices (germ : Germ root state)
    (positions first second : germ.Configuration) (indices : List (Fin state.nuclei.length)) :
    CPS1AtomicDynamics.Body.potential (indices.map (germ.nodeAt positions first)) =
      CPS1AtomicDynamics.Body.potential (indices.map (germ.nodeAt positions second)) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [List.map_cons,CPS1AtomicDynamics.Field.potential_cons]
    rw [ih]
    simp only [List.map_map,Function.comp_def,Germ.nodeAt]

private theorem nuclear_potential_other_momentum (germ : Germ root state) (phase : NuclearPhase germ) :
    CPS1AtomicDynamics.Body.potential (List.ofFn (germ.nodeAt phase.1 phase.2)) =
      CPS1AtomicDynamics.Body.potential (List.ofFn (germ.nodeAt phase.1 germ.momenta)) := by
  simpa only [List.ofFn_eq_map] using nuclear_potential_other_momentum_indices germ
    phase.1 phase.2 germ.momenta (List.finRange state.nuclei.length)

def nuclearDifferential (germ : Germ root state) : NuclearPhase germ →L[ℝ] ℝ :=
  fderiv ℝ (fullNuclearEnergy germ) (germ.positions,germ.momenta)

theorem full_nuclear_hasFDerivAt (germ : Germ root state) :
    HasFDerivAt (fullNuclearEnergy germ) (nuclearDifferential germ) (germ.positions,germ.momenta) := by
  have kinetic := (nuclear_kinetic_differentiable germ germ.momenta).comp
    (germ.positions,germ.momenta)
      ((ContinuousLinearMap.snd ℝ germ.Configuration germ.Configuration).hasFDerivAt
        (x := (germ.positions,germ.momenta))).differentiableAt
  have potential := (nuclear_potential_current_differentiable germ).comp
    (germ.positions,germ.momenta)
      ((ContinuousLinearMap.fst ℝ germ.Configuration germ.Configuration).hasFDerivAt
        (x := (germ.positions,germ.momenta))).differentiableAt
  have electronic := (field_energy_differentiable germ germ.positions).comp
    (germ.positions,germ.momenta)
      ((ContinuousLinearMap.fst ℝ germ.Configuration germ.Configuration).hasFDerivAt
        (x := (germ.positions,germ.momenta))).differentiableAt
  have generated : DifferentiableAt ℝ (fullNuclearEnergy germ) (germ.positions,germ.momenta) := by
    apply ((kinetic.add potential).add electronic).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun phase => by
      rw [full_nuclear_energy_eq,Germ.nuclearEnergy,CPS1AtomicDynamics.Body.energy,
        nuclear_kinetic_other_position,nuclear_potential_other_momentum]
      rfl
  exact generated.hasFDerivAt

/-- The force consumes the derivative of the full original E, including every
moving primitive attraction/pair/kinetic term. It is generated, never an input. -/
def nuclearForce (germ : Germ root state) (id : germ.Id) (axis : Fin 3) : ℝ :=
  -(nuclearDifferential germ (Pi.single id (Pi.single axis 1),0))

theorem full_nuclear_line (germ : Germ root state) (direction : NuclearPhase germ) :
    HasDerivAt (fun time : ℝ => fullNuclearEnergy germ
      ((germ.positions,germ.momenta)+time • direction)) (nuclearDifferential germ direction) 0 := by
  have line : HasDerivAt (fun time : ℝ => (germ.positions,germ.momenta)+time • direction) direction 0 := by
    simpa only [one_smul,id_eq,zero_add,Pi.add_apply] using!
      (hasDerivAt_const (0 : ℝ) (germ.positions,germ.momenta)).add
        ((hasDerivAt_id (0 : ℝ)).smul_const direction)
  have mother : HasFDerivAt (fullNuclearEnergy germ) (nuclearDifferential germ)
      ((germ.positions,germ.momenta)+(0 : ℝ) • direction) := by
    simpa only [zero_smul,add_zero] using full_nuclear_hasFDerivAt germ
  exact mother.comp_hasDerivAt 0 line

def occupiedDifferential (germ : Germ root state) : germ.Coefficients →L[ℝ] ℝ :=
  CPS1ReactiveFieldDynamics.Polynomial.occupiedDifferential
    (CPS1ReactiveFieldDynamics.rawCore state) (CPS1ReactiveFieldDynamics.rawTensor state) state.occupied

theorem full_occupied_hasFDerivAt (germ : Germ root state) :
    HasFDerivAt (fun coefficients : germ.Coefficients =>
      germ.energy ((germ.positions,germ.momenta),coefficients))
      (occupiedDifferential germ) state.occupied := by
  have same : (fun coefficients : germ.Coefficients =>
      germ.energy ((germ.positions,germ.momenta),coefficients)) =
      fun coefficients => (CPS1ReactiveFieldDynamics.withOccupation state coefficients).energy := by
    funext coefficients
    rw [Germ.energy,germ.coefficients_current_square]
  rw [same]
  exact CPS1ReactiveFieldDynamics.actual_energy_hasFDerivAt state state.occupied

theorem full_occupied_line (germ : Germ root state) (direction : germ.Coefficients) :
    HasDerivAt (fun time : ℝ => germ.energy
      ((germ.positions,germ.momenta),state.occupied+time • direction))
      (2*(Matrix.trace (state.occupied.conjTranspose*CPS1ReactiveFieldDynamics.rawFock state*direction)).re) 0 := by
  simpa only [Germ.energy,germ.coefficients_current_square] using
    CPS1ReactiveFieldDynamics.actual_energy_line state direction

end
end CPS1ReactiveNuclear
