import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Translation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Geometry

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Matrix
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.SpatialControl

/-- The literal shift retains the coefficients generated at the original centre0. -/
def movingValue (centre : Point) (n : Nat) (mode : Fin n) (jet : Fin 3 → Nat) (x : Point) : ℂ :=
  CPS1ElectronicSource.spatialValue 0 n mode jet (x-centre)

theorem moving_value_coefficients (centre : Point) (n : Nat) (mode : Fin n) (jet : Fin 3 → Nat) (x : Point) :
    movingValue centre n mode jet x = ∑ primitive : Fin n,
      CPS1ElectronicSource.coefficients 0 n primitive mode *
        CPS1ElectronicSource.orbitalValue centre primitive.val jet x := by
  simp only [movingValue,CPS1ElectronicSource.spatialValue,CPS1ElectronicSource.orbitalValue,sub_zero]

theorem moving_value_memLp (centre : Point) (n : Nat) (mode : Fin n) (jet : Fin 3 → Nat) :
    MemLp (movingValue centre n mode jet) 2 (volume : Measure Point) :=
  (CPS1ElectronicSource.spatial_memLp 0 n mode jet).comp_measurePreserving (sub_preserving centre)

theorem moving_spatial_exact (centre : Point) (n : Nat) (mode : Fin n) (jet : Fin 3 → Nat) :
    (moving_value_memLp centre n mode jet).toLp (movingValue centre n mode jet) =
      movingSpatial centre n mode jet := rfl

theorem moving_jet_inner (centre : Point) (n : Nat) (first second : Fin n) (leftJet rightJet : Fin 3 → Nat) :
    inner ℂ (movingSpatial centre n first leftJet) (movingSpatial centre n second rightJet) =
      inner ℂ (CPS1ElectronicSource.spatialField 0 n first leftJet)
        (CPS1ElectronicSource.spatialField 0 n second rightJet) :=
  (spatialTranslate centre).inner_map_map _ _

def movingNuclearIntegral (centre : Point) (n : Nat) (first second : Fin n) (nucleus : Point) : ℂ :=
  ∫ x : Point, (SourceCoulomb.kernel (x-nucleus) : ℂ) *
    star (movingValue centre n first 0 x) * movingValue centre n second 0 x

def movingPairIntegral (centre : Point) (n : Nat) (first second third fourth : Fin n) : ℂ :=
  ∫ z : Point × Point, (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
    star (movingValue centre n first 0 z.1) * movingValue centre n second 0 z.1 *
    star (movingValue centre n third 0 z.2) * movingValue centre n fourth 0 z.2
    ∂(volume : Measure Point).prod volume

theorem moving_nuclear_integral (centre : Point) (n : Nat) (first second : Fin n) (nucleus : Point) :
    movingNuclearIntegral centre n first second nucleus =
      CPS1ElectronicSource.nuclearIntegral 0 n first second (nucleus-centre) := by
  let integrand : Point → ℂ := fun x => (SourceCoulomb.kernel (x-(nucleus-centre)) : ℂ) *
    star (CPS1ElectronicSource.spatialValue 0 n first 0 x) * CPS1ElectronicSource.spatialValue 0 n second 0 x
  have paid := (sub_preserving centre).integral_comp (measurableEmbedding_subRight centre) integrand
  calc
    movingNuclearIntegral centre n first second nucleus = ∫ x : Point, integrand (x-centre) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        have same : (x-centre)-(nucleus-centre) = x-nucleus := by abel
        simp only [movingValue,integrand,same]
    _ = _ := paid

theorem moving_pair_integral (centre : Point) (n : Nat) (first second third fourth : Fin n) :
    movingPairIntegral centre n first second third fourth = CPS1ElectronicSource.pairIntegral 0 n first second third fourth := by
  let integrand : Point × Point → ℂ := fun z => (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
    star (CPS1ElectronicSource.spatialValue 0 n first 0 z.1) * CPS1ElectronicSource.spatialValue 0 n second 0 z.1 *
    star (CPS1ElectronicSource.spatialValue 0 n third 0 z.2) * CPS1ElectronicSource.spatialValue 0 n fourth 0 z.2
  have preserving := (sub_preserving centre).prod (sub_preserving centre)
  have embedding : MeasurableEmbedding (Prod.map (fun x : Point => x-centre) (fun x : Point => x-centre)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.subRight centre) (MeasurableEquiv.subRight centre)).measurableEmbedding
  have paid := preserving.integral_comp embedding integrand
  calc
    movingPairIntegral centre n first second third fourth =
        ∫ z : Point × Point, integrand ((z.1-centre),(z.2-centre)) ∂(volume : Measure Point).prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        have same : (z.1-centre)-(z.2-centre) = z.1-z.2 := by abel
        simp only [movingValue,integrand,same]
    _ = _ := paid


theorem moving_nuclear_integrable (centre : Point) (n : Nat) (first second : Fin n) (nucleus : Point)
    (leftJet rightJet : Fin 3 → Nat) :
    Integrable (fun x : Point => (SourceCoulomb.kernel (x-nucleus) : ℂ) *
      star (movingValue centre n first leftJet x) * movingValue centre n second rightJet x)
      (volume : Measure Point) := by
  have shifted := (sub_preserving centre).integrable_comp_of_integrable
    (CPS1ElectronicSource.normalized_nuclear_integrable 0 n first second (nucleus-centre) leftJet rightJet)
  convert! shifted using 1
  funext x
  have same : (x-centre)-(nucleus-centre) = x-nucleus := by abel
  simp only [Function.comp_def,movingValue,same,Algebra.smul_def]
  rw [RCLike.algebraMap_eq_ofReal]
  exact mul_assoc _ _ _

theorem moving_pair_integrable (centre : Point) (n : Nat) (first second third fourth : Fin n) :
    Integrable (fun z : Point × Point => (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
      star (movingValue centre n first 0 z.1) * movingValue centre n second 0 z.1 *
      star (movingValue centre n third 0 z.2) * movingValue centre n fourth 0 z.2)
      ((volume : Measure Point).prod volume) := by
  have shifted := ((sub_preserving centre).prod (sub_preserving centre)).integrable_comp_of_integrable
    (CPS1ElectronicSource.normalized_pair_integrable 0 n first second third fourth)
  convert! shifted using 1
  funext z
  have same : (z.1-centre)-(z.2-centre) = z.1-z.2 := by abel
  simp only [Function.comp_def,Prod.map,movingValue,same]

variable {frame : CPS1Recycling.Frame}

def centrePoint (state : CPS1ElectronicSource.State frame) : Point := fun axis => centre state axis

def physicalKinetic (state : CPS1ElectronicSource.State frame)
    (first second : CPS1ElectronicSource.SpatialIndex state.geometry) : ℂ :=
  ((1/(2*state.geometry.electronInertia) : ℝ) : ℂ) * ∑ axis : Fin 3,
    inner ℂ (movingSpatial (centrePoint state) (CPS1ElectronicSource.spatialModes frame state.geometry.originJoint) first
      (SourceGaussianModel.raise 0 axis))
      (movingSpatial (centrePoint state) (CPS1ElectronicSource.spatialModes frame state.geometry.originJoint) second
        (SourceGaussianModel.raise 0 axis))

def physicalAttraction (state : CPS1ElectronicSource.State frame)
    (first second : CPS1ElectronicSource.SpatialIndex state.geometry) : ℂ :=
  (state.geometry.nuclei.map (fun nucleus => -(nucleus.particle.charge : ℂ) *
    movingNuclearIntegral (centrePoint state) (CPS1ElectronicSource.spatialModes frame state.geometry.originJoint)
      first second (CPS1ElectronicSource.Geometry.nucleusPosition nucleus))).sum

def physicalCore (state : CPS1ElectronicSource.State frame) :
    Matrix (CPS1ElectronicSource.SpinIndex state.geometry) (CPS1ElectronicSource.SpinIndex state.geometry) ℂ :=
  fun first second => if first.2 = second.2 then physicalKinetic state first.1 second.1 +
    physicalAttraction state first.1 second.1 else 0

def physicalTwoBody (state : CPS1ElectronicSource.State frame)
    (first second third fourth : CPS1ElectronicSource.SpinIndex state.geometry) : ℂ :=
  if first.2 = third.2 ∧ second.2 = fourth.2 then
    movingPairIntegral (centrePoint state) (CPS1ElectronicSource.spatialModes frame state.geometry.originJoint)
      first.1 third.1 second.1 fourth.1 else 0

def physicalFock (state : CPS1ElectronicSource.State frame) :
    Matrix (CPS1ElectronicSource.SpinIndex state.geometry) (CPS1ElectronicSource.SpinIndex state.geometry) ℂ :=
  fun first third => physicalCore state first third + ∑ second, ∑ fourth,
    state.density fourth second * (physicalTwoBody state first second third fourth-physicalTwoBody state first second fourth third)

def physicalElectronicEnergy (state : CPS1ElectronicSource.State frame) : ℝ :=
  (Matrix.trace (physicalCore state * state.density)).re + (1/2) *
    (∑ first, ∑ second, ∑ third, ∑ fourth, state.density third first * state.density fourth second *
      (physicalTwoBody state first second third fourth-physicalTwoBody state first second fourth third)).re

def physicalEnergy (state : CPS1ElectronicSource.State frame) : ℝ :=
  state.geometry.nuclearEnergy+physicalElectronicEnergy state

theorem physical_kinetic_exact (state : CPS1ElectronicSource.State frame)
    (first second : CPS1ElectronicSource.SpatialIndex state.geometry) :
    physicalKinetic state first second = CPS1ElectronicSource.kinetic (relativeGeometry state) first second := by
  unfold physicalKinetic CPS1ElectronicSource.kinetic
  rw [relative_electron_inertia]
  simp only [moving_jet_inner]
  rfl

theorem relative_nucleus_position (state : CPS1ElectronicSource.State frame) (node : Node) :
    CPS1ElectronicSource.Geometry.nucleusPosition (relativeNode (centre state) node) =
      CPS1ElectronicSource.Geometry.nucleusPosition node-centrePoint state := rfl

theorem physical_attraction_exact (state : CPS1ElectronicSource.State frame)
    (first second : CPS1ElectronicSource.SpatialIndex state.geometry) :
    physicalAttraction state first second = CPS1ElectronicSource.attraction (relativeGeometry state) first second := by
  unfold physicalAttraction CPS1ElectronicSource.attraction
  rw [relative_nuclei,List.map_map]
  simp only [Function.comp_def,relative_particle,moving_nuclear_integral,relative_nucleus_position]
  rfl

theorem physical_core_exact (state : CPS1ElectronicSource.State frame) :
    physicalCore state = CPS1ElectronicSource.core (relativeGeometry state) := by
  ext first second
  simp only [physicalCore,CPS1ElectronicSource.core,physical_kinetic_exact,physical_attraction_exact]

theorem physical_two_body_exact (state : CPS1ElectronicSource.State frame)
    (first second third fourth : CPS1ElectronicSource.SpinIndex state.geometry) :
    physicalTwoBody state first second third fourth = CPS1ElectronicSource.twoBody (relativeGeometry state) first second third fourth := by
  simp only [physicalTwoBody,CPS1ElectronicSource.twoBody,moving_pair_integral]
  rfl

theorem physical_fock_exact (state : CPS1ElectronicSource.State frame) :
    physicalFock state = (relativeState state).hamiltonian := by
  ext first third
  simp only [physicalFock,CPS1ElectronicSource.State.hamiltonian,CPS1ElectronicSource.fock,
    physical_core_exact,physical_two_body_exact]
  rfl

theorem pair_energy_relative (offset : BodyPoint) (first second : Node) :
    CPS1AtomicDynamics.Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
      (relativeNode offset first).row.position (relativeNode offset second).row.position =
      CPS1AtomicDynamics.Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
        first.row.position second.row.position := by
  have same : (first.row.position-offset)-(second.row.position-offset) = first.row.position-second.row.position := by abel
  simp only [relative_position,CPS1AtomicDynamics.Coulomb.pairEnergy,same]

theorem potential_relative (offset : BodyPoint) (nodes : List Node) :
    CPS1AtomicDynamics.Body.potential (nodes.map (relativeNode offset)) = CPS1AtomicDynamics.Body.potential nodes := by
  induction nodes with
  | nil => rfl
  | cons first rest ih =>
    change ((rest.map (relativeNode offset)).map (fun second => CPS1AtomicDynamics.Coulomb.pairEnergy
      (first.particle.charge : ℝ) (second.particle.charge : ℝ)
      (relativeNode offset first).row.position second.row.position)).sum +
      CPS1AtomicDynamics.Body.potential (rest.map (relativeNode offset)) =
      (rest.map (fun second => CPS1AtomicDynamics.Coulomb.pairEnergy (first.particle.charge : ℝ)
        (second.particle.charge : ℝ) first.row.position second.row.position)).sum + CPS1AtomicDynamics.Body.potential rest
    rw [ih]
    simp only [List.map_map,Function.comp_def,relative_particle,pair_energy_relative]

theorem body_energy_relative (offset : BodyPoint) (nodes : List Node) :
    CPS1AtomicDynamics.Body.energy (nodes.map (relativeNode offset)) = CPS1AtomicDynamics.Body.energy nodes := by
  unfold CPS1AtomicDynamics.Body.energy CPS1AtomicDynamics.Body.kinetic
  rw [potential_relative]
  simp only [List.map_map,Function.comp_def,relative_inertia,relative_momentum]

theorem relative_nuclear_energy (state : CPS1ElectronicSource.State frame) :
    (relativeGeometry state).nuclearEnergy = state.geometry.nuclearEnergy := by
  unfold CPS1ElectronicSource.Geometry.nuclearEnergy
  rw [relative_nuclei,body_energy_relative]

theorem physical_electronic_energy_exact (state : CPS1ElectronicSource.State frame) :
    physicalElectronicEnergy state = CPS1ElectronicSource.electronicEnergy (relativeGeometry state) state.density := by
  simp only [physicalElectronicEnergy,CPS1ElectronicSource.electronicEnergy,physical_core_exact,physical_two_body_exact]
  rfl

theorem physical_energy_exact (state : CPS1ElectronicSource.State frame) : physicalEnergy state = energy state := by
  unfold physicalEnergy energy CPS1ElectronicSource.State.energy CPS1ElectronicSource.totalEnergy
  change state.geometry.nuclearEnergy+physicalElectronicEnergy state =
    (relativeGeometry state).nuclearEnergy+CPS1ElectronicSource.electronicEnergy (relativeGeometry state) state.density
  rw [relative_nuclear_energy,physical_electronic_energy_exact]

end
end CPS1Following
