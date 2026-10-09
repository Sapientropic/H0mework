import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Energy

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveField.Carried
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
variable {frame : CPS1Recycling.Frame}

inductive PrimitiveOrigin
  | legacy (address : CPS1AtomicDynamics.Charged.Address)
  | reactive (origin : CPS1AddressedHydrolysis.Origin)
  deriving DecidableEq

structure Primitive where
  origin : PrimitiveOrigin
  centre : Point
  mode : Nat
  spin : Bool

def Primitive.jet (source : Primitive) (jet : Fin 3 → Nat) : SpinSpace :=
  PiLp.single 2 source.spin (orbitalField source.centre source.mode jet)

/-- A stored source expansion, including every occupied field already produced.
The public source entry and continuation generate these coefficients internally. -/
structure Snapshot where
  PrimitiveIndex : Type
  primitiveFinite : Fintype PrimitiveIndex
  primitiveDecidable : DecidableEq PrimitiveIndex
  ElectronIndex : Type
  electronFinite : Fintype ElectronIndex
  electronDecidable : DecidableEq ElectronIndex
  primitive : PrimitiveIndex → Primitive
  occupied : Matrix PrimitiveIndex ElectronIndex ℂ
  nuclei : List CPS1AtomicDynamics.Body.Node
  waterOrigins : List CPS1AddressedHydrolysis.Origin
  electronInertia : ℝ
  reserve : ℝ

attribute [instance] Snapshot.primitiveFinite Snapshot.primitiveDecidable Snapshot.electronFinite Snapshot.electronDecidable

def Snapshot.jet (state : Snapshot) (slot : state.ElectronIndex) (jet : Fin 3 → Nat) : SpinSpace :=
  ∑ primitive, state.occupied primitive slot • (state.primitive primitive).jet jet
def Snapshot.fields (state : Snapshot) : state.ElectronIndex → SpinSpace := fun slot => state.jet slot 0
def Snapshot.Good (state : Snapshot) : Prop := Orthonormal ℂ state.fields
def Snapshot.Ne (state : Snapshot) : Nat := Fintype.card state.ElectronIndex

def Snapshot.nuclearIntegral (state : Snapshot) (p q : state.PrimitiveIndex) (spin : Bool) (nuclear : Point) : ℂ :=
  if (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin then
    CPS1MolecularFrame.primitiveNuclearIntegral (state.primitive p).centre (state.primitive q).centre
      (state.primitive p).mode (state.primitive q).mode nuclear 0 0 else 0
def Snapshot.pairIntegral (state : Snapshot) (p q r s : state.PrimitiveIndex) (spin secondSpin : Bool) : ℂ :=
  if (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin ∧
      (state.primitive r).spin = secondSpin ∧ (state.primitive s).spin = secondSpin then
    CPS1MolecularFrame.primitivePairIntegral (state.primitive p).centre (state.primitive q).centre
      (state.primitive r).centre (state.primitive s).centre (state.primitive p).mode (state.primitive q).mode
      (state.primitive r).mode (state.primitive s).mode 0 0 0 0 else 0
def Snapshot.attraction (state : Snapshot) (i j : state.ElectronIndex) : ℂ :=
  (state.nuclei.map (fun nuclear => -(nuclear.particle.charge : ℂ)*
    (∑ spin : Bool, ∑ p, ∑ q, star (state.occupied p i)*state.occupied q j*
      state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear)))).sum
def Snapshot.kinetic (state : Snapshot) (i j : state.ElectronIndex) : ℂ :=
  ((1/(2*state.electronInertia) : ℝ) : ℂ)*
    ∑ axis : Fin 3, inner ℂ (state.jet i (raise 0 axis)) (state.jet j (raise 0 axis))
def Snapshot.twoBody (state : Snapshot) (i j k l : state.ElectronIndex) : ℂ :=
  ∑ spin : Bool, ∑ secondSpin : Bool, ∑ p, ∑ q, ∑ r, ∑ s,
    (star (state.occupied p i)*state.occupied q k*star (state.occupied r j)*state.occupied s l)*
      state.pairIntegral p q r s spin secondSpin
def Snapshot.energy (state : Snapshot) : ℝ :=
  CPS1AtomicDynamics.Body.energy state.nuclei+
    (∑ i, (state.kinetic i i+state.attraction i i)).re+(1/2)*
      (∑ i, ∑ j, (state.twoBody i j i j-state.twoBody i j j i)).re
def Snapshot.account (state : Snapshot) : ℝ := state.energy+state.reserve
def Snapshot.reprice (state : Snapshot) (reserve : ℝ) : Snapshot := {state with reserve := reserve}

theorem reprice_fields (state : Snapshot) (reserve : ℝ) : (state.reprice reserve).fields = state.fields := rfl
theorem reprice_energy (state : Snapshot) (reserve : ℝ) : (state.reprice reserve).energy = state.energy := rfl

def sourceNuclearParticle {current : Occurrence frame} (source : Inlet current)
    (nuclear : NuclearIndex source.body) : CPS1AddressedReactiveJoint.Particle :=
  (primitive_source current.ingress source.body source.actual
    ((nuclear,⟨0,by unfold modes; omega⟩),false)).choose

theorem source_nuclear_particle {current : Occurrence frame} (source : Inlet current)
    (nuclear : NuclearIndex source.body) :
    sourceNuclearParticle source nuclear ∈ CPS1AddressedReactiveJoint.particles source.body.atoms ∧
    (nucleus source.body nuclear).particle = (sourceNuclearParticle source nuclear).readout ∧
    CPS1AddressedReactiveJoint.Rows.row? source.body.sourceRows (sourceNuclearParticle source nuclear).address =
      some (nucleus source.body nuclear).row := by
  exact (primitive_source current.ingress source.body source.actual
    ((nuclear,⟨0,by unfold modes; omega⟩),false)).choose_spec |>.imp_right (fun paid => ⟨paid.1,paid.2.1⟩)

def bodyOrigin {current : Occurrence frame} (source : Inlet current) (nuclear : NuclearIndex source.body) :
    CPS1AddressedHydrolysis.Origin := (sourceNuclearParticle source nuclear).address.origin

def initialPrimitive {current : Occurrence frame} (source : Inlet current) : CommonPrimitive source → Primitive
  | .inl old => ⟨.legacy (CPS1MolecularFrame.nucleus source.old.reference old.1.1).particle.address,
      source.old.positions old.1.1,old.1.2.val,old.2⟩
  | .inr added => ⟨.reactive (bodyOrigin source added.1.1),position source.body added.1.1,added.1.2.val,added.2⟩

@[reducible] def initial {current : Occurrence frame} (state : Material current) : Snapshot :=
  ⟨CommonPrimitive state.source,inferInstance,inferInstance,OccupiedIndex state.source,inferInstance,inferInstance,
    initialPrimitive state.source,occupiedCoefficient state.source,commonNuclei state.source,
    (waterAtoms state.source).map CPS1AddressedHydrolysis.Atom.origin,
    state.source.old.reference.geometry.electronInertia,state.reserve⟩

theorem initial_jet {current : Occurrence frame} (state : Material current)
    (slot : OccupiedIndex state.source) (jet : Fin 3 → Nat) :
    (initial state).jet slot jet = occupiedJet state.source slot jet := by
  apply Finset.sum_congr rfl
  intro primitive _
  cases primitive <;> rfl

theorem initial_fields {current : Occurrence frame} (state : Material current) :
    (initial state).fields = occupiedFields state.source := by
  funext slot
  exact (initial_jet state slot 0).trans (occupied_jet_fields state.source slot)

theorem initial_good {current : Occurrence frame} (state : Material current) : (initial state).Good := by
  rw [Snapshot.Good,initial_fields]
  exact occupied_orthonormal state.source

theorem initial_energy {current : Occurrence frame} (state : Material current) :
    (initial state).energy = energy state.source := by
  classical
  have centres (index : CommonPrimitive state.source) :
      (initialPrimitive state.source index).centre = commonCentre state.source index := by cases index <;> rfl
  have modes (index : CommonPrimitive state.source) :
      (initialPrimitive state.source index).mode = commonMode state.source index := by cases index <;> rfl
  have spins (index : CommonPrimitive state.source) :
      (initialPrimitive state.source index).spin = commonSpin state.source index := by cases index <;> rfl
  have nuclearKernel (p q : CommonPrimitive state.source) (spin : Bool) (point : Point) :
      (initial state).nuclearIntegral p q spin point = commonNuclearIntegral state.source p q spin point := by
    dsimp only [Snapshot.nuclearIntegral,initial,commonNuclearIntegral]
    rw [centres,centres,modes,modes,spins,spins]
  have pairKernel (p q r s : CommonPrimitive state.source) (spin secondSpin : Bool) :
      (initial state).pairIntegral p q r s spin secondSpin = commonPairIntegral state.source p q r s spin secondSpin := by
    dsimp only [Snapshot.pairIntegral,initial,commonPairIntegral]
    rw [centres,centres,centres,centres,modes,modes,modes,modes,spins,spins,spins,spins]
  have kineticPart (i j : OccupiedIndex state.source) : (initial state).kinetic i j = kinetic state.source i j := by
    unfold Snapshot.kinetic kinetic
    simp only [initial_jet]
  have attractionPart (i j : OccupiedIndex state.source) : (initial state).attraction i j = attraction state.source i j := by
    unfold Snapshot.attraction attraction nuclearIntegral
    simp only [nuclearKernel]
  have pairPart (i j k l : OccupiedIndex state.source) : (initial state).twoBody i j k l = twoBody state.source i j k l := by
    unfold Snapshot.twoBody twoBody pairIntegral
    simp only [pairKernel]
  simp only [Snapshot.energy,kineticPart,attractionPart,pairPart,energy,electronicEnergy]
  change CPS1AtomicDynamics.Body.energy (commonNuclei state.source)+_+_ = _
  ring

end
end CPS1ReactiveField.Carried
