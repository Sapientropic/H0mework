import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Atoms

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel
variable {frame : CPS1Recycling.Frame}

/-- Each finite index keeps its actual nucleus, source mode, and spin. -/
def rawJet (state : CPS1ElectronicSource.State frame) (index : PrimitiveIndex state) (jet : Fin 3 → Nat) : SpinSpace :=
  PiLp.single 2 index.2 (orbitalField (position state index.1.1) index.1.2.val jet)

def rawJetCurve (state : CPS1ElectronicSource.State frame) (time : ℝ) (index : PrimitiveIndex state)
    (jet : Fin 3 → Nat) : SpinSpace :=
  PiLp.single 2 index.2 (orbitalField (centreLine state index.1.1 time) index.1.2.val jet)

def rawJetRate (state : CPS1ElectronicSource.State frame) (time : ℝ) (index : PrimitiveIndex state)
    (jet : Fin 3 → Nat) : SpinSpace :=
  -(∑ axis : Fin 3, velocity state index.1.1 axis • rawJetCurve state time index (raise jet axis))

def rawField (state : CPS1ElectronicSource.State frame) (index : PrimitiveIndex state) : SpinSpace := rawJet state index 0

def rawCurve (state : CPS1ElectronicSource.State frame) (time : ℝ) (index : PrimitiveIndex state) : SpinSpace :=
  rawJetCurve state time index 0

def rawRate (state : CPS1ElectronicSource.State frame) (time : ℝ) (index : PrimitiveIndex state) : SpinSpace :=
  rawJetRate state time index 0

theorem raw_jet_initial (state : CPS1ElectronicSource.State frame) (index : PrimitiveIndex state) (jet : Fin 3 → Nat) :
    rawJetCurve state 0 index jet = rawJet state index jet := by
  simp only [rawJetCurve,rawJet,centre_line_initial]

theorem raw_curve_initial (state : CPS1ElectronicSource.State frame) : rawCurve state 0 = rawField state := by
  funext index
  exact raw_jet_initial state index 0

theorem raw_jet_curve_derivative (state : CPS1ElectronicSource.State frame) (index : PrimitiveIndex state)
    (jet : Fin 3 → Nat) (time : ℝ) :
    HasDerivAt (fun t => rawJetCurve state t index jet) (rawJetRate state time index jet) time := by
  have source := CPS1Following.primitive_curve_derivative index.1.2.val jet
    (centreLine state index.1.1) (velocity state index.1.1) time (source_centre_derivative state index.1.1 time)
  have generated := (CPS1Following.spinInjection index.2).hasFDerivAt.comp_hasDerivAt time source
  simpa only [Function.comp_def,rawJetCurve,rawJetRate,CPS1Following.spin_injection_apply,
    map_neg,map_sum,map_smul] using! generated

theorem raw_curve_derivative (state : CPS1ElectronicSource.State frame) (index : PrimitiveIndex state) (time : ℝ) :
    HasDerivAt (fun t => rawCurve state t index) (rawRate state time index) time :=
  raw_jet_curve_derivative state index 0 time

theorem raw_field_source (state : CPS1ElectronicSource.State frame) (index : PrimitiveIndex state) :
    rawField state index = PiLp.single 2 index.2
      (orbitalField (Geometry.nucleusPosition (state.geometry.nuclei.get index.1.1)) index.1.2.val 0) := rfl

theorem raw_rate_source (state : CPS1ElectronicSource.State frame) (index : PrimitiveIndex state) (time : ℝ) :
    rawRate state time index = -(∑ axis : Fin 3,
      ((state.geometry.nuclei.get index.1.1).row.momentum axis / (state.geometry.nuclei.get index.1.1).row.inertia) •
        rawJetCurve state time index (raise 0 axis)) := rfl

theorem all_nuclei_field_source (state : CPS1ElectronicSource.State frame) (node : CPS1AtomicDynamics.Body.Node)
    (member : node ∈ state.geometry.nuclei) (mode : ModeIndex state) (spin : Bool) :
    ∃ index : PrimitiveIndex state, address state index.1.1 = node.particle.address ∧
      rawField state index = PiLp.single 2 spin (orbitalField (Geometry.nucleusPosition node) mode.val 0) := by
  obtain ⟨nuclear,same⟩ := actual_nucleus_index state node member
  refine ⟨((nuclear,mode),spin),?_,?_⟩
  · change (nucleus state nuclear).particle.address = node.particle.address
    rw [same]
  · change (PiLp.single 2 spin (orbitalField (Geometry.nucleusPosition (nucleus state nuclear)) mode.val 0) : SpinSpace) = _
    rw [same]

theorem nucleus_fields_independent (state : CPS1ElectronicSource.State frame) (nuclear : NuclearIndex state) :
    LinearIndependent ℂ (fun index : ModeIndex state × Bool => rawField state ((nuclear,index.1),index.2)) := by
  have spatial : ∀ spin : Bool, LinearIndependent ℂ
      (fun mode : ModeIndex state => orbitalField (position state nuclear) mode.val 0) :=
    fun _ => orbitals_independent (position state nuclear) (spatialModes frame state.geometry.originJoint)
  have blocks : LinearIndependent ℂ (fun index : Σ _ : Bool, ModeIndex state =>
      (PiLp.single 2 index.1 (orbitalField (position state nuclear) index.2.val 0) : SpinSpace)) :=
    PiLp.linearIndependent_single (p := 2) (𝕜 := ℂ) (fun (_ : Bool) (mode : ModeIndex state) =>
      orbitalField (position state nuclear) mode.val 0) spatial
  have injective : Function.Injective (fun index : ModeIndex state × Bool =>
      (⟨index.2,index.1⟩ : Σ _ : Bool, ModeIndex state)) := by
    intro left right same
    have spin := congrArg Sigma.fst same
    have mode : left.1 = right.1 := by
      cases left
      cases right
      cases same
      rfl
    exact Prod.ext mode spin
  exact blocks.comp (fun index : ModeIndex state × Bool => ⟨index.2,index.1⟩) injective

end
end CPS1MolecularFrame
