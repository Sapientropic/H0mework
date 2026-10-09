import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Translation

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

abbrev NuclearIndex (state : CPS1ElectronicSource.State frame) := Fin state.geometry.nuclei.length
abbrev ModeIndex (state : CPS1ElectronicSource.State frame) :=
  Fin (spatialModes frame state.geometry.originJoint)
abbrev PrimitiveIndex (state : CPS1ElectronicSource.State frame) :=
  (NuclearIndex state × ModeIndex state) × Bool

def nucleus (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) : CPS1AtomicDynamics.Body.Node :=
  state.geometry.nuclei.get index

def address (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) : CPS1AtomicDynamics.Charged.Address :=
  (nucleus state index).particle.address

def position (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) : Point :=
  Geometry.nucleusPosition (nucleus state index)

def inertia (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) : ℝ :=
  (nucleus state index).row.inertia

def momentum (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) : CPS1AtomicDynamics.Body.Point :=
  (nucleus state index).row.momentum

def velocity (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) : Point :=
  fun axis => momentum state index axis / inertia state index

def centreLine (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) (time : ℝ) : Point :=
  position state index + time • velocity state index

theorem nucleus_mem (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) :
    nucleus state index ∈ state.geometry.nuclei := List.get_mem _ _

theorem actual_nuclei_complete (state : CPS1ElectronicSource.State frame) :
    List.ofFn (nucleus state) = state.geometry.nuclei := List.ofFn_get _

theorem actual_nucleus_index (state : CPS1ElectronicSource.State frame) (node : CPS1AtomicDynamics.Body.Node)
    (member : node ∈ state.geometry.nuclei) : ∃ index : NuclearIndex state, nucleus state index = node := by
  exact List.mem_iff_get.mp member

theorem source_row (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) :
    address state index = (state.geometry.nuclei.get index).particle.address ∧
    position state index = Geometry.nucleusPosition (state.geometry.nuclei.get index) ∧
    inertia state index = (state.geometry.nuclei.get index).row.inertia ∧
    momentum state index = (state.geometry.nuclei.get index).row.momentum := ⟨rfl,rfl,rfl,rfl⟩

theorem centre_line_initial (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) :
    centreLine state index 0 = position state index := by simp only [centreLine,zero_smul,add_zero]

theorem source_centre_derivative (state : CPS1ElectronicSource.State frame) (index : NuclearIndex state) (time : ℝ) :
    HasDerivAt (centreLine state index) (velocity state index) time := by
  have motion : HasDerivAt (fun t : ℝ => t • velocity state index) (velocity state index) time := by
    simpa only [one_smul,id_eq] using! (hasDerivAt_id time).smul_const (velocity state index)
  simpa only [centreLine,zero_add] using! (hasDerivAt_const time (position state index)).add motion

end
end CPS1MolecularFrame
