import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualRootPaidDisposition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeFunctionalNextProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1BiologicalUpdate CPS1PhosphorylExchange
open NativePaidEvent NativePaidPositive

variable {frame : CPS1Recycling.Frame}

def attachedJoint (frame : CPS1Recycling.Frame) :=
  CPS1EnzymeBath.Joint.attach frame (sourceJoint frame) .carbamoylPhosphate

def prepareGuard (frame : CPS1Recycling.Frame) : CPS1Deformation.Species frame :=
  .retained (.retained (.retained (.retained (.guard (.body (.missingRow (.nucleus 0)))))))

def prepareReaction (frame : CPS1Recycling.Frame) : CPS1Deformation.Reaction frame :=
  .retained (.retained (.retained (.retained (.prepare (attachedJoint frame)))))

theorem gather_without_rows (graph : CPS1AtomicSource.Graph.Molecule) (nonempty : graph.atoms ≠ []) :
    Body.gather (Charged.particles graph) [] = .error (.missingRow (.nucleus 0)) := by
  rcases graph with ⟨atoms,bonds,dangling⟩
  cases atoms with
  | nil => exact (nonempty rfl).elim
  | cons atom rest => rfl

theorem attached_atoms_nonempty (frame : CPS1Recycling.Frame) :
    (CPS1EnzymeBath.Joint.descriptorGraph frame (attachedJoint frame)).atoms ≠ [] := by
  intro empty
  have allEmpty := List.map_eq_nil_iff.mp empty
  change CPS1EnzymeBath.Joint.atoms frame (attachedJoint frame) = [] at allEmpty
  unfold CPS1EnzymeBath.Joint.atoms at allEmpty
  have bathEmpty := (List.append_eq_nil_iff.mp allEmpty).2
  have components : (attachedJoint frame).components = [⟨0,.carbamoylPhosphate⟩] := rfl
  rw [components] at bathEmpty
  have templateEmpty : (CPS1EnzymeBath.Primary.template .carbamoylPhosphate).atoms = [] := by
    simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_eq_nil_iff] using bathEmpty
  have present : (CPS1EnzymeBath.Primary.template .carbamoylPhosphate).atoms ≠ [] := by decide +kernel
  exact present templateEmpty

theorem template_prepare_cut (frame : CPS1Recycling.Frame) :
    CPS1ElectronicSource.State.fromJoint? frame (attachedJoint frame) =
      .error (.body (.missingRow (.nucleus 0))) := by
  have gathered := gather_without_rows (CPS1EnzymeBath.Joint.descriptorGraph frame (attachedJoint frame))
    (attached_atoms_nonempty frame)
  have rows : (attachedJoint frame).rows = [] := rfl
  simp only [CPS1ElectronicSource.State.fromJoint?,CPS1ElectronicSource.Geometry.fromJoint?,
    CPS1EnzymeBath.Joint.particles,rows,gathered]
  rfl

theorem prepare_reactants (frame : CPS1Recycling.Frame) :
    CPS1Deformation.Reaction.reactants frame (prepareReaction frame) =
      [wrappedJoint (attachedJoint frame),prepareGuard frame] := by
  simp only [prepareReaction,CPS1Deformation.Reaction.reactants,CPS1MolecularFrame.Reaction.reactants,
    CPS1Following.Reaction.reactants,CPS1QuantumNuclear.Reaction.reactants,CPS1ElectronicSource.Reaction.reactants,
    template_prepare_cut,CPS1ElectronicSource.guards,List.map_append,List.map_cons,List.map_nil]
  rfl

end
end CPS1MaterialIncidence.NativeFunctionalNextProbe
