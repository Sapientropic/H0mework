import H0mework.Versions.X.Fock.CopyGraph.TimeModelRestore

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev ExistingModel (depth : Nat) (index : Index depth) :=
  SourceGeneratedActionWords.Model (fun _ : Unit => SourceJointClockGraph.action.toLinearMap)
    (SourceCopyGraph.recover depth index).toLinearMap ()

abbrev modelPoint (depth : Nat) (index : Index depth) :=
  SourceGeneratedActionWords.projection (fun _ : Unit => SourceJointClockGraph.action.toLinearMap)
    (SourceCopyGraph.recover depth index).toLinearMap ()

abbrev modelStep (depth : Nat) (index : Index depth) :=
  SourceGeneratedActionWords.advance (fun _ : Unit => SourceJointClockGraph.action.toLinearMap)
    (SourceCopyGraph.recover depth index).toLinearMap () ()

def modelPhases (depth : Nat) (index : Index depth) : ExistingModel depth index →ₗ[ℂ] Packet depth index :=
  LinearMap.pi fun phase => SourceGeneratedActionWords.readout
    (fun _ : Unit => SourceJointClockGraph.action.toLinearMap) (SourceCopyGraph.recover depth index).toLinearMap ()
    (List.replicate phase.val ())

def modelRestore (depth : Nat) (index : Index depth) (value : ExistingModel depth index) : SourceJointClockGraph.Carrier :=
  restore depth index (modelPhases depth index value)

theorem model_phases_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    modelPhases depth index (modelPoint depth index value) = phases depth index value := by
  funext phase
  simp only [modelPhases, LinearMap.pi_apply, modelPoint, SourceGeneratedActionWords.readout_source]
  rw [phase_source, ← time_word]
  rfl

theorem model_restore_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    modelRestore depth index (modelPoint depth index value) = value := by
  rw [modelRestore, model_phases_source, restore_source]

theorem model_projection_restore (depth : Nat) (index : Index depth) (value : ExistingModel depth index) :
    modelPoint depth index (modelRestore depth index value) = value := by
  refine Submodule.Quotient.induction_on _ value fun source => ?_
  exact congrArg (modelPoint depth index) (model_restore_source depth index source)

theorem model_phases_next (depth : Nat) (index : Index depth) (value : ExistingModel depth index) :
    modelPhases depth index (modelStep depth index value) = next depth index (modelPhases depth index value) := by
  refine Submodule.Quotient.induction_on _ value fun source => ?_
  change modelPhases depth index (SourceGeneratedActionWords.advance _ _ _ _ (modelPoint depth index source)) =
    next depth index (modelPhases depth index (modelPoint depth index source))
  rw [SourceGeneratedActionWords.advance_source]
  change modelPhases depth index (modelPoint depth index (SourceJointClockGraph.action source)) =
    next depth index (modelPhases depth index (modelPoint depth index source))
  rw [model_phases_source, model_phases_source, next_source]

theorem model_restore_next (depth : Nat) (index : Index depth) (value : ExistingModel depth index) :
    modelRestore depth index (modelStep depth index value) = SourceJointClockGraph.action (modelRestore depth index value) := by
  refine Submodule.Quotient.induction_on _ value fun source => ?_
  change modelRestore depth index (SourceGeneratedActionWords.advance _ _ _ _ (modelPoint depth index source)) =
    SourceJointClockGraph.action (modelRestore depth index (modelPoint depth index source))
  rw [SourceGeneratedActionWords.advance_source]
  change modelRestore depth index (modelPoint depth index (SourceJointClockGraph.action source)) =
    SourceJointClockGraph.action (modelRestore depth index (modelPoint depth index source))
  rw [model_restore_source, model_restore_source]

theorem phases_injective (depth : Nat) (index : Index depth) : Function.Injective (phases depth index) :=
  Function.LeftInverse.injective (restore_source depth index)

theorem model_fibre (depth : Nat) (index : Index depth) (left right : SourceJointClockGraph.Carrier) :
    modelPoint depth index left = modelPoint depth index right ↔ phases depth index left = phases depth index right := by
  constructor
  · intro same
    have observed := congrArg (modelPhases depth index) same
    simpa only [model_phases_source] using observed
  · intro same
    exact congrArg (modelPoint depth index) (phases_injective depth index same)

theorem phase_native (depth : Nat) (index : Index depth) (runtime : LivingRuntimeState process)
    (phase : Fin (index.val + 1)) :
    phases depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))) phase =
      SourceCopyGraph.recover depth index
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance phase.val)))) := by
  rw [phase_source, time_native]

theorem model_native_next (depth : Nat) (index : Index depth) (runtime : LivingRuntimeState process) :
    modelStep depth index (modelPoint depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime)))) =
      modelPoint depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next))) := by
  change SourceGeneratedActionWords.advance _ _ _ _ (SourceGeneratedActionWords.projection _ _ _ _) = _
  rw [SourceGeneratedActionWords.advance_source]
  exact congrArg (modelPoint depth index) (SourceJointClockGraph.native_next runtime)

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
