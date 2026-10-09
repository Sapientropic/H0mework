import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Runtime.LoadActionRuntime

/-! # The actual load history pays its complete binding-accounted free-energy debit

The fixed facade installs both numerical accounts and their source-paid balance.
Its existing reachability recursor transports the local law; no new future history
or repeated environment preparation is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source

noncomputable section

theorem loadRuntime_freeEnergyBalance (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadBindingAccountedFreeEnergy (loadCurrentState runtime.tick.next.state.current) -
      loadBindingAccountedFreeEnergy (loadCurrentState runtime.state.current) =
        -(loadEntropyProduction (loadCurrentState runtime.tick.next.state.current) -
          loadEntropyProduction (loadCurrentState runtime.state.current)) :=
  loadStateNext_freeEnergyBalance (loadCurrentState runtime.state.current)

theorem loadRuntime_freeEnergy_is_installed (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadRuntimeFacade.readoutAt runtime .freeEnergy =
      (.inl ⟨PUnit.unit,
        (loadFreeEnergyRead (loadCurrentState runtime.state.current),
          loadFreeEnergyRead (loadCurrentState runtime.tick.next.state.current))⟩ :
        SourceNativeProjectionFiberAt loadProjectionLaw .freeEnergy
          (loadEmitted runtime.state.current)) := rfl

theorem loadRuntime_freeEnergyBalance_is_installed (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadRuntimeFacade.readoutAt runtime .freeEnergyBalance =
      (.inl ⟨PUnit.unit, ⟨loadEntropy_initial_zero,
        loadStateNext_freeEnergyBalance (loadCurrentState runtime.state.current)⟩⟩ :
        SourceNativeProjectionFiberAt loadProjectionLaw .freeEnergyBalance
          (loadEmitted runtime.state.current)) := rfl

/-- The existing canonical reachability proof transports the one-step account from its origin. -/
theorem loadRuntime_entropyPaid (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadEntropyProduction (loadCurrentState runtime.state.current) =
      loadBindingAccountedFreeEnergy loadInitialState -
        loadBindingAccountedFreeEnergy (loadCurrentState runtime.state.current) := by
  have paid (state : loadRuntimeProcess.State)
      (reachable : SourceNativeRuntimeReachableAt loadRuntimeProcess state) :
      loadEntropyProduction (loadCurrentState state.current) =
        loadBindingAccountedFreeEnergy loadInitialState -
          loadBindingAccountedFreeEnergy (loadCurrentState state.current) := by
    induction reachable with
    | initial =>
      change loadEntropyProduction loadInitialState =
        loadBindingAccountedFreeEnergy loadInitialState - loadBindingAccountedFreeEnergy loadInitialState
      rw [loadEntropy_initial_zero, sub_self]
    | @step state _ prior =>
      change loadEntropyProduction (loadStateNext (loadCurrentState state.current)) =
        loadBindingAccountedFreeEnergy loadInitialState -
          loadBindingAccountedFreeEnergy (loadStateNext (loadCurrentState state.current))
      have balance := loadStateNext_freeEnergyBalance (loadCurrentState state.current)
      linarith
  exact paid runtime.state runtime.reachable

theorem loadRuntime_debitNonnegative (runtime : LivingRuntimeState loadRuntimeProcess) :
    0 ≤ loadBindingAccountedFreeEnergy loadInitialState -
      loadBindingAccountedFreeEnergy (loadCurrentState runtime.state.current) := by
  rw [← loadRuntime_entropyPaid runtime]
  exact loadEntropy_nonnegative _

/-- Omitting the binding term is valid exactly when this actual step does not change it. -/
theorem loadRuntime_bareFreeEnergyBalance_iff (runtime : LivingRuntimeState loadRuntimeProcess) :
    (loadPCFreeEnergy (loadCurrentState runtime.tick.next.state.current) -
      loadPCFreeEnergy (loadCurrentState runtime.state.current) =
        -(loadEntropyProduction (loadCurrentState runtime.tick.next.state.current) -
          loadEntropyProduction (loadCurrentState runtime.state.current))) ↔
      boundaryEnergy (loadCurrentState runtime.tick.next.state.current).joint =
        boundaryEnergy (loadCurrentState runtime.state.current).joint := by
  have balance := loadRuntime_freeEnergyBalance runtime
  unfold loadBindingAccountedFreeEnergy at balance
  constructor <;> intro equality <;> linarith

theorem loadRuntime_completeFreeEnergyFace (runtime : LivingRuntimeState loadRuntimeProcess) :
    type_of% (loadRuntimeFace_factorizes runtime .freeEnergy) ∧
    type_of% (loadRuntime_freeEnergy_is_installed runtime) ∧
    type_of% (loadRuntimeFace_factorizes runtime .freeEnergyBalance) ∧
    type_of% (loadRuntime_freeEnergyBalance_is_installed runtime) ∧
    type_of% (loadRuntime_completeEntropyFace runtime) ∧
    type_of% (loadRuntime_freeEnergyBalance runtime) ∧
    type_of% (loadRuntime_entropyPaid runtime) ∧
    type_of% (loadRuntime_debitNonnegative runtime) :=
  ⟨loadRuntimeFace_factorizes runtime .freeEnergy, loadRuntime_freeEnergy_is_installed runtime,
    loadRuntimeFace_factorizes runtime .freeEnergyBalance, loadRuntime_freeEnergyBalance_is_installed runtime,
    loadRuntime_completeEntropyFace runtime, loadRuntime_freeEnergyBalance runtime,
    loadRuntime_entropyPaid runtime, loadRuntime_debitNonnegative runtime⟩

end

end LAlanine40K2025.Thermal.Load.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
