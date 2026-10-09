import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Runtime.LoadRuntimeFreeEnergy

/-! # Strict source-paid thermal cost is installed at the actual first load occurrence

The first action's lower bound is not reissued at later currents with a remembered
environment. The closed classifier retains those later inactive receipts.
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

theorem loadRuntime_initialStrictCost_is_installed :
    loadRuntimeFacade.readoutAt loadRuntimeSeed .initialStrictCost =
      (.inl ⟨PUnit.unit, ⟨loadFirst_sourceGeneratedThermodynamicCost,
        loadFirstEnvironmentHeat_deriv_zero, loadFirstEnvironmentHeat_secondDeriv⟩⟩ :
        SourceNativeProjectionFiberAt loadProjectionLaw .initialStrictCost (loadEmitted .ingress)) := rfl

theorem loadRuntime_nextStrictCost_is_inactive (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadRuntimeFacade.readoutAt runtime.tick.next .initialStrictCost =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt loadProjectionLaw .initialStrictCost
        (loadEmitted runtime.tick.next.state.current)) := rfl

theorem loadRuntime_firstStrictHeat :
    (Propagation.Producer.nativeClockStep : ℝ) ^ 2 / 4 <
      environmentEnergy (loadCurrentState loadRuntimeAfterFirst.state.current).joint -
        environmentEnergy (loadCurrentState loadRuntimeSeed.state.current).joint :=
  loadFirst_strictHeat

theorem loadRuntime_firstStrictGibbsCost :
    0 < loadGibbsExcess (loadCurrentState loadRuntimeAfterFirst.state.current) :=
  loadFirst_strictGibbsCost

theorem loadRuntime_firstStrictEntropyCost :
    0 < loadEntropyProduction (loadCurrentState loadRuntimeAfterFirst.state.current) :=
  loadFirst_strictEntropyCost

theorem loadRuntime_firstStrictFreeEnergyDebit :
    0 < loadBindingAccountedFreeEnergy (loadCurrentState loadRuntimeSeed.state.current) -
      loadBindingAccountedFreeEnergy (loadCurrentState loadRuntimeAfterFirst.state.current) :=
  loadFirst_strictFreeEnergyDebit

theorem loadRuntime_initialStrictCost :
    type_of% (loadRuntimeFace_factorizes loadRuntimeSeed .initialStrictCost) ∧
    type_of% loadRuntime_initialStrictCost_is_installed ∧
    type_of% (loadRuntime_completeFreeEnergyFace loadRuntimeSeed) ∧
    type_of% loadRuntime_firstStrictHeat ∧ type_of% loadRuntime_firstStrictGibbsCost ∧
    type_of% loadRuntime_firstStrictEntropyCost ∧ type_of% loadRuntime_firstStrictFreeEnergyDebit ∧
    type_of% loadRuntimeFirst_is_generated_action ∧ type_of% loadRuntime_first_actual_target ∧
    type_of% generatedLoadAction_next :=
  ⟨loadRuntimeFace_factorizes loadRuntimeSeed .initialStrictCost, loadRuntime_initialStrictCost_is_installed,
    loadRuntime_completeFreeEnergyFace loadRuntimeSeed, loadRuntime_firstStrictHeat,
    loadRuntime_firstStrictGibbsCost, loadRuntime_firstStrictEntropyCost,
    loadRuntime_firstStrictFreeEnergyDebit, loadRuntimeFirst_is_generated_action,
    loadRuntime_first_actual_target, generatedLoadAction_next⟩

theorem loadRuntime_firstCost_not_reissued (runtime : LivingRuntimeState loadRuntimeProcess) :
    type_of% (loadRuntimeFace_factorizes runtime.tick.next .initialStrictCost) ∧
    type_of% (loadRuntime_nextStrictCost_is_inactive runtime) ∧
    type_of% (loadRuntime_completeFreeEnergyFace runtime.tick.next) :=
  ⟨loadRuntimeFace_factorizes runtime.tick.next .initialStrictCost,
    loadRuntime_nextStrictCost_is_inactive runtime, loadRuntime_completeFreeEnergyFace runtime.tick.next⟩

end

end LAlanine40K2025.Thermal.Load.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
