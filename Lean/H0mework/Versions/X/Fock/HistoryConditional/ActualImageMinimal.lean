import H0mework.Versions.X.Fock.HistoryConditional.ActualImageRetention

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors nextRead)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype

theorem nextRead_injective (runtime : LivingRuntimeState process) : Function.Injective (nextRead runtime) := by
  intro left right same
  have clocks := congrArg (SourceConditionalModel.clockRead runtime) same
  rw [SourceConditionalModel.clock_source, SourceConditionalModel.clock_source] at clocks
  apply Fin.ext
  exact_mod_cast add_right_cancel clocks

theorem image_card (runtime : LivingRuntimeState process) : Fintype.card (Image runtime) = inventoryBound runtime + 1 := by
  have source := Fintype.card_congr (Equiv.ofInjective (nextRead runtime) (nextRead_injective runtime))
  exact source.symm.trans (Fintype.card_fin _)

theorem values_injective (runtime : LivingRuntimeState process) :
    Function.Injective (SourceConditionalInventory.values (inventoryBound runtime)) := by
  intro left right same
  apply nextRead_injective runtime
  apply realize_injective runtime
  exact (SourceConditionalInventory.values_original runtime left).symm.trans
    (same.trans (SourceConditionalInventory.values_original runtime right))

theorem faithful_code_lower (runtime : LivingRuntimeState process) {Code : Type*} [Fintype Code]
    (encode : Actors runtime → Code) (decode : Code → SourceJointClockGraph.Carrier)
    (recovers : ∀ index, decode (encode index) = SourceConditionalInventory.values (inventoryBound runtime) index) :
    inventoryBound runtime + 1 ≤ Fintype.card Code := by
  have injective : Function.Injective encode := by
    intro left right same
    apply values_injective runtime
    exact (recovers left).symm.trans ((congrArg decode same).trans (recovers right))
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective encode injective

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
