import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Registration
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRootFromInput

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1MaterialIncidence.NativeRootDataProbe CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction CPS1PhosphorylExchange
attribute [local irreducible] registeredFrame registeredProgrammeData registeredWhole registeredResponse registeredExchange

def IsNativeOutcome {body : Body} {responseRaw : WholeRaw} {raw : CPS1PhosphorylExchange.Raw}
    {repair : LocalRepairDisposition body} {whole : WholeResponse repair responseRaw} :
    CPS1PhosphorylExchange.Disposition responseRaw raw repair whole → Prop
  | .retained _ _ => False
  | .responded .. => True

private theorem generated_input_from_programme (input : RegisteredNativeInput)
    (programme : ProgrammeAt input) (actual : source_programme input = some programme)
    (native :
      let whole := executeWhole programme.2.current input.updateWater input.updateRaw input.updatePath
        input.recycleEvents input.recycleRaw input.physical input.newDepth
      let repair := repairWhole whole input.supply
      IsNativeOutcome (fromWhole repair (wholeResponse repair input.response) input.exchange)) :
    ∃ occurrence : InputOccurrence input,
      generated_input input = some occurrence ∧
      IsNativeOutcome occurrence.outcome := by
  unfold generated_input
  rw [actual]
  exact ⟨_,rfl,native⟩

private theorem registered_source_native_tag :
    IsNativeOutcome (fromWhole (repairWhole registeredWhole registeredSupply)
      (wholeResponse (repairWhole registeredWhole registeredSupply) registeredResponse) registeredExchange) := by
  obtain ⟨receipt,repaired⟩ := registered_repair_selected
  obtain ⟨before,step,actual,source,next,_admitted,_exchanged,positive⟩ := registered_exchange_actual receipt repaired
  let native : LocalRepairDisposition (initialBody ⟨registeredFrame,registeredBefore⟩) → Prop :=
    fun repair => IsNativeOutcome (fromWhole repair (wholeResponse repair registeredResponse) registeredExchange)
  have accepted : native (.repaired receipt) := by
    dsimp only [native]
    rw [positive]
    exact True.intro
  exact Eq.mpr (congrArg native repaired) accepted

theorem registered_generated_input_native :
    ∃ occurrence : InputOccurrence registeredNativeInput,
      generated_input registeredNativeInput = some occurrence ∧
      IsNativeOutcome occurrence.outcome ∧
      NativeProfile registeredNativeInput.supply := by
  have programme : source_programme registeredNativeInput = some ⟨registeredFrame,registeredProgrammeData⟩ :=
    registered_input_programme
  have native :
      let whole := executeWhole registeredProgrammeData.current registeredNativeInput.updateWater registeredNativeInput.updateRaw
        registeredNativeInput.updatePath registeredNativeInput.recycleEvents registeredNativeInput.recycleRaw
        registeredNativeInput.physical registeredNativeInput.newDepth
      let repair := repairWhole whole registeredNativeInput.supply
      IsNativeOutcome (fromWhole repair (wholeResponse repair registeredNativeInput.response) registeredNativeInput.exchange) := by
    have whole : executeWhole registeredProgrammeData.current registeredNativeInput.updateWater registeredNativeInput.updateRaw
        registeredNativeInput.updatePath registeredNativeInput.recycleEvents registeredNativeInput.recycleRaw
        registeredNativeInput.physical registeredNativeInput.newDepth = registeredWhole := by
      unfold registeredNativeInput registeredWhole registeredBefore
      rfl
    dsimp only
    rw [whole]
    exact registered_source_native_tag
  obtain ⟨occurrence,actual,native⟩ := generated_input_from_programme registeredNativeInput
    ⟨registeredFrame,registeredProgrammeData⟩ programme native
  refine ⟨occurrence,actual,native,?_⟩
  simp only [registeredNativeInput,NativeProfile,registeredSupply]
  exact ⟨True.intro,True.intro,True.intro⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
