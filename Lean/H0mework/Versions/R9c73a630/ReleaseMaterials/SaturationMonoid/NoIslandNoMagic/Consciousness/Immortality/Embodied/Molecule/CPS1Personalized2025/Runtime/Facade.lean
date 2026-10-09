import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root.Installation
import H0mework.Versions.R2.Foundation.Runtime.Activation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Root
noncomputable section

def process : SourceNativeLivingRootProcess N where
  State := RootVisit livingRoot.toAuthoritativeRoot.toRoot
  stateAt := fun visit => ⟨V,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨V,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨V,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := livingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit
    let target := visit.next (next := Native.next visit.current) rfl
    refine ⟨target,?_,?_⟩
    · rcases visit with ⟨current,history⟩
      rfl
    · rcases visit with ⟨current,history⟩
      exact HEq.rfl

def facade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _ => Projection
  componentAt := fun _ _ => projectionLaw
  installationAt := fun _ _ => installation
  projectionAt := fun _ face => face

def seed : LivingRuntimeState process := facade.seed
def afterFirst : LivingRuntimeState process := seed.tick.next
def afterSecond : LivingRuntimeState process := afterFirst.tick.next

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Projection) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

theorem actual_analysis_currents :
    Native.erase seed.current.visit.current = Current.registeredSource ∧
    Native.erase afterFirst.current.visit.current = Current.generatedProgram ∧
    Native.erase afterSecond.current.visit.current = Current.independentResponse := ⟨rfl,rfl,rfl⟩

theorem same_source_generated_next (runtime : LivingRuntimeState process) :
    runtime.tick.nextCurrent = process.stateAt (process.successor runtime.state) := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime
