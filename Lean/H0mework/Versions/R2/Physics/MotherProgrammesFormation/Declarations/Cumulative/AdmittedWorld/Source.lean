import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmittedWorld.Material
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRoot.Header
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.NetworkRestriction.Native

/-! One low mother material contains the complete authoritative-root
source and the operands of its original lawful-visit generator. Both
outputs are consumed through their actual Option values. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmittedWorld
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot ZeroLawRootAdmission
noncomputable section

structure Origin {N : WorldRelationNetwork.{0}} (original : StateAt N) where
  rank : Ordinal.{0}
  material : MotherArenaHigher.Material rank
  available : (MotherArenaTheory.formTheory (MotherArenaHigher.split rank material).1).isSome
  presentation :
    let output := (MotherArenaTheory.formTheory (MotherArenaHigher.split rank material).1).get available
    MotherAuthorityRoot.Presentation original.2.1 output.1.1 output.1.2 output.2
  formed : formState presentation.restrictHeader (MotherArenaHigher.split rank material).2 = some original
  originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank
  originalRetained :
    Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
      (MotherArenaHigher.includeOriginal rank originalAddress)

variable {N : WorldRelationNetwork.{0}} {original : StateAt N} (origin : Origin original)

/-- The current is the actual output of the generic authoritative-root
header plus original chronological generator, with no handoff enrichment. -/
def Origin.read : StateAt N :=
  (formState origin.presentation.restrictHeader (MotherArenaHigher.split origin.rank origin.material).2).get
    (by rw [origin.formed]; rfl)

theorem Origin.read_eq : origin.read = original :=
  Option.some.inj ((Option.some_get _).trans origin.formed)

def Origin.world : Σ network : WorldRelationNetwork.{0}, StateAt network :=
  ⟨MotherNetworkRestriction.restrictNetwork origin.presentation.network,
    Equiv.cast (congrArg StateAt (MotherNetworkRestriction.restrictNetwork_eq origin.presentation.network).symm) origin.read⟩

private theorem actual_cast_heq {First Last : Type _} (same : First = Last) (value : First) :
    HEq (Equiv.cast same value) value := by
  cases same
  rfl

theorem Origin.world_eq : origin.world = ⟨N, original⟩ := by
  have same : origin.world = ⟨N, origin.read⟩ :=
    Sigma.ext (MotherNetworkRestriction.restrictNetwork_eq origin.presentation.network)
      (actual_cast_heq (congrArg StateAt (MotherNetworkRestriction.restrictNetwork_eq origin.presentation.network).symm) origin.read)
  exact same.trans (congrArg (Sigma.mk N) origin.read_eq)

/-- The admitted state, root, vocabulary and network all come from one
source material. The original P enters coverage and inverse types only. -/
theorem every_state (N : WorldRelationNetwork.{0}) (original : StateAt N) : Nonempty (Origin original) := by
  obtain ⟨rank, rootMaterial, available, presentation, _rootSame, originalAddress, originalRetained⟩ :=
    MotherAuthorityRoot.every_original_root_recovered N original.1 original.2.1
  obtain ⟨visitMaterial, formed⟩ := state_on_header (rank := rank) original presentation.restrictHeader
    presentation.restrictHeader_eq
  let material := MotherArenaHigher.pack rank (rootMaterial, visitMaterial)
  have splitSame : MotherArenaHigher.split rank material = (rootMaterial, visitMaterial) :=
    MotherArenaHigher.split_pack rank (rootMaterial, visitMaterial)
  have packed : ∃ available : (MotherArenaTheory.formTheory (MotherArenaHigher.split rank material).1).isSome,
      let output := (MotherArenaTheory.formTheory (MotherArenaHigher.split rank material).1).get available
      ∃ presentation : MotherAuthorityRoot.Presentation original.2.1 output.1.1 output.1.2 output.2,
        formState presentation.restrictHeader (MotherArenaHigher.split rank material).2 = some original := by
    rw [splitSame]
    exact ⟨available, presentation, formed⟩
  obtain ⟨packedAvailable, packedPresentation, packedFormed⟩ := packed
  exact ⟨⟨rank, material, packedAvailable, packedPresentation, packedFormed, originalAddress, originalRetained⟩⟩

/-- This is the unchanged original Zero-Law admission domain. -/
theorem every_original_admitted_state (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) (state : LawfulWorldStateAt root) :
    ∃ origin : Origin (⟨V, root, state⟩ : StateAt N),
      origin.world = ⟨N, V, root, state⟩ := by
  obtain ⟨origin⟩ := every_state N ⟨V, root, state⟩
  exact ⟨origin, origin.world_eq⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmittedWorld
