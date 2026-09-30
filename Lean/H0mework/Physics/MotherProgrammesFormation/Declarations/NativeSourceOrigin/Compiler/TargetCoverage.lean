import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.TargetFactory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler.TargetEncoding
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (desired : TargetSection source)

def graph (code : B) : Prop :=
  let pair := MotherHigherLawFamily.unpair code
  ∃ point, coordinates.occurrence point = pair.1 ∧
    targetAddress coordinates (source.toRootSource.actual.compile point.2) (desired point) = some pair.2

def reader (code : B) (_tag : Nat) : ℝ := if graph coordinates desired code then 0 else 1

theorem reader_bit {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates desired)
    (code : B) : bit material 0 code ↔ graph coordinates desired code := by
  by_cases seen : graph coordinates desired code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

theorem raw_graph_at {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates desired)
    (point : Sigma source.toRootSource.actual.OccurrenceAt) (address : B) :
    r2 material 0 (coordinates.occurrence point) address ↔
      targetAddress coordinates (source.toRootSource.actual.compile point.2) (desired point) = some address := by
  rw [r2, reader_bit coordinates desired hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, same, selected⟩
    have same := coordinates.occurrence.injective same
    cases same
    exact selected
  · intro selected
    exact ⟨point, rfl, selected⟩

theorem graph_at {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates desired)
    (point : Sigma source.toRootSource.actual.OccurrenceAt)
    (target : TargetFor source (source.toRootSource.actual.compile point.2)) :
    targetGraph coordinates material point _ target ↔ target = desired point := by
  cases address : targetAddress coordinates (source.toRootSource.actual.compile point.2) target with
  | none =>
      rw [targetGraph, address]
      exact ⟨fun _ => targetAddress_none_unique coordinates _ target (desired point) address, fun _ => True.intro⟩
  | some key =>
      rw [targetGraph, address]
      change r2 material 0 (coordinates.occurrence point) key ↔ _
      rw [raw_graph_at coordinates desired hm point key]
      constructor
      · intro selected
        exact targetAddress_injective coordinates _ (address.trans selected.symm)
      · intro same
        cases same
        exact address

theorem checked {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates desired) :
    TargetCheck coordinates material := fun point =>
  ⟨desired point, (graph_at coordinates desired hm point _).mpr rfl,
    fun target selected => (graph_at coordinates desired hm point target).mp selected⟩

theorem generated_eq {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates desired) :
    generatedTargets coordinates material (checked coordinates desired hm) = desired := by
  funext point
  exact generated_target_eq coordinates material (checked coordinates desired hm) point (desired point)
    ((graph_at coordinates desired hm point _).mpr rfl)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler.TargetEncoding

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

theorem every_target_section (sourceMaterial : M) (value : SourceValue) (coordinates : Coordinates value.2.2)
    (formed : formCoordinatedSource sourceMaterial = some ⟨value, coordinates⟩) (desired : TargetSection value.2.2) :
    ∃ material : M, ∃ targets : TargetSection value.2.2,
      formTargets material = some ⟨value, coordinates, targets⟩ ∧ targets = desired := by
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective (TargetEncoding.reader coordinates desired)
  exact ⟨MotherHigherLawValue.pack (sourceMaterial, material),
    generatedTargets coordinates material (TargetEncoding.checked coordinates desired hm),
    targets_formed sourceMaterial material value coordinates formed (TargetEncoding.checked coordinates desired hm),
    TargetEncoding.generated_eq coordinates desired hm⟩

theorem coordinates_generated (material : M) (value : SourceValue)
    (formed : MotherNativeSourceOrigin.formSource material = some value) :
    ∃ coordinates : Coordinates value.2.2,
      formCoordinatedSource material = some ⟨value, coordinates⟩ := by
  have mapped := (coordinated_source_original material).trans formed
  obtain ⟨⟨other, coordinates⟩, generated, same⟩ := Option.map_eq_some_iff.mp mapped
  cases same
  exact ⟨coordinates, generated⟩

theorem formed_targets_recover_original_target
    (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0}) (original : SourceNativeSource N V)
    (encode : MotherNativeSourceOrigin.Total original ↪ B) (compiler : SourceNativeLedgerCompiler original) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ coordinates : Coordinates generated, ∃ targets : TargetSection generated,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
        formTargets material = some ⟨⟨G, W, generated⟩, coordinates, targets⟩ ∧
        ∀ point : Sigma original.toRootSource.actual.OccurrenceAt,
          (targetAtEquiv p point.2).symm (targets (pointEquiv p point)) = originalTargets compiler point := by
  obtain ⟨sourceMaterial, G, W, generated, n, v, formed, ⟨p⟩⟩ :=
    MotherNativeSourceOrigin.every_jointly_embedded_source N V original encode
  obtain ⟨coordinates, generatedCoordinates⟩ := coordinates_generated sourceMaterial ⟨G, W, generated⟩ formed
  obtain ⟨material, targets, generatedTargets, targetEq⟩ :=
    every_target_section sourceMaterial ⟨G, W, generated⟩ coordinates generatedCoordinates
      (targetSectionEquiv p (originalTargets compiler))
  refine ⟨material, G, W, generated, coordinates, targets, n, v, p, generatedTargets, ?_⟩
  intro point
  rw [targetEq, targetSection_at]
  exact (targetAtEquiv p point.2).symm_apply_apply _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
