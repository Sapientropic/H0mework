import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaCompiler.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
open MotherArenaNetwork MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates (rank := rank) source)

def targetAddress {current : V.Current} : (branch : EvolutionAt V current) → TargetFor source branch → Option B
  | .nativeWrite write, target => some (coordinates.occurrence ⟨V.nativeTarget write, target⟩)
  | .relationWrite write, target => some (coordinates.occurrence ⟨V.relationTarget write, target⟩)
  | .continuedTransport write, target => some (coordinates.occurrence ⟨V.continuedTarget write, target⟩)
  | .borromeanRedirect write, target => some (coordinates.occurrence ⟨V.redirectTarget write, target⟩)
  | .faithfulTerminal _, _ => none

theorem targetAddress_injective {current : V.Current} (branch : EvolutionAt V current) :
    Function.Injective (targetAddress coordinates branch) := by
  intro a b same
  cases branch with
  | nativeWrite write | relationWrite write | continuedTransport write | borromeanRedirect write =>
      exact (Function.Embedding.sigmaMk (β := source.toRootSource.actual.OccurrenceAt) _).injective
        (coordinates.occurrence.injective (Option.some.inj same))
  | faithfulTerminal => exact @Subsingleton.elim PUnit inferInstance _ _

theorem targetAddress_none_unique {current : V.Current} (branch : EvolutionAt V current)
    (target desired : TargetFor source branch) (absent : targetAddress coordinates branch target = none) :
    target = desired := by
  cases branch <;> simp only [targetAddress, reduceCtorEq] at absent
  exact @Subsingleton.elim PUnit inferInstance _ _

def targetGraph (material : M) (point : Sigma source.toRootSource.actual.OccurrenceAt)
    (branch : EvolutionAt V point.1) (target : TargetFor source branch) : Prop :=
  match targetAddress coordinates branch target with
  | none => True
  | some address => r2 material 0 (coordinates.occurrence point) address

def TargetCheck (material : M) : Prop :=
  ∀ point : Sigma source.toRootSource.actual.OccurrenceAt,
    ∃! target : TargetFor source (source.toRootSource.actual.compile point.2),
      targetGraph coordinates material point _ target

def generatedTargets (material : M) (checked : TargetCheck coordinates material) : TargetSection source :=
  fun point => Classical.choose (checked point)

def formTargetSection (material : M) : Option (TargetSection source) :=
  if checked : TargetCheck coordinates material then some (generatedTargets coordinates material checked) else none

theorem targetSection_formed (material : M) (checked : TargetCheck coordinates material) :
    formTargetSection coordinates material = some (generatedTargets coordinates material checked) := by
  simp only [formTargetSection, dif_pos checked]

theorem generated_target_eq (material : M) (checked : TargetCheck coordinates material)
    (point : Sigma source.toRootSource.actual.OccurrenceAt)
    (target : TargetFor source (source.toRootSource.actual.compile point.2))
    (selected : targetGraph coordinates material point _ target) :
    generatedTargets coordinates material checked point = target :=
  ((Classical.choose_spec (checked point)).2 target selected).symm

/-- The source and its coordinates come from the same source factory output.
The second source material supplies actual target occurrences, indexed only
by the present event and its already generated structural branch. -/
def formTargets (material : M) :
    Option (Σ source : SourceValue, Coordinates (rank := rank) source.2.2 × TargetSection source.2.2) :=
  let parts := (MotherArenaHigher.split rank) material
  match formCoordinatedSource parts.1 with
  | none => none
  | some ⟨source, coordinates⟩ =>
      (formTargetSection coordinates parts.2).map (fun targets => ⟨source, coordinates, targets⟩)

theorem targets_formed (sourceMaterial targetMaterial : M) (value : SourceValue)
    (coordinates : Coordinates (rank := rank) value.2.2)
    (formed : formCoordinatedSource sourceMaterial = some ⟨value, coordinates⟩)
    (checked : TargetCheck coordinates targetMaterial) :
    formTargets ((MotherArenaHigher.pack rank) (sourceMaterial, targetMaterial)) =
      some ⟨value, coordinates, generatedTargets coordinates targetMaterial checked⟩ := by
  simp only [formTargets, (MotherArenaHigher.split_pack rank)]
  rw [formed]
  simp only [targetSection_formed coordinates targetMaterial checked, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
