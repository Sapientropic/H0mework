import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRoot.Factory
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Root.Coverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRoot
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms MotherPatchInventory
open MotherPatchInventory
open MotherLedgerRoot
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

namespace EmittedEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (desired : Emitted source)

def graph (code : B) : Prop :=
  let parts := (MotherArenaHigher.unpair rank) code
  ∃ current, coordinates.current current = parts.1 ∧ coordinates.event current (desired current) = parts.2

def reader (code : B) (_tag : Nat) : ℝ := if graph coordinates desired code then 0 else 1

theorem reader_bit {material : MotherArenaHigher.Material rank} (hm : (MotherArenaHigher.read rank) material = reader coordinates desired)
    (code : B) : bit material 0 code ↔ graph coordinates desired code := by
  by_cases seen : graph coordinates desired code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

theorem graph_at {material : MotherArenaHigher.Material rank} (hm : (MotherArenaHigher.read rank) material = reader coordinates desired)
    (current : V.Current) (event : source.toRootSource.actual.OccurrenceAt current) :
    r2 material 0 (coordinates.current current) (coordinates.event current event) ↔ event = desired current := by
  rw [r2, reader_bit coordinates desired hm]
  simp only [graph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨other, same, selected⟩
    have currentEq := coordinates.current.injective same
    cases currentEq
    exact (coordinates.event current).injective selected.symm
  · intro same
    cases same
    exact ⟨current, rfl, rfl⟩

theorem checked {material : MotherArenaHigher.Material rank} (hm : (MotherArenaHigher.read rank) material = reader coordinates desired) :
    EmittedCheck coordinates material := fun current =>
  ⟨desired current, (graph_at coordinates desired hm current _).mpr rfl,
    fun event selected => (graph_at coordinates desired hm current event).mp selected⟩

theorem generated_eq {material : MotherArenaHigher.Material rank} (hm : (MotherArenaHigher.read rank) material = reader coordinates desired)
    (check : EmittedCheck coordinates material) : generatedEmitted coordinates material check = desired := by
  funext current
  exact (graph_at coordinates desired hm current _).mp (Classical.choose_spec (check current)).1
end EmittedEncoding

theorem every_emitted_section (parent : M) (value : CompilerValue)
    (formed : MotherArenaPatches.formCompiler parent = some value) (desired : Emitted value.1.1.2.2)
    (commutes : RootCheck value desired) :
    ∃ material : M, formRoot material = some ⟨value.1.1.1, value.1.1.2.1, rootOf value desired commutes⟩ := by
  let coordinates := compilerCoordinates parent value formed
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank) (EmittedEncoding.reader coordinates desired)
  refine ⟨(MotherArenaHigher.pack rank) (parent, material), ?_⟩
  change formRootParts ((MotherArenaHigher.split rank) ((MotherArenaHigher.pack rank) (parent, material))).1
    ((MotherArenaHigher.split rank) ((MotherArenaHigher.pack rank) (parent, material))).2 = _
  rw [MotherArenaHigher.split_pack]
  simp only [formRootParts, formed, Option.pbind_some]
  have check : EmittedCheck coordinates material := EmittedEncoding.checked coordinates desired hm
  rw [dif_pos check]
  have same := EmittedEncoding.generated_eq coordinates desired hm check
  let finish := fun emitted : Emitted value.1.1.2.2 =>
    if check : RootCheck value emitted then some (⟨value.1.1.1, value.1.1.2.1, rootOf value emitted check⟩ : RootValue) else none
  exact (congrArg finish same).trans (dif_pos commutes)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRoot
