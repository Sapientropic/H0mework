import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Programmes

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def Encoding.ofTotal {old : TheoryState N} (encode : Total old ↪ B) : Encoding (rank := rank) old where
  version := ⟨fun value => encode (.inl value), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  law := ⟨fun value => encode (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (encode.injective same))⟩
  expression := ⟨fun value => encode (.inr (.inr (.inl value))),
    fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (encode.injective same)))⟩
  realization := ⟨fun value => encode (.inr (.inr (.inr (.inl value)))),
    fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (encode.injective same))))⟩
  without := ⟨fun value => encode (.inr (.inr (.inr (.inr (.inl value))))),
    fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (encode.injective same)))))⟩
  theoremMember := ⟨fun value => encode (.inr (.inr (.inr (.inr (.inr value))))),
    fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (encode.injective same)))))⟩

/-- Material pays all dependent carriers before the complete theorem
programmes are formed. Both directions of each native presentation recover. -/
theorem every_theory_at (coordinates : Coordinates (rank := rank) N) (old : TheoryState N)
    (encode : Total old ↪ B) :
    ∃ material programme : M, ∃ generated : TheoryState N,
      formTheoryAt coordinates material programme = some generated ∧ Nonempty (Presentation old generated) := by
  let code := Encoding.ofTotal encode
  obtain ⟨material, hm⟩ := MotherArenaHigher.read_surjective rank (Encoding.reader coordinates old code)
  let checked := Encoding.checked coordinates old code hm
  let presentations := Encoding.programmes coordinates old code hm
  obtain ⟨programme, programmeFormed⟩ := MotherArenaAdmission.every_presentation_section
    (expressionAddress coordinates material)
    (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
    (fun point => coordinates.holds point.1 (denotes coordinates material checked point.2)) presentations
  refine ⟨material, programme, theory coordinates material checked presentations, ?_,
    ⟨Encoding.presentation coordinates old code hm⟩⟩
  unfold formTheoryAt
  rw [dif_pos checked]
  change (MotherArenaAdmission.formPresentationSection _ _ _ programme).map (theory coordinates material checked) = _
  rw [programmeFormed]
  rfl

theorem every_theory_on_data (parent : M) (value : SourcePair) (data : PresentationData value)
    (formed : MotherArenaAdmission.formDeclarationData parent = some ⟨value, data⟩)
    (old : TheoryState value.1.1.1.1.1) (encode : Total old ↪ B) :
    ∃ material : M, ∃ generated : TheoryState value.1.1.1.1.1,
      formTheory material = some ⟨⟨value, data⟩, generated⟩ ∧ Nonempty (Presentation old generated) := by
  obtain ⟨material, programme, generated, generatedFormed, presentation⟩ :=
    every_theory_at (coordinatesOfData parent value data formed) old encode
  refine ⟨MotherArenaHigher.pack rank (parent, MotherArenaHigher.pack rank (material, programme)),
    generated, ?_, presentation⟩
  simp only [formTheory, MotherArenaHigher.split_pack, formTheoryParts, formed, Option.pbind_some]
  rw [generatedFormed]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
