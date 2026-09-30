import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmittedWorld.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Consumer

/-! Both material levels are completions of the same fixed Mother's actual
finite evaluator. The formation conclusions below refer to the completed
material itself, before any world or process factory reads its fields. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FixedMotherRealization
open UniformSpace MotherFamilyOccurrence
noncomputable section
universe u

/-- A raw finite programme contains an actual visit of the fixed MotherRoot. -/
def lowProgramme (rank : Ordinal.{0}) (programme : MotherArenaHigher.Programme rank) :
    MotherArenaHigher.Material rank :=
  ((⟨MotherArenaHigher.finiteLaw rank programme, ⟨programme, rfl⟩⟩ : MotherArenaHigher.Raw rank) :
    MotherArenaHigher.Material rank)

def highProgramme (rank : Ordinal.{u}) (programme : MotherReceiptHigher.Programme rank) :
    MotherReceiptHigher.Material rank :=
  ((⟨MotherReceiptHigher.finiteLaw rank programme, ⟨programme, rfl⟩⟩ : MotherReceiptHigher.Raw rank) :
    MotherReceiptHigher.Material rank)

theorem lowProgramme_read (rank : Ordinal.{0}) (programme : MotherArenaHigher.Programme rank)
    (input : MotherArenaHigher.Base rank) :
    MotherArenaHigher.read rank (lowProgramme rank programme) input =
      MotherPointwiseLaws.finiteLaw programme.2.2
        (MotherStreamLaws.pad programme.1
          (fun index => MotherArenaHigher.observe rank (programme.2.1 index) input)) := by
  exact congrFun (MotherArenaFormation.Observed.read_coe (MotherArenaHigher.observe rank)
    ⟨MotherArenaHigher.finiteLaw rank programme, ⟨programme, rfl⟩⟩) input

theorem highProgramme_read (rank : Ordinal.{u}) (programme : MotherReceiptHigher.Programme rank)
    (input : MotherReceiptHigher.Base rank) :
    MotherReceiptHigher.read rank (highProgramme rank programme) input =
      MotherPointwiseLaws.finiteLaw programme.2.2
        (MotherStreamLaws.pad programme.1
          (fun index => MotherReceiptHigher.observe rank (programme.2.1 index) input)) := by
  exact congrFun (MotherReceiptObserved.read_coe (MotherReceiptHigher.observe rank)
    ⟨MotherReceiptHigher.finiteLaw rank programme, ⟨programme, rfl⟩⟩) input

/-- Full completion membership, not an address or representability premise. -/
def LowFormation (rank : Ordinal.{0}) (material : MotherArenaHigher.Material rank) : Prop :=
  material ∈ closure (Set.range (lowProgramme rank))

def HighFormation (rank : Ordinal.{u}) (material : MotherReceiptHigher.Material rank) : Prop :=
  material ∈ closure (Set.range (highProgramme rank))

theorem low_formation (rank : Ordinal.{0}) (material : MotherArenaHigher.Material rank) :
    LowFormation rank material := by
  have same : Set.range (lowProgramme rank) =
      Set.range ((↑) : MotherArenaHigher.Raw rank → MotherArenaHigher.Material rank) := by
    ext value
    constructor
    · rintro ⟨programme, rfl⟩
      exact ⟨⟨MotherArenaHigher.finiteLaw rank programme, ⟨programme, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨value, programme, same⟩, rfl⟩
      subst value
      exact ⟨programme, rfl⟩
  unfold LowFormation
  rw [same]
  exact Completion.denseRange_coe material

theorem high_formation (rank : Ordinal.{u}) (material : MotherReceiptHigher.Material rank) :
    HighFormation rank material := by
  have same : Set.range (highProgramme rank) =
      Set.range ((↑) : MotherReceiptHigher.Raw rank → MotherReceiptHigher.Material rank) := by
    ext value
    constructor
    · rintro ⟨programme, rfl⟩
      exact ⟨⟨MotherReceiptHigher.finiteLaw rank programme, ⟨programme, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨value, programme, same⟩, rfl⟩
      subst value
      exact ⟨programme, rfl⟩
  unfold HighFormation
  rw [same]
  exact Completion.denseRange_coe material

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FixedMotherRealization
