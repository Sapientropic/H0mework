import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaProjection.Encoding
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Operations

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection.Encoding
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open MotherPatchInventory
open MotherProjectionOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeLedgerSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source.source) (old : SourceNativeProjectionLaw source) (encode : Encoding (rank := rank) old)
    {material : MotherArenaHigher.Material rank} (hm : (MotherArenaHigher.read rank) material = reader coordinates old encode)

abbrev classEquiv (p : old.Projection) (point : Point source.source) :=
  Equiv.sumCongr (activeEquiv coordinates old encode hm p point) (inactiveEquiv coordinates old encode hm p point)

theorem classify_graph (p : old.Projection) (point : Point source.source)
    (value : old.ActiveAt p point.2 ⊕ old.InactiveAt p point.2) :
    classificationGraph coordinates material (projectionEquiv coordinates old encode hm p) point
      (classEquiv coordinates old encode hm p point value) ↔ old.classify p point.2 = value := by
  cases value with
  | inl active =>
      change r3 material 4 (encode.projection p) (coordinates.occurrence point) (encode.active ⟨p, point, active⟩) ↔ _
      rw [r3, reader_bit coordinates old encode hm]
      simp only [graph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨q, other, value, pEq, pointEq, activeEq, selected⟩
        have same := encode.projection.injective pEq
        cases same
        have same := coordinates.occurrence.injective pointEq
        cases same
        have same := (activeAt old encode p point).injective activeEq
        cases same
        exact selected
      · intro selected
        exact ⟨p, point, active, rfl, rfl, rfl, selected⟩
  | inr inactive =>
      change r3 material 5 (encode.projection p) (coordinates.occurrence point) (encode.inactive ⟨p, point, inactive⟩) ↔ _
      rw [r3, reader_bit coordinates old encode hm]
      simp only [graph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨q, other, value, pEq, pointEq, inactiveEq, selected⟩
        have same := encode.projection.injective pEq
        cases same
        have same := coordinates.occurrence.injective pointEq
        cases same
        have same := (inactiveAt old encode p point).injective inactiveEq
        cases same
        exact selected
      · intro selected
        exact ⟨p, point, inactive, rfl, rfl, rfl, selected⟩

theorem project_graph (p : old.Projection) (point : Point source.source) (active : old.ActiveAt p point.2)
    (payload : old.PayloadAt p point.2 active) :
    r4 material 6 (projectionEquiv coordinates old encode hm p).val (coordinates.occurrence point)
      (activeEquiv coordinates old encode hm p point active).val
      (payloadEquiv coordinates old encode hm p point active payload).val ↔ payload = old.project p point.2 active := by
  rw [r4, reader_bit coordinates old encode hm]
  simp only [graph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨q, other, value, pEq, pointEq, activeEq, payloadEq⟩
    have same := encode.projection.injective pEq
    cases same
    have same := coordinates.occurrence.injective pointEq
    cases same
    have same := (activeAt old encode p point).injective activeEq
    cases same
    exact ((payloadAt old encode p point active).injective payloadEq).symm
  · intro same
    cases same
    exact ⟨p, point, active, rfl, rfl, rfl, rfl⟩

include hm in
theorem checked : Check coordinates material where
  classify := by
    intro projection point
    obtain ⟨p, rfl⟩ := (projectionEquiv coordinates old encode hm).surjective projection
    refine ⟨classEquiv coordinates old encode hm p point (old.classify p point.2),
      (classify_graph coordinates old encode hm p point _).mpr rfl, ?_⟩
    intro output selected
    obtain ⟨value, rfl⟩ := (classEquiv coordinates old encode hm p point).surjective output
    exact congrArg (classEquiv coordinates old encode hm p point)
      ((classify_graph coordinates old encode hm p point value).mp selected).symm
  project := by
    intro projection point active
    obtain ⟨p, rfl⟩ := (projectionEquiv coordinates old encode hm).surjective projection
    obtain ⟨active, rfl⟩ := (activeEquiv coordinates old encode hm p point).surjective active
    refine ⟨payloadEquiv coordinates old encode hm p point active (old.project p point.2 active),
      (project_graph coordinates old encode hm p point active _).mpr rfl, ?_⟩
    intro output selected
    obtain ⟨payload, rfl⟩ := (payloadEquiv coordinates old encode hm p point active).surjective output
    exact congrArg (payloadEquiv coordinates old encode hm p point active)
      ((project_graph coordinates old encode hm p point active payload).mp selected)

def presentation : Presentation old (projectionLaw coordinates material (checked coordinates old encode hm)) where
  projection := projectionEquiv coordinates old encode hm
  active := activeEquiv coordinates old encode hm
  inactive := inactiveEquiv coordinates old encode hm
  payload := payloadEquiv coordinates old encode hm
  classify := by
    intro p point
    let produced := Classical.choose ((checked coordinates old encode hm).classify
      (projectionEquiv coordinates old encode hm p) point)
    have selected := (Classical.choose_spec ((checked coordinates old encode hm).classify
      (projectionEquiv coordinates old encode hm p) point)).1
    obtain ⟨value, valueEq⟩ := (classEquiv coordinates old encode hm p point).surjective produced
    have selectedImage := Eq.mpr (congrArg (classificationGraph coordinates material
      (projectionEquiv coordinates old encode hm p) point) valueEq) selected
    exact valueEq.symm.trans (congrArg (classEquiv coordinates old encode hm p point)
      ((classify_graph coordinates old encode hm p point value).mp selectedImage).symm)
  project := by
    intro p point active
    let produced := Classical.choose ((checked coordinates old encode hm).project
      (projectionEquiv coordinates old encode hm p) point (activeEquiv coordinates old encode hm p point active))
    have selected := (Classical.choose_spec ((checked coordinates old encode hm).project
      (projectionEquiv coordinates old encode hm p) point (activeEquiv coordinates old encode hm p point active))).1
    obtain ⟨value, valueEq⟩ := (payloadEquiv coordinates old encode hm p point active).surjective produced
    have selectedImage := Eq.mpr (congrArg
      (fun output : Payload coordinates material (projectionEquiv coordinates old encode hm p) point
          (activeEquiv coordinates old encode hm p point active) =>
        r4 material 6 (projectionEquiv coordinates old encode hm p).val (coordinates.occurrence point)
          (activeEquiv coordinates old encode hm p point active).val output.val) valueEq) selected
    exact valueEq.symm.trans (congrArg (payloadEquiv coordinates old encode hm p point active)
      ((project_graph coordinates old encode hm p point active value).mp selectedImage))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection.Encoding
