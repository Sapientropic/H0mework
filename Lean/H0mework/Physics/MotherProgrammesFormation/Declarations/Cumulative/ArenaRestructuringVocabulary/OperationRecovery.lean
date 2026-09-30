import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRestructuringVocabulary.OperationEncoding
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
open MotherArenaNetwork MotherRestructuringOrigin
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

namespace OperationEncoding
variable (base families : MotherArenaHigher.Material rank) (old : Operations (formedSorts base) (formedFamilies base families))
    {material : MotherArenaHigher.Material rank} (hm : (MotherArenaHigher.read rank) material = reader base families old)

theorem null_eq : (checked base families old hm).nullValue = old.null :=
  (null_graph base families old hm _).mp (Classical.choose_spec (checked base families old hm).null).1

theorem complement_eq (value : Field base 8) : (checked base families old hm).complementValue value = old.complement value :=
  (complement_graph base families old hm value _).mp (Classical.choose_spec ((checked base families old hm).complement value)).1

theorem anchor_eq (source : Field base 0) : (checked base families old hm).anchorValue source =
    (old.anchorIdentity source, old.anchorScope source, old.anchorLineage source) :=
  (anchor_graph base families old hm source _).mp (Classical.choose_spec ((checked base families old hm).anchor source)).1

theorem incidence_eq (source : Field base 0) : (checked base families old hm).incidenceValue source = old.incidence source :=
  (incidence_graph base families old hm source _).mp (Classical.choose_spec ((checked base families old hm).incidence source)).1

theorem content_eq (source : Field base 0) (obstruction : Obstruction base families source) :
    (checked base families old hm).contentValue source obstruction = old.demandContent obstruction :=
  (content_graph base families old hm source obstruction _).mp
    (Classical.choose_spec ((checked base families old hm).demandContent source obstruction)).1

theorem residual_eq (source : Field base 0) (obstruction : Obstruction base families source) :
    (checked base families old hm).residualValue source obstruction = old.demandResidual obstruction :=
  (residual_graph base families old hm source obstruction _).mp
    (Classical.choose_spec ((checked base families old hm).demandResidual source obstruction)).1

theorem laws : Laws (checked base families old hm) where
  involutive := by
    have same := funext (complement_eq base families old hm)
    exact Eq.mpr (congrArg Function.Involutive same) old.involutive
  nontrivial := by
    intro same
    have left := null_eq base families old hm
    have right := (complement_eq base families old hm _).trans (congrArg old.complement left)
    exact old.nontrivial (left.symm.trans (same.trans right))
  registered := by
    intro source same
    have left := congrArg Prod.fst (anchor_eq base families old hm source)
    have right := (complement_eq base families old hm _).trans (congrArg old.complement left)
    exact old.anchorRegistered source (left.symm.trans (same.trans right))

theorem recovered : operations (checked base families old hm) (laws base families old hm) = old := by
  apply operations_ext
  · exact null_eq base families old hm
  · exact funext (complement_eq base families old hm)
  · exact funext (fun source => congrArg Prod.fst (anchor_eq base families old hm source))
  · exact funext (fun source => congrArg (fun body : AnchorBody base => body.2.1) (anchor_eq base families old hm source))
  · exact funext (fun source => congrArg (fun body : AnchorBody base => body.2.2) (anchor_eq base families old hm source))
  · exact funext (incidence_eq base families old hm)
  · exact funext (fun source => funext (content_eq base families old hm source))
  · exact funext (fun source => funext (residual_eq base families old hm source))
end OperationEncoding

theorem every_operations (base families : M) (old : Operations (formedSorts base) (formedFamilies base families)) :
    ∃ material : M, formVocabularyParts base families material = some (restructuring (formedSorts base) (formedFamilies base families) old) := by
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank) (OperationEncoding.reader base families old)
  refine ⟨material, ?_⟩
  let checked := OperationEncoding.checked base families old hm
  let laws := OperationEncoding.laws base families old hm
  unfold formVocabularyParts
  rw [dif_pos checked, dif_pos laws, OperationEncoding.recovered base families old hm]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
