import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Tower.Consumer
import H0mework.Realization.ObservationActions.WordsModel
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCofinalCommonAction"

/-! The original packet successor and literal source action induce an action
on the existing common native coefficient words. Source sites and grades
stay dependent. The already generated joint observer supplies the existing
allowed-action-word model without assuming stability of a prefix kernel. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalCommonAction
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open SourceOperationScalarPresentation CofinalHistorySettlement
namespace T
export ActualCofinalNativeTower (NativeValue Words CommonWords component stageInventory sourceMap completion_zero_iff)
export ActualCofinalNativeTower.SF (Factory)
export ActualCofinalNativeTower.L (Value groups)
export ActualCofinalNativeTower.M (Frame)
export ActualCofinalNativeTower.A (Programme)
end T
namespace A
export ActualCofinalSourceAction (sourceWordAction wordTransport packetTransport sourceBorn bornStock born_inventory source_word_action_in_born actual_next_packet nativePacket receiverOld receiverIncrement source_word_action_inventory)
export ActualCofinalSourceAction.D (packetAt packetAt_successor_grade)
export ActualCofinalSourceAction.AS (AdmissionPacket)
end A

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup (T.Value W grade target) := T.groups W grade target

private abbrev PacketWords (packet : A.AdmissionPacket (W := W) (X := X) (s := s)) :=
 Formal ℤ (T.Value W packet.1) X s

private def packetWordTransport
 {first second : A.AdmissionPacket (W := W) (X := X) (s := s)} (same : first = second) :
 PacketWords first ≃ₗ[ℤ] PacketWords second := by
 cases same
 exact LinearEquiv.refl ℤ _

private def packetLanguageWord {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : A.AdmissionPacket (W := W) (X := Y) (s := s)) :
 Formal ℤ (T.Value W packet.1) Y s ≃ₗ[ℤ]
 Formal ℤ (T.Value W (A.packetTransport same packet).1) Z s := by
 cases same
 exact LinearEquiv.refl ℤ _

/-- Membership is in the original complete inventory of that exact packet. -/
def WordInInventory (packet : A.AdmissionPacket (W := W) (X := X) (s := s))
 (word : Formal ℤ (T.Value W packet.1) X s) : Prop :=
 ∃ stock : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (T.Value W packet.1) X s)),
  packet.2.1.1.inventory = some stock ∧ .relation word ∈ stock.trace

private theorem inventory_packet_transport
 {first second : A.AdmissionPacket (W := W) (X := X) (s := s)} (same : first = second)
 (word : PacketWords first) (member : WordInInventory first word) :
 WordInInventory second (packetWordTransport same word) := by
 cases same
 exact member

private theorem inventory_language_transport {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : A.AdmissionPacket (W := W) (X := Y) (s := s))
 (word : Formal ℤ (T.Value W packet.1) Y s) (member : WordInInventory packet word) :
 WordInInventory (A.packetTransport same packet) (packetLanguageWord same packet word) := by
 cases same
 exact member

variable (factory : T.Factory W X s)
variable (initial : T.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : T.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

abbrev site (ordinal : Nat) := A.packetAt factory initial cfg language ordinal

private def transportedAction (packet : A.AdmissionPacket (W := W) (X := X) (s := s)) :
 PacketWords packet →ₗ[ℤ]
 PacketWords (A.packetTransport packet.2.2.2.down (A.sourceBorn factory packet)) :=
 (packetLanguageWord packet.2.2.2.down (A.sourceBorn factory packet)).toLinearMap.comp
  (A.sourceWordAction packet)

/-- The original literal action lands in the original actual next full packet. -/
def siteAction (ordinal : Nat) : T.Words factory initial cfg language ordinal →ₗ[ℤ]
 T.Words factory initial cfg language (ordinal+1) :=
 (packetWordTransport (A.actual_next_packet factory initial cfg language ordinal).symm).toLinearMap.comp
  (transportedAction factory (site factory initial cfg language ordinal))

/-- Linear extension of this source-produced action on every complete native site word. -/
def action : T.CommonWords factory initial cfg language →ₗ[ℤ] T.CommonWords factory initial cfg language :=
 DFinsupp.lsum ℤ fun ordinal =>
  (DFinsupp.lsingle (R := ℤ) (ordinal+1)).comp (siteAction factory initial cfg language ordinal)

theorem action_source_word (ordinal : Nat) (word : T.Words factory initial cfg language ordinal) :
 action factory initial cfg language (DFinsupp.single ordinal word) =
 DFinsupp.single (ordinal+1) (siteAction factory initial cfg language ordinal word) :=
 DFinsupp.lsum_single _ _ _ _

theorem action_next_component (ordinal : Nat) (word : T.Words factory initial cfg language ordinal) :
 T.component factory initial cfg language (ordinal+1)
  (action factory initial cfg language (DFinsupp.single ordinal word)) =
 siteAction factory initial cfg language ordinal word := by
 rw [action_source_word]
 exact DFinsupp.single_eq_same

/-- The complete acted word is installed in the original actual next packet inventory. -/
theorem site_action_inventory (ordinal : Nat)
 (word : T.Words factory initial cfg language ordinal)
 (member : WordInInventory (site factory initial cfg language ordinal) word) :
 WordInInventory (site factory initial cfg language (ordinal+1))
  (siteAction factory initial cfg language ordinal word) := by
 rcases member with ⟨prior,present,belongs⟩
 have born : WordInInventory (A.sourceBorn factory (site factory initial cfg language ordinal))
  (A.sourceWordAction (site factory initial cfg language ordinal) word) :=
  ⟨A.bornStock factory _,A.born_inventory factory _,
   A.source_word_action_in_born factory _ prior present word belongs⟩
 have languageMember := inventory_language_transport
  (site factory initial cfg language ordinal).2.2.2.down
  (A.sourceBorn factory (site factory initial cfg language ordinal))
  (A.sourceWordAction (site factory initial cfg language ordinal) word) born
 exact inventory_packet_transport
  (A.actual_next_packet factory initial cfg language ordinal).symm
  (transportedAction factory (site factory initial cfg language ordinal) word) languageMember

/-- Read the original receiver Env through the exact full-packet word recognition. -/
def receiverRead (ordinal : Nat) : T.Words factory initial cfg language (ordinal+1) →ₗ[ℤ]
 PairValue (T.NativeValue factory initial cfg language ordinal) s :=
 (SourceOperationScalarRelations.evaluation (R := ℤ)
  (A.nativePacket factory (site factory initial cfg language ordinal)).2.1.1.registered.input.environment).comp
  ((packetLanguageWord (site factory initial cfg language ordinal).2.2.2.down
   (A.sourceBorn factory (site factory initial cfg language ordinal))).symm.toLinearMap.comp
   (packetWordTransport (A.actual_next_packet factory initial cfg language ordinal).symm).symm.toLinearMap)

/-- This word square consumes the actual receiver coordinates; no next-site Env equality is assumed. -/
theorem actual_receiver_square (ordinal : Nat) (word : T.Words factory initial cfg language ordinal) :
 receiverRead factory initial cfg language ordinal (siteAction factory initial cfg language ordinal word) =
 updateInventory (R := ℤ) (A.receiverOld factory (site factory initial cfg language ordinal))
  (A.receiverIncrement factory (site factory initial cfg language ordinal)) word := by
 change SourceOperationScalarRelations.evaluation (R := ℤ)
  (A.nativePacket factory (site factory initial cfg language ordinal)).2.1.1.registered.input.environment
  ((packetLanguageWord (site factory initial cfg language ordinal).2.2.2.down
    (A.sourceBorn factory (site factory initial cfg language ordinal))).symm
   ((packetWordTransport (A.actual_next_packet factory initial cfg language ordinal).symm).symm
    ((packetWordTransport (A.actual_next_packet factory initial cfg language ordinal).symm)
     ((packetLanguageWord (site factory initial cfg language ordinal).2.2.2.down
       (A.sourceBorn factory (site factory initial cfg language ordinal)))
      (A.sourceWordAction (site factory initial cfg language ordinal) word))))) = _
 rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
 exact LinearMap.congr_fun (A.source_word_action_inventory factory _) word

/-- The observer is the original actual old/effect inventory at every generated native site. -/
def jointObserver : T.CommonWords factory initial cfg language →ₗ[ℤ]
 ((ordinal : Nat) → T.NativeValue factory initial cfg language ordinal s ×
  T.NativeValue factory initial cfg language ordinal s) :=
 LinearMap.pi fun ordinal => T.stageInventory factory initial cfg language ordinal

/-- Every allowed letter is this source-generated action; no future action table is supplied. -/
def actions (_letter : PUnit.{u+1}) := action factory initial cfg language

abbrev Model := SourceGeneratedActionWords.Model
 (actions factory initial cfg language) (jointObserver factory initial cfg language) PUnit.unit
abbrev projection := SourceGeneratedActionWords.projection
 (actions factory initial cfg language) (jointObserver factory initial cfg language) PUnit.unit
abbrev modelAction := SourceGeneratedActionWords.advance
 (actions factory initial cfg language) (jointObserver factory initial cfg language) PUnit.unit PUnit.unit

/-- The existing maximal future-invariant consumer derives the quotient action from the real action. -/
theorem model_action_source (word : T.CommonWords factory initial cfg language) :
 modelAction factory initial cfg language (projection factory initial cfg language word) =
 projection factory initial cfg language (action factory initial cfg language word) :=
 SourceGeneratedActionWords.advance_source _ _ _ _ word

/-- Every complete future word/site observation controls the complete generated fibre. -/
theorem model_fibre (left right : T.CommonWords factory initial cfg language) :
 projection factory initial cfg language left = projection factory initial cfg language right ↔
 ∀ word : List PUnit.{u+1}, ∀ ordinal,
  T.stageInventory factory initial cfg language ordinal
   (SourceGeneratedActionWords.run (actions factory initial cfg language) word left) =
  T.stageInventory factory initial cfg language ordinal
   (SourceGeneratedActionWords.run (actions factory initial cfg language) word right) :=
 (SourceGeneratedActionWords.projection_fibre _ _ _ left right).trans
  (forall_congr' fun _ => funext_iff)

end ActualCofinalCommonAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
