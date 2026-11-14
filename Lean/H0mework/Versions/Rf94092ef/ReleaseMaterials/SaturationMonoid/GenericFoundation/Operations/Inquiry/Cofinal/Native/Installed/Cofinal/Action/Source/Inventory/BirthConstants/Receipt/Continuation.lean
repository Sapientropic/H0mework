import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthConstants.Receipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.BirthRelation

open SourceOperationEffects SourceOperationScalarRelations CofinalHistorySettlement

namespace CA
export ActualCofinalCommonAction
  (site WordInInventory siteAction site_action_inventory action_source_word modelAction model_action_source projection)
end CA
namespace Tower
export ActualCofinalNativeTower (Words)
end Tower

variable {S : Type u} {W X : S → Type u} [∀ target, AddCommGroup (W target)] {s : S}
attribute [local instance] familyGroups
variable (factory : SF.Factory W X s)
variable (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s)) (language : cfg.LowVar = X)

local notation "site" => D.packetAt factory initial cfg language
local notation "Words" => Tower.Words factory initial cfg language
local notation "step" => CA.siteAction factory initial cfg language

/-- The same installed action carries the full relation span by linearity of its actual writes. -/
theorem site_action_installed_span (ordinal : Nat) (word : Words ordinal)
    (present : word ∈ Submodule.span ℤ {term | CA.WordInInventory (site ordinal) term}) :
    step ordinal word ∈ Submodule.span ℤ {term | CA.WordInInventory (site (ordinal+1)) term} := by
  let source : Submodule ℤ (Words ordinal) := Submodule.span ℤ {term | CA.WordInInventory (site ordinal) term}
  let target : Submodule ℤ (Words (ordinal+1)) := Submodule.span ℤ {term | CA.WordInInventory (site (ordinal+1)) term}
  have mapped : source ≤ target.comap (step ordinal) := by
    apply Submodule.span_le.mpr
    intro term stored
    change CA.WordInInventory (site ordinal) term at stored
    exact Submodule.subset_span (CA.site_action_inventory factory initial cfg language ordinal term stored)
  exact mapped present

/-- The original cofinal model consumes the written affine relation as a span element at its literal next site. -/
theorem actual_written_model_step (ordinal : Nat) :
    let packet := site ordinal
    ∀ (stock : Feed.Inventory (V := L.Value W packet.1) (X := X) (s := s))
      (present : packet.2.1.1.inventory = some stock) (origin : Feed.RelationOccurrence stock),
    ∃ normalized : Words (ordinal+1),
      HEq normalized (written factory packet stock present origin).val ∧
      step (ordinal+1) normalized ∈
        Submodule.span ℤ {term | CA.WordInInventory (site ((ordinal+1)+1)) term} ∧
      CA.modelAction factory initial cfg language
        (CA.projection factory initial cfg language (DFinsupp.single (ordinal+1) normalized)) =
      CA.projection factory initial cfg language
        (DFinsupp.single ((ordinal+1)+1) (step (ordinal+1) normalized)) := by
  intro packet stock present origin
  let target : AS.AdmissionPacket (W := W) (X := X) (s := s) := site (ordinal+1)
  let value := (written factory packet stock present origin).val
  have read : ∃ nextStock : Feed.Inventory (V := L.Value W target.1) (X := X) (s := s),
      target.2.1.1.inventory = some nextStock ∧
      ∃ normalized ∈ Feed.relationSpace nextStock, HEq normalized value :=
    actual_written_next factory initial cfg language ordinal stock present origin
  rcases read with ⟨nextStock,nextPresent,normalized,member,same⟩
  have included : Feed.relationSpace nextStock ≤
      Submodule.span ℤ {term | CA.WordInInventory (site (ordinal+1)) term} := by
    apply Submodule.span_mono
    intro term stored
    exact ⟨nextStock,nextPresent,stored⟩
  have writtenStep := site_action_installed_span factory initial cfg language (ordinal+1) normalized (included member)
  have model := CA.model_action_source factory initial cfg language (DFinsupp.single (ordinal+1) normalized)
  have literal := CA.action_source_word factory initial cfg language (ordinal+1) normalized
  exact ⟨normalized,same,writtenStep,model.trans (congrArg (CA.projection factory initial cfg language) literal)⟩

end ActualCofinalSourceAction.BirthRelation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
