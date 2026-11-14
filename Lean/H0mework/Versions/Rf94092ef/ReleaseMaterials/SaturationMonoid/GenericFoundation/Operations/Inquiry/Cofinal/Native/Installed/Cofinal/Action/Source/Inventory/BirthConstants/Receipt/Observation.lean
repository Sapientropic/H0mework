import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthConstants.Receipt.Continuation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.PostDecoderRead

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.BirthRelation

open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift

namespace CA
export ActualCofinalCommonAction (modelRead model_read_source)
end CA
namespace Tower
export ActualCofinalNativeTower (nativeInventory stageInventory installed_environment updated_environment oldEnvironment actualIncrement)
end Tower
namespace Post
export ActualCofinalCommonAction.PostDecoder (updated_environment_current)
end Post

variable {S : Type u} {W X : S → Type u} [∀ target, AddCommGroup (W target)] {s : S}
attribute [local instance] familyGroups
private abbrev Packet (Y : S → Type u) := AS.AdmissionPacket (W := W) (X := Y) (s := s)
private abbrev WordAt {Y : S → Type u} (packet : Packet (W := W) (s := s) Y) := Formal ℤ (L.Value W packet.1) Y s

private def packetInventory {Y : S → Type u} (packet : Packet (W := W) (s := s) Y) :
    WordAt packet →ₗ[ℤ] PairValue (L.Value W packet.1) s :=
  let old := packet.2.1.1.registered.input.environment
  updateInventory (R := ℤ) old (packet.2.1.1.activeEnvironment-old)

private theorem written_difference {G : Type u} [AddCommGroup G] {before after increment : G}
    (written : before+increment=after) : after-before=increment := by
  rw [← written]
  abel

private theorem packet_updated_value {Y : S → Type u} (packet : Packet (W := W) (s := s) Y)
    (word : WordAt packet) :
    evaluation (R := ℤ) packet.2.1.1.activeEnvironment word =
      (packetInventory packet word).1+(packetInventory packet word).2 := by
  let old := packet.2.1.1.registered.input.environment
  let increment := packet.2.1.1.activeEnvironment-old
  have decoder : old+increment=packet.2.1.1.activeEnvironment := by
    dsimp only [old,increment]
    abel
  exact (congrArg (fun env => evaluation (R := ℤ) env word) decoder.symm).trans
    (LinearMap.congr_fun (evaluation_update (R := ℤ) old increment) word)

private theorem transport_observation {Y Z : S → Type u}
    (born : Packet (W := W) (s := s) Y) (target : Packet (W := W) (s := s) Z)
    (language : Y=Z) (literal : packetTransport language born = target)
    (before : WordAt born) (after : WordAt target) (same : HEq after before) :
    HEq (packetInventory target after) (packetInventory born before) ∧
    (packetInventory target after = 0 ↔ packetInventory born before = 0) ∧
    (evaluation (R := ℤ) target.2.1.1.activeEnvironment after = 0 ↔
      evaluation (R := ℤ) born.2.1.1.activeEnvironment before = 0) := by
  cases language
  cases literal
  cases eq_of_heq same
  exact ⟨HEq.rfl,Iff.rfl,Iff.rfl⟩

variable (factory : SF.Factory W X s)

private theorem native_birth_inventory (packet : Packet (W := W) (s := s) X)
    (stock : Feed.Inventory (V := L.Value W packet.1) (X := X) (s := s))
    (installed : packet.2.1.1.inventory = some stock) (origin : Feed.RelationOccurrence stock) :
    let born := sourceBorn factory packet
    let effect := (receiptInventory factory packet stock installed origin).2
    packetInventory born (written factory packet stock installed origin).val = (-effect,effect) := by
  intro born effect
  let registered : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := born.2.1.1.registered.input.environment
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (selected factory packet).activeEnvironment
  let delta := birthIncrement factory packet
  let word : Formal ℤ (L.Value W (packet.1+1)) packet.2.2.1.LowVar s :=
    (written factory packet stock installed origin).val
  have old : registered = before := born.2.1.1.raw_environment.symm.trans (birth_registered_environment factory packet)
  have committed : registered+delta = born.2.1.1.activeEnvironment :=
    (congrArg (· + delta) old).trans (birth_decoded_environment factory packet)
  have increment := written_difference committed
  have observed : packetInventory born word = updateInventory (R := ℤ) before delta word :=
    congrArg₂ (fun rho delta => updateInventory (R := ℤ) rho delta word) old increment
  exact observed.trans (written_inventory factory packet stock installed origin)

variable (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s)) (language : cfg.LowVar = X)

local notation "site" => D.packetAt factory initial cfg language
local notation "Words" => Tower.Words factory initial cfg language
local notation "project" => CA.projection factory initial cfg language
local notation "read" => CA.modelRead factory initial cfg language []

private theorem model_observes_packet (ordinal : Nat) (word : Words ordinal) :
    read (project (DFinsupp.single ordinal word)) ordinal = packetInventory (site ordinal) word := by
  let packet := site ordinal
  let registered := packet.2.1.1.registered.input.environment
  let increment := Tower.actualIncrement factory initial cfg language ordinal
  have old : Tower.oldEnvironment factory initial cfg language ordinal = registered :=
    (Tower.installed_environment factory initial cfg language ordinal).trans
      (ActualCofinalInstalledRaw.materialAtStop_source factory initial cfg language ordinal).1
  have after : registered+increment = packet.2.1.1.activeEnvironment :=
    (congrArg (· + increment) old.symm).trans
      ((Tower.updated_environment factory initial cfg language ordinal).symm.trans
        (Post.updated_environment_current factory initial cfg language ordinal))
  have delta := (written_difference after).symm
  have observed : read (project (DFinsupp.single ordinal word)) ordinal =
      Tower.nativeInventory factory initial cfg language ordinal word := by
    refine (CA.model_read_source factory initial cfg language [] (DFinsupp.single ordinal word) ordinal).trans ?_
    change Tower.nativeInventory factory initial cfg language ordinal ((DFinsupp.single ordinal word) ordinal) = _
    rw [DFinsupp.single_eq_same]
  exact observed.trans (congrArg₂ (fun rho delta => updateInventory (R := ℤ) rho delta word) old delta)

/-- The original cofinal model retains both receipt channels at the literal born site. -/
theorem actual_written_model_observation (ordinal : Nat) :
    let packet := site ordinal
    let target := site (ordinal+1)
    ∀ (stock : Feed.Inventory (V := L.Value W packet.1) (X := X) (s := s))
      (present : packet.2.1.1.inventory = some stock) (origin : Feed.RelationOccurrence stock),
    let effect := (receiptInventory factory packet stock present origin).2
    ∃ normalized : Words (ordinal+1),
      HEq normalized (written factory packet stock present origin).val ∧
      HEq (read (project (DFinsupp.single (ordinal+1) normalized)) (ordinal+1)) (-effect,effect) ∧
      evaluation (R := ℤ) target.2.1.1.activeEnvironment normalized = 0 ∧
      (effect ≠ 0 → project (DFinsupp.single (ordinal+1) normalized) ≠ 0) := by
  intro packet target stock present origin effect
  let born := sourceBorn factory packet
  let paid : WordAt born := (written factory packet stock present origin).val
  have next : ∃ nextStock : Feed.Inventory (V := L.Value W target.1) (X := X) (s := s),
      target.2.1.1.inventory = some nextStock ∧
      ∃ normalized ∈ Feed.relationSpace nextStock, HEq normalized paid :=
    actual_written_next factory initial cfg language ordinal stock present origin
  rcases next with ⟨_,_,normalized,_,same⟩
  have literal := actual_next_packet factory initial cfg language ordinal
  have transport := transport_observation born target packet.2.2.2.down literal.symm paid normalized same
  have source : packetInventory born paid = (-effect,effect) := native_birth_inventory factory packet stock present origin
  have observed := model_observes_packet factory initial cfg language (ordinal+1) normalized
  have zero : evaluation (R := ℤ) born.2.1.1.activeEnvironment paid = 0 := by
    refine (packet_updated_value born paid).trans ?_
    rw [source]
    exact neg_add_cancel effect
  refine ⟨normalized,same,(heq_of_eq observed).trans (transport.1.trans (heq_of_eq source)),transport.2.2.mpr zero,?_⟩
  intro live empty
  have readZero := (congrArg (fun value => read value (ordinal+1)) empty).trans
    (congrFun (map_zero read) (ordinal+1))
  have nativeZero := transport.2.1.mp (observed.symm.trans readZero)
  exact live (congrArg Prod.snd (source.symm.trans nativeZero))

end ActualCofinalSourceAction.BirthRelation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
