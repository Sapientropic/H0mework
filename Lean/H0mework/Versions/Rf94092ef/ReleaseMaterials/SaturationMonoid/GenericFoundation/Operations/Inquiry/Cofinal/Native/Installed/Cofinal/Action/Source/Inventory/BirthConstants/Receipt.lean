import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthConstants
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Action

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.BirthRelation

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual
open SourceInventoryExecutionFeed.AdmissionReceipt (formalItems formal_source_items update_inventory_formal_items)

namespace Feed
export SourceInventoryExecutionFeed (Inventory relationSpace history_relation_space)
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end Feed
namespace Located
export SourceReceiptOccurrence (acted atBirth SupportIndex)
end Located
namespace Native
export ActualNativeRelationTransport (normalizeSource bornHistory)
end Native

variable {S : Type u} {V Y : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}

private theorem constant_inventory (before increment : Env V Y) (table : V s →₀ ℤ) :
    updateInventory (R := ℤ) before increment (constantMap (R := ℤ) (Var := Y) table) =
      (ScalarRelationPresentation.freeEvaluation (R := ℤ) (V s) table, 0) := by
  have effect : (effectEvaluator (R := ℤ) (s := s) before increment).comp (constantMap (R := ℤ)) = 0 := by
    apply Finsupp.lhom_ext
    intro value coefficient
    simp only [LinearMap.comp_apply, constantMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      effectEvaluator, Finsupp.linearCombination_single, Expr.effect, smul_zero, LinearMap.zero_apply]
  exact Prod.ext (LinearMap.congr_fun (evaluation_constantMap (R := ℤ) before) table)
    (LinearMap.congr_fun effect table)

private theorem value_map_items (environment : Env V Y) (items : List (Expr V Y s × ℤ)) :
    (∑ i : Fin items.length, Finsupp.single ((items.get i).1.eval environment) (items.get i).2) =
      valueMap (R := ℤ) environment (formalItems items) := by
  let read := fun item : Expr V Y s × ℤ => Finsupp.single (item.1.eval environment) item.2
  change (∑ i : Fin items.length, read (items.get i)) = _
  rw [← List.sum_ofFn]
  change (List.ofFn (read ∘ items.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get, formalItems, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro item _
  simp only [Function.comp_apply, read, valueMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

variable {W X : S → Type u} [∀ t, AddCommGroup (W t)]
attribute [local instance] familyGroups
variable (factory : SF.Factory W X s) (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
variable (stock : Feed.Inventory (V := L.Value W packet.1) (X := X) (s := s))
variable (installed : packet.2.1.1.inventory = some stock) (origin : Feed.RelationOccurrence stock)

local notation "acted" => Located.acted factory packet stock installed origin
local notation "support" => Located.SupportIndex factory packet stock installed origin
local notation "executed" => Located.atBirth factory packet stock installed origin
local notation "word" => sourceWordAction packet origin.word
local notation "frame" => selected factory packet
set_option quotPrecheck false in
local notation "config" => (nativePacket factory packet).2.2.1
set_option quotPrecheck false in
local notation "decoded" => (sourceBorn factory packet).2.1.1.activeEnvironment

/-- The signed terminal constants come from the exact support addresses of this relation. -/
def receiptTable : L.Value W (packet.1+1) s →₀ ℤ :=
  ∑ i : support, Finsupp.single ((executed i).request.expression.eval (executed i).decoder)
    (executed i).request.coefficient

theorem receipt_table_action :
    receiptTable factory packet stock installed origin = birthConstantTable factory packet origin.word := by
  let items := Coefficients.sourceItems (acted).word
  calc
    _ = ∑ i : Fin items.length, Finsupp.single ((items.get i).1.eval (decoded)) (items.get i).2 := by
      apply Finset.sum_congr rfl
      intro i _
      let request := executed i
      change Finsupp.single ((items.get i).1.eval request.decoder) (items.get i).2 = _
      rw [← request.decoder_source]
    _ = valueMap (R := ℤ) (decoded) (formalItems items) := value_map_items _ _
    _ = _ := (congrArg (valueMap (R := ℤ) (decoded)) (formal_source_items (acted).word)).trans
      (birth_constant_table_decoded factory packet origin.word).symm

/-- Every exact support receipt contributes both channels of the actual birth action. -/
def receiptInventory : PairValue (L.Value W (packet.1+1)) s :=
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (frame).activeEnvironment
  let increment := birthIncrement factory packet
  ∑ i : support, let request := (executed i).request
    request.coefficient • (liftExpr request.expression).eval (pairEnvironment before increment)

theorem receipt_inventory_action :
    receiptInventory factory packet stock installed origin = birthWordInventory factory packet origin.word := by
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (frame).activeEnvironment
  let increment := birthIncrement factory packet
  let items := Coefficients.sourceItems (acted).word
  let update := updateInventory (R := ℤ) (s := s) before increment
  change (∑ i : Fin items.length, let item := items.get i
      item.2 • (liftExpr item.1).eval (pairEnvironment before increment)) = update (word)
  exact (update_inventory_formal_items before increment items).trans
    (congrArg update (formal_source_items (acted).word))

/-- Normalize the same relation in its installed born history. -/
def written : (Native.bornHistory (frame) (config)).relationClosure :=
  Native.normalizeSource (frame) (config) ⟨word, Submodule.subset_span (by
    change PresentedRelationEventAt.relation word ∈
      (ActualNativeRelationTransport.AS.stockScalar (frame) (config)).trace
    rw [(acted).trace_eq]
    exact List.mem_append_right _ List.mem_cons_self)⟩

theorem written_from_receipts :
    (written factory packet stock installed origin).val =
      word - constantMap (R := ℤ) (Var := packet.2.2.1.LowVar)
        (receiptTable factory packet stock installed origin) := by
  let table := receiptTable factory packet stock installed origin
  let addConstant := fun values : L.Value W (packet.1+1) s →₀ ℤ =>
    word - constantMap (R := ℤ) (Var := packet.2.2.1.LowVar) values
  have action : table = valueMap (R := ℤ) (decoded) (word) :=
    (receipt_table_action factory packet stock installed origin).trans
      (birth_constant_table_decoded factory packet origin.word)
  have paid : (written factory packet stock installed origin).val = addConstant (valueMap (R := ℤ) (decoded) (word)) := rfl
  exact paid.trans (congrArg addConstant action.symm)

private theorem opposite_components {G : Type u} [AddCommGroup G] (value : G × G) :
    value - (value.1+value.2,0) = (-value.2,value.2) := by
  rcases value with ⟨old, effect⟩
  apply Prod.ext
  · change old-(old+effect) = -effect
    abel
  · exact sub_zero effect

/-- The complete written relation retains its two opposite effect channels. -/
theorem written_inventory :
    let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (frame).activeEnvironment
    let increment := birthIncrement factory packet
    let effect := (receiptInventory factory packet stock installed origin).2
    updateInventory (R := ℤ) before increment (written factory packet stock installed origin).val =
      (-effect, effect) := by
  intro before increment effect
  let table := receiptTable factory packet stock installed origin
  let pair := receiptInventory factory packet stock installed origin
  have action := receipt_inventory_action factory packet stock installed origin
  let update := updateInventory (R := ℤ) (s := s) before increment
  have source : update (word) = pair := action.symm
  have value : ScalarRelationPresentation.freeEvaluation (R := ℤ) (L.Value W (packet.1+1) s) table =
      pair.1+pair.2 := (congrArg _ (receipt_table_action factory packet stock installed origin)).trans
        ((birth_constant_table_value factory packet origin.word).trans
          (congrArg (fun coordinates => coordinates.1+coordinates.2) action.symm))
  have constants : update (constantMap (R := ℤ) (Var := packet.2.2.1.LowVar) table) = (pair.1+pair.2,0) :=
    (constant_inventory before increment table).trans (congrArg (fun v => (v,0)) value)
  have formula := written_from_receipts factory packet stock installed origin
  change update (written factory packet stock installed origin).val = (-pair.2,pair.2)
  calc
    _ = update (word) - update (constantMap (R := ℤ) (Var := packet.2.2.1.LowVar) table) :=
      (congrArg update formula).trans (map_sub update _ _)
    _ = pair - (pair.1+pair.2,0) := congrArg₂ (· - ·) source constants
    _ = (-pair.2,pair.2) := opposite_components pair

theorem written_inverse_fibre (candidate : Formal ℤ (L.Value W (packet.1+1)) packet.2.2.1.LowVar s) :
    let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (frame).activeEnvironment
    let increment := birthIncrement factory packet
    let effect := (receiptInventory factory packet stock installed origin).2
    let update := updateInventory (R := ℤ) (s := s) before increment
    canonicalResidual update candidate = canonicalResidual update (written factory packet stock installed origin).val ↔
      evaluation (R := ℤ) before candidate = -effect ∧ effectEvaluator (R := ℤ) before increment candidate = effect := by
  intro before increment effect update
  let normalized : Formal ℤ (L.Value W (packet.1+1)) packet.2.2.1.LowVar s :=
    (written factory packet stock installed origin).val
  have values : update normalized = (-effect,effect) := written_inventory factory packet stock installed origin
  have fibre : canonicalResidual update candidate = canonicalResidual update normalized ↔
      update candidate = update normalized := by
    simpa only [map_sub,sub_eq_zero] using canonicalResidual_eq_zero_iff update (candidate-normalized)
  exact fibre.trans (by
    rw [values]
    change (evaluation (R := ℤ) before candidate, effectEvaluator (R := ℤ) before increment candidate) =
      (-effect,effect) ↔ _
    simp only [Prod.mk.injEq])

section Next

private theorem keep_installed_span {Y Z : S → Type u}
    (packet : AS.AdmissionPacket (W := W) (X := Y) (s := s))
    (target : AS.AdmissionPacket (W := W) (X := Z) (s := s))
    (sameLanguage : Y = Z) (samePacket : packetTransport sameLanguage packet = target)
    (inventory : Feed.Inventory (V := L.Value W packet.1) (X := Y) (s := s))
    (present : packet.2.1.1.inventory = some inventory)
    (value : Formal ℤ (L.Value W packet.1) Y s) (paid : value ∈ Feed.relationSpace inventory) :
    ∃ nextStock : Feed.Inventory (V := L.Value W target.1) (X := Z) (s := s),
      target.2.1.1.inventory = some nextStock ∧
      ∃ nextWord ∈ Feed.relationSpace nextStock, HEq nextWord value := by
  cases sameLanguage
  cases samePacket
  exact ⟨inventory,present,value,paid,HEq.rfl⟩

/-- The normalized word enters the original next inventory with the exact packet and language transports. -/
theorem actual_written_next (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
    (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s)) (language : cfg.LowVar = X)
    (ordinal : Nat) :
    let packet := D.packetAt factory initial cfg language ordinal
    let target := D.packetAt factory initial cfg language (ordinal+1)
    ∀ (stock : Feed.Inventory (V := L.Value W packet.1) (X := X) (s := s))
      (installed : packet.2.1.1.inventory = some stock) (origin : Feed.RelationOccurrence stock),
    ∃ nextStock : Feed.Inventory (V := L.Value W target.1) (X := X) (s := s),
      target.2.1.1.inventory = some nextStock ∧
      ∃ nextWord ∈ Feed.relationSpace nextStock,
        HEq nextWord (written factory packet stock installed origin).val := by
  intro packet target stock installed origin
  let born := sourceBorn factory packet
  let paid := written factory packet stock installed origin
  have installedNext := born_inventory factory packet
  have same := actual_next_packet factory initial cfg language ordinal
  have normalized : paid.val ∈ Feed.relationSpace (bornStock factory packet) := by
    simpa only [ActualNativeRelationTransport.bornHistory, Feed.history_relation_space] using paid.property
  exact keep_installed_span born target packet.2.2.2.down same.symm
    (bornStock factory packet) installedNext paid.val normalized

end Next

end ActualCofinalSourceAction.BirthRelation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
