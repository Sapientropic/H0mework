import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Factory
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Coverage

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptPayload
open scoped Classical
noncomputable section
universe u v w
variable {rank : Ordinal.{u}}

private theorem zero_test (p : Prop) : (if p then (0 : ℝ) else 1) = 0 ↔ p := by
  by_cases present : p <;> simp only [present, if_true, if_false, one_ne_zero, iff_self]

private def imageEquiv {A : Type v} (encode : A ↪ MotherReceiptHigher.Base rank)
    (p : MotherReceiptHigher.Base rank → Prop)
    (complete : ∀ b, p b ↔ ∃ a, encode a = b) : A ≃ {b // p b} :=
  Equiv.ofBijective (fun a => ⟨encode a, (complete _).mpr ⟨a, rfl⟩⟩) ⟨
    fun _ _ same => encode.injective (congrArg Subtype.val same),
    fun b => by obtain ⟨a, ha⟩ := (complete b.val).mp b.property; exact ⟨a, Subtype.ext ha⟩⟩

structure Presentation (I : Type v) (F : I → Type w) (selected : Sigma F) (value : Value rank) where
  answer : I ≃ Answer value.1
  receipt : ∀ index, F index ≃ Receipt value.1 (answer index)
  selected_eq : value.2 = ⟨answer selected.1, receipt selected.1 selected.2⟩

def Presentation.totalEquiv {I : Type v} {F : I → Type w} {selected : Sigma F} {value : Value rank}
    (p : Presentation I F selected value) : Sigma F ≃ Point value.1 :=
  (Equiv.sigmaCongrRight p.receipt).trans (Equiv.sigmaCongrLeft p.answer)

theorem Presentation.total_projects {I : Type v} {F : I → Type w} {selected : Sigma F} {value : Value rank}
    (p : Presentation I F selected value) (point : Sigma F) :
    (p.totalEquiv point).1 = p.answer point.1 := rfl

/-- The original types are inverse schemas. The selected answer and receipt
are both read from the actual generated dependent point. -/
def Presentation.restrict {I : Type v} {F : I → Type w} {selected : Sigma F} {value : Value rank}
    (p : Presentation I F selected value) : Sigma F := p.totalEquiv.symm value.2

theorem Presentation.restrict_eq {I : Type v} {F : I → Type w} {selected : Sigma F} {value : Value rank}
    (p : Presentation I F selected value) : p.restrict = selected := by
  apply p.totalEquiv.injective
  rw [Presentation.restrict, Equiv.apply_symm_apply]
  exact p.selected_eq

theorem every_carrier (I : Type v) (F : I → Type w)
    (indexCode : I ↪ MotherReceiptHigher.Base rank)
    (valueCode : (Sigma F) ↪ MotherReceiptHigher.Base rank) :
    ∃ base : MotherReceiptHigher.Material rank, ∃ context : I ≃ Answer base,
      Nonempty ((index : I) → F index ≃ Receipt base (context index)) := by
  let domain (address : MotherReceiptHigher.Base rank) := ∃ index, indexCode index = address
  let fibers (address : MotherReceiptHigher.Base rank) := ∃ point : Sigma F,
    indexCode point.1 = (MotherReceiptHigher.unpair rank address).1 ∧
      valueCode point = (MotherReceiptHigher.unpair rank address).2
  obtain ⟨base, readback⟩ := MotherReceiptHigher.read_surjective rank (fun address tag =>
    if tag = 0 then (if domain address then 0 else 1) else (if fibers address then 0 else 1))
  have at_domain (address : MotherReceiptHigher.Base rank) : bit base 0 address ↔ domain address := by
    simp only [bit, readback, ite_true]
    exact zero_test _
  let context := imageEquiv indexCode (bit base 0) at_domain
  have at_receipt (index : I) (address : MotherReceiptHigher.Base rank) :
      relation base 1 (context index).val address ↔ ∃ receipt : F index, valueCode ⟨index, receipt⟩ = address := by
    simp only [relation, bit, readback, show ¬ (1 : Nat) = 0 from by decide, if_false]
    have represented : fibers (MotherReceiptHigher.pair rank ((context index).val, address)) ↔
        ∃ receipt : F index, valueCode ⟨index, receipt⟩ = address := by
      simp only [fibers, MotherReceiptHigher.unpair_pair]
      change (∃ point : Sigma F, indexCode point.1 = indexCode index ∧ valueCode point = address) ↔ _
      constructor
      · rintro ⟨⟨other, receipt⟩, same, encoded⟩
        have same := indexCode.injective same
        cases same
        exact ⟨receipt, encoded⟩
      · rintro ⟨receipt, encoded⟩
        exact ⟨⟨index, receipt⟩, rfl, encoded⟩
    exact (zero_test _).trans represented
  exact ⟨base, context, ⟨fun index => imageEquiv
    ((Function.Embedding.sigmaMk index).trans valueCode)
    (relation base 1 (context index).val) (at_receipt index)⟩⟩

theorem every_payload_at (I : Type v) (F : I → Type w) (selected : Sigma F)
    (indexCode : I ↪ MotherReceiptHigher.Base rank)
    (valueCode : (Sigma F) ↪ MotherReceiptHigher.Base rank) :
    ∃ material : MotherReceiptHigher.Material rank, ∃ value : Value rank,
      form material = some value ∧ Nonempty (Presentation I F selected value) := by
  obtain ⟨base, answer, ⟨receipt⟩⟩ := every_carrier I F indexCode valueCode
  let point : Point base := ⟨answer selected.1, receipt selected.1 selected.2⟩
  obtain ⟨material, formed⟩ := every_selected base point
  exact ⟨material, ⟨base, point⟩, formed, ⟨{ answer, receipt, selected_eq := rfl }⟩⟩

/-- All answer/receipt fibres and their selected dependent value are covered
in one stage. No address or fixed-carrier condition is a caller premise. -/
theorem every_payload (I : Type v) (F : I → Type w) (selected : Sigma F) :
    ∃ rank : Ordinal.{max v w}, ∃ material : MotherReceiptHigher.Material rank,
      ∃ value : Value rank, form material = some value ∧
        Nonempty (Presentation I F selected value) := by
  let Total := ULift.{w, v} I ⊕ Sigma F
  let rank := MotherReceiptHigher.carrierRank Total
  let shared := MotherReceiptHigher.carrierAddress Total
  let indexCode : I ↪ MotherReceiptHigher.Base rank :=
    ⟨fun value => shared (.inl (ULift.up value)), fun _ _ same =>
      congrArg ULift.down (Sum.inl.inj (shared.injective same))⟩
  let valueCode : (Sigma F) ↪ MotherReceiptHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨material, value, formed, presentation⟩ := every_payload_at I F selected indexCode valueCode
  exact ⟨rank, material, value, formed, presentation⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptPayload
