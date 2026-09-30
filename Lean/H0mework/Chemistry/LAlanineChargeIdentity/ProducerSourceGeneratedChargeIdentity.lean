import H0mework.Chemistry.LAlanineChargeIdentity.CalculationFullFieldRecovery
import H0mework.Chemistry.LAlanineChargeIdentity.RepresentationElementConsumerKernel

/-! Source-fixed M3 unit fields recover the original nuclear-charge face without another physical step. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open LAlanine40K2025.Force.Interface SourceData

def chargeIdentityClosure : Prop :=
  type_of% Runtime.chargeParent_installed ∧
  type_of% Runtime.chargeParent_actual ∧
  type_of% Runtime.chargeParent_clock ∧
  type_of% Runtime.chargeParent_error_and_memory ∧
  type_of% Recovery.leftInverse_exact ∧
  (∀ i, Algebra.rowAbsSum Source.leftInverse i * Source.epsilon < 1 / 2) ∧
  type_of% FullFieldRecovery.independent_full_field_injective ∧
  (∀ row : FieldRow, WholeField.actualResidual row = Source.reportedFullResidual row ∧
    |Source.reportedFullResidual row| ≤ 509) ∧
  FullFieldRecovery.Compatible Source.decodedCharge ∧
  (∃! z : Atom → Int, FullFieldRecovery.Compatible z) ∧
  (∀ atom : Atom, 0 < Source.decodedCharge atom) ∧
  (∀ atom : Atom, Source.decodedCharge atom = parentCharge atom) ∧
  Nonempty Consumers.elementConsumers.Consumer ∧
  FaceKernelExactAt Consumers.elementConsumers Consumers.elementFace ∧
  Nonempty (Consumers.elementConsumers.Quotient ≃ Set.range Consumers.elementFace) ∧
  (∀ consumer, ∃! factor : Set.range Consumers.elementFace → Consumers.elementConsumers.Output consumer,
    ∀ atom, factor ⟨Consumers.elementFace atom, atom, rfl⟩ = Consumers.elementConsumers.read consumer atom) ∧
  (∀ {Alternate : Type} (alternate : Atom → Alternate),
    FaceKernelExactAt Consumers.elementConsumers alternate →
    ∃! equivalence : Set.range Consumers.elementFace ≃ Set.range alternate,
      ∀ atom, equivalence ⟨Consumers.elementFace atom, atom, rfl⟩ = ⟨alternate atom, atom, rfl⟩) ∧
  (∀ left right : Atom, Consumers.elementFace left ≠ Consumers.elementFace right →
    ¬ Consumers.elementConsumers.Indistinguishable left right) ∧
  (∀ atom : Atom, (Consumers.atomEquivElementResidual atom).1 = Consumers.elementFace atom ∧
    (Consumers.atomEquivElementResidual atom).2.val = atom) ∧
  (∀ atom : Atom, Consumers.atomEquivElementResidual.symm (Consumers.atomEquivElementResidual atom) = atom) ∧
  type_of% Consumers.sameElement_differentActualAttraction ∧
  type_of% Consumers.element_cannotMint_attraction ∧
  type_of% Consumers.elementFace_not_injective

theorem sourceGeneratedChargeIdentity : chargeIdentityClosure :=
  ⟨Runtime.chargeParent_installed, Runtime.chargeParent_actual, Runtime.chargeParent_clock,
    Runtime.chargeParent_error_and_memory, Recovery.leftInverse_exact, Recovery.row_separation,
    FullFieldRecovery.independent_full_field_injective, WholeField.actualResidual_exact_and_bounded,
    FullFieldRecovery.decoded_full_field_compatible, FullFieldRecovery.actual_integer_recovery_unique,
    Recovery.decoded_positive, Recovery.decoded_eq_original, Consumers.elementConsumers.positive,
    Consumers.elementFace_kernelExact, ⟨Consumers.elementQuotientEquivRange⟩,
    Consumers.everyConsumer_uniqueFactorization, fun alternate exact => Consumers.completeCarrier_uniqueIso alternate exact,
    fun _ _ different => Consumers.noHiddenElementDirection different,
    Consumers.atomEquivElementResidual_commutes, Consumers.atomEquivElementResidual_reconstructs,
    Consumers.sameElement_differentActualAttraction, Consumers.element_cannotMint_attraction,
    Consumers.elementFace_not_injective⟩

end LAlanine40K2025.ChargeIdentity.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
