import H0mework.Chemistry.LAlanineChargeIdentity.CalculationIntegerRecovery
import H0mework.Chemistry.LAlanineChargeIdentity.CalculationWholeField

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.FullFieldRecovery

open LAlanine40K2025.Force.Interface SourceData
open scoped Matrix BigOperators
noncomputable section

theorem selectedB_commutes (i j : Atom) :
    Source.selectedB i j = Source.fullB (Source.selectedRows i) j := by
  change (Source.selectedBInteger i j : ℚ) / Source.unitScale =
    (Source.fullBInteger (Source.selectedRows i) j : ℚ) / Source.unitScale
  rw [ExactRows.selectedIncidenceRows i j]

theorem selected_mulVec_commutes (z : Atom → ℚ) (i : Atom) :
    (Source.selectedB *ᵥ z) i = (Source.fullB *ᵥ z) (Source.selectedRows i) := by
  change (∑ j : Atom, Source.selectedB i j * z j) = ∑ j : Atom, Source.fullB (Source.selectedRows i) j * z j
  exact Finset.sum_congr rfl (fun j _ => congrArg (· * z j) (selectedB_commutes i j))

theorem independent_full_field_injective :
    Function.Injective (fun z : Atom → ℚ => Source.fullB *ᵥ z) := by
  intro z w same
  apply Recovery.independentField_injective
  funext i
  change (Source.selectedB *ᵥ z) i = (Source.selectedB *ᵥ w) i
  rw [selected_mulVec_commutes, selected_mulVec_commutes]
  exact congrFun same (Source.selectedRows i)

theorem residual_commutes (z : Atom → Int) (i : Atom) :
    Algebra.residual Source.selectedB Source.selectedField z i =
      Algebra.residual Source.fullB Source.fullField z (Source.selectedRows i) := by
  change Source.fullField (Source.selectedRows i) + (Source.selectedB *ᵥ (fun j => (z j : ℚ))) i = _
  rw [selected_mulVec_commutes]
  rfl

theorem reported_full_field_exact (row : FieldRow) :
    Algebra.residual Source.fullB Source.fullField Source.reportedCharge row =
      (Source.reportedFullResidual row : ℚ) / 1000000000000000 := by
  change (parentFieldInteger row : ℚ) / 1000000000000 +
    (∑ j : Atom, ((Source.fullBInteger row j : ℚ) / 1000000000000000) * (Source.reportedCharge j : ℚ)) = _
  rw [Algebra.scaled_residual_entry]
  exact congrArg (fun r : Int => (r : ℚ) / 1000000000000000)
    (WholeField.actualResidual_exact_and_bounded row).1

def Compatible (z : Atom → Int) : Prop :=
  ∀ row : FieldRow, |Algebra.residual Source.fullB Source.fullField z row| ≤ Source.epsilon

theorem reported_full_field_compatible : Compatible Source.reportedCharge := by
  intro row
  rw [reported_full_field_exact]
  apply Algebra.scaled_residual_bound
  have bound := (WholeField.actualResidual_exact_and_bounded row).2
  omega

theorem decoded_full_field_compatible : Compatible Source.decodedCharge := by
  rw [Recovery.decoded_eq_reported]
  exact reported_full_field_compatible

theorem actual_integer_recovery_unique : ∃! z : Atom → Int, Compatible z := by
  refine ⟨Source.decodedCharge, decoded_full_field_compatible, ?_⟩
  intro z compatible
  apply Recovery.compatible_integer_unique
  intro i
  rw [residual_commutes]
  exact compatible (Source.selectedRows i)

end
end LAlanine40K2025.ChargeIdentity.FullFieldRecovery
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
