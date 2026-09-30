import H0mework.NavierStokes.Restart.NativeRecursion

/-!
# Cumulative kinetic dissipation on the native whole restart run

Every source-selected successor contact already carries the exact kinetic
ledger of its actual unforced whole prefix.  This module telescopes those
same-run payments.  Restart charts therefore cannot charge the physical
vorticity dissipation twice: every finite prefix, and hence the complete
nonnegative family, is paid by the kinetic mass of the initial contact.

No time partition, cutoff, target path, continuation oracle, or payment
certificate is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation

open scoped BigOperators

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

/-- The physical vorticity dissipation paid by the actual successor receipt
generated at one native restart current. -/
def wholeRestartNextKineticDissipationPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  2 * ν.coeff *
    wholePrefixVorticityMass
      (run initial index).nextContact.time
      (run initial index).nextReceipt.stateLimit

theorem wholeRestartNextKineticDissipationPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 ≤ wholeRestartNextKineticDissipationPayment initial index := by
  unfold wholeRestartNextKineticDissipationPayment
  exact mul_nonneg
    (mul_nonneg (by norm_num) ν.coeff_pos.le)
    (wholePrefixVorticityMass_nonneg
      (run initial index).nextContact.time
      (run initial index).nextReceipt.stateLimit)

/-- The actual viscous debit vanishes exactly when the generated prefix
state on that same successor edge is zero.  Positivity of viscosity removes
the scalar factor; the conclusion is therefore a state rigidity theorem,
not a zero-payment label. -/
theorem wholeRestartNextKineticDissipationPayment_eq_zero_iff
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartNextKineticDissipationPayment initial index = 0 ↔
      restrictCommonTimeLpCLM
          (Tsmall := (run initial index).nextContact.time.1)
          (run initial index).nextContact.time.2.2
          (run initial index).nextReceipt.stateLimit = 0 := by
  unfold wholeRestartNextKineticDissipationPayment
  calc
    2 * ν.coeff *
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit = 0 ↔
        wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit = 0 := by
      constructor
      · intro paymentZero
        exact (mul_eq_zero.mp paymentZero).resolve_left
          (mul_ne_zero (by norm_num) ν.coeff_pos.ne')
      · intro stateZero
        rw [stateZero, mul_zero]
    _ ↔ _ := wholePrefixVorticityMass_eq_zero_iff _ _

/-- One actual successor edge spends its vorticity payment and writes the
next physical kinetic state in the same source event. -/
theorem run_contact_kineticDissipation_succ_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    puncturedWholeVorticityKineticMass
          (run initial (index + 1)).contact.physicalState +
        wholeRestartNextKineticDissipationPayment initial index ≤
      puncturedWholeVorticityKineticMass
        (run initial index).contact.physicalState := by
  rw [run_succ]
  change
    puncturedWholeVorticityKineticMass
          (run initial index).nextContact.physicalState +
        2 * ν.coeff *
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit ≤
      puncturedWholeVorticityKineticMass
        (run initial index).contact.physicalState
  exact nextContact_kineticDissipation_le (run initial index)

/-- Total physical vorticity dissipation of the first `length` generated
successor edges. -/
def wholeRestartAccumulatedKineticDissipationPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartNextKineticDissipationPayment initial index

theorem wholeRestartAccumulatedKineticDissipationPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    0 ≤ wholeRestartAccumulatedKineticDissipationPayment
      initial length := by
  unfold wholeRestartAccumulatedKineticDissipationPayment
  exact Finset.sum_nonneg fun index _indexMem =>
    wholeRestartNextKineticDissipationPayment_nonneg initial index

/-- Exact no-double-payment telescope on the authoritative native run. -/
theorem run_contact_kineticMass_add_accumulatedDissipation_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ length : ℕ,
      puncturedWholeVorticityKineticMass
            (run initial length).contact.physicalState +
          wholeRestartAccumulatedKineticDissipationPayment
            initial length ≤
        puncturedWholeVorticityKineticMass
          initial.contact.physicalState
  | 0 => by
      simp [wholeRestartAccumulatedKineticDissipationPayment]
  | length + 1 => by
      have step :=
        run_contact_kineticDissipation_succ_le initial length
      have prefixBound :=
        run_contact_kineticMass_add_accumulatedDissipation_le
          initial length
      unfold wholeRestartAccumulatedKineticDissipationPayment at prefixBound ⊢
      rw [Finset.sum_range_succ]
      calc
        puncturedWholeVorticityKineticMass
              (run initial (length + 1)).contact.physicalState +
            ((∑ index ∈ Finset.range length,
                wholeRestartNextKineticDissipationPayment initial index) +
              wholeRestartNextKineticDissipationPayment initial length) =
            (puncturedWholeVorticityKineticMass
                (run initial (length + 1)).contact.physicalState +
              wholeRestartNextKineticDissipationPayment initial length) +
              ∑ index ∈ Finset.range length,
                wholeRestartNextKineticDissipationPayment initial index := by
          ring
        _ ≤
            puncturedWholeVorticityKineticMass
                (run initial length).contact.physicalState +
              ∑ index ∈ Finset.range length,
                wholeRestartNextKineticDissipationPayment initial index :=
          add_le_add step le_rfl
        _ ≤
            puncturedWholeVorticityKineticMass
              initial.contact.physicalState := prefixBound

/-- Every finite source-selected dissipation prefix is uniformly paid by
the initial contact's physical kinetic mass. -/
theorem wholeRestartAccumulatedKineticDissipationPayment_le_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    wholeRestartAccumulatedKineticDissipationPayment initial length ≤
      puncturedWholeVorticityKineticMass
        initial.contact.physicalState := by
  have ledger :=
    run_contact_kineticMass_add_accumulatedDissipation_le
      initial length
  have terminalNonneg :=
    puncturedWholeVorticityKineticMass_nonneg
      (run initial length).contact.physicalState
  linarith

/-- The complete native successor family has finite physical vorticity
dissipation. -/
theorem summable_wholeRestartNextKineticDissipationPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    Summable (wholeRestartNextKineticDissipationPayment initial) := by
  apply summable_of_sum_range_le
  · exact wholeRestartNextKineticDissipationPayment_nonneg initial
  · intro length
    exact
      wholeRestartAccumulatedKineticDissipationPayment_le_initial
        initial length

/-- The infinite same-run payment retains the sharp initial kinetic
ceiling inherited from the finite telescopes. -/
theorem tsum_wholeRestartNextKineticDissipationPayment_le_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    (∑' index : ℕ,
        wholeRestartNextKineticDissipationPayment initial index) ≤
      puncturedWholeVorticityKineticMass
        initial.contact.physicalState := by
  exact
    (summable_wholeRestartNextKineticDissipationPayment initial).tsum_le_of_sum_range_le
      (wholeRestartAccumulatedKineticDissipationPayment_le_initial initial)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
end NavierStokes
end SaturationMonoid
