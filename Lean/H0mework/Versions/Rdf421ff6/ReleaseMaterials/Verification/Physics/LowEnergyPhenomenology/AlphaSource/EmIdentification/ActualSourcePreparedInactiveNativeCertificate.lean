import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedInactiveNativeData

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedInactiveNativeCertificate
open PreparationVacuumOriginalGreenFeedback ActualSourcePreparedInactiveNativeData
open scoped Matrix BigOperators

def sourceInactive (i : Fin 289) : Prop := (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val
instance (i : Fin 289) : Decidable (sourceInactive i) := inferInstanceAs (Decidable ((73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val))

/-- Restriction of the same complete original source dictionary. All three
spatial coordinates survive; only the prescribed static temporal face is read. -/
def sourceStaticInactiveTerms : List SourceTerm :=
  originalJacobiTerms.filter (fun a => decide (a.powers.temporal=0 ∧ sourceInactive a.row ∧ sourceInactive a.column))

theorem source_inactive_native_cleared_left_certificate :
    fastNormalizeTerms (productTerms sourceInactiveInverseNumeratorTerms sourceStaticInactiveTerms ++
      negativeTerms sourceInactiveWeightTerms)=[] := by
  decide +kernel

theorem source_inactive_native_cleared_right_certificate :
    fastNormalizeTerms (productTerms sourceStaticInactiveTerms sourceInactiveInverseNumeratorTerms ++
      negativeTerms sourceInactiveWeightTerms)=[] := by
  decide +kernel

/-- The untrusted generated numerator is multiplied back into the original
source on both sides before any inverse or Green regularity is asserted. -/
theorem source_inactive_native_cleared_products (p : Fin 4 → ℂ) :
    sourceMatrix sourceInactiveInverseNumeratorTerms p*sourceMatrix sourceStaticInactiveTerms p=
      sourceMatrix sourceInactiveWeightTerms p ∧
    sourceMatrix sourceStaticInactiveTerms p*sourceMatrix sourceInactiveInverseNumeratorTerms p=
      sourceMatrix sourceInactiveWeightTerms p := by
  constructor
  · rw [←productTerms_value]
    exact normalization_equal _ _ source_inactive_native_cleared_left_certificate p
  · rw [←productTerms_value]
    exact normalization_equal _ _ source_inactive_native_cleared_right_certificate p

end LowEnergy.GaussComposite.ActualSourcePreparedInactiveNativeCertificate
