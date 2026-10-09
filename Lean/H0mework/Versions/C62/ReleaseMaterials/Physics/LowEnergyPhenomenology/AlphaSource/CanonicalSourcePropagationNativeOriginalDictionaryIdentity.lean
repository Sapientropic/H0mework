import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeSourceRecords
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeStructuralSourceSort

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open PreparationVacuumOriginalGreenFeedback
open scoped BigOperators

def nativeWholeSourceRecords := nativeGravitySourceRecords ++ nativeGaugeSourceRecords ++
  nativeScalarSourceRecords ++ nativeDiracSourceRecords

def nativeWholeJacobiTerms := nativeSourceQuadraticTerms nativeWholeSourceRecords




theorem nativeWholeJacobiTerms_original :
    nativeFuelCanonical nativeWholeJacobiTerms = nativeFuelCanonical originalJacobiTerms := by
  decide +kernel

theorem nativeWholeJacobiMatrix_original (p : Fin 4 → ℂ) :
    sourceMatrix nativeWholeJacobiTerms p = originalJacobi p := by
  rw [←nativeFuelCanonical_value nativeWholeJacobiTerms p, nativeWholeJacobiTerms_original,
    nativeFuelCanonical_value]
  rfl

theorem nativeWholeLiteralFourier_original (p : Fin 4 → ℂ) :
    nativeFourierHessian (nativeLiteralHessian (nativeSourceRealTerms nativeWholeSourceRecords)) p =
      originalJacobi p := by
  rw [nativeSourceFourier_sound]
  exact nativeWholeJacobiMatrix_original p

end LowEnergy.SourcePropagationNativeActionHessian
