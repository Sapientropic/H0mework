import H0mework.NavierStokes.MaterialJets.CovariantReceipt

set_option autoImplicit false
open scoped Matrix BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeDensitizedMaterial

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeMaterialAdjointPrincipal NativeMaterialMomentumJet NativePauliCoframeAction
open NativePhysicalFourier

noncomputable section

local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def gammaCoordinate (direction : Fin 4) : MatterCoordinateCarrier →L[ℂ] MatterCoordinateCarrier :=
  (matterCoordinateEquiv.toLinearMap.comp
    ((Complex.I • diracMatrixMatterAction (diracGamma direction)).comp matterCoordinateEquiv.symm.toLinearMap)).toContinuousLinearMap

theorem gammaCoordinate_apply (direction : Fin 4) (matter : DiracExteriorMatterCarrier) :
    gammaCoordinate direction (matterCoordinateEquiv matter) =
      matterCoordinateEquiv (Complex.I • diracMatrixMatterAction (diracGamma direction) matter) := by
  change matterCoordinateEquiv (Complex.I • diracMatrixMatterAction _ (matterCoordinateEquiv.symm (matterCoordinateEquiv matter))) = _
  rw [matterCoordinateEquiv.symm_apply_apply]

def actualTerm (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) : MatterCoordinateCarrier :=
  matterCoordinateEquiv ((volumeFactor velocity : ℂ) • principal velocity direction
    (NativeBalancedMaterialJet.derivative velocity derivative direction))

theorem spatial_coefficient (velocity : PhysicalSpace) (direction : Fin 3) : coefficient velocity direction.succ = 1 := by
  rw [coefficient_eq]
  simp

theorem actualTerm_spatial (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 3) :
    actualTerm velocity derivative direction.succ = gammaCoordinate direction.succ
      (matterCoordinateEquiv (NativeBalancedMaterialJet.derivative velocity derivative direction.succ)) := by
  rw [actualTerm, gammaCoordinate_apply, principal_gamma, LinearMap.smul_apply, smul_smul]
  have scalar : (volumeFactor velocity : ℂ) *
      (Complex.I * (NativeCanonicalFluidCoframe.diagonal velocity direction.succ : ℂ)⁻¹) = Complex.I := by
    calc
      _ = Complex.I * (coefficient velocity direction.succ : ℂ) := by
        simp only [coefficient, Complex.ofReal_div]
        ring
      _ = _ := by rw [spatial_coefficient]; simp
  rw [scalar]

theorem actualTerm_sum (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    (∑ direction, actualTerm velocity derivative direction) =
      matterCoordinateEquiv ((volumeFactor velocity : ℂ) •
        gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (NativeBalancedMaterialJet.derivative velocity derivative)) := by
  simp only [actualTerm, gaugeVectorAt, principal, LinearMap.smul_apply,
    map_sum, Finset.smul_sum]

end
end SaturationMonoid.NavierStokes.NativeDensitizedMaterial
