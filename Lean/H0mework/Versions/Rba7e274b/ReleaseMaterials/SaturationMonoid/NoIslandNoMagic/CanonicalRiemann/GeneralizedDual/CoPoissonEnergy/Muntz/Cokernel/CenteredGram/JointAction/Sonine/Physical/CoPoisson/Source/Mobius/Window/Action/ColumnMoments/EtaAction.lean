import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.ColumnPullback
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource

def wholeReturnResponse (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  wholeReturnEuler coordinate+(star coordinate.value-1/2) • wholeReturn coordinate

def etaRemainingSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(burnolTateReciprocalL2 (FiniteMobiusResolventFlux.M (fourierL2 (wholeContactResponse coordinate))))+
    S.D (wholeReturnResponse coordinate)-
      (2*(star coordinate.value-1/2)*Kernel.beta coordinate) • S.D (OriginalRieszFiniteSource.fourierPrimitive coordinate)

-- F² is reduced only on the original even response; the Tate, return, and Fourier endpoint prices remain.
theorem original_eta_defect_action (coordinate : BurnolCompletedMellinCoordinate) :
    S.D (FiniteMobiusResolventFlux.S.regularSource coordinate)=
      FiniteMobiusResolventFlux.M (wholeContactResponse coordinate)+etaRemainingSource coordinate := by
  rw [original_eta_actual_response]
  unfold sourcePrimitiveEta
  simp only [map_sub,map_add,map_smul]
  have forward : S.D (fourierL2 (wholeContactResponse coordinate))=
      FiniteMobiusResolventFlux.M (wholeContactResponse coordinate)-
        burnolTateReciprocalL2 (FiniteMobiusResolventFlux.M (fourierL2 (wholeContactResponse coordinate))) := by
    unfold S.D
    simp only [sub_apply,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry]
    rw [fourierL2_fourierL2,whole_response_even]
  rw [forward]
  unfold etaRemainingSource wholeReturnResponse
  simp only [map_add,map_smul]
  module

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
