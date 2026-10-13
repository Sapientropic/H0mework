import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Action
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.EdgeResponse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Prior
export OriginalReturnResponseSource.Prior (coordinate coordinate_value originalK)
end Prior
namespace ReturnPaid
export OriginalReturnResponseSource.Paid (D Rplus)
end ReturnPaid
namespace Paid
export OriginalReturnResponseSource.Paid (D Rplus)
end Paid

def generatedEtaAction (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(burnolTateReciprocalL2 (generatedFourierReturn coordinate))+
    OriginalReturnResponseSource.generatedReturnDefect coordinate-
    (2*(star coordinate.value-1/2)*Kernel.beta coordinate) •
      ReturnPaid.Rplus (star coordinate.value/2) (ReturnPaid.D (OriginalRieszFiniteSource.fourierPrimitive coordinate))

theorem original_eta_fourier_action (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalReturnResponseSource.retainedEtaAction coordinate=generatedEtaAction coordinate := by
  unfold OriginalReturnResponseSource.retainedEtaAction generatedEtaAction
  rw [original_Rplus_Tate_response]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def completeFourierReturnPrice (h : ℝ) : ℂ :=
  -inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (Paid.D (FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half)))-
  (1/2:ℂ)*(OriginalColumnMomentSource.generatedResponseRead (Prior.coordinate observation nontrivial half) h+
    inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
      (generatedEtaAction (Prior.coordinate observation nontrivial half)))+
  inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (OriginalColumnMomentSource.S.inverseAction (observation.coordinate/2) (star observation.coordinate/2)
      (OriginalColumnMomentSource.contactFluxSource observation nontrivial half))-
  FiniteMobiusResolventFlux.sourceA observation*
    OriginalColumnMomentSource.sourceBandPrice (Prior.coordinate observation nontrivial half)
      (fourierL2 (Prior.originalK observation nontrivial half)) h

theorem original_complete_fourier_return_price (h : ℝ) :
    OriginalReturnResponseSource.completeReturnPrice observation nontrivial half h=completeFourierReturnPrice observation nontrivial half h := by
  unfold OriginalReturnResponseSource.completeReturnPrice completeFourierReturnPrice
  rw [original_eta_fourier_action]

theorem original_correction_fourier_return_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeFourierReturnPrice observation nontrivial half h) := by
  rw [OriginalReturnResponseSource.original_correction_return_price _ _ _ _ nonnegative bounded,original_complete_fourier_return_price]

theorem original_fixed_residual_fourier_return_price :
    -burnolPaFixedShiftResidual (Prior.coordinate observation nontrivial half)
      (by rw [Prior.coordinate_value];exact observation.mathlibZero)=
      (pairedMellinTranslationCharacter observation.coordinate (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star observation.coordinate) (Real.log stageZeroSonineQ))*
          OriginalRieszFinitePairing.kernelSelfSource (Prior.coordinate observation nontrivial half)-
      (1/2:ℂ)*star
        (OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-(Real.log stageZeroSonineQ))
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeFourierReturnPrice observation nontrivial half (Real.log stageZeroSonineQ)) := by
  rw [OriginalReturnResponseSource.original_fixed_residual_return_price,original_complete_fourier_return_price]

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
