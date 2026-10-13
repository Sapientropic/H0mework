import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ReturnResponse.Consumer
import H0mework.Versions.V2.Arithmetic.RieszEuler.SourceKernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
open OriginalRieszSource
namespace C
export OriginalColumnMomentSource (contactResponse wholeContactResponse originalB)
end C
local notation "q" => (1/4:ℝ)

def fullFourierSource (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolRadiusTruncatedFourierRaw q (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2) x

def fullFourierResponse (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolRadiusTruncatedFourierRaw q (C.contactResponse coordinate) x

-- The whole Fourier source retains the actual Fourier mean beyond the centered return r.
theorem original_full_source_mean (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    fullFourierSource coordinate x=burnolRieszReturnRaw coordinate x+
      burnolQuarterMeanCoefficient (burnolTruncatedFourier (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)) := by
  unfold fullFourierSource burnolRieszReturnRaw burnolMeanZeroFourierRaw
  ring

 theorem original_full_response_ward (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    fullFourierResponse coordinate x=Kernel.beta coordinate*Edge.raw q x-
      ((x:ℂ)*burnolRieszReturnRawDerivative coordinate x+star coordinate.value*fullFourierSource coordinate x) := by
  have generated := Euler.source_kernel_ward coordinate (Euler.sourceEuler coordinate) (Euler.source_euler coordinate) x
  have solved := Euler.sourceEuler_eq coordinate
  have response : (Euler.sourceEuler coordinate:BurnolQuarterIntervalL2)=
      (star coordinate.value-1/2) • (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)+C.contactResponse coordinate := by
    rw [solved]
    unfold C.contactResponse
    change ((star coordinate.value-1/2) • (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)+Kernel.A coordinate • (Response.u:BurnolQuarterIntervalL2)-Kernel.beta coordinate • (Response.v:BurnolQuarterIntervalL2))=_
    module
  have fourier := congrArg (fun value : BurnolQuarterIntervalL2=>burnolRadiusTruncatedFourierRaw q value x) response
  simp only [burnolRadiusTruncatedFourierRaw_add,burnolRadiusTruncatedFourierRaw_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at fourier
  unfold fullFourierResponse fullFourierSource
  rw [fourier] at generated
  linear_combination generated

 theorem actual_fourier_response_read (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (C.wholeContactResponse coordinate):ℝ→ℂ)=ᵐ[volume] fullFourierResponse coordinate :=
  burnolRadiusFourierL2_zeroExtension_ae_eq_raw (C.contactResponse coordinate)

 theorem actual_fourier_source_read (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (C.originalB coordinate):ℝ→ℂ)=ᵐ[volume] fullFourierSource coordinate :=
  burnolRadiusFourierL2_zeroExtension_ae_eq_raw (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
