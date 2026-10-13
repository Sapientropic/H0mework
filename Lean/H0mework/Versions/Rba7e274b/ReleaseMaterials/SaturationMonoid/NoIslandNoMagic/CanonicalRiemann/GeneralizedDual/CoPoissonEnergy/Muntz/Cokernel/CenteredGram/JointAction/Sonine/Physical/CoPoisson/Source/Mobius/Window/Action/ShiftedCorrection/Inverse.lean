import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.BandEuler
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalInverseReturnActionSource
open Complex MeasureTheory Set Filter
open scoped Topology InnerProductSpace BigOperators
open OriginalRieszSource
namespace Paid
export FiniteMobiusResolventFlux (M D actualMean coefficient)
end Paid
local notation "q" => (1/4:ℝ)

def returnMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (burnolTruncatedFourier (Constructor.returnState coordinate:BurnolQuarterIntervalL2))
def fullInverseReturnProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolRieszSingleFourierSourceRaw coordinate x-Translator.ForcingWhole.raw coordinate x+
    Translator.ForcingMeanZero.mean coordinate+returnMean coordinate

theorem original_inverse_return_profile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    Constructor.fourierRaw (burnolRieszReturnRaw coordinate) x=fullInverseReturnProfile coordinate x := by
  have generated := congrFun (Constructor.secondReturnRaw_eq_fourier coordinate) x
  change Constructor.secondReturnRaw coordinate x=Constructor.fourierRaw (burnolRieszReturnRaw coordinate) x-returnMean coordinate at generated
  unfold fullInverseReturnProfile
  change Constructor.fourierRaw (burnolRieszReturnRaw coordinate) x=(burnolRieszFourierForcingRaw coordinate x+Constructor.secondReturnRaw coordinate x)-Translator.ForcingWhole.raw coordinate x+Translator.ForcingMeanZero.mean coordinate+returnMean coordinate
  rw [Translator.ForcingMeanZero.forcingRaw_eq,generated]
  ring

def wholeReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 := OriginalColumnMomentSource.wholeReturn coordinate

theorem original_return_fourier_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (wholeReturn coordinate):ℝ→ℂ)=ᵐ[volume] fullInverseReturnProfile coordinate := by
  have source:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw (Constructor.returnState coordinate:BurnolQuarterIntervalL2)
  have raw : burnolRadiusTruncatedFourierRaw q (Constructor.returnState coordinate:BurnolQuarterIntervalL2)=
      Constructor.fourierRaw (burnolRieszReturnRaw coordinate) := by
    funext x
    exact (congrFun (Constructor.fourierRaw_state (Constructor.returnState coordinate:BurnolQuarterIntervalL2)) x).symm.trans
      (congrFun (Constructor.fourierRaw_congr _ _ (Constructor.returnState_read coordinate)) x)
  change (fourierL2 (wholeReturn coordinate):ℝ→ℂ)=ᵐ[volume] burnolRadiusTruncatedFourierRaw q
    (Constructor.returnState coordinate:BurnolQuarterIntervalL2) at source
  apply source.trans
  exact Filter.EventuallyEq.of_eq (by funext x;rw [raw,original_inverse_return_profile])

def inverseReturnMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  (2:ℂ)*(∫ x : ℝ in symmetricInterval q,fullInverseReturnProfile coordinate x)

theorem original_inverse_return_mean (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.actualMean (fourierL2 (wholeReturn coordinate))=inverseReturnMean coordinate := by
  change (‖intervalConstant q‖^2:ℂ)⁻¹*inner ℂ (intervalConstant q)
    (burnolRadiusRestriction q (fourierL2 (wholeReturn coordinate)))=_
  rw [burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)]
  norm_num
  rw [L2.inner_def]
  unfold inverseReturnMean
  congr 1
  apply integral_congr_ae
  filter_upwards [intervalConstant_coeFn q,LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
    (fourierL2 (wholeReturn coordinate)),ae_restrict_of_ae (original_return_fourier_raw coordinate)] with x constant restricted source
  change burnolRadiusRestriction q (fourierL2 (wholeReturn coordinate)) x=fourierL2 (wholeReturn coordinate) x at restricted
  rw [constant,restricted,source,RCLike.inner_apply]
  simp only [starRingEnd_apply,star_one,mul_one]
end OriginalInverseReturnActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
