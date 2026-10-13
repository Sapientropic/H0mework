import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.WholeEuler
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
open Complex MeasureTheory Set Filter FourierTransform SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

open FourierTransform

private theorem actual_typed_fourier_Euler (field : TemperedDistribution ℝ ℂ) :
 OriginalRieszSource.GapEuler.euler ((fourierCLM ℂ (TemperedDistribution ℝ ℂ)) field)=
 -(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.GapEuler.euler field) :=
 OriginalRieszSource.GapEuler.euler_fourier field

def actualGapCorrected : BurnolL2:=
 (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)-actualGapA • Seed.seed+
 actualGapBeta • fourierL2 Seed.seed

def actualGapVelocity : BurnolL2:=
 -(1/2:ℂ) • (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)+
 actualGapA • (fourierL2 OriginalRieszSource.Response.wholeU-OriginalRieszSource.Response.wholeV)+
 actualGapBeta • (OriginalRieszSource.Response.wholeU-fourierL2 OriginalRieszSource.Response.wholeV)+
 ((1/2:ℂ)*actualGapA) • Seed.seed+((1/2:ℂ)*actualGapBeta) • fourierL2 Seed.seed

def actualFourierGapCorrected : BurnolL2:=fourierL2 actualGapCorrected
def actualFourierGapVelocity : BurnolL2:= -fourierL2 actualGapVelocity

theorem actual_Fourier_seed_Euler :
 OriginalRieszSource.GapEuler.euler (fourierL2 Seed.seed:TemperedDistribution ℝ ℂ)=
 (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.GapEuler.edge q)+
 (1/2:ℂ) • (fourierL2 Seed.seed:TemperedDistribution ℝ ℂ) :=by
 have source:=actualConstantEulerSource
 have native:(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (Seed.seed:TemperedDistribution ℝ ℂ)=
  (fourierL2 Seed.seed:TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 rw [←native,actual_typed_fourier_Euler,source]
 simp only [map_neg,map_sub,map_smul]
 module

/-- Actual G source contact correction is performed before the unitary strong action is produced. -/
theorem actual_gap_corrected_Euler :
 OriginalRieszSource.GapEuler.euler (actualGapCorrected:TemperedDistribution ℝ ℂ)=
 (actualGapVelocity:TemperedDistribution ℝ ℂ) :=by
 have G:=actual_gap_mean_Euler
 have seed:=actualConstantEulerSource
 have Fseed:=actual_Fourier_seed_Euler
 change OriginalRieszSource.GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 actualGapCorrected)=
  Lp.toTemperedDistributionCLM ℂ volume 2 actualGapVelocity
 unfold actualGapCorrected actualGapVelocity
 simp only [map_sub,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
 rw [G,seed,Fseed]
 have PsiRead:(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) OriginalRieszSource.Response.Psi=
  (OriginalRieszSource.Response.wholeU:TemperedDistribution ℝ ℂ)-
  (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.Response.wholeV:TemperedDistribution ℝ ℂ)-
  (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.GapEuler.edge q):=OriginalRieszSource.Response.Psi_fourier
 have rawPsi:OriginalRieszSource.Response.Psi=
  (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.Response.wholeU:TemperedDistribution ℝ ℂ)-
  (OriginalRieszSource.Response.wholeV:TemperedDistribution ℝ ℂ)-OriginalRieszSource.GapEuler.edge q:=rfl
 rw [PsiRead,rawPsi]
 have FU:(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.Response.wholeU:TemperedDistribution ℝ ℂ)=
  (fourierL2 OriginalRieszSource.Response.wholeU:TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 have FV:(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.Response.wholeV:TemperedDistribution ℝ ℂ)=
  (fourierL2 OriginalRieszSource.Response.wholeV:TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 rw [FU,FV]
 module

/-- The opposite G source action is generated by actual Fourier anti-Euler, not a projection commutation. -/
theorem actual_fourier_gap_corrected_Euler :
 OriginalRieszSource.GapEuler.euler (actualFourierGapCorrected:TemperedDistribution ℝ ℂ)=
 (actualFourierGapVelocity:TemperedDistribution ℝ ℂ) :=by
 have field:(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (actualGapCorrected:TemperedDistribution ℝ ℂ)=
  (fourierL2 actualGapCorrected:TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 have rhs:(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (actualGapVelocity:TemperedDistribution ℝ ℂ)=
  (fourierL2 actualGapVelocity:TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 unfold actualFourierGapCorrected actualFourierGapVelocity
 rw [←field,actual_typed_fourier_Euler,actual_gap_corrected_Euler,rhs]
 exact ((Lp.toTemperedDistributionCLM ℂ volume 2).map_neg _).symm

theorem actual_gap_source_strong :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift actualGapCorrected) actualGapVelocity 0 :=
 OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _ actual_gap_corrected_Euler
theorem actual_fourier_gap_source_strong :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift actualFourierGapCorrected) actualFourierGapVelocity 0 :=
 OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _ actual_fourier_gap_corrected_Euler

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
