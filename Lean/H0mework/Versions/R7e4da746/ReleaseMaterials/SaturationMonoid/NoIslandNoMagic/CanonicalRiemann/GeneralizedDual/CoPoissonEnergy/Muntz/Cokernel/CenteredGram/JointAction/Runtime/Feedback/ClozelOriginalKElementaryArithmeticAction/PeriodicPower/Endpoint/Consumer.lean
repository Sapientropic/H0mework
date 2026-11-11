import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Consumer
open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszSource.Translator
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source
open scoped InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "P" => positionSource
local notation "b" => burnolRieszSingleFourierSourceRaw
namespace BF
export OriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice
  (sourceColumn forcingDensity boundarySourceRead finiteSourcePrice)
end BF

theorem actual_original_beta (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) : Kernel.beta c=fourierEndpoint c := by
  rw [actual_original_beta_field,actual_original_periodic_zero_quarter c zero,zero_add]

theorem actual_original_forcing_mean (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) :
    star c.value*ForcingMeanZero.mean c=
      resolvedRaw c 0+jumpCoefficient c*burnolRadiusTruncatedFourierRaw q (intervalConstant q) q-
        aliasRaw c q-ForcingWhole.coefficient c*ForcingMeanZero.edgeMean := by
  have mean:=ForcingMeanZero.raw_mean_boundary c
  rw [actual_original_forcing_point,actual_original_periodic_zero_quarter c zero,zero_add] at mean
  linear_combination -mean

/-- Both endpoint reads belong to the original inverse; the quarter zero has been consumed. -/
theorem actual_original_endpoint_bill (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) :
    star (Kernel.A c)*Kernel.A c-star (Kernel.beta c)*Kernel.beta c=
      star (positionEndpoint c)*positionEndpoint c-star (fourierEndpoint c)*fourierEndpoint c := by
  rw [actual_original_A,actual_original_beta c zero]

def endpointDensity (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  star (positionEndpoint c)*(star (BF.sourceColumn 0 x)*P c (Real.exp h*x)+
    star (BF.sourceColumn 1 x)*b c (Real.exp h*x))+
  star (fourierEndpoint c)*(star (BF.sourceColumn 1 x)*P c (Real.exp h*x)+
    star (BF.sourceColumn 0 x)*b c (Real.exp h*x))+
  positionEndpoint c*(star (P c x)*BF.sourceColumn 0 (Real.exp h*x)+
    star (b c x)*BF.sourceColumn 1 (Real.exp h*x))+
  fourierEndpoint c*(star (P c x)*BF.sourceColumn 1 (Real.exp h*x)+
    star (b c x)*BF.sourceColumn 0 (Real.exp h*x))

def endpointBoundary (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (q:ℂ)*(star (positionEndpoint c)*P c (Real.exp h*q)+
    star (fourierEndpoint c)*b c (Real.exp h*q))-
  (q*Real.exp (-h):ℂ)*(star (P c (q*Real.exp (-h)))*positionEndpoint c+
    star (b c (q*Real.exp (-h)))*fourierEndpoint c)

theorem actual_original_boundary (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) (h : ℝ) : BF.boundarySourceRead c h=endpointBoundary c h := by
  unfold BF.boundarySourceRead endpointBoundary
  rw [actual_original_A,actual_original_beta c zero]

theorem actual_original_density (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) (h x : ℝ) : BF.forcingDensity c h x=endpointDensity c h x := by
  unfold BF.forcingDensity endpointDensity
  rw [actual_original_A,actual_original_beta c zero]

def endpointPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (2:ℂ)*(Real.exp (h/2):ℂ)*
    ((∫ x:ℝ in (q*Real.exp (-h))..q,endpointDensity c h x)+endpointBoundary c h)/
      (c.value+star c.value-1)

theorem actual_original_price (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) (h : ℝ) : BF.finiteSourcePrice c h=endpointPrice c h := by
  unfold BF.finiteSourcePrice endpointPrice
  simp_rw [actual_original_density c zero,actual_original_boundary c zero]

def completeEndpointNet (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (pairedMellinTranslationCharacter c.value h-pairedMellinTranslationCharacter (star c.value) h)*
    kernelSelfSource c+(1/2:ℂ)*star (endpointPrice c h)

theorem actual_original_fixed_consumer (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) :
    BurnolPaBoundaryCancellationAt c zero ↔ completeEndpointNet c (Real.log stageZeroSonineQ)=0 := by
  rw [OriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer.actual_original_fixed_consumer c zero]
  rw [OriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer.completeResponseNet,
    ←OriginalKPairedBEulerJunctionSource.ResponseForcing.Source.actual_finite_price,actual_original_price c zero]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
