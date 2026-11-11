import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Fourier
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mass

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.PowerPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mass OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Fourier
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Rq" => burnolQuarterRestriction
local notation "Hq" => BurnolQuarterIntervalL2

/-- The Fourier reader is the actual L2 field's original compact Fourier integral. -/
def countFourierRaw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):ℝ→ℂ:=
  burnolRadiusTruncatedFourierRaw q (Rq (fullFloorValue c zero))

theorem actual_L2_fourier_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (fourierL2 (fullFloorValue c zero):ℝ→ℂ)=ᵐ[volume]countFourierRaw c zero:=by
  rw [←actual_floor_compact c zero]
  exact burnolRadiusFourierL2_zeroExtension_ae_eq_raw (Rq (fullFloorValue c zero))

private theorem count_fourier_read (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Constructor.fourierRaw (fullFloorRaw c)=countFourierRaw c zero:=by
  exact (Constructor.fourierRaw_congr (Rq (fullFloorValue c zero)) (fullFloorRaw c)
    (actual_floor_quarter_raw c zero)).symm

private theorem count_mass_read (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    (∫x:ℝ,fullFloorRaw c x ∂μq)=2*deriv (poleFreeSource c) 1/(1-star c.value):=by
  have source:=actual_quarter_mean_finite_part c zero
  rw [Constructor.mean_integral,integral_congr_ae (actual_floor_quarter_raw c zero)] at source
  linear_combination (1/2:ℂ)*source

/-- Both the actual Fourier field and its complete Unit mass now have native source values. -/
theorem actual_complete_fourier_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (y:ℝ):
    HasSum (fun n:ℕ=>(((n+1:ℕ):ℂ)⁻¹)*
      Constructor.fourierRaw (dualRaw c.value c.belowOne) (y/(n+1:ℕ)))
      (countFourierRaw c zero y-2*deriv (poleFreeSource c) 1/(1-star c.value)):=by
  have source:=actual_count_fourier_source c zero y
  rw [count_fourier_read c zero,count_mass_read c zero] at source
  exact source

def programme (c:BurnolCompletedMellinCoordinate) (N:ℕ) (y:ℝ):ℂ:=
  ∑n∈Finset.range N,(((n+1:ℕ):ℂ)⁻¹)*
    Constructor.fourierRaw (dualRaw c.value c.belowOne) (y/(n+1:ℕ))

theorem actual_programme_limit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (y:ℝ):
    Tendsto (fun N:ℕ=>programme c N y) atTop
      (𝓝 (countFourierRaw c zero y-2*deriv (poleFreeSource c) 1/(1-star c.value))):=
  (actual_complete_fourier_source c zero y).tendsto_sum_nat

private theorem original_fourier_split (c:BurnolCompletedMellinCoordinate):
    Constructor.fourierRaw (dualRaw c.value c.belowOne)=
      Constructor.fourierRaw (seedRaw c.value)+
        Constructor.fourierRaw (correction c.value c.belowOne:Hq):=by
  have split:Constructor.fourierRaw (dualRaw c.value c.belowOne)=
      Constructor.fourierRaw (seedRaw c.value)+Constructor.fourierRaw (correctionRaw c.value c.belowOne):=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner
      (actual_seed_integrable c.value c.belowOne)
      (actual_correction_continuous c.value c.belowOne).integrableOn_Icc
  rw [←Constructor.fourierRaw_congr (correction c.value c.belowOne:Hq)
    (correctionRaw c.value c.belowOne) (actual_correction_raw c.value c.belowOne)] at split
  exact split

/-- The seed and the actual BI correction share exactly the same finite upper clock. -/
theorem actual_complete_finite_programme (c:BurnolCompletedMellinCoordinate) (N:ℕ) (y:ℝ):
    programme c N y=
      (∑n∈Finset.range N,(((n+1:ℕ):ℂ)⁻¹)*Constructor.fourierRaw (seedRaw c.value) (y/(n+1:ℕ)))+
      (∑n∈Finset.range N,(((n+1:ℕ):ℂ)⁻¹)*
        Constructor.fourierRaw (correction c.value c.belowOne:Hq) (y/(n+1:ℕ))):=by
  simp only [programme,original_fourier_split,Pi.add_apply,mul_add,Finset.sum_add_distrib]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
