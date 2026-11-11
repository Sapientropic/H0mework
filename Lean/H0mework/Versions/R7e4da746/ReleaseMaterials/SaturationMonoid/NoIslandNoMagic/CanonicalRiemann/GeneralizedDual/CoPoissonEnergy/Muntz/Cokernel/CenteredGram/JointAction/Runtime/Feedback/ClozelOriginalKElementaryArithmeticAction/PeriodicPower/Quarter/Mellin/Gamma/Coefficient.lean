import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Position
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Fourier

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Coefficient
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Pair OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Position
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Fourier
open scoped Topology InnerProductSpace

/-- The two actual Gaussian limits of the same original resolved source determine its forcing head. -/
theorem actual_forcing_gamma_balance (c:BurnolCompletedMellinCoordinate):
    2*ForcingPrimitive.leadingCoefficient c*Gammaℝ (star c.value)=Gammaℝ (1-star c.value):=by
  have same:(fun n:ℕ=>∫x:ℝ in Ioi 0,positionReading c (n:ℝ) x)=
      (fun n:ℕ=>∫x:ℝ in Ioi 0,fourierReading c (n:ℝ) x):=by
    funext n
    exact actual_scaled_pair c (n:ℝ)
  have position:=actual_position_gaussian_limit c
  rw [same] at position
  have equality:=tendsto_nhds_unique (actual_fourier_gaussian_limit c) position
  linear_combination 4*equality

theorem actual_forcing_gamma_coefficient (c:BurnolCompletedMellinCoordinate):
    ForcingPrimitive.leadingCoefficient c=Gammaℝ (1-star c.value)/(2*Gammaℝ (star c.value)):=by
  have gamma:Gammaℝ (star c.value)≠0:=Gammaℝ_ne_zero_of_re_pos
    (by simp only [star_def,conj_re];linarith [c.rightHalf])
  apply (eq_div_iff (mul_ne_zero (by norm_num) gamma)).mpr
  linear_combination actual_forcing_gamma_balance c

theorem actual_forcing_leading_nonzero (c:BurnolCompletedMellinCoordinate):
    ForcingPrimitive.leadingCoefficient c≠0:=by
  have gamma:Gammaℝ (1-star c.value)≠0:=Gammaℝ_ne_zero_of_re_pos
    (by simp only [sub_re,one_re,star_def,conj_re];linarith [c.belowOne])
  intro zero
  have balance:=actual_forcing_gamma_balance c
  rw [zero,mul_zero,zero_mul] at balance
  exact gamma balance.symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Coefficient
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
