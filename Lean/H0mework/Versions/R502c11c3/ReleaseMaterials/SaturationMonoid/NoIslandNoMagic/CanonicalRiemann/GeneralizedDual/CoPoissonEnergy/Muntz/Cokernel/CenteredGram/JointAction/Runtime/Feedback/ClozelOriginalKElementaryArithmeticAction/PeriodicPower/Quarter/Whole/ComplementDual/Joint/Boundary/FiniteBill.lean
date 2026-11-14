import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.UnitLog
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FiniteSchur

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FiniteBill
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.ForcingPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FiniteSchur OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.UnitLog
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Mean
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "ell"=>CenteredCountingDual.logarithm
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "R"=>burnolDirectRightResolventCLM
local notation "h₀"=>Real.log stageZeroSonineQ

private theorem conjugate_plain (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    star (plainCoefficient c j)=(2/(1-star c.value))^j*star (nativeCotestGap c):=by
  simp only [plainCoefficient,star_mul,star_pow,star_div₀,star_sub,star_one,star_ofNat]
  ring

private theorem conjugate_contact (c:BurnolCompletedMellinCoordinate):
    star (plainContact c)=2*star c.value*(q:ℂ)^(1-star c.value)/(1-star c.value)^2:=by
  have argNe:(q:ℂ).arg≠Real.pi:=by
    rw [Complex.arg_ofReal_of_nonneg (by norm_num:(0:ℝ)≤q)]
    exact ne_of_lt Real.pi_pos
  have power:star ((q:ℂ)^(1-c.value))=(q:ℂ)^(1-star c.value):=by
    have source:=Complex.cpow_conj (q:ℂ) (1-c.value) argNe
    simpa only [Complex.conj_ofReal,map_sub,map_one,Complex.star_def] using source.symm
  rw [plainContact,star_div₀,star_mul,star_mul,star_pow,star_sub,star_one,star_ofNat,power]
  ring

def finiteNativeBill (c:BurnolCompletedMellinCoordinate) (j:ℕ):ℂ:=
  star (nativeActedAmplitude c j+plainContact c*plainCoefficient c j)/2+
    ∑k∈Finset.range j,star (nativeCoefficient c j k)*
      inner ℂ (centeredLogColumn (barC c) k) (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source.correction c.value c.belowOne)

/-- Original count mass and Unit projection cancel the complete plain-log price with the exact native contact. -/
theorem actual_original_native_finite_bill (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    rieszAmplitude c*evaluatorSource c h₀=finiteNativeBill c (order c.value):=by
  have source:=actual_native_boundary_bill c zero
  rw [actual_native_source,inner_add_right,inner_neg_right,
    actual_native_forcing_amplitude_price c zero,actual_native_finite_correction_price c zero,
    actual_native_unit_gap_price,compactMass,actual_compact_correction_mean c zero] at source
  have logPrice:inner ℂ ell (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source.correction c.value c.belowOne)=
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (fullFloorValue c zero))/2+
        star (plainContact c)/2:=by
    rw [conjugate_contact]
    linear_combination -(actual_native_count_mass_log c zero)
  rw [source,logPrice]
  unfold finiteNativeBill
  rw [star_add,star_mul,conjugate_plain]
  ring

/-- The installed original fixed consumer reads the finite current and every retained original source coefficient. -/
theorem actual_original_finite_current_consumer (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    BurnolPaBoundaryCancellationAt c zero↔finiteNativeBill c (order c.value)=0:=by
  have original:=actual_original_native_source_consumer c zero
  rw [←actual_native_boundary_bill c zero,actual_original_native_finite_bill c zero] at original
  exact original

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FiniteBill
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
