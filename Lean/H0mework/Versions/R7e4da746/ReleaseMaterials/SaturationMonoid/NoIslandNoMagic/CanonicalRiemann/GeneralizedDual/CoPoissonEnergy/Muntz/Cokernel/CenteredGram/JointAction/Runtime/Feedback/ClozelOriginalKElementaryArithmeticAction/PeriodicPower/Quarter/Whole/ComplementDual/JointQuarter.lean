import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointQuarter
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward InverseAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionHead OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
open scoped Topology InnerProductSpace
open private integer_sum window_norm_summable window_zero compact_indicator from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Rq" => burnolQuarterRestriction
local notation "Cq" => intervalConstant q
local notation "BI" => burnolMeanZeroBlockInverse

private theorem regular_quarter_hasSum (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    HasSum (fun n:ℕ=>countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero)) (forwardQuarter c zero):=by
  have summable:Summable (fun n:ℕ=>countingWindow (n:ℝ) (regularQuarter c zero)):=
    (window_norm_summable c zero).of_norm
  have shifted:Summable (fun n:ℕ=>countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero)):=
    (summable_nat_add_iff 1).mpr summable
  have value:=summable.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one,Nat.cast_zero,window_zero,zero_add,integer_sum] at value
  rw [←value]
  exact shifted.hasSum

def jointTerm (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (n:ℕ):Hq:=
  quarterTerm c n+countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero)

theorem actual_joint_term_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (n:ℕ):
    (jointTerm c zero n:ℝ→ℂ)=ᵐ[μq]fun x:ℝ=>(((n+1:ℕ):ℂ)⁻¹)*
      (Constructor.fourierRaw (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source.dualRaw c.value c.belowOne) (x/(n+1:ℕ))+
        regularCompactRaw c (x/(n+1:ℕ))):=by
  have source:=countingWindow_raw ((n+1:ℕ):ℝ) (by positivity) (regularQuarter c zero)
    (regularCompactRaw c) (actual_regular_quarter_raw c zero)
  filter_upwards [Lp.coeFn_add (quarterTerm c n)
      (countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero)),actual_quarter_term_raw c n,source]
    with x added count regular
  rw [jointTerm,added,Pi.add_apply,count,regular,countingRaw,compact_indicator]
  simp only [Complex.ofReal_natCast]
  ring

/-- The same integer clock generates the two actual q contacts jointly, with both Unit constants. -/
theorem actual_joint_quarter_hasSum (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    HasSum (jointTerm c zero)
      (Rq (wholeValue c zero h positive+fourierL2 (fullFloorValue c zero))+
        (wholeReciprocalFinitePart c-2*deriv (poleFreeSource c) 1/(1-star c.value)) • Cq):=by
  have source:=(actual_quarter_hasSum c zero).add (regular_quarter_hasSum c zero)
  have field:Rq (fourierL2 (fullFloorValue c zero))-
      (2*deriv (poleFreeSource c) 1/(1-star c.value)) • Cq+forwardQuarter c zero=
      Rq (wholeValue c zero h positive+fourierL2 (fullFloorValue c zero))+
        (wholeReciprocalFinitePart c-2*deriv (poleFreeSource c) 1/(1-star c.value)) • Cq:=by
    rw [map_add,actual_whole_quarter_source c zero h positive]
    module
  rw [field] at source
  exact source

/-- The joint source is consumed by the actual original inverse, rather than merely given a domain. -/
theorem actual_joint_position_inverse_hasSum (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    HasSum (fun n:ℕ=>BI (Constructor.zeroMean (jointTerm c zero n)))
      (BI (Constructor.zeroMean (Rq (wholeValue c zero h positive+fourierL2 (fullFloorValue c zero))))):=by
  have source:=(actual_joint_quarter_hasSum c zero h positive).mapL
    (burnolMeanZeroBlockInverse.comp Constructor.zeroMean)
  simp only [ContinuousLinearMap.comp_apply,map_add,map_smul,Constructor.zeroMean_constant,smul_zero,
    add_zero,map_zero] at source
  simpa only [map_add] using source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointQuarter
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
