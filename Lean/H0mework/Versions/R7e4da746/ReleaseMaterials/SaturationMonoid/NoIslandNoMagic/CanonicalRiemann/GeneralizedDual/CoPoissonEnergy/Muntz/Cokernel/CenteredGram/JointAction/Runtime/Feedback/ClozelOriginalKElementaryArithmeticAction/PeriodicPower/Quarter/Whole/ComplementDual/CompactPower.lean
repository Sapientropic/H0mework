import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Price

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPower
open Complex ComplexConjugate Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalKFiniteOrderRelease.UnitPowerJordanSource
open scoped Topology InnerProductSpace ENNReal
open private even_half_integral from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "Cq" => intervalConstant q

def logMoment (c:BurnolCompletedMellinCoordinate) (k:ℕ) (raw:ℝ→ℂ):ℂ:=
  ∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(c.value-1)*(Real.log (q/x):ℂ)^k*raw x

private theorem divided_star (c:BurnolCompletedMellinCoordinate) (k:ℕ) (x:ℝ):
    star (dividedLogRaw c k x)=
      (((|x|:ℝ):ℂ)^(c.value-1)*(Real.log (q/|x|):ℂ)^k)/(k.factorial:ℂ):=by
  have arg:(((|x|:ℝ):ℂ)).arg≠Real.pi:=by
    rw [Complex.arg_ofReal_of_nonneg (abs_nonneg x)]
    exact ne_of_lt Real.pi_pos
  have power:star (SingularCounting.powerRaw c x)=((|x|:ℝ):ℂ)^(c.value-1):=by
    simpa only [SingularCounting.powerRaw,star_def,map_sub,map_one,Complex.conj_ofReal]
      using (Complex.conj_cpow (((|x|:ℝ):ℂ)) (c.value-1) arg).symm
  rw [dividedLogRaw,star_div₀,star_mul,star_pow,star_natCast,power,
    show star (Real.log (q/|x|):ℂ)=(Real.log (q/|x|):ℂ) from Complex.conj_ofReal _]
  ring

theorem actual_log_pair (c:BurnolCompletedMellinCoordinate) (k:ℕ) (state:Hq) (raw:ℝ→ℂ)
    (read:(state:ℝ→ℂ)=ᵐ[μq]raw) (even:∀x:ℝ,raw (-x)=raw x):
    inner ℂ (dividedLogColumn c k) state=(2/(k.factorial:ℂ))*logMoment c k raw:=by
  let product:ℝ→ℂ:=fun x=>star (dividedLogRaw c k x)*raw x
  have domain:Integrable product μq:=by
    apply (L2.integrable_inner (dividedLogColumn c k) state).congr
    filter_upwards [dividedLogColumn_profile c k,read] with x column actual
    rw [column,actual]
    simp only [product,RCLike.inner_apply,starRingEnd_apply]
    ring
  have pair:inner ℂ (dividedLogColumn c k) state=∫x:ℝ,product x ∂μq:=by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dividedLogColumn_profile c k,read] with x column actual
    rw [column,actual]
    simp only [product,RCLike.inner_apply,starRingEnd_apply]
    ring
  have parity:∀x:ℝ,product (-x)=product x:=by
    intro x
    simp only [product,dividedLogRaw,SingularCounting.powerRaw,abs_neg,even]
  rw [pair,even_half_integral product domain parity,
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]
  have price:(∫x:ℝ in (0:ℝ)..q,product x)=
      (k.factorial:ℂ)⁻¹*logMoment c k raw:=by
    rw [logMoment,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x inside
    dsimp only [product]
    rw [divided_star c k x,abs_of_pos inside.1]
    ring
  rw [price]
  ring

theorem actual_top_log_coefficient_zero (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    sourceCoefficient c (j+1) j=0:=by
  induction j with
  | zero => exact source_initial_amplitude_zero c
  | succ j previous =>
    change -2*sourceCoefficient c (j+1) j=0
    rw [previous,mul_zero]

private theorem constant_price (state:Hq):
    inner ℂ Cq state=(1/2:ℂ)*burnolQuarterMeanCoefficient state:=by
  unfold burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)]
  norm_num
  ring

/-- Compact support consumes the complete adjoint quarter, including its original constant field. -/
theorem actual_original_compact_power (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (state:Hq):
    let observation:=burnolPaZeroObservation c zero
    let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (E state))=
      (star (sourceConstant c m)/2)*burnolQuarterMeanCoefficient state+
      ∑k∈Finset.range m,star (sourceCoefficient c m k)*inner ℂ (dividedLogColumn c k) state:=by
  dsimp only
  let observation:=burnolPaZeroObservation c zero
  let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
  have same:burnolDivisionZeroCompletedMellinCoordinate observation half.down=c:=by cases c;rfl
  have read:=actual_full_power_read observation half (E state)
  change inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
    (CombSource.Division.rawIterate observation half.down
      (generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate) (E state))=
      inner ℂ (fulladjointPowerZ observation half) (E state) at read
  rw [read,←actual_sourceField observation half,same,
    show E=burnolQuarterRestriction.adjoint from rfl,ContinuousLinearMap.adjoint_inner_right,
    source_quarter_finite,inner_add_left,inner_smul_left,constant_price]
  simp only [finiteQuarterSource,sum_inner,inner_smul_left,starRingEnd_apply]
  ring

/-- Every remaining log slot is an honest source integral; no Pa admission or erased Q term enters. -/
theorem actual_original_compact_log_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (state:Hq) (raw:ℝ→ℂ)
    (read:(state:ℝ→ℂ)=ᵐ[μq]raw) (even:∀x:ℝ,raw (-x)=raw x):
    let observation:=burnolPaZeroObservation c zero
    let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (E state))=
      (star (sourceConstant c m)/2)*burnolQuarterMeanCoefficient state+
      ∑k∈Finset.range m,star (sourceCoefficient c m k)*(2/(k.factorial:ℂ))*logMoment c k raw:=by
  dsimp only
  rw [actual_original_compact_power c zero state]
  congr 1
  apply Finset.sum_congr rfl
  intro k inside
  rw [actual_log_pair c k state raw read even]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPower
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
