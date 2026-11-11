import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPowerWaveDilationSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalUnitMellinSource.Band
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2

def bandLog (x:ℝ):ℂ:=((Real.log x-Real.log q:ℝ):ℂ)

private theorem log_power_integrable (j:Nat) (x:ℝ) (after:q<x):
    IntervalIntegrable (fun t:ℝ=>(t:ℂ)⁻¹*(bandLog t)^j) volume q x:=by
  have logContinuous:ContinuousOn bandLog (Icc q x):=by
    have realLog:ContinuousOn Real.log (Icc q x):=by
      apply Real.continuousOn_log.mono
      intro t inside
      have positive:0<t:=by linarith [inside.1]
      exact positive.ne'
    exact Complex.continuous_ofReal.comp_continuousOn (realLog.sub continuousOn_const)
  have continuous:ContinuousOn (fun t:ℝ=>(t:ℂ)⁻¹*(bandLog t)^j) (Icc q x):=
    ((Complex.continuous_ofReal.continuousOn.inv₀ (fun t inside=>
      Complex.ofReal_ne_zero.mpr (by linarith [inside.1]))).mul (logContinuous.pow j))
  exact continuous.intervalIntegrable_of_Icc after.le

private theorem log_power_integral (j:Nat) (x:ℝ) (after:q<x):
    (∫t:ℝ in q..x,(t:ℂ)⁻¹*(bandLog t)^j)=(bandLog x)^(j+1)/(j+1:ℕ):=by
  have derivative (t:ℝ) (positive:0<t):
      HasDerivAt (fun t:ℝ=>(bandLog t)^(j+1)/(j+1:ℕ))
        ((t:ℂ)⁻¹*(bandLog t)^j) t:=by
    have logDerivative:HasDerivAt bandLog ((t:ℂ)⁻¹) t:=by
      change HasDerivAt (fun t:ℝ=>((Real.log t-Real.log q:ℝ):ℂ)) ((t:ℂ)⁻¹) t
      convert! ((Real.hasDerivAt_log positive.ne').sub_const (Real.log q)).ofReal_comp using 1
      simp only [Complex.ofReal_inv]
    convert! (logDerivative.pow (j+1)).div_const ((j+1:ℕ):ℂ) using 1
    simp only [Nat.add_sub_cancel]
    have nonzero:((j+1:ℕ):ℂ)≠0:=by exact_mod_cast (Nat.succ_ne_zero j)
    field_simp [nonzero]
  have integrated:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=q) (b:=x) (fun t inside=>derivative t (by
      rw [uIcc_of_le after.le] at inside
      linarith [inside.1])) (log_power_integrable j x after)
  simpa only [bandLog,sub_self,Complex.ofReal_zero,zero_pow (Nat.succ_ne_zero j),zero_div,sub_zero] using integrated

private theorem tail_split (coordinate:BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (x:ℝ) (after:q<x):
    burnolRadiusMellinTailEvaluator q (by norm_num) coordinate.value coordinate.rightHalf value=
      (∫t:ℝ in q..x,(t:ℂ)^(-coordinate.value)*value t)+
        burnolRadiusMellinTailEvaluator x (by linarith) coordinate.value coordinate.rightHalf value:=by
  have full:=burnolRadiusMellinWeight_integrableOn_tail q (by norm_num)
    coordinate.value coordinate.rightHalf value
  have upper:=burnolRadiusMellinWeight_integrableOn_tail x (by linarith)
    coordinate.value coordinate.rightHalf value
  have union:Ioc q x∪Ioi x=Ioi q:=by
    ext t
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (inside|outside)
      · exact inside.1
      · exact after.trans outside
    · intro lower
      by_cases upper:t≤x
      · exact Or.inl ⟨lower,upper⟩
      · exact Or.inr (lt_of_not_ge upper)
  have disjoint:Disjoint (Ioc q x) (Ioi x):=by
    apply Set.disjoint_left.mpr
    intro t inside outside
    exact not_lt_of_ge inside.2 outside
  rw [burnolRadiusMellinTailEvaluator_eq_integral,burnolRadiusMellinTailEvaluator_eq_integral,
    intervalIntegral.integral_of_le after.le,←union]
  exact setIntegral_union disjoint measurableSet_Ioi
    (full.mono_set (fun _ inside=>inside.1)) upper

/-- The original outward action retains its true tail scalar and the actual finite band. -/
theorem actual_volterra_band_step (coordinate:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    ∀ᵐ x:ℝ ∂volume,q<x →
      sourceVolterraResolvent coordinate value x=
        2*(x:ℂ)^(coordinate.value-1)*((∫t:ℝ in q..x,(t:ℂ)^(-coordinate.value)*value t)-
          burnolAmbientCompletedMellinEvaluator coordinate value+
          burnolAmbientGapCoefficient q value*(q:ℂ)^(1-coordinate.value)/(1-coordinate.value)):=by
  filter_upwards [sourceVolterraResolvent_positive_profile coordinate value] with x source after
  have split:=tail_split coordinate value x after
  have ambient:burnolAmbientCompletedMellinEvaluator coordinate value=
      burnolAmbientGapCoefficient q value*(q:ℂ)^(1-coordinate.value)/(1-coordinate.value)+
        burnolRadiusMellinTailEvaluator q (by norm_num) coordinate.value coordinate.rightHalf value:=by
    change burnolRadiusMellinGapMoment q coordinate.value*burnolAmbientGapCoefficient q value+_=_
    unfold burnolRadiusMellinGapMoment
    change (q:ℂ)^(1-coordinate.value)/(1-coordinate.value)*burnolAmbientGapCoefficient q value+
      burnolRadiusMellinTailEvaluator q (by norm_num) coordinate.value coordinate.rightHalf value=_
    ring
  rw [source (by linarith),ambient,split]
  ring

private theorem polynomial_band_integral (coordinate:BurnolCompletedMellinCoordinate)
    (value:BurnolL2) (gamma coefficient:ℂ) (j:Nat)
    (profile:∀ᵐ t:ℝ ∂volume,q<t → t<2*q →
      value t=gamma+coefficient*(t:ℂ)^(coordinate.value-1)*(bandLog t)^j)
    (x:ℝ) (after:q<x) (upper:x<2*q):
    (∫t:ℝ in q..x,(t:ℂ)^(-coordinate.value)*value t)=
      gamma*((x:ℂ)^(1-coordinate.value)-(q:ℂ)^(1-coordinate.value))/(1-coordinate.value)+
        coefficient*(bandLog x)^(j+1)/(j+1:ℕ):=by
  have powerBound:-1<(-coordinate.value).re:=by
    simp only [Complex.neg_re]
    linarith [coordinate.belowOne]
  have powerInt:IntervalIntegrable (fun t:ℝ=>(t:ℂ)^(-coordinate.value)) volume q x:=
    intervalIntegral.intervalIntegrable_cpow' powerBound
  have raw:(∫t:ℝ in q..x,(t:ℂ)^(-coordinate.value)*value t)=
      ∫t:ℝ in q..x,gamma*(t:ℂ)^(-coordinate.value)+
        coefficient*((t:ℂ)⁻¹*(bandLog t)^j):=by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [profile] with t source inside
    rw [uIoc_of_le after.le] at inside
    have positive:0<t:=by linarith [inside.1]
    have inverse:(t:ℂ)^(-coordinate.value)*(t:ℂ)^(coordinate.value-1)=(t:ℂ)⁻¹:=by
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),
        show -coordinate.value+(coordinate.value-1)=(-1:ℂ) by ring,
        Complex.cpow_neg_one]
    rw [source inside.1 (inside.2.trans_lt upper)]
    calc
      _=gamma*(t:ℂ)^(-coordinate.value)+
        coefficient*((t:ℂ)^(-coordinate.value)*(t:ℂ)^(coordinate.value-1))*(bandLog t)^j:=by ring
      _=_:=by rw [inverse];ring
  rw [raw,intervalIntegral.integral_add (powerInt.const_mul gamma)
    ((log_power_integrable j x after).const_mul coefficient),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_cpow (Or.inl powerBound),log_power_integral j x after]
  rw [show -coordinate.value+1=1-coordinate.value by ring]
  ring

/-- The whole source action propagates the actual first-cell polynomial, including its nonzero tail read. -/
theorem actual_polynomial_band_step (coordinate:BurnolCompletedMellinCoordinate)
    (value:BurnolL2) (gamma coefficient:ℂ) (j:Nat)
    (gap:burnolAmbientGapCoefficient q value=gamma)
    (profile:∀ᵐ t:ℝ ∂volume,q<t → t<2*q →
      value t=gamma+coefficient*(t:ℂ)^(coordinate.value-1)*(bandLog t)^j):
    ∀ᵐ x:ℝ ∂volume,q<x → x<2*q →
      sourceVolterraResolvent coordinate value x=2*gamma/(1-coordinate.value)+
        (x:ℂ)^(coordinate.value-1)*
          (2*coefficient*(bandLog x)^(j+1)/(j+1:ℕ)-
            2*burnolAmbientCompletedMellinEvaluator coordinate value):=by
  filter_upwards [actual_volterra_band_step coordinate value] with x source after upper
  rw [source after,polynomial_band_integral coordinate value gamma coefficient j profile x after upper,gap]
  have inverse:(x:ℂ)^(coordinate.value-1)*(x:ℂ)^(1-coordinate.value)=1:=by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (show 0<x by linarith).ne'),
      show (coordinate.value-1)+(1-coordinate.value)=0 by ring,Complex.cpow_zero]
  calc
    _=(2*gamma/(1-coordinate.value))*
      ((x:ℂ)^(coordinate.value-1)*(x:ℂ)^(1-coordinate.value))+
        (x:ℂ)^(coordinate.value-1)*(2*coefficient*(bandLog x)^(j+1)/(j+1:ℕ)-
          2*burnolAmbientCompletedMellinEvaluator coordinate value):=by ring
    _=_:=by rw [inverse,mul_one]

private theorem first_channel (x:ℝ) (lower:1<x) (upper:x<2):
    burnolUnitTailDirichletChannels 1 x={1}:=by
  have ceiling:⌈|x|/(1:ℝ)⌉₊=2:=by
    rw [abs_of_pos (by linarith),div_one]
    have above:1<⌈x⌉₊:=Nat.lt_ceil.mpr (by exact_mod_cast lower)
    have below:⌈x⌉₊≤2:=Nat.ceil_le.mpr (by exact_mod_cast upper.le)
    omega
  rw [burnolUnitTailDirichletChannels,ceiling]
  decide

private theorem first_dirichlet (s:ℂ) (x:ℝ) (lower:1<x) (upper:x<2):
    burnolUnitTailDirichletRaw s 1 x=1/s-(x:ℂ)^(-s):=by
  simp only [burnolUnitTailDirichletRaw,first_channel x lower upper,
    Complex.ofReal_one,Complex.one_cpow,Finset.sum_singleton,Nat.cast_one,
    mul_one,abs_of_pos (show 0<x by linarith)]

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "U"=>OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
local notation "m"=>generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e"=>burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
open private power_succ_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
include nontrivial

def bandMean (coordinate:BurnolCompletedMellinCoordinate) (j:Nat):ℂ:=
  (2/(1-coordinate.value))^j*(-(4:ℂ)^(1-coordinate.value)/(1-coordinate.value))

def bandCoefficient (j:Nat):ℂ:=(2:ℂ)^j/(j.factorial:ℂ)

omit nontrivial in
private theorem bandMean_succ (coordinate:BurnolCompletedMellinCoordinate) (j:Nat):
    bandMean coordinate (j+1)=2*bandMean coordinate j/(1-coordinate.value):=by
  unfold bandMean
  rw [pow_succ]
  ring

omit nontrivial in
private theorem bandCoefficient_succ (j:Nat):
    bandCoefficient (j+1)=2*bandCoefficient j/(j+1:ℕ):=by
  unfold bandCoefficient
  rw [pow_succ,Nat.factorial_succ]
  simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
  ring

omit nontrivial in
private theorem original_fourier_step (j:Nat):
    F (U (j+1))=sourceVolterraResolvent c (F (U j)):=by
  have step:=power_succ_left observation half j (burnolUnitTailResponse c 4)
  have right:1/4<((c).value/2).re:=by rw [Complex.div_re];norm_num;linarith [(c).rightHalf]
  change U (j+1)=burnolDirectRightResolvent ((c).value/2) (U j) at step
  rw [step,FiniteMobiusResolventFlux.fourier_R _ right,FiniteMobiusResolventFlux.Rplus_tate _ right]
  rfl

private theorem original_fourier_gap_mean (j:Nat) (before:j<m):
    burnolAmbientGapCoefficient q (F (U j))=bandMean c j:=by
  let p:BurnolPaAmbientCarrier:=⟨U j,OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical
    observation nontrivial half j before⟩
  let fp:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius p
  have gap:burnolQuarterRestriction (fp:BurnolL2)=bandMean c j • intervalConstant q:=
    OriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource.actual_fourier_quarter_power observation nontrivial half j before
  change burnolConstantGapCoefficient q fp=bandMean c j
  exact burnolConstantGapCoefficient_eq q (by norm_num) fp _ gap.symm

private theorem original_fourier_ambient (j:Nat) (before:j<m):
    burnolAmbientCompletedMellinEvaluator c (F (U j))=
      inner ℂ (F (burnolCompletedMellinRieszVector c:BurnolL2)) (U j):=by
  let p:BurnolPaAmbientCarrier:=⟨U j,OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical
    observation nontrivial half j before⟩
  let fp:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius p
  have restrict:=congrArg (fun r:BurnolPaAmbientCarrier→L[ℂ]ℂ=>r fp)
    (burnolAmbientCompletedMellinEvaluator_restrict c)
  change burnolAmbientCompletedMellinEvaluator c (fp:BurnolL2)=burnolCompletedMellinEvaluator c fp at restrict
  change burnolAmbientCompletedMellinEvaluator c (fp:BurnolL2)=_
  rw [restrict,←burnolCompletedMellinRieszVector_readback]
  have moved:=(evenFaceFourierEquiv burnolUnscaledCommonGapRadius).inner_map_map
    (burnolCompletedMellinRieszVector c) fp
  have invol:(evenFaceFourierEquiv burnolUnscaledCommonGapRadius) fp=p:=
    evenFaceFourier_involutive burnolUnscaledCommonGapRadius p
  rw [invol] at moved
  exact moved.symm

/-- The first actual Fourier cell has its n=1 channel and its full original mean. -/
theorem actual_unit_fourier_first_cell:
    ∀ᵐ x:ℝ ∂volume,q<x → x<2*q →
      F (burnolUnitTailResponse c 4) x=
        -(4:ℂ)^(1-(c).value)/(1-(c).value)+(x:ℂ)^((c).value-1):=by
  let character:=fullMellinTranslationCharacter (c).value (-Real.log 4)
  have radius:(1:ℝ)*Real.exp (Real.log 4)=4:=by
    rw [one_mul,Real.exp_log (by norm_num:(0:ℝ)<4)]
  have action:=congrArg F (burnolUnitTailResponse_radius_dilation c 1
    (by norm_num) (by norm_num) (-Real.log 4) (by rw [neg_neg,radius];norm_num))
  rw [fourierL2_burnolMultiplicativeDilation,neg_neg,map_smul,radius] at action
  have factor:character*(4:ℂ)^(1-(c).value)=(Real.exp (Real.log 4/2):ℂ):=by
    unfold character fullMellinTranslationCharacter
    rw [Complex.cpow_def_of_ne_zero (by norm_num:(4:ℂ)≠0),
      show Complex.log (4:ℂ)=(Real.log 4:ℂ) from (Complex.ofReal_log (by norm_num:(0:ℝ)≤4)).symm,
      ←Complex.exp_add,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>(4:ℝ)*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=(4:ℝ)) (by norm_num))
  have raw:=scale.ae (burnolZeroOwnedUnitFourier_dirichlet_coeFn observation nontrivial half.down)
  filter_upwards [Lp.coeFn_smul character (F (burnolUnitTailResponse c 4)),
    burnolMultiplicativeDilation_coeFn (Real.log 4) (F (burnolUnitTailResponse c 1)),raw]
    with x acted dilation profile lower upper
  have positive:0<x:=by linarith
  have lowerFour:1<4*x:=by linarith
  have upperFour:4*x<2:=by linarith
  have read:=congrArg (fun v:BurnolL2=>v x) action
  rw [acted,dilation] at read
  change (Real.exp (Real.log 4/2):ℂ)*F (burnolUnitTailResponse c 1)
    (Real.exp (Real.log 4)*x)=character*F (burnolUnitTailResponse c 4) x at read
  rw [Real.exp_log (by norm_num:(0:ℝ)<4),profile,
    first_dirichlet _ _ lowerFour upperFour,←factor] at read
  change character*(4:ℂ)^(1-(c).value)*
    -(1/(1-(c).value)-((4*x:ℝ):ℂ)^(-(1-(c).value)))=
      character*F (burnolUnitTailResponse c 4) x at read
  have inverse:(4:ℂ)^(1-(c).value)*(4:ℂ)^((c).value-1)=1:=by
    rw [←Complex.cpow_add _ _ (by norm_num:(4:ℂ)≠0),
      show (1-(c).value)+((c).value-1)=0 by ring,Complex.cpow_zero]
  have scaled:(4:ℂ)^(1-(c).value)*((4*x:ℝ):ℂ)^(- (1-(c).value))=
      (x:ℂ)^((c).value-1):=by
    rw [show -(1-(c).value)=(c).value-1 by ring,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by norm_num:(0:ℝ)≤4) positive.le]
    norm_num only [Complex.ofReal_ofNat]
    rw [←mul_assoc,inverse,one_mul]
  have nonzero:character≠0:=Complex.exp_ne_zero _
  apply mul_left_cancel₀ nonzero
  calc
    _=character*((4:ℂ)^(1-(c).value)*
      (-(1/(1-(c).value)-((4*x:ℝ):ℂ)^(-(1-(c).value))))):=by
        linear_combination -read
    _=character*(-(4:ℂ)^(1-(c).value)/(1-(c).value)+(x:ℂ)^((c).value-1)):=by
      rw [mul_neg,mul_sub,scaled]
      ring

/-- Every lower original R word retains its actual logarithmic first cell. -/
theorem actual_fourier_first_cell_power (j:Nat) (before:j<m):
    ∀ᵐ x:ℝ ∂volume,q<x → x<2*q →
      F (U j) x=bandMean c j+bandCoefficient j*(x:ℂ)^((c).value-1)*(bandLog x)^j:=by
  induction j with
  | zero=>
    simpa only [OriginalKFiniteOrderRelease.UnitPowerSource.unitPower,CombSource.Division.rawIterate,
      pow_zero,one_apply_eq_self,bandMean,bandCoefficient,Nat.factorial_zero,Nat.cast_one,
      div_one,one_mul,mul_one] using actual_unit_fourier_first_cell observation nontrivial half
  | succ j previous=>
    have lower:j<m:=by omega
    have mean:=original_fourier_gap_mean observation nontrivial half j lower
    have polynomial:=actual_polynomial_band_step c (F (U j)) (bandMean c j) (bandCoefficient j) j mean
      (previous lower)
    have ambient:=original_fourier_ambient observation nontrivial half j lower
    have zero:=OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_low
      observation nontrivial half j before
    rw [zero] at ambient
    rw [←original_fourier_step observation half j,ambient] at polynomial
    filter_upwards [polynomial] with x source after upper
    rw [source after upper,bandMean_succ,bandCoefficient_succ]
    ring

/-- The exact Xi order leaves both the finite-cell log term and the original nonzero top release. -/
theorem actual_top_fourier_first_cell:
    ∀ᵐ x:ℝ ∂volume,q<x → x<2*q →
      F (U m) x=bandMean c m+(x:ℂ)^((c).value-1)*
        (bandCoefficient m*(bandLog x)^m-2*e):=by
  have positive:0<m:=generatedRiemannXiZeroOrder_pos observation nontrivial
  have previous:m-1<m:=by omega
  have mean:=original_fourier_gap_mean observation nontrivial half (m-1) previous
  have polynomial:=actual_polynomial_band_step c (F (U (m-1))) (bandMean c (m-1))
    (bandCoefficient (m-1)) (m-1) mean
    (actual_fourier_first_cell_power observation nontrivial half (m-1) previous)
  have ambient:=original_fourier_ambient observation nontrivial half (m-1) previous
  have top:=OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_top observation nontrivial half
  rw [top] at ambient
  have step:=original_fourier_step observation half (m-1)
  have next:m-1+1=m:=by omega
  rw [next] at step
  rw [←step,ambient,next] at polynomial
  have gamma:=bandMean_succ c (m-1)
  have coefficient:=bandCoefficient_succ (m-1)
  rw [next] at gamma coefficient
  filter_upwards [polynomial] with x source after upper
  rw [source after upper,gamma,coefficient]
  ring

end OriginalUnitMellinSource.Band
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
