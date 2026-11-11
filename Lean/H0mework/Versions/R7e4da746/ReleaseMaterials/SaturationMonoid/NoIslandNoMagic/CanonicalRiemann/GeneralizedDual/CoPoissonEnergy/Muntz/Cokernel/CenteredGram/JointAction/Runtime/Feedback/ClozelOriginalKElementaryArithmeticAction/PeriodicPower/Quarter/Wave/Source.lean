import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DilationWard
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Consumer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point
open ProlateKernel ProlateFourierTail
open scoped Topology ENNReal InnerProductSpace
open private box_fourier_trig from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open private shifted_distance from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
local notation "q" => (1/4:ℝ)
local notation "window" => Icc (-(1/2):ℝ) (1/2:ℝ)
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => volume.restrict (symmetricInterval q)
local instance finiteQuarter : IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem coefficient_eq_jump (c : BurnolCompletedMellinCoordinate) :
    ForcingWhole.coefficient c=jumpCoefficient c := by
  have gap:=GapEuler.gapMean_primitive q (by norm_num) c
  unfold ForcingWhole.coefficient jumpCoefficient
  linear_combination -gap

private theorem box_derivative (x : ℝ) (nonzero : x≠0) :
    HasDerivAt box (Edge.raw q x/(x:ℂ)) x := by
  have omegaNe : frequency≠0 := by
    unfold frequency
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have xNe : (x:ℂ)≠0:=Complex.ofReal_ne_zero.mpr nonzero
  have inner := (hasDerivAt_id (x:ℂ)).const_mul scale
  have sine := (Complex.hasDerivAt_sin (scale*(x:ℂ))).comp (x:ℂ) inner
  have generated := ((sine.const_mul 2).div ((hasDerivAt_id (x:ℂ)).const_mul frequency)
    (mul_ne_zero omegaNe xNe)).comp_ofReal
  have read : HasDerivAt (fun y:ℝ=>2*Complex.sin (scale*(y:ℂ))/(frequency*(y:ℂ)))
      (Edge.raw q x/(x:ℂ)) x := by
    convert! generated using 1
    rw [EdgeTrig.original_trig x nonzero]
    simp only [id_eq,mul_one,Function.comp_apply]
    field_simp
    unfold scale
    ring
  apply read.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds nonzero] with y hy
  exact box_fourier_trig y hy

def resolvedSlope (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (star c.value-1)*ForcingWhole.raw c x/(x:ℂ)

theorem actual_resolved_derivative (c : BurnolCompletedMellinCoordinate)
    (x : ℝ) (nonzero : x≠0) : HasDerivAt (resolvedFourierRaw c) (resolvedSlope c x) x := by
  have generated := (original_first_hasDerivAt c nonzero).sub
    ((box_derivative x nonzero).const_mul (jumpCoefficient c))
  convert! generated using 1
  unfold first resolvedSlope
  rw [coefficient_eq_jump]
  ring

private def valueBound (c : BurnolCompletedMellinCoordinate) : ℝ :=
  Classical.choose (original_value_bound c)
private theorem valueBound_nonnegative (c : BurnolCompletedMellinCoordinate) : 0≤valueBound c :=
  (Classical.choose_spec (original_value_bound c)).1
private theorem value_bound (c : BurnolCompletedMellinCoordinate) (x : ℝ) (outside : q≤|x|) :
    ‖ForcingWhole.raw c x‖≤valueBound c/|x| :=
  (Classical.choose_spec (original_value_bound c)).2 x outside

private def slopeBound (c : BurnolCompletedMellinCoordinate) : ℝ := ‖star c.value-1‖*valueBound c
private theorem slopeBound_nonnegative (c : BurnolCompletedMellinCoordinate) : 0≤slopeBound c :=
  mul_nonneg (norm_nonneg _) (valueBound_nonnegative c)
private theorem slope_bound (c : BurnolCompletedMellinCoordinate) (x : ℝ) (outside : q≤|x|) :
    ‖resolvedSlope c x‖≤slopeBound c/|x|^2 := by
  unfold resolvedSlope slopeBound
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _≤(‖star c.value-1‖*(valueBound c/|x|))/|x| :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (value_bound c x outside) (norm_nonneg _))
        (abs_nonneg x)
    _=_ := by ring

def aliasSlopeTerm (c : BurnolCompletedMellinCoordinate) (k : ℤ) (x : ℝ) : ℂ :=
  if k=0 then 0 else resolvedSlope c (x+k)
def aliasSlope (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ := ∑'k:ℤ,aliasSlopeTerm c k x

private theorem slope_term_bound (c : BurnolCompletedMellinCoordinate) (k : ℤ)
    (x : ℝ) (inside : x∈window) : ‖aliasSlopeTerm c k x‖≤4*slopeBound c/(k:ℝ)^2 := by
  by_cases zero:k=0
  · subst k;simp [aliasSlopeTerm]
  · rw [aliasSlopeTerm,if_neg zero]
    have distance:=shifted_distance x inside k zero
    have one : (1:ℝ)≤|(k:ℝ)|:=by exact_mod_cast Int.one_le_abs zero
    have outside : q≤|x+k|:=by linarith
    apply (slope_bound c (x+k) outside).trans
    have squared : (k:ℝ)^2≤4*|x+k|^2:=by nlinarith [sq_abs (k:ℝ)]
    have denominator : (0:ℝ)<(k:ℝ)^2:=sq_pos_of_ne_zero (by exact_mod_cast zero)
    apply (div_le_div_iff₀ (by nlinarith : (0:ℝ) < |x+k|^2) denominator).mpr
    nlinarith [mul_le_mul_of_nonneg_left squared (slopeBound_nonnegative c)]

private theorem slope_majorant (c : BurnolCompletedMellinCoordinate) :
    Summable (fun k:ℤ=>4*slopeBound c/(k:ℝ)^2) := by
  simpa only [div_eq_mul_inv,one_mul] using
    (Real.summable_one_div_int_pow.mpr (by decide:1<2)).mul_left (4*slopeBound c)

private theorem alias_term_derivative (c : BurnolCompletedMellinCoordinate) (k : ℤ)
    (x : ℝ) (inside : x∈window) : HasDerivAt (aliasRawTerm c k) (aliasSlopeTerm c k x) x := by
  by_cases zero:k=0
  · subst k
    have source : aliasRawTerm c 0=(fun _:ℝ=>(0:ℂ)):=by funext y;simp [aliasRawTerm]
    rw [source]
    simpa only [aliasSlopeTerm,ite_true] using hasDerivAt_const x (0:ℂ)
  · have distance:=shifted_distance x inside k zero
    have one : (1:ℝ)≤|(k:ℝ)|:=by exact_mod_cast Int.one_le_abs zero
    have nonzero : x+(k:ℝ)≠0:=by intro same;rw [same,abs_zero] at distance;linarith
    have generated := (actual_resolved_derivative c _ nonzero).scomp x
      ((hasDerivAt_id x).add_const (k:ℝ))
    have source : aliasRawTerm c k=(fun y:ℝ=>resolvedFourierRaw c (y+k)) := by
      funext y;rw [aliasRawTerm,if_neg zero]
    rw [source]
    simpa only [aliasSlopeTerm,if_neg zero,Function.comp_def,one_smul,id_eq] using generated

theorem actual_alias_derivative (c : BurnolCompletedMellinCoordinate)
    (x : ℝ) (inside : x∈Ioo (-(1/2):ℝ) (1/2:ℝ)) : HasDerivAt (aliasRaw c) (aliasSlope c x) x := by
  have base : Summable (fun k:ℤ=>aliasRawTerm c k 0) := by
    apply Summable.of_norm_bounded
      (g:=fun k:ℤ=>4*tailBound c/(k:ℝ)^2)
    · simpa only [div_eq_mul_inv,one_mul] using
        (Real.summable_one_div_int_pow.mpr (by decide:1<2)).mul_left (4*tailBound c)
    · intro k
      exact actual_alias_uniform_bound c k 0 (by norm_num)
  exact hasDerivAt_tsum_of_isPreconnected (slope_majorant c) isOpen_Ioo isPreconnected_Ioo
    (fun k y hy=>alias_term_derivative c k y ⟨hy.1.le,hy.2.le⟩)
    (fun k y hy=>slope_term_bound c k y ⟨hy.1.le,hy.2.le⟩)
    (by norm_num : (0:ℝ)∈Ioo (-(1/2):ℝ) (1/2:ℝ)) base inside

theorem actual_alias_slope_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (aliasSlope c) window := by
  apply continuousOn_tsum _ (slope_majorant c) (slope_term_bound c)
  intro k
  by_cases zero:k=0
  · subst k
    have source : aliasSlopeTerm c 0=(fun _:ℝ=>(0:ℂ)):=by funext y;simp [aliasSlopeTerm]
    rw [source]
    exact continuousOn_const
  · have source : aliasSlopeTerm c k=(fun y:ℝ=>resolvedSlope c (y+k)) := by
      funext y;rw [aliasSlopeTerm,if_neg zero]
    rw [source]
    intro x inside
    have distance:=shifted_distance x inside k zero
    have one : (1:ℝ)≤|(k:ℝ)|:=by exact_mod_cast Int.one_le_abs zero
    have nonzero : x+(k:ℝ)≠0:=by intro same;rw [same,abs_zero] at distance;linarith
    have field : ContinuousAt (fun y:ℝ=>ForcingWhole.raw c (y+k)) x :=
      ContinuousAt.comp (g:=ForcingWhole.raw c) (f:=fun y:ℝ=>y+k)
        (ForcingWhole.raw_continuousAt c nonzero) (continuous_id.add continuous_const).continuousAt
    exact ((continuousAt_const.mul field).div
      (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).continuousAt
      (Complex.ofReal_ne_zero.mpr nonzero)).continuousWithinAt

def quarterWave (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (periodicQuarter c)

def companionRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((star c.value-1)*jumpCoefficient c)*box x+(x:ℂ)*aliasSlope c x-
    (star c.value-1)*(aliasRaw c x-resolvedRaw c 0)

private theorem companion_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (companionRaw c) window := by
  exact ((continuousOn_const.mul (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant q)).continuousOn).add
    (Complex.continuous_ofReal.continuousOn.mul (actual_alias_slope_continuous c))).sub
    (continuousOn_const.mul ((actual_alias_raw_continuous c).sub continuousOn_const))

private theorem companion_memLp (c : BurnolCompletedMellinCoordinate) : MemLp (companionRaw c) 2 μq := by
  have regular : ContinuousOn (companionRaw c) (symmetricInterval q) :=
    (companion_continuous c).mono (by intro x h;constructor <;> linarith [h.1,h.2])
  obtain ⟨bound,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn regular
  apply MemLp.of_bound (regular.aestronglyMeasurable (measurableSet_symmetricInterval q)) bound
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  exact bounded x inside

def companionQuarter (c : BurnolCompletedMellinCoordinate) : Hq :=
  (companion_memLp c).toLp (companionRaw c)
def companion (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (companionQuarter c)
def velocity (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (star c.value-1/2) • quarterWave c+companion c

theorem actual_companion_raw (c : BurnolCompletedMellinCoordinate) :
    (companionQuarter c:ℝ→ℂ)=ᵐ[μq]companionRaw c := (companion_memLp c).coeFn_toLp

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
