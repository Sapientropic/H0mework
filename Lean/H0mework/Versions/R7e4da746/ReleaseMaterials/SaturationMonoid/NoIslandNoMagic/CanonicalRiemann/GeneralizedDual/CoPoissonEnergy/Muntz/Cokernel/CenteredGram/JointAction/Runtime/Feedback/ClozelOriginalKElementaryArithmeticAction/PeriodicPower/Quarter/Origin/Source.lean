import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mean.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point
open scoped Topology ENNReal InnerProductSpace FourierTransform
local notation "q" => (1/4:ℝ)

private theorem alias_slope_bounded (c:BurnolCompletedMellinCoordinate) :
    ∃ B:ℝ, 0≤B ∧ ∀ x∈symmetricInterval q, ‖aliasSlope c x‖≤B := by
  have regular : ContinuousOn (aliasSlope c) (symmetricInterval q) :=
    (actual_alias_slope_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2])
  obtain ⟨B,bound⟩ := isCompact_Icc.exists_bound_of_continuousOn regular
  exact ⟨max 0 B,le_max_left _ _,fun x hx=>(bound x hx).trans (le_max_right _ _)⟩

private def aliasBound (c:BurnolCompletedMellinCoordinate) : ℝ :=
  (alias_slope_bounded c).choose
private theorem aliasBound_nonnegative (c:BurnolCompletedMellinCoordinate) : 0≤aliasBound c :=
  (alias_slope_bounded c).choose_spec.1
private theorem aliasBound_read (c:BurnolCompletedMellinCoordinate)
    (x:ℝ) (inside:x∈symmetricInterval q) : ‖aliasSlope c x‖≤aliasBound c :=
  (alias_slope_bounded c).choose_spec.2 x inside

private theorem alias_change (c:BurnolCompletedMellinCoordinate)
    (x y:ℝ) (hx:x∈symmetricInterval q) (hy:y∈symmetricInterval q) :
    ‖aliasRaw c y-aliasRaw c x‖≤aliasBound c*|y-x| := by
  have derivative : ∀ z∈symmetricInterval q,
      HasDerivWithinAt (aliasRaw c) (aliasSlope c z) (symmetricInterval q) z := by
    intro z hz
    exact (actual_alias_derivative c z (by constructor <;> linarith [hz.1,hz.2])).hasDerivWithinAt
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le derivative (aliasBound_read c)
      (convex_Icc _ _) hx hy

def regularClockRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  (Real.exp (h/2):ℂ)*(aliasRaw c (Real.exp h*x)-resolvedRaw c 0)-
    Complex.exp ((star c.value-1/2)*(h:ℂ))*(aliasRaw c x-resolvedRaw c 0)

private def clockBound (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℝ :=
  (Real.exp (h/2)*Real.exp h+‖Complex.exp ((star c.value-1/2)*(h:ℂ))‖)*aliasBound c

/-- The complete alias and constant clock has a source-generated local modulus. -/
theorem actual_regular_clock_bound (c:BurnolCompletedMellinCoordinate) (h x:ℝ)
    (inside:x∈symmetricInterval q) (moved:Real.exp h*x∈symmetricInterval q) :
    ‖regularClockRaw c h x-regularClockRaw c h 0‖≤clockBound c h*|x| := by
  have zero : (0:ℝ)∈symmetricInterval q := by norm_num [symmetricInterval]
  have left := alias_change c 0 (Real.exp h*x) zero moved
  have right := alias_change c 0 x zero inside
  have read : regularClockRaw c h x-regularClockRaw c h 0=
      (Real.exp (h/2):ℂ)*(aliasRaw c (Real.exp h*x)-aliasRaw c 0)-
        Complex.exp ((star c.value-1/2)*(h:ℂ))*(aliasRaw c x-aliasRaw c 0) := by
    unfold regularClockRaw
    simp only [mul_zero]
    ring
  rw [read]
  calc
    _≤‖(Real.exp (h/2):ℂ)*(aliasRaw c (Real.exp h*x)-aliasRaw c 0)‖+
        ‖Complex.exp ((star c.value-1/2)*(h:ℂ))*(aliasRaw c x-aliasRaw c 0)‖ := norm_sub_le _ _
    _≤Real.exp (h/2)*(aliasBound c*|Real.exp h*x|)+
        ‖Complex.exp ((star c.value-1/2)*(h:ℂ))‖*(aliasBound c*|x|) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact add_le_add (mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using left) (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using right) (norm_nonneg _))
    _=clockBound c h*|x| := by
      rw [abs_mul,abs_of_pos (Real.exp_pos h)]
      unfold clockBound
      ring

def innerRadius (h:ℝ) : ℝ := q*Real.exp (-h)
def innerRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  𝓕 (compactRaw c h) x+regularClockRaw c h x
def outerRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  -Complex.exp ((star c.value-1/2)*(h:ℂ))*periodicRaw c x

/-- The value at zero is the continuous Fourier source head, with no zero assertion. -/
def positiveRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  if x ≤ innerRadius h then innerRaw c h x else outerRaw c h x

private theorem innerRadius_positive (h:ℝ) : 0 < innerRadius h := by
  unfold innerRadius
  positivity
private theorem innerRadius_le (h:ℝ) (nonnegative:0≤h) : innerRadius h≤q := by
  unfold innerRadius
  have exponent := Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)
  nlinarith
private theorem inner_moved (h x:ℝ) (inside:x∈Icc 0 (innerRadius h)) :
    Real.exp h*x∈symmetricInterval q := by
  have inverse : Real.exp h*Real.exp (-h)=1 := by rw [←Real.exp_add];simp
  have upper := mul_le_mul_of_nonneg_left inside.2 (Real.exp_pos h).le
  unfold innerRadius at upper
  have movedUpper : Real.exp h*x≤q := by nlinarith [upper]
  constructor
  · have positive := mul_nonneg (Real.exp_pos h).le inside.1
    linarith
  · exact movedUpper
private theorem inner_inside (h:ℝ) (nonnegative:0≤h) (x:ℝ)
    (inside:x∈Icc 0 (innerRadius h)) : x∈symmetricInterval q :=
  ⟨by linarith [inside.1],inside.2.trans (innerRadius_le h nonnegative)⟩

private theorem character_read (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    waveCharacter c h=Complex.exp ((star c.value-1/2)*(h:ℂ)) := by
  unfold waveCharacter fullMellinTranslationCharacter
  congr 1
  push_cast
  ring

private theorem inner_read (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h)
    (x:ℝ) (nonzero:x≠0) :
    innerRaw c h x=(Real.exp (h/2):ℂ)*periodicRaw c (Real.exp h*x)-
      Complex.exp ((star c.value-1/2)*(h:ℂ))*periodicRaw c x := by
  rw [innerRaw,actual_fourier_difference c h nonnegative x nonzero]
  unfold fourierDifference regularClockRaw periodicRaw
  rw [character_read]
  ring

theorem actual_positive_raw (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h)
    (x:ℝ) (positive:0<x) (bounded:x≤q) : positiveRaw c h x=differenceRaw c h x := by
  have inside : x∈symmetricInterval q := ⟨by linarith, bounded⟩
  unfold positiveRaw differenceRaw quarterRaw
  rw [indicator_of_mem inside]
  by_cases small:x ≤ innerRadius h
  · rw [if_pos small,inner_read c h nonnegative x positive.ne',
      indicator_of_mem (inner_moved h x ⟨positive.le,small⟩)]
  · have outside : Real.exp h*x∉symmetricInterval q := by
      intro member
      have upper := mul_le_mul_of_nonneg_left member.2 (Real.exp_pos (-h)).le
      have inverse : Real.exp (-h)*Real.exp h=1 := by rw [←Real.exp_add];simp
      have bound : x ≤ innerRadius h := by unfold innerRadius;nlinarith [upper]
      exact small bound
    rw [if_neg small,indicator_of_notMem outside,outerRaw,mul_zero]
    ring

private def innerSlope (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  deriv (𝓕 (compactRaw c h)) x+
    (Real.exp (h/2):ℂ)*((Real.exp h:ℂ)*aliasSlope c (Real.exp h*x))-
    Complex.exp ((star c.value-1/2)*(h:ℂ))*aliasSlope c x

private theorem inner_derivative (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h)
    (x:ℝ) (inside:x∈Icc 0 (innerRadius h)) : HasDerivAt (innerRaw c h) (innerSlope c h x) x := by
  have original := inner_inside h nonnegative x inside
  have moved := inner_moved h x inside
  have mapped := (actual_alias_derivative c (Real.exp h*x)
    (by constructor <;> linarith [moved.1,moved.2])).scomp x
      ((hasDerivAt_id x).const_mul (Real.exp h))
  have direct := actual_alias_derivative c x (by constructor <;> linarith [original.1,original.2])
  have fourier := ((actual_compact_fourier_smooth c h nonnegative 1).differentiable_one x).hasDerivAt
  have source := fourier.add (((mapped.sub_const (resolvedRaw c 0)).const_mul (Real.exp (h/2):ℂ)).sub
    ((direct.sub_const (resolvedRaw c 0)).const_mul (Complex.exp ((star c.value-1/2)*(h:ℂ)))))
  convert! source using 1
  simp only [innerSlope,mul_one,Complex.real_smul]
  ring

private theorem inner_slope_continuous (c:BurnolCompletedMellinCoordinate) (h:ℝ)
    (nonnegative:0≤h) : ContinuousOn (innerSlope c h) (Icc 0 (innerRadius h)) := by
  have direct : ContinuousOn (aliasSlope c) (Icc 0 (innerRadius h)) :=
    (actual_alias_slope_continuous c).mono (by
      intro x hx
      have inside := inner_inside h nonnegative x hx
      constructor <;> linarith [inside.1,inside.2])
  have mapped : ContinuousOn (fun x:ℝ=>aliasSlope c (Real.exp h*x)) (Icc 0 (innerRadius h)) :=
    (actual_alias_slope_continuous c).comp (continuous_const.mul continuous_id).continuousOn (by
      intro x hx
      have inside := inner_moved h x hx
      constructor <;> linarith [inside.1,inside.2])
  exact (((actual_compact_fourier_smooth c h nonnegative 1).continuous_deriv_one.continuousOn).add
    (continuousOn_const.mul (continuousOn_const.mul mapped))).sub (continuousOn_const.mul direct)

private def outerSlope (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  -Complex.exp ((star c.value-1/2)*(h:ℂ))*(resolvedSlope c x+aliasSlope c x)

private theorem outer_derivative (c:BurnolCompletedMellinCoordinate) (h:ℝ)
    (x:ℝ) (inside:x∈Icc (innerRadius h) q) : HasDerivAt (outerRaw c h) (outerSlope c h x) x := by
  have positive : 0<x := (innerRadius_positive h).trans_le inside.1
  have generated := ((actual_resolved_derivative c x positive.ne').add
    (actual_alias_derivative c x (by constructor <;> linarith [inside.2]))).sub_const (resolvedRaw c 0)
  exact generated.const_mul _

private theorem outer_slope_continuous (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    ContinuousOn (outerSlope c h) (Icc (innerRadius h) q) := by
  apply continuousOn_const.mul
  apply ContinuousOn.add
  · intro x hx
    have positive : 0<x := (innerRadius_positive h).trans_le hx.1
    exact ((continuousAt_const.mul (ForcingWhole.raw_continuousAt c positive.ne')).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr positive.ne')).continuousWithinAt
  · exact (actual_alias_slope_continuous c).mono (by
      intro x hx
      have positive : 0<x := (innerRadius_positive h).trans_le hx.1
      constructor <;> linarith [hx.2])

private theorem inner_lipschitz (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h) :
    ∃ B:ℝ, 0≤B ∧ ∀ x∈Icc 0 (innerRadius h), ∀ y∈Icc 0 (innerRadius h),
      ‖innerRaw c h y-innerRaw c h x‖≤B*|y-x| := by
  obtain ⟨B,bound⟩ := isCompact_Icc.exists_bound_of_continuousOn (inner_slope_continuous c h nonnegative)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro x hx y hy
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz=>(inner_derivative c h nonnegative z hz).hasDerivWithinAt)
      (fun z hz=>(bound z hz).trans (le_max_right _ _)) (convex_Icc _ _) hx hy

private theorem outer_lipschitz (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    ∃ B:ℝ, 0≤B ∧ ∀ x∈Icc (innerRadius h) q, ∀ y∈Icc (innerRadius h) q,
      ‖outerRaw c h y-outerRaw c h x‖≤B*|y-x| := by
  obtain ⟨B,bound⟩ := isCompact_Icc.exists_bound_of_continuousOn (outer_slope_continuous c h)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro x hx y hy
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz=>(outer_derivative c h z hz).hasDerivWithinAt)
      (fun z hz=>(bound z hz).trans (le_max_right _ _)) (convex_Icc _ _) hx hy

private theorem source_seam (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) : innerRaw c h (innerRadius h)=outerRaw c h (innerRadius h) := by
  rw [inner_read c h nonnegative _ (innerRadius_positive h).ne']
  have moved : Real.exp h*innerRadius h=q := by
    unfold innerRadius
    have inverse : Real.exp h*Real.exp (-h)=1 := by rw [←Real.exp_add];simp
    nlinarith
  rw [moved,actual_original_periodic_zero_quarter c zero,mul_zero,outerRaw]
  ring

/-- The original q zero joins the two genuine source pieces into one Lipschitz quarter field. -/
theorem actual_positive_lipschitz (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) :
    ∃ B:NNReal, LipschitzOnWith B (positiveRaw c h) (Icc 0 q) := by
  obtain ⟨B1,positive1,left⟩ := inner_lipschitz c h nonnegative
  obtain ⟨B2,positive2,right⟩ := outer_lipschitz c h
  have rPositive := (innerRadius_positive h).le
  have rBound := innerRadius_le h nonnegative
  have seam := source_seam c zero h nonnegative
  have ordered : ∀ x∈Icc 0 q, ∀ y∈Icc 0 q, x≤y →
      ‖positiveRaw c h y-positiveRaw c h x‖≤(B1+B2)*(y-x) := by
    intro x hx y hy order
    by_cases smallY : y ≤ innerRadius h
    · have smallX : x ≤ innerRadius h := order.trans smallY
      rw [positiveRaw,if_pos smallY,positiveRaw,if_pos smallX]
      have bound := left x ⟨hx.1,smallX⟩ y ⟨hy.1,smallY⟩
      rw [abs_of_nonneg (sub_nonneg.mpr order)] at bound
      exact bound.trans (by nlinarith [mul_nonneg positive2 (sub_nonneg.mpr order)])
    · have largeY : innerRadius h≤y := (lt_of_not_ge smallY).le
      by_cases smallX : x ≤ innerRadius h
      · rw [positiveRaw,if_neg smallY,positiveRaw,if_pos smallX]
        have boundLeft := left x ⟨hx.1,smallX⟩ (innerRadius h) ⟨rPositive,le_rfl⟩
        have boundRight := right (innerRadius h) ⟨le_rfl,rBound⟩ y ⟨largeY,hy.2⟩
        rw [abs_of_nonneg (sub_nonneg.mpr smallX)] at boundLeft
        rw [abs_of_nonneg (sub_nonneg.mpr largeY)] at boundRight
        calc
          _=‖(outerRaw c h y-outerRaw c h (innerRadius h))+
              (innerRaw c h (innerRadius h)-innerRaw c h x)‖ := by rw [seam];congr 1;ring
          _≤‖outerRaw c h y-outerRaw c h (innerRadius h)‖+
              ‖innerRaw c h (innerRadius h)-innerRaw c h x‖ := norm_add_le _ _
          _≤B2*(y-innerRadius h)+B1*(innerRadius h-x) := add_le_add boundRight boundLeft
          _≤(B1+B2)*(y-x) := by
            nlinarith [mul_nonneg positive1 (sub_nonneg.mpr largeY),
              mul_nonneg positive2 (sub_nonneg.mpr smallX)]
      · rw [positiveRaw,if_neg smallY,positiveRaw,if_neg smallX]
        have bound := right x ⟨(lt_of_not_ge smallX).le,hx.2⟩ y ⟨largeY,hy.2⟩
        rw [abs_of_nonneg (sub_nonneg.mpr order)] at bound
        exact bound.trans (by nlinarith [mul_nonneg positive1 (sub_nonneg.mpr order)])
  refine ⟨⟨B1+B2,add_nonneg positive1 positive2⟩,?_⟩
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  change ‖positiveRaw c h x-positiveRaw c h y‖≤(B1+B2)*‖x-y‖
  rcases le_total x y with order|order
  · calc
      _=‖positiveRaw c h y-positiveRaw c h x‖ := norm_sub_rev _ _
      _≤(B1+B2)*(y-x) := ordered x hx y hy order
      _=(B1+B2)*‖x-y‖ := by rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr order)];ring
  · calc
      _≤(B1+B2)*(x-y) := ordered y hy x hx order
      _=(B1+B2)*‖x-y‖ := by rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr order)]

theorem actual_positive_endpoint (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) : positiveRaw c h q=0 := by
  rw [actual_positive_raw c h nonnegative q (by norm_num) le_rfl]
  exact actual_difference_outer_zero c zero h nonnegative q (by norm_num)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
