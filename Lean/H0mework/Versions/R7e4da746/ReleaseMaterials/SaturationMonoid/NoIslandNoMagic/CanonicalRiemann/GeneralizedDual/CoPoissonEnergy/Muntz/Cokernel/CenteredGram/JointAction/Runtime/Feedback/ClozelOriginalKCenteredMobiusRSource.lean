import H0mework.Arithmetic.MobiusSource.MobiusFiniteCutoff
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitFourier.Realization
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Window
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCenteredMobiusRSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalPaPhysicalGreen
open scoped ENNReal Topology BigOperators
local notation "q" => (1/4:ℝ)

def weightedCentered (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ) (x:ℝ) : ℂ :=
  (x:ℂ)^(c.value-1)*(raw x-raw 0)

/-- Positive-kernel source representative with the original, independently generated centering. -/
def sourceRRaw (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ) (x:ℝ) : ℂ :=
  -2*raw 0/c.value-2*((|x|:ℝ):ℂ)^(-c.value)*(∫ v:ℝ in 0..|x|,weightedCentered c raw v)

theorem sourceRRaw_gap (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ)
    (gap:∀{x:ℝ},|x|≤ q → raw x=raw 0) {x:ℝ} (inside:|x|≤q) :
    sourceRRaw c raw x= -2*raw 0/c.value := by
  have integralZero:(∫ v:ℝ in 0..|x|,weightedCentered c raw v)=0 := by
    rw [intervalIntegral.integral_of_le (abs_nonneg x)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v hv
    have bounds:0≤v ∧ v≤|x|:=⟨hv.1.le,hv.2⟩
    unfold weightedCentered
    rw [gap (by rw [abs_of_nonneg bounds.1];exact bounds.2.trans inside),sub_self,mul_zero]
  rw [sourceRRaw,integralZero,mul_zero,sub_zero]

theorem sourceRRaw_zero (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ) :
    sourceRRaw c raw 0= -2*raw 0/c.value := by
  simp only [sourceRRaw,abs_zero,intervalIntegral.integral_same,mul_zero,sub_zero]

/-- A single cutoff is valid for the whole positive prefix, before any integral interchange. -/
theorem inverse_prefix_cutoff (raw:ℝ→ℂ)
    (gap:∀{x:ℝ},|x|≤ q → raw x=raw 0) (t v:ℝ)
    (positive:0<t) (nonnegative:0≤v) (before:v≤t) :
    burnolCenteredMobiusInverse raw v=
      ∑ n∈burnolCenteredMobiusCutoffFinset t,burnolCenteredMobiusSummand raw v n := by
  change (∑' n:ℕ+,burnolCenteredMobiusSummand raw v n)=_
  apply tsum_eq_sum
  intro n outside
  apply burnolCenteredMobiusSummand_eq_zero_of_cutoff_le raw gap v n
  have nlarge:burnolCenteredMobiusCutoff t≤(n:Nat):=by
    simpa only [mem_burnolCenteredMobiusCutoffFinset,not_lt] using outside
  have cutoff:burnolCenteredMobiusCutoff v≤burnolCenteredMobiusCutoff t := by
    unfold burnolCenteredMobiusCutoff
    rw [abs_of_nonneg nonnegative,abs_of_pos positive]
    exact Nat.ceil_le_ceil (by linarith)
  exact cutoff.trans nlarge

private theorem weighted_integrable (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ)
    (native:MemLp raw 2 volume) (gap:∀{x:ℝ},|x|≤ q → raw x=raw 0)
    (t:ℝ) (positive:0<t) : IntervalIntegrable (weightedCentered c raw) volume 0 t := by
  let safe:ℝ→ℂ:=fun v=>((max q v:ℝ):ℂ)^(c.value-1)
  have safeSmooth:Continuous safe := by
    have base:Continuous (fun v:ℝ=>((max q v:ℝ):ℂ)):=
      Complex.continuous_ofReal.comp (continuous_const.max continuous_id)
    exact continuousOn_univ.mp (base.continuousOn.cpow_const (fun v _=>
      Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by norm_num : (0:ℝ)<q) (le_max_left q v))))
  have localRaw:=native.locallyIntegrable (by norm_num : (1:ℝ≥0∞)≤2)
  have first:IntervalIntegrable raw volume 0 t:=
    (localRaw.integrableOn_isCompact isCompact_Icc).intervalIntegrable
  have bounded:IntervalIntegrable (fun v=>safe v*(raw v-raw 0)) volume 0 t:=
    (first.sub intervalIntegrable_const).continuousOn_mul safeSmooth.continuousOn
  apply bounded.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v inside
  have bounds:0≤v ∧ v≤t:=by
    rw [uIoc_of_le positive.le] at inside
    exact ⟨inside.1.le,inside.2⟩
  unfold weightedCentered
  by_cases insideGap:v≤q
  · rw [gap (by rwa [abs_of_nonneg bounds.1]),sub_self,mul_zero,mul_zero]
  · dsimp only [safe]
    rw [max_eq_right (le_of_not_ge insideGap)]

private theorem scaled_power (c:BurnolCompletedMellinCoordinate) (v:ℝ) (nonnegative:0≤v) (n:ℕ+) :
    ((n:Nat):ℂ)^(c.value-1)*((v/(n:Nat):ℝ):ℂ)^(c.value-1)=(v:ℂ)^(c.value-1) := by
  have np:0<((n:Nat):ℝ):=by exact_mod_cast n.property
  calc
    _=((((n:Nat):ℝ)*(v/(n:Nat)):ℝ):ℂ)^(c.value-1) := by
      rw [Complex.ofReal_mul]
      simpa only [Complex.ofReal_natCast] using
        (Complex.mul_cpow_ofReal_nonneg np.le (div_nonneg nonnegative np.le) (c.value-1)).symm
    _=_ := by congr 1;field_simp

private theorem weighted_scaled_integrable (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ)
    (native:MemLp raw 2 volume) (gap:∀{x:ℝ},|x|≤ q → raw x=raw 0)
    (t:ℝ) (positive:0<t) (n:ℕ+) :
    IntervalIntegrable (fun v:ℝ=>(v:ℂ)^(c.value-1)*(raw (v/(n:Nat))-raw 0)) volume 0 t := by
  have np:0<((n:Nat):ℝ):=by exact_mod_cast n.property
  have previous:=weighted_integrable c raw native gap (t/(n:Nat)) (div_pos positive np)
  have scaled:=previous.comp_mul_right (c:=((n:Nat):ℝ)⁻¹)
  have domains:IntervalIntegrable (fun v:ℝ=>weightedCentered c raw (v/(n:Nat))) volume 0 t := by
    simpa only [zero_div,div_inv_eq_mul,div_mul_cancel₀ _ np.ne',←div_eq_mul_inv,zero_mul] using scaled
  apply (domains.const_mul (((n:Nat):ℂ)^(c.value-1))).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v inside
  rw [uIoc_of_le positive.le] at inside
  have nonnegative:0≤v:=inside.1.le
  dsimp only [weightedCentered]
  rw [←mul_assoc,scaled_power c v nonnegative n]


/-- The canonical positive prefix is computed by scaling the actual source integrand. -/
private theorem prefix_scaled (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ)
    (t:ℝ) (positive:0<t) (n:ℕ+) :
    (∫ v:ℝ in 0..t,(v:ℂ)^(c.value-1)*(raw (v/(n:Nat))-raw 0))=
      ((n:Nat):ℂ)^c.value*(∫ v:ℝ in 0..t/(n:Nat),weightedCentered c raw v) := by
  have np:0<((n:Nat):ℝ):=by exact_mod_cast n.property
  calc
    _=(∫ v:ℝ in 0..t,((n:Nat):ℂ)^(c.value-1)*weightedCentered c raw (v/(n:Nat))) := by
      apply intervalIntegral.integral_congr
      intro v inside
      have nonnegative:0≤v:=(by simpa only [uIcc_of_le positive.le,mem_Icc] using inside:0≤v ∧ v≤t).1
      dsimp only [weightedCentered]
      rw [←mul_assoc,scaled_power c v nonnegative n]
    _=((n:Nat):ℂ)^(c.value-1)*(((n:Nat):ℝ) • ∫ v:ℝ in 0..t/(n:Nat),weightedCentered c raw v) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div _ np.ne',zero_div]
    _=_ := by
      have up:((n:Nat):ℂ)^(c.value-1)*((n:Nat):ℂ)=((n:Nat):ℂ)^c.value := by
        calc
          _=((n:Nat):ℂ)^(c.value-1)*((n:Nat):ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
          _=((n:Nat):ℂ)^((c.value-1)+1) := (Complex.cpow_add _ _ (by exact_mod_cast np.ne')).symm
          _=_ := by rw [sub_add_cancel]
      rw [Complex.real_smul,Complex.ofReal_natCast,←mul_assoc,up]


/-- Complete untruncated centred inversion commutes with the original inward prefix source action. -/
theorem source_inverse_R_action (c:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ)
    (native:MemLp raw 2 volume) (gap:∀{x:ℝ},|x|≤ q → raw x=raw 0)
    (t:ℝ) (positive:0<t) :
    burnolCenteredMobiusInverse (sourceRRaw c raw) t=
      -2*(t:ℂ)^(-c.value)*(∫ v:ℝ in 0..t,(v:ℂ)^(c.value-1)*burnolCenteredMobiusInverse raw v) := by
  have returnedGap:∀{x:ℝ},|x|≤q→sourceRRaw c raw x=sourceRRaw c raw 0:=by
    intro x inside
    rw [sourceRRaw_gap c raw gap inside,sourceRRaw_zero]
  rw [burnolCenteredMobiusInverse_eq_cutoffSum _ returnedGap]
  have integrals:∀n∈burnolCenteredMobiusCutoffFinset t,
      IntervalIntegrable (fun v:ℝ=>(ArithmeticFunction.moebius (n:Nat):ℂ)*((n:Nat):ℂ)⁻¹*
        ((v:ℂ)^(c.value-1)*(raw (v/(n:Nat))-raw 0))) volume 0 t := by
    intro n _
    exact (weighted_scaled_integrable c raw native gap t positive n).const_mul _
  have prefixRead:(∫ v:ℝ in 0..t,(v:ℂ)^(c.value-1)*burnolCenteredMobiusInverse raw v)=
      ∑ n∈burnolCenteredMobiusCutoffFinset t,(ArithmeticFunction.moebius (n:Nat):ℂ)*((n:Nat):ℂ)⁻¹*
        (∫ v:ℝ in 0..t,(v:ℂ)^(c.value-1)*(raw (v/(n:Nat))-raw 0)) := by
    calc
      _=(∫ v:ℝ in 0..t,∑ n∈burnolCenteredMobiusCutoffFinset t,
        (ArithmeticFunction.moebius (n:Nat):ℂ)*((n:Nat):ℂ)⁻¹*((v:ℂ)^(c.value-1)*(raw (v/(n:Nat))-raw 0))) := by
          apply intervalIntegral.integral_congr
          intro v inside
          have bounds:0≤v ∧ v≤t:=by simpa only [uIcc_of_le positive.le,mem_Icc] using inside
          dsimp only
          rw [inverse_prefix_cutoff raw gap t v positive bounds.1 bounds.2,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          unfold burnolCenteredMobiusSummand
          ring
      _=_ := by rw [intervalIntegral.integral_finsetSum integrals];simp only [intervalIntegral.integral_const_mul]
  rw [prefixRead,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have np:0<((n:Nat):ℝ):=by exact_mod_cast n.property
  rw [burnolCenteredMobiusSummand,sourceRRaw,sourceRRaw_zero,abs_of_pos (div_pos positive np),prefix_scaled c raw t positive n]
  have powers:((t/(n:Nat):ℝ):ℂ)^(-c.value)=(t:ℂ)^(-c.value)*((n:Nat):ℂ)^c.value := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg positive.le np.le]
    simp only [Complex.ofReal_natCast,Complex.cpow_neg,div_eq_mul_inv,inv_inv]
  rw [powers]
  ring

private theorem tail_tate_to_core (c : ℂ) (raw : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ in Ioi x⁻¹, (u : ℂ) ^ (-c) * burnolTateReciprocalRaw raw u) =
      ∫ v : ℝ in (0 : ℝ)..x, (v : ℂ) ^ (c - 1) * raw v := by
  have image : (fun u : ℝ => u⁻¹) '' Ioi x⁻¹ = Ioo 0 x := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      have vp : 0 < v := lt_trans (inv_pos.mpr hx) hv
      refine ⟨inv_pos.mpr vp, ?_⟩
      simpa only [inv_inv] using (inv_lt_inv₀ vp (inv_pos.mpr hx)).mpr hv
    · intro hu
      refine ⟨u⁻¹, ?_, inv_inv u⟩
      exact (inv_lt_inv₀ hx hu.1).mpr hu.2
  have derivative : ∀ u ∈ Ioi x⁻¹,
      HasDerivWithinAt (fun s : ℝ => s⁻¹) (-(u ^ 2)⁻¹) (Ioi x⁻¹) u := by
    intro u hu
    exact (hasDerivAt_inv (ne_of_gt (lt_trans (inv_pos.mpr hx) hu))).hasDerivWithinAt
  have change := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi derivative
    inv_injective.injOn (fun v : ℝ => (v : ℂ) ^ (c - 1) * raw v)
  rw [image] at change
  rw [intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo, change]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have up : 0 < u := lt_trans (inv_pos.mpr hx) hu
  have un : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr up.ne'
  simp only [burnolTateReciprocalRaw, abs_of_pos up,
    abs_neg, abs_inv, abs_pow, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow]
  rw [Complex.inv_cpow_ofReal_nonneg up.le, ← Complex.cpow_neg]
  have power : ((u : ℂ)^2)⁻¹ * (u : ℂ)^(-(c-1)) =
      (u : ℂ)^(-c) * (u : ℂ)⁻¹ := by
    rw [show ((u : ℂ)^2)⁻¹ = (u : ℂ)^(-2 : ℂ) by
      rw [Complex.cpow_neg, Complex.cpow_ofNat]]
    rw [← Complex.cpow_add _ _ un]
    rw [show (u : ℂ)⁻¹ = (u : ℂ)^(-1 : ℂ) by
      rw [Complex.cpow_neg, Complex.cpow_one]]
    rw [← Complex.cpow_add _ _ un]
    congr 1
    ring
  simpa only [mul_assoc] using congrArg (fun z : ℂ => z * raw u⁻¹) power.symm

private theorem actual_direct_R_positive_kernel (c : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (raw : ℝ → ℂ) (rawRead : (value : ℝ → ℂ) =ᵐ[volume] raw) :
    ∀ᵐ x : ℝ ∂volume, 0 < x →
      burnolDirectRightResolvent (c.value / 2) value x =
        -2 * (x : ℂ) ^ (-c.value) *
          (∫ s : ℝ in (0 : ℝ)..x, (s : ℂ) ^ (c.value - 1) * raw s) := by
  let plus := sourceVolterraResolvent c (burnolTateReciprocalL2 value)
  have plusRead := sourceVolterraResolvent_coeFn c (burnolTateReciprocalL2 value)
  have moved := burnolTateReciprocalRaw_ae_congr (Lp.memLp plus)
    ((memLp_congr_ae plusRead).mp (Lp.memLp plus)) plusRead
  have read := (burnolTateReciprocalL2_coeFn plus).trans moved
  have back : burnolTateReciprocalL2 plus = burnolDirectRightResolvent (c.value / 2) value := by
    change burnolTateReciprocalL2 (burnolTateReciprocalL2
      (burnolDirectRightResolvent (c.value / 2)
        (burnolTateReciprocalL2 (burnolTateReciprocalL2 value)))) = _
    rw [burnolTateReciprocalL2_involutive, burnolTateReciprocalL2_involutive]
  rw [back] at read
  filter_upwards [read] with x atx positive
  rw [atx, burnolTateReciprocalRaw, abs_of_pos positive,
    burnolFourierRightDivisionRaw_eq_tail _ _ (inv_pos.mpr positive)]
  have half : 2 * (c.value / 2) = c.value := by ring
  have negHalf : -2 * (c.value / 2) = -c.value := by ring
  rw [half, negHalf]
  have tailRead :
      (∫ u : ℝ in Ioi x⁻¹, (u : ℂ) ^ (-c.value) * burnolTateReciprocalL2 value u) =
        ∫ u : ℝ in Ioi x⁻¹, (u : ℂ) ^ (-c.value) * burnolTateReciprocalRaw value u := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (burnolTateReciprocalL2_coeFn value)] with u hu
    rw [hu]
  rw [tailRead, tail_tate_to_core _ _ positive]
  have coreRead :
      (∫ s : ℝ in (0 : ℝ)..x, (s : ℂ) ^ (c.value - 1) * value s) =
        ∫ s : ℝ in (0 : ℝ)..x, (s : ℂ) ^ (c.value - 1) * raw s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [rawRead] with s hs _
    rw [hs]
  rw [coreRead]
  have scale : (x : ℂ)⁻¹ * ((x⁻¹ : ℝ) : ℂ) ^ (c.value - 1) = (x : ℂ) ^ (-c.value) := by
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg positive.le, ← Complex.cpow_neg]
    rw [show (x : ℂ)⁻¹ = (x : ℂ) ^ (-1 : ℂ) by rw [Complex.cpow_neg, Complex.cpow_one]]
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
    congr 1
    ring
  calc
    _ = -2 * ((x : ℂ)⁻¹ * ((x⁻¹ : ℝ) : ℂ) ^ (c.value - 1)) *
      (∫ s : ℝ in (0 : ℝ)..x, (s : ℂ) ^ (c.value - 1) * raw s) := by ring
    _ = _ := by rw [scale]


/-- The explicit centred prefix is read back on the same actual full original R input. -/
theorem actual_R_positive_read (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) (raw:ℝ→ℂ)
    (read:(value:ℝ→ℂ)=ᵐ[volume] raw) (gap:∀{x:ℝ},|x|≤ q → raw x=raw 0) :
    ∀ᵐ x:ℝ ∂volume,0<x→burnolDirectRightResolvent (c.value/2) value x=sourceRRaw c raw x := by
  have native:MemLp raw 2 volume:=(memLp_congr_ae read).mp (Lp.memLp value)
  have positiveRead:=actual_direct_R_positive_kernel c value raw read
  filter_upwards [positiveRead] with x actual positive
  have parameterNe:c.value≠0:=by intro zero;have:=c.rightHalf;rw [zero] at this;norm_num at this
  have pure:IntervalIntegrable (fun v:ℝ=>(v:ℂ)^(c.value-1)) volume 0 x:=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [Complex.sub_re,Complex.one_re];linarith [c.rightHalf])
  have pureRead:(∫ v:ℝ in 0..x,(v:ℂ)^(c.value-1))=(x:ℂ)^c.value/c.value := by
    rw [integral_cpow (Or.inl (by simp only [Complex.sub_re,Complex.one_re];linarith [c.rightHalf]))]
    simp only [sub_add_cancel,Complex.ofReal_zero,Complex.zero_cpow parameterNe,sub_zero]
  have centered:=weighted_integrable c raw native gap x positive
  have total:(∫ v:ℝ in 0..x,(v:ℂ)^(c.value-1)*raw v)=
      (∫ v:ℝ in 0..x,weightedCentered c raw v)+raw 0*((x:ℂ)^c.value/c.value) := by
    calc
      _=(∫ v:ℝ in 0..x,weightedCentered c raw v+raw 0*(v:ℂ)^(c.value-1)) := by
        apply intervalIntegral.integral_congr
        intro v _
        dsimp only [weightedCentered]
        ring
      _=_ := by rw [intervalIntegral.integral_add centered (pure.const_mul _),intervalIntegral.integral_const_mul,pureRead]
  rw [actual positive,total]
  unfold sourceRRaw
  rw [abs_of_pos positive]
  have inverse:(x:ℂ)^(-c.value)*(x:ℂ)^c.value=1 := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),neg_add_cancel,Complex.cpow_zero]
  calc
    _ = -2*(x:ℂ)^(-c.value)*(∫ v:ℝ in 0..x,weightedCentered c raw v)
        -2*((x:ℂ)^(-c.value)*(x:ℂ)^c.value)*raw 0/c.value := by ring
    _ = _ := by rw [inverse]; ring


namespace NativeMobiusTriangle
open Finset

private theorem finite_multiplicative_fibres (N : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ pair ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun pair => pair.1*pair.2≤N), f pair.1 pair.2)=
      ∑ r∈Finset.Ioc 0 N,∑ pair∈r.divisorsAntidiagonal,f pair.1 pair.2 := by
  symm
  trans ∑ r∈Finset.Ioc 0 N,∑ pair∈(Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun pair => pair.1*pair.2=r),f pair.1 pair.2
  · refine sum_congr rfl fun r hr => ?_
    exact congrArg (fun s : Finset (ℕ×ℕ) => ∑ pair∈s,f pair.1 pair.2)
      (Nat.divisorsAntidiagonal_eq_prod_filter_of_le (Finset.mem_Ioc.mp hr).1.ne' (Finset.mem_Ioc.mp hr).2)
  · simp_rw [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun pair hp => ?_
    have hp' := mem_product.mp hp
    have positive : 0<pair.1*pair.2 := Nat.mul_pos (Finset.mem_Ioc.mp hp'.1).1 (Finset.mem_Ioc.mp hp'.2).1
    simp only [sum_ite_eq,Finset.mem_Ioc,positive,true_and]

private theorem complex_moebius_divisor_sum (r : ℕ) :
    (∑ d∈r.divisors,(ArithmeticFunction.moebius d:ℂ))=if r=1 then 1 else 0 := by
  have identity := congrArg (fun f : ArithmeticFunction ℂ => f r)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R:=ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at identity
  simpa only [ArithmeticFunction.intCoe_apply,ArithmeticFunction.one_apply] using identity

private theorem triangular_Ioc (N : ℕ) (h : ℕ → ℂ) :
    (∑ n∈Finset.Ioc 0 N,∑ k∈(Finset.Ioc 0 N).filter (fun k => n*k≤N),
      (ArithmeticFunction.moebius n:ℂ)*h (n*k))=if 1≤N then h 1 else 0 := by
  calc
    _ = ∑ pair∈(Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun pair => pair.1*pair.2≤N),
          (ArithmeticFunction.moebius pair.1:ℂ)*h (pair.1*pair.2) := by
      simp only [sum_filter,sum_product]
    _ = ∑ r∈Finset.Ioc 0 N,∑ pair∈r.divisorsAntidiagonal,
          (ArithmeticFunction.moebius pair.1:ℂ)*h (pair.1*pair.2) :=
      finite_multiplicative_fibres N (fun n k => (ArithmeticFunction.moebius n:ℂ)*h (n*k))
    _ = ∑ r∈Finset.Ioc 0 N,(if r=1 then (1:ℂ) else 0)*h r := by
      refine sum_congr rfl fun r hr => ?_
      calc
        _ = ∑ pair∈r.divisorsAntidiagonal,(ArithmeticFunction.moebius pair.1:ℂ)*h r := by
          refine sum_congr rfl fun pair hp => ?_
          rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
        _ = (∑ pair∈r.divisorsAntidiagonal,(ArithmeticFunction.moebius pair.1:ℂ))*h r := by
          rw [sum_mul]
        _ = (∑ d∈r.divisors,(ArithmeticFunction.moebius d:ℂ))*h r := by
          exact congrArg (fun z:ℂ => z*h r) (Nat.sum_divisorsAntidiagonal (fun n _ :ℕ => (ArithmeticFunction.moebius n:ℂ)))
        _ = _ := by rw [complex_moebius_divisor_sum r]
    _ = _ := by simp only [ite_mul,one_mul,zero_mul,sum_ite_eq',Finset.mem_Ioc,Nat.zero_lt_one,true_and]

/-- Exact finite Möbius inverse triangle, with every source product retained until its divisor fibre. -/
private theorem native_mobius_triangle (N : ℕ) (h : ℕ → ℂ) :
    (∑ n∈Finset.Ico 1 N,∑ k∈(Finset.Ico 1 N).filter (fun k => n*k<N),
      (ArithmeticFunction.moebius n:ℂ)*h (n*k))=if 1<N then h 1 else 0 := by
  cases N with
  | zero => simp
  | succ N =>
    have interval : Finset.Ico 1 (N+1)=Finset.Ioc 0 N := by ext n; simp only [Finset.mem_Ico,Finset.mem_Ioc]; omega
    simpa only [interval,Nat.lt_succ_iff] using triangular_Ioc N h

end NativeMobiusTriangle

/-- The original unit response retains its own finite Dirichlet channels and reciprocal mean. -/
def unitRaw (c:BurnolCompletedMellinCoordinate) : ℝ→ℂ := burnolUnitTailDirichletRaw c.value 4

theorem unitRaw_read (c:BurnolCompletedMellinCoordinate) :
    (burnolUnitTailResponse c 4:ℝ→ℂ)=ᵐ[volume] unitRaw c :=
  burnolUnitTailResponse_coeFn c 4 (by norm_num) (by norm_num)

theorem unitRaw_native (c:BurnolCompletedMellinCoordinate) : MemLp (unitRaw c) 2 volume :=
  (memLp_congr_ae (unitRaw_read c)).mp (Lp.memLp _)

theorem unitRaw_gap (c:BurnolCompletedMellinCoordinate) {x:ℝ} (inside:|x|≤4) :
    unitRaw c x=(4:ℂ)^(-c.value)/c.value := by
  have small:Nat.ceil (|x|/4)≤1 := Nat.ceil_le.mpr (by linarith)
  have empty:Finset.Ico 1 (Nat.ceil (|x|/4))=∅:=Finset.Ico_eq_empty_of_le small
  simp only [unitRaw,burnolUnitTailDirichletRaw,burnolUnitTailDirichletChannels,empty,
    Finset.sum_empty,mul_zero,sub_zero]
  norm_num

theorem unitRaw_zero (c:BurnolCompletedMellinCoordinate) :
    unitRaw c 0=(4:ℂ)^(-c.value)/c.value := unitRaw_gap c (by norm_num)

private theorem unit_channels_scaled (t:ℝ) (n:ℕ) (positive:0<n) :
    burnolUnitTailDirichletChannels 4 (t/n)=
      (burnolUnitTailDirichletChannels 4 t).filter (fun k=>n*k<Nat.ceil (|t|/4)) := by
  have np:0<(n:ℝ):=by exact_mod_cast positive
  have incidence (k:ℕ) : k<Nat.ceil (|t/(n:ℝ)|/4) ↔ n*k<Nat.ceil (|t|/4) := by
    rw [Nat.lt_ceil,Nat.lt_ceil]
    rw [show |t/(n:ℝ)|/4=(|t|/4)/(n:ℝ) by rw [abs_div,abs_of_pos np];ring,
      lt_div_iff₀ np]
    push_cast
    rw [mul_comm]
  ext k
  simp only [burnolUnitTailDirichletChannels,Finset.mem_Ico,Finset.mem_filter,incidence]
  constructor
  · rintro ⟨kp,product⟩
    exact ⟨⟨kp,(Nat.le_mul_of_pos_left k positive).trans_lt product⟩,product⟩
  · rintro ⟨⟨kp,_⟩,product⟩
    exact ⟨kp,product⟩

private theorem unit_inverse_cutoff (c:BurnolCompletedMellinCoordinate) (t:ℝ) :
    burnolCenteredMobiusInverse (unitRaw c) t=
      ∑ n∈burnolUnitTailDirichletChannels 4 t,(ArithmeticFunction.moebius n:ℂ)*(n:ℂ)⁻¹*
        (unitRaw c (t/n)-unitRaw c 0) := by
  classical
  let term:ℕ→ℂ:=fun n=>if 0<n then (ArithmeticFunction.moebius n:ℂ)*(n:ℂ)⁻¹*
    (unitRaw c (t/n)-unitRaw c 0) else 0
  have support:Function.support term⊆{n:ℕ|0<n}:=by
    intro n active
    by_contra h
    exact active (if_neg h)
  calc
    _=∑' n:ℕ+,term (n:ℕ) := by
      apply tsum_congr
      intro n
      dsimp only [term]
      rw [if_pos n.pos]
      ring
    _=∑' n:ℕ,term n:=tsum_subtype_eq_of_support_subset support
    _=∑ n∈burnolUnitTailDirichletChannels 4 t,term n := by
      apply tsum_eq_sum
      intro n outside
      by_cases positive:0<n
      · have large:Nat.ceil (|t|/4)≤n:=by
          simp only [burnolUnitTailDirichletChannels,Finset.mem_Ico] at outside
          omega
        have np:0<(n:ℝ):=by exact_mod_cast positive
        have bound:|t/(n:ℝ)|≤4 := by
          rw [abs_div,abs_of_pos np]
          apply (div_le_iff₀ np).mpr
          have high:(|t|/4)≤(n:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast large)
          linarith
        simp only [term,positive,ite_true,unitRaw_gap c bound,unitRaw_zero,sub_self,mul_zero]
      · exact if_neg positive
    _=_ := by
      apply Finset.sum_congr rfl
      intro n belongs
      have positive:0<n:=(Finset.mem_Ico.mp belongs).1
      simp only [term,positive,ite_true]

/-- Complete centred Möbius inversion recovers the actual unit's original tail source. -/
theorem original_unit_inverse_source (c:BurnolCompletedMellinCoordinate) (t:ℝ) :
    burnolCenteredMobiusInverse (unitRaw c) t=burnolRadiusUnitTailRaw c.value 4 t := by
  classical
  let N:=Nat.ceil (|t|/4)
  have normalized:
      (∑ n∈burnolUnitTailDirichletChannels 4 t,(ArithmeticFunction.moebius n:ℂ)*(n:ℂ)⁻¹*
        (unitRaw c (t/n)-unitRaw c 0))=
      -((|t|:ℝ):ℂ)^(-c.value)*
        ∑ n∈Finset.Ico 1 N,∑ k∈(Finset.Ico 1 N).filter (fun k=>n*k<N),
          (ArithmeticFunction.moebius n:ℂ)*((n*k:ℕ):ℂ)^(c.value-1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n belongs
    have positive:0<n:=(Finset.mem_Ico.mp belongs).1
    have np:0<(n:ℝ):=by exact_mod_cast positive
    have incidence:4 < |t/(n:ℝ)| := by
      have below:(n:ℝ)< |t|/4:=Nat.lt_ceil.mp (Finset.mem_Ico.mp belongs).2
      rw [abs_div,abs_of_pos np,lt_div_iff₀ np]
      linarith
    have scale:(n:ℂ)⁻¹*(-((|t/(n:ℝ)|:ℝ):ℂ)^(-c.value))=
        -((|t|:ℝ):ℂ)^(-c.value)*(n:ℂ)^(c.value-1) := by
      have paid:(n:ℂ)⁻¹*burnolRadiusUnitTailRaw c.value 4 (t/n)=
          if n∈burnolUnitTailDirichletChannels 4 t
          then -((|t|:ℝ):ℂ)^(-c.value)*(n:ℂ)^(c.value-1) else 0 :=
        burnolRadiusUnitTail_source_term c.value 4 t (by norm_num) (⟨n,positive⟩:ℕ+)
      simpa only [burnolRadiusUnitTailRaw,if_pos incidence,if_pos belongs] using paid
    have difference:unitRaw c (t/n)-unitRaw c 0=
        -((|t/(n:ℝ)|:ℝ):ℂ)^(-c.value)*
          ∑ k∈burnolUnitTailDirichletChannels 4 (t/n),(k:ℂ)^(c.value-1) := by
      rw [unitRaw_zero]
      unfold unitRaw burnolUnitTailDirichletRaw
      simp only [Complex.ofReal_ofNat]
      ring
    rw [difference,unit_channels_scaled t n positive]
    change _= -((|t|:ℝ):ℂ)^(-c.value)*
      ∑ k∈(burnolUnitTailDirichletChannels 4 t).filter (fun k=>n*k<N),
        (ArithmeticFunction.moebius n:ℂ)*((n*k:ℕ):ℂ)^(c.value-1)
    calc
      _=(ArithmeticFunction.moebius n:ℂ)*
          ((n:ℂ)⁻¹*(-((|t/(n:ℝ)|:ℝ):ℂ)^(-c.value)))*
          ∑ k∈(burnolUnitTailDirichletChannels 4 t).filter (fun k=>n*k<N),
            (k:ℂ)^(c.value-1) := by ring
      _=_ := by
        rw [scale,Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
        ring
  rw [unit_inverse_cutoff,normalized,
    NativeMobiusTriangle.native_mobius_triangle N (fun r:ℕ=>(r:ℂ)^(c.value-1))]
  have active:1<N↔4< |t|:=by
    change 1<Nat.ceil (|t|/4)↔_
    rw [Nat.lt_ceil]
    norm_num
    constructor <;> intro h <;> linarith
  simp [active,burnolRadiusUnitTailRaw]

end OriginalKCenteredMobiusRSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
