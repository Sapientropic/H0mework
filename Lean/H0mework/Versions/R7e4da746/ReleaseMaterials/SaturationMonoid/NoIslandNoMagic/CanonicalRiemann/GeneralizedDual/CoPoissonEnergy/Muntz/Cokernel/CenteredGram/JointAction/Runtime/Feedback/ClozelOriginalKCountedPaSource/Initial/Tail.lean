import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.Incidence
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial
open Complex Filter MeasureTheory Set
open scoped BigOperators Topology InnerProductSpace

private theorem harmonic_Ioc (a b : ℕ) (ordered : a≤b) :
    (∑ n∈Finset.Ioc a b,(n:ℝ)⁻¹)=(harmonic b:ℝ)-(harmonic a:ℝ) := by
  refine Nat.le_induction ?_ ?_ b ordered
  · simp
  intro n hn previous
  rw [Finset.sum_Ioc_succ_top hn,previous,harmonic_succ]
  push_cast
  ring

/-- One original harmonic inventory is controlled as a complete sum minus log. -/
private theorem harmonic_floor_error (x : ℝ) (large : 2≤x) :
    |(harmonic ⌊x⌋₊:ℝ)-Real.log x-Real.eulerMascheroniConstant|≤2/x := by
  let n:=⌊x⌋₊
  have hx:0<x := by linarith
  have hn:1≤n := (Nat.le_floor_iff' (by decide : (1:ℕ)≠0)).mpr (by norm_num;linarith)
  have hnpos:0<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have lower:(n:ℝ)≤x := Nat.floor_le hx.le
  have upper:x<(n:ℝ)+1 := Nat.lt_floor_add_one x
  have logLower:=Real.strictMonoOn_log.monotoneOn hnpos hx lower
  have logUpper:=Real.strictMonoOn_log.monotoneOn hx (by positivity : 0<(n:ℝ)+1) upper.le
  have gammaLower:=Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have gammaUpper:=Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq,Real.eulerMascheroniSeq',show n≠0 by omega,if_false] at gammaLower gammaUpper
  have width : Real.log ((n:ℝ)+1)-Real.log n≤(n:ℝ)⁻¹ := by
    rw [←Real.log_div (by positivity) hnpos.ne']
    have paid:=Real.log_le_sub_one_of_pos (show 0<((n:ℝ)+1)/(n:ℝ) by positivity)
    convert paid using 1
    field_simp
    ring
  have error : |(harmonic n:ℝ)-Real.log x-Real.eulerMascheroniConstant|≤(n:ℝ)⁻¹ := by
    rw [abs_le]
    constructor <;> linarith
  apply error.trans
  rw [inv_eq_one_div,div_le_div_iff₀ hnpos hx]
  have natLower:(1:ℝ)≤n := by exact_mod_cast hn
  nlinarith

private theorem harmonic_raw_real (l u x : ℝ) (hl:0<l) (ordered:l≤u) :
    burnolHarmonicStepWaveRaw l u x=
      (((harmonic ⌊|x|/l⌋₊:ℝ)-(harmonic ⌊|x|/u⌋₊:ℝ)-Real.log (u/l)):ℂ) := by
  have hu:0<u:=hl.trans_le ordered
  have indices:⌊|x|/u⌋₊≤⌊|x|/l⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_left (abs_nonneg x) hl ordered)
  have sum:(∑n∈Finset.Ioc ⌊|x|/u⌋₊ ⌊|x|/l⌋₊,(n:ℂ)⁻¹)=
      (((harmonic ⌊|x|/l⌋₊:ℝ)-(harmonic ⌊|x|/u⌋₊:ℝ)):ℂ) := by
    have actual:=congrArg Complex.ofReal (harmonic_Ioc ⌊|x|/u⌋₊ ⌊|x|/l⌋₊ indices)
    simpa only [Complex.ofReal_sum,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_sub] using actual
  rw [burnolHarmonicStepWaveRaw,burnolHarmonicStepChannels,sum]

/-- The true harmonic source has a 1/x tail, independently of a zeta qualification. -/
theorem harmonic_tail (l u x : ℝ) (hl:0<l) (ordered:l≤u) (large:2*u≤|x|) :
    ‖burnolHarmonicStepWaveRaw l u x‖≤4*u/|x| := by
  have hu:0<u:=hl.trans_le ordered
  have hx:0 < |x|:=lt_of_lt_of_le (by positivity : 0<2*u) large
  have ly:2≤|x|/u := (le_div_iff₀ hu).mpr large
  have lz:2≤|x|/l := (le_div_iff₀ hl).mpr (by nlinarith)
  have ey:=harmonic_floor_error (|x|/u) ly
  have ez:=harmonic_floor_error (|x|/l) lz
  have ratio : Real.log (u/l)=Real.log (|x|/l)-Real.log (|x|/u) := by
    rw [Real.log_div hu.ne' hl.ne',Real.log_div hx.ne' hl.ne',Real.log_div hx.ne' hu.ne']
    ring
  rw [harmonic_raw_real l u x hl ordered,←Complex.ofReal_sub,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have split : (harmonic ⌊|x|/l⌋₊:ℝ)-(harmonic ⌊|x|/u⌋₊:ℝ)-Real.log (u/l)=
      ((harmonic ⌊|x|/l⌋₊:ℝ)-Real.log (|x|/l)-Real.eulerMascheroniConstant)-
      ((harmonic ⌊|x|/u⌋₊:ℝ)-Real.log (|x|/u)-Real.eulerMascheroniConstant) := by rw [ratio];ring
  rw [split]
  apply (abs_sub _ _).trans ((add_le_add ez ey).trans _)
  field_simp
  nlinarith

def wholeCutoff (M b : ℝ) : ℝ := M*(1+1/b)

/-- The moving cutoff controls both scaled whole tails with no scale-range restriction. -/
theorem harmonic_product_tail (l u b M x : ℝ) (hl:0<l) (ordered:l≤u) (upper:u≤4)
    (hb:0<b) (large:8≤M) (beyond:wholeCutoff M b≤|x|) :
    ‖star (burnolHarmonicStepWaveRaw l u x)*burnolHarmonicStepWaveRaw 1 (3/2) (b*x)‖≤
      (24*u)/(b*|x|^2) := by
  have hu:0<u:=hl.trans_le ordered
  have hM:0<M:=by linarith
  have cutoff: M≤wholeCutoff M b := by unfold wholeCutoff;have:=one_div_pos.mpr hb;nlinarith
  have hx:0 < |x|:=(hM.trans_le cutoff).trans_le beyond
  have firstLarge:2*u≤|x|:=by linarith
  have scaled: b*wholeCutoff M b=M*(b+1) := by unfold wholeCutoff;field_simp
  have secondLarge:2*(3/2:ℝ)≤|b*x| := by
    rw [abs_mul,abs_of_pos hb]
    have monotone:=mul_le_mul_of_nonneg_left beyond hb.le
    rw [scaled] at monotone
    nlinarith
  have left:=harmonic_tail l u x hl ordered firstLarge
  have right:=harmonic_tail 1 (3/2) (b*x) (by norm_num) (by norm_num) secondLarge
  rw [norm_mul,norm_star]
  apply (mul_le_mul left right (norm_nonneg _) (by positivity)).trans_eq
  rw [abs_mul,abs_of_pos hb]
  field_simp
  ring

/-- The reciprocal-count leg uses its paid source bound, retaining the same scaled harmonic foot. -/
theorem mixed_product_tail (l u b M x : ℝ) (hl:0<l) (ordered:l≤u)
    (hb:0<b) (large:8≤M) (beyond:wholeCutoff M b≤|x|) :
    ‖star (burnolReciprocalStepWaveRaw l u x)*burnolHarmonicStepWaveRaw 1 (3/2) (b*x)‖≤
      6/(b*|x|^2) := by
  have hM:0<M:=by linarith
  have cutoff:M≤wholeCutoff M b := by unfold wholeCutoff;have:=one_div_pos.mpr hb;nlinarith
  have hx:0 < |x|:=(hM.trans_le cutoff).trans_le beyond
  have scaled:b*wholeCutoff M b=M*(b+1) := by unfold wholeCutoff;field_simp
  have secondLarge:2*(3/2:ℝ)≤|b*x| := by
    rw [abs_mul,abs_of_pos hb]
    have monotone:=mul_le_mul_of_nonneg_left beyond hb.le
    rw [scaled] at monotone
    nlinarith
  have left:=burnolReciprocalStepWave_bound l u x hl ordered (abs_pos.mp hx)
  have right:=harmonic_tail 1 (3/2) (b*x) (by norm_num) (by norm_num) secondLarge
  rw [norm_mul,norm_star]
  apply (mul_le_mul left right (norm_nonneg _) (by positivity)).trans_eq
  rw [abs_mul,abs_of_pos hb]
  field_simp
  ring

end CountedPaInitial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
