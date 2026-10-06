import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCutoff
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.CanonicalPreparationSquareCutoff
open CanonicalPreparationCutoff
open scoped Topology ContDiff BigOperators

theorem half_exponential_square (x : ℝ) :
    expNegInvGlue (2*x)^2=expNegInvGlue x := by
  by_cases nonpositive : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos nonpositive,
      expNegInvGlue.zero_of_nonpos (by linarith)]
    norm_num
  · have positive : 0<x := lt_of_not_ge nonpositive
    simp only [expNegInvGlue, if_neg nonpositive,
      if_neg (by linarith : ¬ 2*x ≤ 0), pow_two, ←Real.exp_add]
    congr 1
    field_simp
    ring

theorem half_exponential_root (x : ℝ) :
    Real.sqrt (expNegInvGlue x)=expNegInvGlue (2*x) := by
  rw [←half_exponential_square x, Real.sqrt_sq (expNegInvGlue.nonneg _)]

def transitionRoot (x : ℝ) : ℝ :=
  expNegInvGlue (2*x)/Real.sqrt (expNegInvGlue x+expNegInvGlue (1-x))

theorem transitionRoot_literal (x : ℝ) :
    transitionRoot x=Real.sqrt (Real.smoothTransition x) := by
  rw [Real.smoothTransition,Real.sqrt_div (expNegInvGlue.nonneg x),half_exponential_root]
  rfl

theorem transitionRoot_smooth : ContDiff ℝ ∞ transitionRoot := by
  unfold transitionRoot
  have denom : ContDiff ℝ ∞ (fun x : ℝ => expNegInvGlue x+expNegInvGlue (1-x)) :=
    expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))
  apply (expNegInvGlue.contDiff.comp (contDiff_const.mul contDiff_id)).div
    (denom.sqrt (fun x => (Real.smoothTransition.pos_denom x).ne'))
  intro x
  exact (Real.sqrt_pos.mpr (Real.smoothTransition.pos_denom x)).ne'

theorem sourceChi_root_smooth : ContDiff ℝ ∞ (fun t => Real.sqrt (sourceChi t)) := by
  have identity : (fun t => Real.sqrt (sourceChi t))=fun t => transitionRoot (t-1) := by
    funext t
    rw [sourceChi_transition,transitionRoot_literal]
  rw [identity]
  exact transitionRoot_smooth.comp (contDiff_id.sub contDiff_const)

def factorRoot (d : ℝ) : ℝ :=
  transitionRoot (2-d/sourceRadius)*transitionRoot (2+d/sourceRadius)

theorem factorRoot_literal (d : ℝ) : factorRoot d=Real.sqrt (sourceCutFactor d) := by
  rw [sourceCutFactor_product,Real.sqrt_mul (Real.smoothTransition.nonneg _)]
  simp only [factorRoot,transitionRoot_literal]

theorem factorRoot_smooth : ContDiff ℝ ∞ factorRoot :=
  (transitionRoot_smooth.comp (contDiff_const.sub (contDiff_id.div_const sourceRadius))).mul
    (transitionRoot_smooth.comp (contDiff_const.add (contDiff_id.div_const sourceRadius)))

def sourcePsiRoot (z : FlatConfiguration) : ℝ :=
  ∏ i : Fin 100, factorRoot (z i-flatSource i)

theorem sourcePsiRoot_literal (z : FlatConfiguration) : sourcePsiRoot z=Real.sqrt (sourcePsi z) := by
  rw [sourcePsi, Real.sqrt_prod _ (fun i _ => factor_nonnegative _)]
  apply Finset.prod_congr rfl
  intro i _
  exact factorRoot_literal _

theorem sourcePsiRoot_smooth : ContDiff ℝ ∞ sourcePsiRoot := by
  unfold sourcePsiRoot
  apply contDiff_prod
  intro i _
  exact factorRoot_smooth.comp ((contDiff_apply ℝ ℝ i).sub contDiff_const)

theorem sourcePsiRoot_square (z : FlatConfiguration) : sourcePsiRoot z^2=sourcePsi z := by
  rw [sourcePsiRoot_literal,Real.sq_sqrt (sourcePsi_nonnegative _)]

theorem sourcePsiRoot_support : Function.support sourcePsiRoot=sourceOpenBox := by
  rw [←sourcePsi_support]
  ext z
  simp only [Function.mem_support,sourcePsiRoot_literal]
  exact not_congr (Real.sqrt_eq_zero (sourcePsi_nonnegative _))

theorem sourcePsiRoot_compact : HasCompactSupport sourcePsiRoot := by
  change IsCompact (tsupport sourcePsiRoot)
  have original : IsCompact (tsupport sourcePsi) := sourcePsi_compact
  simpa only [tsupport,sourcePsiRoot_support,sourcePsi_support] using original

-- This is the original center_unit_p100 in the compact-majorant producer.
def sourceUnitMomentum (i : Fin 100) : ℝ :=
  if i=0 ∨ i=2 ∨ i=5 then Real.sqrt 87403953/21378 else
  if i=67 ∨ i=80 ∨ i=94 then 45*Real.sqrt 3563/7126 else 0

theorem sourceUnitMomentum_unit : (∑ i : Fin 100, sourceUnitMomentum i^2)=1 := by
  have restricted : (∑ i : Fin 100, sourceUnitMomentum i^2)=
    ∑ i ∈ ({0,2,5,67,80,94} : Finset (Fin 100)), sourceUnitMomentum i^2 := by
    symm
    apply Finset.sum_subset (by simp)
    intro i _ outside
    have indices : i≠0 ∧ i≠2 ∧ i≠5 ∧ i≠67 ∧ i≠80 ∧ i≠94 := by
      simpa using outside
    simp [sourceUnitMomentum,indices.1,indices.2.1,indices.2.2.1,
      indices.2.2.2.1,indices.2.2.2.2.1,indices.2.2.2.2.2]
  rw [restricted]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [Finset.sum_insert,Finset.sum_singleton,sourceUnitMomentum,div_pow,mul_pow,
    Real.sq_sqrt,Fin.ext_iff]

def sourceTheta (z p : FlatConfiguration) : ℝ :=
  (∏ i : Fin 100, sourceCutFactor (2*(z i-flatSource i)))*
    ∏ i : Fin 100, sourceCutFactor (2*(p i-sourceUnitMomentum i))

def sourceThetaRoot (zp : FlatConfiguration×FlatConfiguration) : ℝ :=
  (∏ i : Fin 100, factorRoot (2*(zp.1 i-flatSource i)))*
    ∏ i : Fin 100, factorRoot (2*(zp.2 i-sourceUnitMomentum i))

theorem sourceTheta_nonnegative (z p : FlatConfiguration) : 0 ≤ sourceTheta z p :=
  mul_nonneg (Finset.prod_nonneg (fun _ _ => factor_nonnegative _))
    (Finset.prod_nonneg (fun _ _ => factor_nonnegative _))

theorem sourceThetaRoot_literal (zp : FlatConfiguration×FlatConfiguration) :
    sourceThetaRoot zp=Real.sqrt (sourceTheta zp.1 zp.2) := by
  unfold sourceThetaRoot sourceTheta
  rw [Real.sqrt_mul (Finset.prod_nonneg (fun _ _ => factor_nonnegative _)),
    Real.sqrt_prod _ (fun _ _ => factor_nonnegative _),
    Real.sqrt_prod _ (fun _ _ => factor_nonnegative _)]
  simp only [factorRoot_literal]

theorem sourceThetaRoot_smooth : ContDiff ℝ ∞ sourceThetaRoot := by
  unfold sourceThetaRoot
  apply ContDiff.mul
  · apply contDiff_prod
    intro i _
    exact factorRoot_smooth.comp (contDiff_const.mul
      (((contDiff_apply ℝ ℝ i).comp contDiff_fst).sub contDiff_const))
  · apply contDiff_prod
    intro i _
    exact factorRoot_smooth.comp (contDiff_const.mul
      (((contDiff_apply ℝ ℝ i).comp contDiff_snd).sub contDiff_const))

theorem sourceThetaRoot_square (zp : FlatConfiguration×FlatConfiguration) :
    sourceThetaRoot zp^2=sourceTheta zp.1 zp.2 := by
  rw [sourceThetaRoot_literal,Real.sq_sqrt (sourceTheta_nonnegative _ _)]

theorem sourceTheta_at_source : sourceTheta flatSource sourceUnitMomentum=1 := by
  have factor : sourceCutFactor 0=1 := by
    rw [sourceCutFactor_transition]
    exact Real.smoothTransition.one_of_one_le (by norm_num)
  simp [sourceTheta,factor]

abbrev PhysicalMomentum := EuclideanSpace ℝ (Fin 100)

def radialRoot (p : PhysicalMomentum) : ℝ := Real.sqrt (sourceChi (2*‖p‖))

theorem radialRoot_zero {p : PhysicalMomentum} (low : ‖p‖ ≤ 1/2) : radialRoot p=0 := by
  simp only [radialRoot,sourceChi,if_pos (by linarith : 2*‖p‖ ≤ 1),Real.sqrt_zero]

theorem radialRoot_smooth : ContDiff ℝ ∞ radialRoot := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases nonzero : p≠0
  · exact sourceChi_root_smooth.contDiffAt.comp p
      (contDiffAt_const.mul (contDiffAt_norm ℝ nonzero))
  · have zero : p=0 := not_not.mp nonzero
    subst p
    have localZero : radialRoot =ᶠ[𝓝 (0 : PhysicalMomentum)] (fun _ => (0 : ℝ)) := by
      have nearby : ∀ᶠ p : PhysicalMomentum in 𝓝 0, ‖p‖ < 1/2 :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
      filter_upwards [nearby] with p low
      exact radialRoot_zero low.le
    exact contDiffAt_const.congr_of_eventuallyEq localZero

def normalizedMomentum (p : PhysicalMomentum) : FlatConfiguration := fun i => p i/‖p‖

theorem normalizedMomentum_smooth {p : PhysicalMomentum} (nonzero : p≠0) :
    ContDiffAt ℝ ∞ normalizedMomentum p := by
  apply contDiffAt_pi.mpr
  intro i
  exact (PiLp.proj 2 (fun _ : Fin 100 => ℝ) i).contDiff.contDiffAt.div
    (contDiffAt_norm ℝ nonzero) (norm_ne_zero_iff.mpr nonzero)

def factorWeight (zp : FlatConfiguration×PhysicalMomentum) : ℝ :=
  sourceThetaRoot (zp.1,normalizedMomentum zp.2)*radialRoot zp.2

theorem factorWeight_zero {zp : FlatConfiguration×PhysicalMomentum} (low : ‖zp.2‖ ≤ 1/2) :
    factorWeight zp=0 := by
  simp only [factorWeight,radialRoot_zero low,mul_zero]

theorem factorWeight_smooth : ContDiff ℝ ∞ factorWeight := by
  rw [contDiff_iff_contDiffAt]
  intro zp
  by_cases nonzero : zp.2≠0
  · exact (sourceThetaRoot_smooth.contDiffAt.comp zp
      (contDiffAt_fst.prodMk ((normalizedMomentum_smooth nonzero).comp zp contDiffAt_snd))).mul
        (radialRoot_smooth.contDiffAt.comp zp contDiffAt_snd)
  · have zero : zp.2=0 := not_not.mp nonzero
    have localZero : factorWeight =ᶠ[𝓝 zp] (fun _ => (0 : ℝ)) := by
      have nearby : ∀ᶠ q : FlatConfiguration×PhysicalMomentum in 𝓝 zp, ‖q.2‖ < 1/2 :=
        (isOpen_lt continuous_snd.norm continuous_const).mem_nhds
          (by change ‖zp.2‖ < 1/2; rw [zero]; norm_num)
      filter_upwards [nearby] with q low
      exact factorWeight_zero low.le
    exact contDiffAt_const.congr_of_eventuallyEq localZero

theorem factorWeight_square (zp : FlatConfiguration×PhysicalMomentum) :
    factorWeight zp^2=sourceTheta zp.1 (normalizedMomentum zp.2)*sourceChi (2*‖zp.2‖) := by
  rw [factorWeight,mul_pow,sourceThetaRoot_square,radialRoot,
    Real.sq_sqrt (chi_nonnegative _)]

def sourceMomentum : PhysicalMomentum := WithLp.toLp 2 sourceUnitMomentum

theorem sourceMomentum_unit : ‖sourceMomentum‖=1 := by
  rw [EuclideanSpace.norm_eq]
  change Real.sqrt (∑ i : Fin 100, ‖sourceUnitMomentum i‖^2)=1
  simp only [Real.norm_eq_abs,sq_abs,sourceUnitMomentum_unit,Real.sqrt_one]

theorem factorWeight_at_source : factorWeight (flatSource,sourceMomentum)=1 := by
  have direction : normalizedMomentum sourceMomentum=sourceUnitMomentum := by
    ext i
    change sourceUnitMomentum i/‖sourceMomentum‖=sourceUnitMomentum i
    rw [sourceMomentum_unit,div_one]
  rw [factorWeight,direction,sourceThetaRoot_literal,sourceTheta_at_source,
    radialRoot,sourceMomentum_unit]
  norm_num [sourceChi]

end LowEnergy.CanonicalPreparationSquareCutoff
#print axioms LowEnergy.CanonicalPreparationSquareCutoff.sourceThetaRoot_smooth
#print axioms LowEnergy.CanonicalPreparationSquareCutoff.sourceThetaRoot_square
#print axioms LowEnergy.CanonicalPreparationSquareCutoff.factorWeight_smooth
#print axioms LowEnergy.CanonicalPreparationSquareCutoff.factorWeight_square
