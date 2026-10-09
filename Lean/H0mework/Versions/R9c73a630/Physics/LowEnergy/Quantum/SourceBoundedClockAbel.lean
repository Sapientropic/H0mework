import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceBoundedClockAbel
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussFockWeights GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusResponsePositiveSource SourceClockYukawaCubicCurrent
open SourceRelativePowerTail SourceFamilyHilbert SourceFamilyOperator
open FullYSourceCutoffNorm
open FullYSourceFiniteTimeIntegral FullYSourceTimeFamilyGraph FullYSourceCutoffTimeGraph
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev Op := H →L[ℂ] H
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev L2H := Lp H 2 (MeasureTheory.volume : Measure ℝ)
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : SecondCountableTopologyEither ℝ Op := ⟨Or.inl inferInstance⟩
local instance : NormedAlgebra ℚ Op := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] finiteResolvent SourceClockYukawaCubicCurrent.resolventCore

/-- Dimensionless original clock instrument on the positive-volume chart. -/
def clockProfile (z : SourceCoordinateSlice) : ℝ := GaussNativeEnergy.volume z/(1+GaussNativeEnergy.volume z)
private theorem clock_smooth (z : physicalChart) : ContDiffAt ℝ ∞ clockProfile z.val :=
  volume_smooth.contDiffAt.div (contDiffAt_const.add volume_smooth.contDiffAt)
    (ne_of_gt (by have h:=volume_pos z; positivity))
private theorem clock_range (z : physicalChart) : 0 ≤ clockProfile z ∧ clockProfile z ≤ 1 := by
  have h:=volume_pos z
  unfold clockProfile
  have hd:0<1+GaussNativeEnergy.volume z:=by positivity
  exact ⟨div_nonneg h.le hd.le,(div_le_one hd).mpr (by linarith)⟩
private def clockFiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (clockProfile z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem clock_fiber_smooth (z : physicalChart) : ContDiffAt ℝ ∞ clockFiber z.val :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (clock_smooth z)).smul contDiffAt_const
private theorem clock_weight (z : physicalChart) (w : ℕ → ℂ) : Commute (weight w) (clockFiber z) :=
  (Commute.one_right _).smul_right _
private theorem clock_fiber_bound (z : physicalChart) (f : FockFiber) : ‖clockFiber z f‖ ≤ 1*‖f‖ := by
  change ‖(clockProfile z:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (clock_range z).1]
  exact mul_le_mul_of_nonneg_right (clock_range z).2 (norm_nonneg f)
private def clockRoot : Op := GaussBoundedMultiplier.extension clockFiber clock_fiber_smooth clock_weight
  1 zero_le_one clock_fiber_bound
private theorem clock_root_norm : ‖clockRoot‖ ≤ 1 :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
def clockCore : End := multiply clockProfile clock_smooth
private theorem clock_root_core (f : QuantumTest) : clockRoot (embed f)=embed (clockCore f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem clock_root_pair (x y : H) : inner ℂ (clockRoot x) y=inner ℂ x (clockRoot y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  obtain ⟨g,rfl⟩:=coreEquiv.surjective b
  change inner ℂ (clockRoot (embed f)) (embed g)=inner ℂ (embed f) (clockRoot (embed g))
  rw [clock_root_core,clock_root_core]
  exact (multiply_pair _ _ _ _).symm
/-- The squared actual multiplier is a positive contraction, with its original core retained. -/
def clockObservable : Op := star clockRoot*clockRoot
private theorem clock_positive : 0 ≤ clockObservable := star_mul_self_nonneg _
private theorem clock_norm : ‖clockObservable‖ ≤ 1 := by
  calc ‖clockObservable‖ ≤ ‖star clockRoot‖*‖clockRoot‖:=norm_mul_le _ _
       _=‖clockRoot‖*‖clockRoot‖:=by rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint.norm_map]
       _≤1*1:=mul_le_mul clock_root_norm clock_root_norm (norm_nonneg _) zero_le_one
       _=1:=one_mul _
private theorem clock_le_one : clockObservable ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ clock_positive).mp clock_norm
private theorem clock_core (f : QuantumTest) : clockObservable (embed f)=embed (clockCore (clockCore f)) := by
  have hp:IsSelfAdjoint clockRoot := (show clockRoot.toLinearMap.IsSymmetric from clock_root_pair).isSelfAdjoint
  change (star clockRoot) (clockRoot (embed f))=_
  rw [hp.star_eq,clock_root_core,clock_root_core]

private abbrev C (F : Index) : Op := GaussGradedCompression.compression F
private def orbit (F : Index) (t : ℝ) : Op :=
  SourceFiniteUnitary.time (C F) (-t)*clockObservable*SourceFiniteUnitary.time (C F) t
private theorem time_norm_le (F : Index) (t : ℝ) : ‖SourceFiniteUnitary.time (C F) t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using (SourceFiniteUnitary.time_norm (C F)
    (GaussGradedCompression.compression_selfAdjoint F) t x).le
private theorem orbit_norm (F : Index) (t : ℝ) : ‖orbit F t‖ ≤ 1 := by
  calc ‖orbit F t‖ ≤ (‖SourceFiniteUnitary.time (C F) (-t)‖*‖clockObservable‖)*
      ‖SourceFiniteUnitary.time (C F) t‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
       _≤(1*1)*1:=mul_le_mul (mul_le_mul (time_norm_le F (-t)) clock_norm (norm_nonneg _) zero_le_one)
        (time_norm_le F t) (norm_nonneg _) (by norm_num)
       _=1:=by norm_num
private theorem time_continuous (F : Index) : Continuous (SourceFiniteUnitary.time (C F)) :=
  continuous_iff_continuousAt.mpr (fun t=>(hasDerivAt_exp_smul_const ((-Complex.I) • C F) t).continuousAt)
private theorem orbit_continuous (F : Index) : Continuous (orbit F) :=
  ((time_continuous F).comp continuous_neg).mul continuous_const |>.mul (time_continuous F)
private theorem orbit_positive (F : Index) (t : ℝ) : 0 ≤ orbit F t := by
  have hs:star (SourceFiniteUnitary.time (C F) t)=SourceFiniteUnitary.time (C F) (-t) := by
    rw [ContinuousLinearMap.star_eq_adjoint,FullYSourceCutoffVolterra.time_adjoint,
      (GaussGradedCompression.compression_selfAdjoint F).adjoint_eq]
  rw [orbit,←hs]
  exact star_left_conjugate_nonneg clock_positive _
private theorem orbit_le_one (F : Index) (t : ℝ) : orbit F t ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (orbit_positive F t)).mp (orbit_norm F t)

private def dampedOrbit (μ : ℝ) (F : Index) (t : ℝ) : Op := (Real.exp (-4*μ*t):ℂ) • orbit F t
private theorem exp_integrable (μ : ℝ) (hμ : 0<μ) :
    IntegrableOn (fun t:ℝ=>Real.exp (-4*μ*t)) (Set.Ioi 0) :=
  integrableOn_exp_mul_Ioi (by linarith) 0
private theorem exp_integral (μ : ℝ) (hμ : 0<μ) :
    (∫ t:ℝ in Set.Ioi 0,Real.exp (-4*μ*t))=(4*μ)⁻¹ := by
  rw [integral_exp_mul_Ioi (by linarith : -4*μ<0) 0]
  simp only [mul_zero,Real.exp_zero]
  field_simp
private theorem damped_integrable (μ : ℝ) (hμ : 0<μ) (F : Index) :
    IntegrableOn (dampedOrbit μ F) (Set.Ioi 0) := by
  apply (exp_integrable μ hμ).mono' (((by fun_prop : Continuous (fun t:ℝ=>Real.exp (-4*μ*t))).smul
    (orbit_continuous F)).aestronglyMeasurable)
  exact Eventually.of_forall (fun t=>by
    change ‖dampedOrbit μ F t‖ ≤ Real.exp (-4*μ*t)
    rw [dampedOrbit,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (orbit_norm F t) (Real.exp_pos _).le).trans_eq (mul_one _))
/-- ν=2μ Abel observable from the same finite graded compression and its full unitary action. -/
def abelObservable (μ : ℝ) (F : Index) : Op := (4*μ:ℂ) • ∫ t:ℝ in Set.Ioi 0,dampedOrbit μ F t
private theorem positive_csmul (c:ℝ) (hc:0≤c) (A:Op) (hA:0≤A) : 0≤(c:ℂ) • A :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (((ContinuousLinearMap.nonneg_iff_isPositive _).mp hA).smul_of_nonneg (Complex.zero_le_real.mpr hc))
private theorem integral_positive {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f:ℝ→E →L[ℂ] E) (hf:∀t,0≤f t) : (0:E →L[ℂ] E)≤∫t:ℝ in Set.Ioi 0,f t :=
  integral_nonneg hf
private theorem abel_positive (μ : ℝ) (hμ : 0<μ) (F : Index) : 0 ≤ abelObservable μ F := by
  have hi:(0:Op)≤∫t:ℝ in Set.Ioi 0,dampedOrbit μ F t := by
    apply integral_positive (E:=H) (dampedOrbit μ F)
    intro t
    unfold dampedOrbit
    exact positive_csmul (Real.exp (-4*μ*t)) (Real.exp_pos _).le (orbit F t) (orbit_positive F t)
  have h:=positive_csmul (4*μ) (by positivity) (∫t:ℝ in Set.Ioi 0,dampedOrbit μ F t) hi
  simpa only [abelObservable,Complex.ofReal_mul,Complex.ofReal_ofNat] using h
private theorem abel_norm (μ : ℝ) (hμ : 0<μ) (F : Index) : ‖abelObservable μ F‖ ≤ 1 := by
  rw [abelObservable,norm_smul,show ‖(4*μ:ℂ)‖=4*μ by norm_cast;rw [Real.norm_eq_abs,abs_of_pos (by positivity)]]
  have hi:‖∫ t:ℝ in Set.Ioi 0,dampedOrbit μ F t‖ ≤ (4*μ)⁻¹ := by
    apply (norm_integral_le_integral_norm _).trans
    rw [←exp_integral μ hμ]
    apply integral_mono (damped_integrable μ hμ F).norm (exp_integrable μ hμ)
    intro t
    change ‖dampedOrbit μ F t‖ ≤ Real.exp (-4*μ*t)
    rw [dampedOrbit,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (orbit_norm F t) (Real.exp_pos _).le).trans_eq (mul_one _)
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))
private theorem abel_le_one (μ : ℝ) (hμ : 0<μ) (F : Index) : abelObservable μ F ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (abel_positive μ hμ F)).mp (abel_norm μ hμ F)

def abelCurrent (μ : ℝ) (F : Index) : Op := C F*abelObservable μ F-abelObservable μ F*C F

private theorem orbit_derivative (F : Index) (t : ℝ) :
    HasDerivAt (orbit F) (Complex.I • (C F*orbit F t-orbit F t*C F)) t := by
  have hp:=hasDerivAt_exp_smul_const ((-Complex.I) • C F) t
  have hm:HasDerivAt (fun s:ℝ=>SourceFiniteUnitary.time (C F) (-s))
      (Complex.I • (C F*SourceFiniteUnitary.time (C F) (-t))) t := by
    simpa only [SourceFiniteUnitary.time,neg_smul,smul_neg,neg_neg,smul_mul_assoc] using
      (hasDerivAt_exp_smul_const' (Complex.I • C F) t)
  have h:HasDerivAt (orbit F)
      ((Complex.I • (C F*SourceFiniteUnitary.time (C F) (-t)))*clockObservable*
        SourceFiniteUnitary.time (C F) t+
      (SourceFiniteUnitary.time (C F) (-t)*clockObservable)*
        (SourceFiniteUnitary.time (C F) t*((-Complex.I) • C F))) t :=
    (hm.mul_const clockObservable).mul hp
  apply h.congr_deriv
  simp only [smul_mul_assoc,mul_smul_comm,neg_smul,orbit,smul_sub,mul_assoc]
  simp only [mul_neg,mul_smul_comm,sub_eq_add_neg]
private def generator (μ : ℝ) (F : Index) : Op →L[ℂ] Op :=
  (-4*μ:ℂ) • (1:Op →L[ℂ] Op)+Complex.I •
    (ContinuousLinearMap.mul ℂ Op (C F)-(ContinuousLinearMap.mul ℂ Op).flip (C F))
private theorem generator_apply (μ : ℝ) (F : Index) (A : Op) :
    generator μ F A=(-4*μ:ℂ) • A+Complex.I • (C F*A-A*C F) := rfl
private theorem damped_derivative (μ : ℝ) (F : Index) (t : ℝ) :
    HasDerivAt (dampedOrbit μ F) (generator μ F (dampedOrbit μ F t)) t := by
  have hr:HasDerivAt (fun s:ℝ=>Real.exp (-4*μ*s)) ((-4*μ)*Real.exp (-4*μ*t)) t := by
    simpa only [id_eq,one_mul,mul_comm] using (((hasDerivAt_id t).const_mul (-4*μ)).exp)
  have he:HasDerivAt (fun s:ℝ=>(Real.exp (-4*μ*s):ℂ))
      (((-4*μ)*Real.exp (-4*μ*t):ℝ):ℂ) t := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hr
  have h:=he.smul (orbit_derivative F t)
  change HasDerivAt ((fun s:ℝ=>(Real.exp (-4*μ*s):ℂ)) • orbit F) _ t
  apply h.congr_deriv
  rw [generator_apply]
  simp only [dampedOrbit,smul_mul_assoc,mul_smul_comm,smul_sub,smul_smul,
    Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  module
private theorem damped_zero (μ : ℝ) (F : Index) : dampedOrbit μ F 0=clockObservable := by
  simp [dampedOrbit,orbit,SourceFiniteUnitary.time_zero]
private theorem damped_decay (μ : ℝ) (hμ : 0<μ) (F : Index) :
    Tendsto (dampedOrbit μ F) atTop (𝓝 0) := by
  have he:Tendsto (fun t:ℝ=>Real.exp (-4*μ*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -4*μ<0))
  apply squeeze_zero_norm _ he
  intro t
  rw [dampedOrbit,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (orbit_norm F t) (Real.exp_pos _).le).trans_eq (mul_one _)
private theorem abel_current_source (μ : ℝ) (hμ : 0<μ) (F : Index) :
    Complex.I • abelCurrent μ F=(4*μ:ℂ) • (abelObservable μ F-clockObservable) := by
  have hi:=damped_integrable μ hμ F
  have hd:=integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (_:t∈Set.Ici (0:ℝ))=>damped_derivative μ F t)
    ((generator μ F).integrable_comp hi) (damped_decay μ hμ F)
  rw [(generator μ F).integral_comp_comm hi,damped_zero,zero_sub,generator_apply] at hd
  have he:=congrArg (fun A:Op=>(4*μ:ℂ) • A) hd
  change (4*μ:ℂ) • ((-4*μ:ℂ) • _+Complex.I • _)=_ at he
  unfold abelCurrent abelObservable
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub,smul_smul] at he ⊢
  linear_combination (norm := module) he
private theorem current_norm (μ : ℝ) (hμ : 0<μ) (F : Index) : ‖abelCurrent μ F‖ ≤ 8*μ := by
  have h:=congrArg norm (abel_current_source μ hμ F)
  rw [norm_smul,Complex.norm_I,one_mul,norm_smul] at h
  have hc:‖(4*μ:ℂ)‖=4*μ := by norm_cast;rw [Real.norm_eq_abs,abs_of_pos (by positivity)]
  rw [hc] at h
  calc ‖abelCurrent μ F‖=4*μ*‖abelObservable μ F-clockObservable‖:=h
       _≤4*μ*(‖abelObservable μ F‖+‖clockObservable‖):=
         mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
       _≤4*μ*(1+1):=mul_le_mul_of_nonneg_left (add_le_add (abel_norm μ hμ F) clock_norm) (by positivity)
       _=8*μ:=by ring
/-- The actual volume instrument generates a positive Abel observable and a uniformly bounded
moving compression current at ν=2μ, including the original escape subspace. -/
theorem actual_bounded_clock_abel_source (μ : ℝ) (hμ : 0<μ) (F : Index) :
    (∀ f:QuantumTest,clockObservable (embed f)=embed (clockCore (clockCore f))) ∧
    0 ≤ abelObservable μ F ∧ abelObservable μ F ≤ 1 ∧
    Complex.I • abelCurrent μ F=(4*μ:ℂ) • (abelObservable μ F-clockObservable) ∧
    ‖abelCurrent μ F‖ ≤ 8*μ :=
  ⟨clock_core,abel_positive μ hμ F,abel_le_one μ hμ F,abel_current_source μ hμ F,current_norm μ hμ F⟩

open SourceClockRadiusResponseAffine GaussNativePotential SourceCornerForcing SourceRetardedBandCurrent
open SourceLocalizedInverseFormPayment
private theorem phi_inverse_core (f:QuantumTest) : phiInverseBounded (embed f)=embed (phiInverseAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem phi_inverse_norm : ‖phiInverseBounded‖≤1 := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem phi_inverse_pair (x y:H) : inner ℂ (phiInverseBounded x) y=inner ℂ x (phiInverseBounded y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  obtain ⟨g,rfl⟩:=coreEquiv.surjective b
  change inner ℂ (phiInverseBounded (embed f)) (embed g)=inner ℂ (embed f) (phiInverseBounded (embed g))
  rw [phi_inverse_core,phi_inverse_core]
  exact (multiply_pair _ _ _ _).symm
private theorem phi_inverse_positive : 0≤phiInverseBounded := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨phi_inverse_pair,?_⟩
  intro x
  change 0≤(inner ℂ (phiInverseBounded x) x).re
  rw [phi_inverse_pair]
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_le continuous_const (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  change 0≤(inner ℂ (embed f) (phiInverseBounded (embed f))).re
  rw [phi_inverse_core]
  change 0≤(sourcePair f (phiInverseAction f)).re
  rw [sourcePair_integral]
  have hr:(∫z,densityPair f (phiInverseAction f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫z,(densityPair f (phiInverseAction f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re (densityPair_integrable f (phiInverseAction f))).symm
  rw [hr]
  apply integral_nonneg
  intro z
  change 0≤(densityPair f (phiInverseAction f) z).re
  by_cases hz:z∈physicalChart
  · have hp:0≤(densityPair f f z).re := by
      change 0≤RCLike.re (inner ℂ (weight (fun N=>(density N z:ℂ)) (f z)) (f z))
      rw [GaussBoundedMultiplier.weighted_square _ (fun N=>(density_pos N ⟨z,hz⟩).le)]
      exact sq_nonneg _
    have he:densityPair f (phiInverseAction f) z=(phiReciprocal z:ℂ)*densityPair f f z :=
      inner_smul_right _ _ _
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hp
  · have hf:f z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]
private def phiComplement : Op := 1-phiInverseBounded
private theorem phi_complement_positive : 0≤phiComplement :=
  sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_inverse_positive).mp phi_inverse_norm)
private theorem phi_complement_le_one : phiComplement≤1 := sub_le_self _ phi_inverse_positive
/-- The same actual affine radial powers, on the full weighted Hilbert space. -/
def phiTail (m ell:ℕ) : Op := phiComplement^(m+1)-phiComplement^(ell+1)
private theorem phi_power_core (n:ℕ) (f:QuantumTest) :
    (phiComplement^n) (embed f)=embed (((1-phiInverseAction)^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change phiComplement ((phiComplement^n) (embed f))=embed ((1-phiInverseAction) (((1-phiInverseAction)^n) f))
    rw [ih]
    change embed (((1-phiInverseAction)^n) f)-phiInverseBounded (embed (((1-phiInverseAction)^n) f))=_
    rw [phi_inverse_core,←map_sub]
    rfl
private theorem phi_tail_core (m ell:ℕ) (f:QuantumTest) :
    phiTail m ell (embed f)=embed (phiThetaAction m ell f) := by
  simp only [phiTail,sub_apply,phi_power_core,phiThetaAction,LinearMap.sub_apply,map_sub]
private theorem phi_tail_pair (m ell:ℕ) (x y:H) :
    inner ℂ (phiTail m ell x) y=inner ℂ x (phiTail m ell y) := by
  have hp:=((ContinuousLinearMap.nonneg_iff_isPositive _).mp phi_complement_positive).isSymmetric
  simp only [phiTail,sub_apply,inner_sub_left,inner_sub_right]
  rw [power_pair phiComplement hp (m+1),power_pair phiComplement hp (ell+1)]

private abbrev TH := TimeSpace (MeasureTheory.volume:Measure ℝ)
private def readFamily (A:Op) (f:Family L2H sourceFilter) : Family L2H sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) f
private theorem family_value_sub {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f g:Family E sourceFilter) (F:Index) : value (f-g) F=value f F-value g F := rfl
private theorem read_value (A:Op) (f:Family L2H sourceFilter) (F:Index) :
    value (readFamily A f) F=A.compLpL 2 MeasureTheory.volume (value f F) := rfl
private theorem read_family_norm (A:Op) (f:Family L2H sourceFilter) :
    ‖readFamily A f‖=‖familyReader (MeasureTheory.volume:Measure ℝ) A (f:TH)‖ := by
  unfold familyReader
  rw [lift_coe,UniformSpace.Completion.norm_coe]
  rfl
private theorem lp_decreasing {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (Q:E →L[ℂ] E) (hQ₀:0≤Q) (hQ₁:Q≤1) (f:Lp E 2 (MeasureTheory.volume:Measure ℝ))
    {m n:ℕ} (hmn:m≤n) :
    ‖(Q^n).compLpL 2 MeasureTheory.volume f-(Q^m).compLpL 2 MeasureTheory.volume f‖^2 ≤
      ‖(Q^m).compLpL 2 MeasureTheory.volume f‖^2-‖(Q^n).compLpL 2 MeasureTheory.volume f‖^2 := by
  let a:Lp E 2 (MeasureTheory.volume:Measure ℝ):=(Q^n).compLpL 2 MeasureTheory.volume f
  let b:Lp E 2 (MeasureTheory.volume:Measure ℝ):=(Q^m).compLpL 2 MeasureTheory.volume f
  change ‖a-b‖^2≤‖b‖^2-‖a‖^2
  rw [square_integral MeasureTheory.volume (a-b),square_integral MeasureTheory.volume b,
    square_integral MeasureTheory.volume a,←integral_sub (square_integrable MeasureTheory.volume b)
      (square_integrable MeasureTheory.volume a)]
  apply integral_mono_ae (square_integrable MeasureTheory.volume (a-b))
    ((square_integrable MeasureTheory.volume b).sub (square_integrable MeasureTheory.volume a))
  filter_upwards [Lp.coeFn_sub a b,(Q^n).coeFn_compLpL f,(Q^m).coeFn_compLpL f] with t hs hn hm
  simp only [hs,Pi.sub_apply]
  change ‖a t-b t‖^2≤‖b t‖^2-‖a t‖^2
  rw [hn,hm]
  exact positive_power_distance Q hQ₀ hQ₁ (f t) hmn
private theorem lifted_decreasing {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A:ℕ→E →L[ℂ] E)
    (hA:∀x m n,m≤n→‖A n x-A m x‖^2≤‖A m x‖^2-‖A n x‖^2)
    (x:SourceFamilyHilbert.Hilbert E sourceFilter) {m n:ℕ} (hmn:m≤n) :
    ‖lift sourceFilter (SourceFamilyOperator.constant (A n)) x-lift sourceFilter (SourceFamilyOperator.constant (A m)) x‖^2 ≤
    ‖lift sourceFilter (SourceFamilyOperator.constant (A m)) x‖^2-
      ‖lift sourceFilter (SourceFamilyOperator.constant (A n)) x‖^2 := by
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [lift_coe,lift_coe,←UniformSpace.Completion.coe_sub]
  simp only [UniformSpace.Completion.norm_coe]
  apply le_of_tendsto_of_tendsto (square_tendsto sourceFilter _)
    ((square_tendsto sourceFilter _).sub (square_tendsto sourceFilter _))
  exact Eventually.of_forall (fun F=>hA (value f F) m n hmn)
private theorem lifted_power_distance (f:TH) {m n:ℕ} (hmn:m≤n) :
    ‖familyReader MeasureTheory.volume (phiComplement^n) f-familyReader MeasureTheory.volume (phiComplement^m) f‖^2 ≤
    ‖familyReader MeasureTheory.volume (phiComplement^m) f‖^2-
      ‖familyReader MeasureTheory.volume (phiComplement^n) f‖^2 :=
  lifted_decreasing (fun n=>(phiComplement^n).compLpL 2 (MeasureTheory.volume:Measure ℝ))
    (fun x _ _ h=>lp_decreasing phiComplement phi_complement_positive phi_complement_le_one x h) f hmn
private theorem lp_sub {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B:E →L[ℂ] E) : (A-B).compLpL 2 (MeasureTheory.volume:Measure ℝ)=
      A.compLpL 2 MeasureTheory.volume-B.compLpL 2 MeasureTheory.volume := by
  have h:A-B=A+(-1:ℂ) • B:=by rw [neg_one_smul,sub_eq_add_neg]
  rw [h,ContinuousLinearMap.add_compLpL,ContinuousLinearMap.smul_compLpL,neg_one_smul]
  exact (sub_eq_add_neg _ _).symm
private theorem read_family_sub (A B:Op) (f:Family L2H sourceFilter) :
    readFamily (A-B) f=readFamily A f-readFamily B f := by
  apply Family.ext
  funext F
  change (A-B).compLpL 2 MeasureTheory.volume (value f F)=
    A.compLpL 2 MeasureTheory.volume (value f F)-B.compLpL 2 MeasureTheory.volume (value f F)
  exact congrArg (fun T:L2H →L[ℂ] L2H=>T (value f F)) (lp_sub A B)
private theorem read_coe (A:Op) (f:Family L2H sourceFilter) :
    (readFamily A f:TH)=familyReader (MeasureTheory.volume:Measure ℝ) A (f:TH) :=
  (lift_coe sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) f).symm
attribute [local irreducible] phiComplement phiTail readFamily
private theorem family_tail (f:Family L2H sourceFilter) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),‖value (readFamily (phiTail m ell) f) F‖^2≤ε := by
  intro ε hε
  let u:ℕ→TH:=fun n=>(readFamily (phiComplement^n) f:TH)
  have hd:∀m n,m≤n→‖u n-u m‖^2≤‖u m‖^2-‖u n‖^2 := by
    intro m n hmn
    simpa only [u,read_coe] using lifted_power_distance (f:TH) hmn
  obtain ⟨N,hN⟩:=decreasing_distance_tail u hd
    (Real.sqrt (ε/2)) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨N,fun m hm ell hml=>?_⟩
  let r:=readFamily (phiTail m ell) f
  have hr:‖r‖^2<ε := by
    have h:=hN m hm ell hml
    have hrf:r=readFamily (phiComplement^(m+1)) f-readFamily (phiComplement^(ell+1)) f := by
      dsimp only [r]
      unfold phiTail
      exact read_family_sub _ _ f
    have he: (r:TH)=u (m+1)-u (ell+1) := by
      have h:=congrArg (fun x:Family L2H sourceFilter=>(x:TH)) hrf
      rw [UniformSpace.Completion.coe_sub] at h
      exact h
    rw [←he,UniformSpace.Completion.norm_coe] at h
    have hs:=Real.sq_sqrt (by positivity : 0≤ε/2)
    nlinarith only [h,hs,norm_nonneg r,Real.sqrt_nonneg (ε/2)]
  filter_upwards [(square_tendsto sourceFilter r).eventually (gt_mem_nhds hr)] with F hF
  exact hF.le

private theorem frequency_nonreal (advanced:Bool) (μ:ℝ) (hμ:0<μ) (w:ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem finite_star (F:Index) (z:ℂ) : finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (C F-star z • 1)=(Ring.inverse (C F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced:Bool) (μ:ℝ) (hμ:0<μ) (F:Index) :
    Continuous (fun w:ℝ=>finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact finite_frequency_continuous μ hμ F
  · have he:(fun w:ℝ=>finiteResolvent F (actualFrequency true μ w))=
        (fun w:ℝ=>(finiteResolvent F (line μ w)).adjoint) := funext (fun w=>finite_star F (line μ w))
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp (finite_frequency_continuous μ hμ F))
private theorem whole_memLp (advanced:Bool) (μ:ℝ) (hμ:0<μ) (F:Index) (g:H) :
    MemLp (fun w:ℝ=>finiteResolvent F (actualFrequency advanced μ w) g) 2 (MeasureTheory.volume:Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (((frequency_continuous advanced μ hμ F).clm_apply continuous_const).aestronglyMeasurable)).mpr
  have hi:Integrable (fun w:ℝ=>‖finiteResolvent F (line μ w) g‖^2) := by
    simpa only [line,mul_comm (μ:ℂ) Complex.I] using SourceActualResolventEnergy.actual_square_integrable F μ hμ g
  have he:∀w,‖finiteResolvent F (actualFrequency advanced μ w) g‖=‖finiteResolvent F (line μ w) g‖ := by
    intro w
    cases advanced
    · rfl
    · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
        (by simpa only [line_im] using hμ.ne') g
  simpa only [he] using hi
private theorem whole_read (advanced:Bool) (μ:ℝ) (hμ:0<μ) (F:Index) (g:H) :
    (fun w:ℝ=>value (wholeInputFamily advanced μ hμ g) F w)=ᵐ[MeasureTheory.volume]
      (fun w:ℝ=>finiteResolvent F (actualFrequency advanced μ w) g) :=
  (whole_memLp advanced μ hμ F g).coeFn_toLp
private def currentOperator (μ:ℝ) (hμ:0<μ) : Operator Index L2H where
  component F := (abelCurrent μ F).compLpL 2 MeasureTheory.volume
  bounded := by
    refine ⟨8*μ,by positivity,fun F x=>?_⟩
    exact ((abelCurrent μ F).compLpL 2 MeasureTheory.volume).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right ((ContinuousLinearMap.norm_compLpL_le _).trans (current_norm μ hμ F)) (norm_nonneg x))
private def currentFamily (μ:ℝ) (hμ:0<μ) (advanced:Bool) (g:H) : Family L2H sourceFilter :=
  act sourceFilter (currentOperator μ hμ) (wholeInputFamily advanced μ hμ g)
private def rowFamily (μ:ℝ) (hμ:0<μ) (advanced:Bool) (g:diagonal.domain) : Family L2H sourceFilter :=
  currentFamily μ hμ advanced (g:H)-readFamily phiInverseBounded
    (currentFamily μ hμ advanced (phiRadiusSource g:H))
def rawRow (μ:ℝ) (F:Index) (z:ℂ) (g:diagonal.domain) : H :=
  abelCurrent μ F (finiteResolvent F z (g:H))-
    phiInverseBounded (abelCurrent μ F (finiteResolvent F z (phiRadiusSource g:H)))
private theorem current_read (μ:ℝ) (hμ:0<μ) (advanced:Bool) (F:Index) (g:H) :
    (fun w:ℝ=>value (currentFamily μ hμ advanced g) F w)=ᵐ[MeasureTheory.volume]
      (fun w:ℝ=>abelCurrent μ F (finiteResolvent F (actualFrequency advanced μ w) g)) := by
  filter_upwards [(abelCurrent μ F).coeFn_compLpL (value (wholeInputFamily advanced μ hμ g) F),
    whole_read advanced μ hμ F g] with w hA hR
  change ((abelCurrent μ F).compLpL 2 MeasureTheory.volume (value (wholeInputFamily advanced μ hμ g) F)) w=_
  rw [hA,hR]
private theorem row_read (μ:ℝ) (hμ:0<μ) (advanced:Bool) (F:Index) (g:diagonal.domain) :
    (fun w:ℝ=>value (rowFamily μ hμ advanced g) F w)=ᵐ[MeasureTheory.volume]
      (fun w:ℝ=>rawRow μ F (actualFrequency advanced μ w) g) := by
  let a:=value (currentFamily μ hμ advanced (g:H)) F
  let b:=value (currentFamily μ hμ advanced (phiRadiusSource g:H)) F
  filter_upwards [Lp.coeFn_sub a (phiInverseBounded.compLpL 2 MeasureTheory.volume b),
    phiInverseBounded.coeFn_compLpL b,current_read μ hμ advanced F (g:H),
    current_read μ hμ advanced F (phiRadiusSource g:H)] with w hs hb ha hc
  rw [rowFamily,family_value_sub,read_value]
  change (a-phiInverseBounded.compLpL 2 MeasureTheory.volume b) w=_
  rw [hs,Pi.sub_apply,hb]
  change a w-phiInverseBounded (b w)=_
  rw [ha,hc]
  rfl
private theorem row_integral (m ell:ℕ) (μ:ℝ) (hμ:0<μ) (advanced:Bool) (F:Index) (g:diagonal.domain) :
    (∫⁻w:ℝ,ENNReal.ofReal (‖phiTail m ell (rawRow μ F (actualFrequency advanced μ w) g)‖^2))=
      ENNReal.ofReal (‖value (readFamily (phiTail m ell) (rowFamily μ hμ advanced g)) F‖^2) := by
  let r:=value (rowFamily μ hμ advanced g) F
  have he:(fun w:ℝ=>‖phiTail m ell (rawRow μ F (actualFrequency advanced μ w) g)‖^2)=ᵐ[MeasureTheory.volume]
      (fun w:ℝ=>‖value (readFamily (phiTail m ell) (rowFamily μ hμ advanced g)) F w‖^2) := by
    filter_upwards [(phiTail m ell).coeFn_compLpL r,row_read μ hμ advanced F g] with w ht hr
    rw [read_value]
    change _=‖((phiTail m ell).compLpL 2 MeasureTheory.volume r) w‖^2
    rw [ht,hr]
  have hi:=(square_integrable MeasureTheory.volume
    (value (readFamily (phiTail m ell) (rowFamily μ hμ advanced g)) F)).congr he.symm
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _=>sq_nonneg _)),
    integral_congr_ae he,←square_integral]
private theorem row_common_tail (μ:ℝ) (hμ:0<μ) (g:diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (‖phiTail m ell (rawRow μ F (actualFrequency advanced μ w) g)‖^2))≤ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=family_tail (rowFamily μ hμ false g) ε hε
  obtain ⟨N₁,h₁⟩:=family_tail (rowFamily μ hμ true g) ε hε
  refine ⟨max N₀ N₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hf ht
  intro advanced
  rw [row_integral m ell μ hμ advanced F g]
  cases advanced
  · exact ENNReal.ofReal_le_ofReal hf
  · exact ENNReal.ofReal_le_ofReal ht

/-- The real Abel block uses the actual two-seed endpoint column (θv,−Sθv). -/
def realBlock (m ell:ℕ) (μ:ℝ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : ℝ :=
  -2*(inner ℂ (abelCurrent μ F (finiteResolvent F z (g:H)))
    (phiTail m ell (embed (phiResponseCore m ell F z hz g)))).re+
  2*(inner ℂ (abelCurrent μ F (finiteResolvent F z (phiRadiusSource g:H)))
    (phiInverseBounded (phiTail m ell (embed (phiResponseCore m ell F z hz g))))).re
private theorem block_return (m ell:ℕ) (μ:ℝ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    realBlock m ell μ F z hz g= -2*(inner ℂ (phiTail m ell (rawRow μ F z g))
      (embed (phiResponseCore m ell F z hz g))).re := by
  unfold realBlock rawRow
  rw [←phi_inverse_pair,←phi_tail_pair,←phi_tail_pair]
  simp only [map_sub,inner_sub_left,Complex.sub_re]
  ring
private theorem block_price (m ell:ℕ) (μ:ℝ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain)
    (η:ℝ) (hη:0<η) :
    |realBlock m ell μ F z hz g|-η*‖embed (phiResponseCore m ell F z hz g)‖^2 ≤
      ‖phiTail m ell (rawRow μ F z g)‖^2/η := by
  rw [block_return,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have hi:|(inner ℂ (phiTail m ell (rawRow μ F z g)) (embed (phiResponseCore m ell F z hz g))).re| ≤
      ‖phiTail m ell (rawRow μ F z g)‖*‖embed (phiResponseCore m ell F z hz g)‖ :=
    Complex.abs_re_le_norm _ |>.trans (norm_inner_le_norm _ _)
  apply (le_div_iff₀ hη).mpr
  nlinarith [sq_nonneg (η*‖embed (phiResponseCore m ell F z hz g)‖-‖phiTail m ell (rawRow μ F z g)‖)]
/-- The real moving Abel subblock has a common φ cutoff tail after an arbitrarily small
response-norm payment. Its actual bounded current and both source families are generated above. -/
theorem actual_real_abel_block_common_tail (μ:ℝ) (hμ:0<μ) (g:diagonal.domain) (η:ℝ) (hη:0<η) :
    (∀m ell (f:QuantumTest),phiTail m ell (embed f)=embed (phiThetaAction m ell f)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (|realBlock m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|-
        η*‖embed (phiResponseCore m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)‖^2))≤ENNReal.ofReal ε := by
  refine ⟨phi_tail_core,?_⟩
  intro ε hε
  obtain ⟨N,hN⟩:=row_common_tail μ hμ g (ε*η) (mul_pos hε hη)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  calc _≤∫⁻w:ℝ,ENNReal.ofReal (‖phiTail m ell (rawRow μ F (actualFrequency advanced μ w) g)‖^2/η) := by
         apply lintegral_mono
         intro w
         exact ENNReal.ofReal_le_ofReal (block_price m ell μ F (actualFrequency advanced μ w)
           (frequency_nonreal advanced μ hμ w) g η hη)
       _=ENNReal.ofReal (η⁻¹)*(∫⁻w:ℝ,ENNReal.ofReal (‖phiTail m ell
          (rawRow μ F (actualFrequency advanced μ w) g)‖^2)) := by
         simp_rw [div_eq_mul_inv,mul_comm _ η⁻¹,ENNReal.ofReal_mul (inv_nonneg.mpr hη.le)]
         rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
       _≤ENNReal.ofReal (η⁻¹)*ENNReal.ofReal (ε*η):=mul_le_mul le_rfl (hF advanced) zero_le zero_le
       _=ENNReal.ofReal ε := by
         rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hη.le)]
         congr 1
         field_simp

end LowEnergy.SourceBoundedClockAbel
