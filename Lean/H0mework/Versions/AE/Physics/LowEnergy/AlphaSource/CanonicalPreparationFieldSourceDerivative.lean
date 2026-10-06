import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldUniformVariation
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCausalFieldResponse

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldPerturbation
open SourceFiniteUnitary CanonicalGradedVariation SourceFamilyOperator SourceFamilyHilbert
open Filter Set
open scoped Topology

section Filtered
variable {I E G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (G →L[ℂ] G) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance (u : Ultrafilter I) : NormedAlgebra ℝ (Hilbert G u →L[ℂ] Hilbert G u) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

 def exponentialBound (A B : E →L[ℂ] E) (r t : ℝ) : ℝ :=
  Real.exp ((‖A‖+|r| *‖B‖)*|t|)

 theorem time_family_bound (C A B : E →L[ℂ] E) (hC : IsSelfAdjoint C) (r t : ℝ) :
    ‖time (C+A+r • B) t‖ ≤ exponentialBound A B r t := by
  have h:=perturbed_time_bound C (A+r • B) hC t
  rw [←add_assoc] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le A (r • B)) (abs_nonneg t)

 theorem base_time_bound (C A : E →L[ℂ] E) (hC : IsSelfAdjoint C) (s t : ℝ) (within : |s| ≤ |t|) :
    ‖time (C+A) s‖ ≤ Real.exp (‖A‖*|t|) :=
  (perturbed_time_bound C A hC s).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left within (norm_nonneg A)))

 def derivativeBound (A B : E →L[ℂ] E) (t : ℝ) : ℝ :=
  |t| *(Real.exp (‖A‖*|t|))^2*‖B‖

omit [CompleteSpace E] in
 theorem derivativeBound_nonneg (A B : E →L[ℂ] E) (t : ℝ) : 0 ≤ derivativeBound A B t := by
  unfold derivativeBound
  positivity

 theorem derivative_family_bound (C A B : E →L[ℂ] E) (hC : IsSelfAdjoint C) (t : ℝ) :
    ‖variation (C+A) B t‖ ≤ derivativeBound A B t := by
  have base := fun s hs=>base_time_bound C A hC s t hs
  have h:=variationBetween_window (C+A) B 0 |t| (Real.exp (‖A‖*|t|)) (Real.exp (‖A‖*|t|)) t
    (Real.exp_pos _).le (Real.exp_pos _).le le_rfl base (by simpa only [zero_smul,add_zero] using base)
  exact h.trans_eq (by unfold derivativeBound;ring)

 def errorBound (A B : E →L[ℂ] E) (t : ℝ) : ℝ :=
  |t|^2*Real.exp ((‖A‖+‖B‖)*|t|)*‖B‖^2*(Real.exp (‖A‖*|t|))^2

omit [CompleteSpace E] in
 theorem errorBound_nonneg (A B : E →L[ℂ] E) (t : ℝ) : 0 ≤ errorBound A B t := by
  unfold errorBound
  positivity

 theorem uniform_error_bound (C A B : E →L[ℂ] E) (hC : IsSelfAdjoint C) (r t : ℝ) (small : |r| ≤ 1) :
    ‖time (C+A+r • B) t-time (C+A) t-r • variation (C+A) B t‖ ≤ errorBound A B t*‖r‖^2 :=
  parameter_remainder_window (C+A) B r |t| (Real.exp (‖A‖*|t|)) (Real.exp ((‖A‖+‖B‖)*|t|)) t
    (Real.exp_pos _).le (Real.exp_pos _).le le_rfl
    (fun s hs=>base_time_bound C A hC s t hs)
    (fun s hs=>perturbed_time_window C A B hC r |t| s (abs_nonneg t) small hs)

 def imageTimeFamily (C : I→E →L[ℂ] E) (hC : ∀ i,IsSelfAdjoint (C i))
    (A B : E →L[ℂ] E) (L : (E →L[ℂ] E) →L[ℝ] (G →L[ℂ] G)) (r t : ℝ) : Operator I G where
  component i:=L (time (C i+A+r • B) t)
  bounded:=⟨‖L‖*exponentialBound A B r t,mul_nonneg (norm_nonneg L) (Real.exp_pos _).le,fun i x=>
    ((L (time (C i+A+r • B) t)).le_opNorm x).trans (mul_le_mul_of_nonneg_right
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (time_family_bound (C i) A B (hC i) r t) (norm_nonneg L))) (norm_nonneg x))⟩

 def imageDerivativeFamily (C : I→E →L[ℂ] E) (hC : ∀ i,IsSelfAdjoint (C i))
    (A B : E →L[ℂ] E) (L : (E →L[ℂ] E) →L[ℝ] (G →L[ℂ] G)) (t : ℝ) : Operator I G where
  component i:=L (variation (C i+A) B t)
  bounded:=⟨‖L‖*derivativeBound A B t,mul_nonneg (norm_nonneg L) (derivativeBound_nonneg A B t),fun i x=>
    ((L (variation (C i+A) B t)).le_opNorm x).trans (mul_le_mul_of_nonneg_right
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (derivative_family_bound (C i) A B (hC i) t) (norm_nonneg L))) (norm_nonneg x))⟩

 def imageErrorFamily (C : I→E →L[ℂ] E) (hC : ∀ i,IsSelfAdjoint (C i))
    (A B : E →L[ℂ] E) (L : (E →L[ℂ] E) →L[ℝ] (G →L[ℂ] G)) (r t : ℝ) : Operator I G where
  component i:=L (time (C i+A+r • B) t-time (C i+A) t-r • variation (C i+A) B t)
  bounded:=⟨‖L‖*(exponentialBound A B r t+Real.exp (‖A‖*|t|)+|r| *derivativeBound A B t),by
    have := derivativeBound_nonneg A B t
    unfold exponentialBound
    positivity,fun i x=>by
    have bound : ‖time (C i+A+r • B) t-time (C i+A) t-r • variation (C i+A) B t‖ ≤
        exponentialBound A B r t+Real.exp (‖A‖*|t|)+|r| *derivativeBound A B t := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add ((norm_sub_le _ _).trans (add_le_add (time_family_bound (C i) A B (hC i) r t)
        (perturbed_time_bound (C i) A (hC i) t)))
          (mul_le_mul_of_nonneg_left (derivative_family_bound (C i) A B (hC i) t) (abs_nonneg r))
    exact ((L _).le_opNorm x).trans (mul_le_mul_of_nonneg_right
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left bound (norm_nonneg L))) (norm_nonneg x))⟩

omit [CompleteSpace G] in
 theorem image_lift_error (u : Ultrafilter I) (C : I→E →L[ℂ] E) (hC : ∀ i,IsSelfAdjoint (C i))
    (A B : E →L[ℂ] E) (L : (E →L[ℂ] E) →L[ℝ] (G →L[ℂ] G)) (r t : ℝ) :
    lift u (imageErrorFamily C hC A B L r t)=
      lift u (imageTimeFamily C hC A B L r t)-lift u (imageTimeFamily C hC A B L 0 t)-
        r • lift u (imageDerivativeFamily C hC A B L t) := by
  apply SourceFamilyOperator.ext u
  intro f
  rw [sub_apply,sub_apply,smul_apply,lift_coe,lift_coe,lift_coe,lift_coe,
    ←UniformSpace.Completion.coe_sub,←UniformSpace.Completion.coe_smul,←UniformSpace.Completion.coe_sub]
  congr 1
  apply Family.ext
  funext i
  change (L (time (C i+A+r • B) t-time (C i+A) t-r • variation (C i+A) B t)) (value f i)=
    L (time (C i+A+r • B) t) (value f i)-L (time (C i+A+(0:ℝ) • B) t) (value f i)-
      r • L (variation (C i+A) B t) (value f i)
  simp only [map_sub,map_smul,zero_smul,add_zero,sub_apply,smul_apply]

omit [CompleteSpace G] in
 theorem image_lift_remainder (u : Ultrafilter I) (C : I→E →L[ℂ] E) (hC : ∀ i,IsSelfAdjoint (C i))
    (A B : E →L[ℂ] E) (L : (E →L[ℂ] E) →L[ℝ] (G →L[ℂ] G)) (r t : ℝ) (small : |r| ≤ 1) :
    ‖lift u (imageTimeFamily C hC A B L r t)-lift u (imageTimeFamily C hC A B L 0 t)-
      r • lift u (imageDerivativeFamily C hC A B L t)‖ ≤ (‖L‖*errorBound A B t)*‖r‖^2 := by
  rw [←image_lift_error]
  apply lift_bound u _ _ (mul_nonneg (mul_nonneg (norm_nonneg L) (errorBound_nonneg A B t)) (sq_nonneg ‖r‖))
  intro i
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
    (uniform_error_bound (C i) A B (hC i) r t small) (norm_nonneg L)).trans_eq (by ring))

omit [CompleteSpace G] in
 theorem image_lift_derivative (u : Ultrafilter I) (C : I→E →L[ℂ] E) (hC : ∀ i,IsSelfAdjoint (C i))
    (A B : E →L[ℂ] E) (L : (E →L[ℂ] E) →L[ℝ] (G →L[ℂ] G)) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>lift u (imageTimeFamily C hC A B L r t))
      (lift u (imageDerivativeFamily C hC A B L t)) 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero]
  let K:=‖L‖*errorBound A B t
  have convergence : Tendsto (fun r : ℝ=>K*‖r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using ((continuous_norm:Continuous (fun r:ℝ=>‖r‖)).tendsto 0).const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun r=>mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg _))) ?_ convergence
  have small : ∀ᶠ r : ℝ in 𝓝 0,|r| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with r hr
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr : |r|<1).le
  filter_upwards [small] with r hr
  have bound:=mul_le_mul_of_nonneg_left (image_lift_remainder u C hC A B L r t hr) (inv_nonneg.mpr (norm_nonneg r))
  have scalar : ‖r‖⁻¹*(K*‖r‖^2)=K*‖r‖ := by
    by_cases zero : ‖r‖=0
    · simp only [zero,inv_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · field_simp
  exact bound.trans_eq scalar

end Filtered

open GaussCoreHilbert GaussComposite GaussComposite.SourceGraph
open CanonicalPhysicalSpatial CanonicalGradedSpatialSource CanonicalPhysicalLaplace FullYSourceCutoffVolterra
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumCausalFieldResponse (forceGauss)
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion)
open scoped InnerProductSpace
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

 def actualTimeFamily (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (r t : ℝ) : Operator Index H :=
  imageTimeFamily (compression p) (compression_selfAdjoint p) (cutoff cut) (forceGauss f p phi)
    (ContinuousLinearMap.id ℝ Op) r t

 def actualVariationFamily (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (t : ℝ) : Operator Index H :=
  imageDerivativeFamily (compression p) (compression_selfAdjoint p) (cutoff cut) (forceGauss f p phi)
    (ContinuousLinearMap.id ℝ Op) t

 def actualEvolution (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (r t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (actualTimeFamily p cut f phi r t)

 def actualVariation (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (actualVariationFamily p cut f phi t)

 theorem actual_field_parameter_derivative (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>actualEvolution p cut f phi r t) (actualVariation p cut f phi t) 0 :=
  image_lift_derivative sourceFilter (compression p) (compression_selfAdjoint p) (cutoff cut)
    (forceGauss f p phi) (ContinuousLinearMap.id ℝ Op) t

 theorem actual_uniform_remainder (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (r t : ℝ) (small : |r| ≤ 1) :
    ‖actualEvolution p cut f phi r t-actualEvolution p cut f phi 0 t-r • actualVariation p cut f phi t‖ ≤
      remainderBound cut (forceGauss f p phi) |t| *‖r‖^2 := by
  change ‖lift sourceFilter (imageTimeFamily (compression p) (compression_selfAdjoint p) (cutoff cut)
      (forceGauss f p phi) (ContinuousLinearMap.id ℝ Op) r t)-
    lift sourceFilter (imageTimeFamily (compression p) (compression_selfAdjoint p) (cutoff cut)
      (forceGauss f p phi) (ContinuousLinearMap.id ℝ Op) 0 t)-
    r • lift sourceFilter (imageDerivativeFamily (compression p) (compression_selfAdjoint p) (cutoff cut)
      (forceGauss f p phi) (ContinuousLinearMap.id ℝ Op) t)‖ ≤ _
  rw [←image_lift_error sourceFilter (compression p) (compression_selfAdjoint p) (cutoff cut)
    (forceGauss f p phi) (ContinuousLinearMap.id ℝ Op) r t]
  apply lift_bound sourceFilter _ _ (mul_nonneg (remainderBound_nonneg cut (forceGauss f p phi) |t|) (sq_nonneg ‖r‖))
  intro F
  exact original_parameter_remainder p F cut (forceGauss f p phi) r |t| t (abs_nonneg t) small le_rfl

 theorem actual_variation_polynomial_bound (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (t : ℝ) :
    ‖actualVariation p cut f phi t‖ ≤ |t| *(timeBound cut |t|)^2*‖forceGauss f p phi‖ := by
  apply lift_bound sourceFilter _ _ (by positivity)
  intro F
  have base := fun s hs=>original_time_window p F cut |t| s (abs_nonneg t) hs
  have bound := variationBetween_window (compression p F+cutoff cut) (forceGauss f p phi) 0 |t|
    (timeBound cut |t|) (timeBound cut |t|) t (timeBound_nonneg _ _) (timeBound_nonneg _ _) le_rfl
    base (by simpa only [zero_smul,add_zero] using base)
  exact bound.trans_eq (by ring)

 def preparationRead (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    (HistorySpace →L[ℂ] HistorySpace) →L[ℝ] ℂ :=
  ((innerSL ℂ (inclusion (completedLeg left lc ls u))).comp
    (ContinuousLinearMap.apply ℂ HistorySpace (inclusion (completedLeg right rc rs v)))).restrictScalars ℝ

 theorem prepared_parameter_derivative (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (t : ℝ)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    HasDerivAt (fun r : ℝ=>SourceGraph.response (actualEvolution p cut f phi r t) left right lc ls rc rs u v)
      (SourceGraph.response (actualVariation p cut f phi t) left right lc ls rc rs u v) 0 := by
  exact (preparationRead left right lc ls rc rs u v).hasFDerivAt.comp_hasDerivAt 0
    (actual_field_parameter_derivative p cut f phi t)

 theorem prepared_remainder_bound (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (r t : ℝ)
    (small : |r| ≤ 1) (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    ‖SourceGraph.response (actualEvolution p cut f phi r t) left right lc ls rc rs u v-
      SourceGraph.response (actualEvolution p cut f phi 0 t) left right lc ls rc rs u v-
      r • SourceGraph.response (actualVariation p cut f phi t) left right lc ls rc rs u v‖ ≤
      legBound^2*(remainderBound cut (forceGauss f p phi) |t| *‖r‖^2)*‖u‖*‖v‖ := by
  have same : SourceGraph.response (actualEvolution p cut f phi r t) left right lc ls rc rs u v-
      SourceGraph.response (actualEvolution p cut f phi 0 t) left right lc ls rc rs u v-
      r • SourceGraph.response (actualVariation p cut f phi t) left right lc ls rc rs u v=
    SourceGraph.response (actualEvolution p cut f phi r t-actualEvolution p cut f phi 0 t-r • actualVariation p cut f phi t)
      left right lc ls rc rs u v := by
    simp only [SourceGraph.response,sub_apply,smul_apply,inner_sub_right,inner_smul_right_eq_smul]
  rw [same]
  apply (SourceGraph.response_bound _ left right lc ls rc rs u v).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (actual_uniform_remainder p cut f phi r t small) (sq_nonneg _)) (norm_nonneg u)) (norm_nonneg v)

 open CanonicalPreparationCore.Completed CanonicalPreparationCreation PreparationVacuumNativeClosure
 open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation

 theorem original_prepared_derivative (x : zeroLocalizedSpace actualNativeLocalizer)
    (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (t : ℝ)
    (left right : Bool) (lc ls rc rs : Fin 2) :
    (∃ h : prepared (zeroLocalizedProfile actualNativeLocalizer x)∈GaussRadialDomain.closedY.domain,
      ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared (zeroLocalizedProfile actualNativeLocalizer x),h⟩-
        cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer x))‖ ≤
          (915/916:ℝ)^(n+1)*916*GaussYukawaCoefficient.bound*‖x‖) ∧
    HasDerivAt (fun r : ℝ=>SourceGraph.response (actualEvolution p cut f phi r t) left right lc ls rc rs
      (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x))
      (SourceGraph.response (actualVariation p cut f phi t) left right lc ls rc rs
        (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x)) 0 := by
  obtain ⟨h,_,bound⟩:=PreparationVacuumLocalizedYukawa.original_prepared_Y_domain x
  exact ⟨⟨h,bound⟩,prepared_parameter_derivative p cut f phi t left right lc ls rc rs _ _⟩

end LowEnergy.PreparationVacuumFieldPerturbation
