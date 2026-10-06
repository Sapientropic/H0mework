import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationNonlinearObservableComparison

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNonlinearLaplace
open SourceFiniteUnitary CanonicalGradedVariation PreparationVacuumFieldPerturbation
open PreparationVacuumDampedFieldPerturbation PreparationVacuumNonlinearFieldCurve
open PreparationVacuumCausalFieldResponse PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open GaussCoreHilbert CanonicalPhysicalSpatial FullYSourceCutoffVolterra GaussUnitaryHistory
open CanonicalGradedSpatialSource SourceFamilyOperator SourceFamilyHilbert MeasureTheory Set Filter
open scoped Topology Interval
abbrev Op := PreparationVacuumFieldPerturbation.Op
local instance : NormedAlgebra ℚ Op := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : SecondCountableTopologyEither ℝ Op := ⟨Or.inl inferInstance⟩
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

def nonlinearIntegrand (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r t : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping t • actualObservable cut F f g phi psi p r t

def comparisonIntegrand (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r t : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping t •
    (actualObservable cut F f g phi psi p r t-sourceFirstJet cut F f g phi psi p r t)

theorem comparisonIntegrand_continuous (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) :
    Continuous (comparisonIntegrand cut F f g phi psi p frequency damping r) := by
  have affine : Continuous (sourceFirstJet cut F f g phi psi p r) :=
    (((time_continuous _).comp continuous_neg).mul continuous_const).mul (time_continuous _)
  exact (CanonicalGradedFrequency.weight_continuous frequency damping).smul
    ((actualObservable_continuous cut F f g phi psi p r).sub affine)

theorem comparisonIntegrand_integrable (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) :
    IntegrableOn (comparisonIntegrand cut F f g phi psi p frequency damping r) (Ioi 0) := by
  apply ((laplaceMajorant_integrable damping positive).const_mul
    (‖r‖^2*comparisonScale cut f g phi psi p damping)).mono'
    (comparisonIntegrand_continuous cut F f g phi psi p frequency damping r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (actual_affine_damped_comparison cut F f g phi psi p frequency damping r t positive small ht.le).trans_eq (by ring)

theorem nonlinearIntegrand_split (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r t : ℝ) :
    nonlinearIntegrand cut F f g phi psi p frequency damping r t=
      jetLaplaceIntegrand p F cut f g phi psi frequency damping r t+
        comparisonIntegrand cut F f g phi psi p frequency damping r t := by
  unfold nonlinearIntegrand jetLaplaceIntegrand comparisonIntegrand
  rw [smul_sub]
  abel


def nonlinearTimeScale (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ) : ℝ :=
  sourceJetTimeScale cut f g phi psi p damping+comparisonScale cut f g phi psi p damping

theorem nonlinearTimeScale_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ)
    (positive : 0<damping) : 0≤nonlinearTimeScale cut f g phi psi p damping :=
  add_nonneg (sourceJetTimeScale_nonneg cut f g phi psi p damping positive)
    (comparisonScale_nonneg cut f g phi psi p damping)

theorem nonlinearIntegrand_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r t : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) (future : 0≤t) :
    ‖nonlinearIntegrand cut F f g phi psi p frequency damping r t‖≤
      nonlinearTimeScale cut f g phi psi p damping*laplaceMajorant damping t := by
  rw [nonlinearIntegrand_split]
  have h1:=jetLaplace_bound p F cut f g phi psi frequency damping r t positive
    (nonlinearRadius_affine g psi p cut damping r positive small) future
  have h2:=actual_affine_damped_comparison cut F f g phi psi p frequency damping r t positive small future
  have quadratic : ‖r‖^2≤1 := by
    rw [Real.norm_eq_abs]
    nlinarith [nonlinearRadius_unit g psi p cut damping r small,abs_nonneg r]
  have scale : 0≤comparisonScale cut f g phi psi p damping*laplaceMajorant damping t :=
    mul_nonneg (comparisonScale_nonneg cut f g phi psi p damping) (laplaceMajorant_nonneg damping t)
  exact (norm_add_le _ _).trans ((add_le_add h1
    (h2.trans ((mul_le_mul_of_nonneg_right quadratic scale).trans_eq (one_mul _)))).trans_eq
      (by unfold nonlinearTimeScale;ring))

theorem nonlinearIntegrand_integrable (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) :
    IntegrableOn (nonlinearIntegrand cut F f g phi psi p frequency damping r) (Ioi 0) := by
  have continuous : Continuous (nonlinearIntegrand cut F f g phi psi p frequency damping r) :=
    (CanonicalGradedFrequency.weight_continuous frequency damping).smul
      (actualObservable_continuous cut F f g phi psi p r)
  apply ((laplaceMajorant_integrable damping positive).const_mul
    (nonlinearTimeScale cut f g phi psi p damping)).mono' continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact nonlinearIntegrand_bound cut F f g phi psi p frequency damping r t positive small ht.le

def finiteNonlinearLaplace (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) : Op :=
  ∫ t in Ioi 0,nonlinearIntegrand cut F f g phi psi p frequency damping r t

theorem finiteNonlinearLaplace_split (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) :
    finiteNonlinearLaplace cut F f g phi psi p frequency damping r=
      finiteJetLaplace p F cut f g phi psi frequency damping r+
        ∫ t in Ioi 0,comparisonIntegrand cut F f g phi psi p frequency damping r t := by
  unfold finiteNonlinearLaplace finiteJetLaplace
  simp_rw [nonlinearIntegrand_split]
  exact integral_add
    (jetLaplace_integrable p F cut f g phi psi frequency damping r positive
      (nonlinearRadius_affine g psi p cut damping r positive small))
    (comparisonIntegrand_integrable cut F f g phi psi p frequency damping r positive small)

theorem finiteNonlinearLaplace_zero (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping : ℝ) :
    finiteNonlinearLaplace cut F f g phi psi p frequency damping 0=
      finiteJetLaplace p F cut f g phi psi frequency damping 0 := by
  unfold finiteNonlinearLaplace finiteJetLaplace nonlinearIntegrand jetLaplaceIntegrand
  simp only [actualObservable_zero]

theorem finiteNonlinearLaplace_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) :
    ‖finiteNonlinearLaplace cut F f g phi psi p frequency damping r‖≤
      nonlinearTimeScale cut f g phi psi p damping*laplaceMass damping := by
  have h:=norm_integral_le_of_norm_le
    ((laplaceMajorant_integrable damping positive).const_mul (nonlinearTimeScale cut f g phi psi p damping))
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),
      ‖nonlinearIntegrand cut F f g phi psi p frequency damping r t‖≤
        nonlinearTimeScale cut f g phi psi p damping*laplaceMajorant damping t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact nonlinearIntegrand_bound cut F f g phi psi p frequency damping r t positive small ht.le)
  rw [integral_const_mul] at h
  exact h

theorem finiteNonlinearLaplace_comparison (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) :
    ‖finiteNonlinearLaplace cut F f g phi psi p frequency damping r-
      finiteJetLaplace p F cut f g phi psi frequency damping r‖≤
      (comparisonScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2 := by
  rw [finiteNonlinearLaplace_split cut F f g phi psi p frequency damping r positive small,add_sub_cancel_left]
  have h:=norm_integral_le_of_norm_le
    ((laplaceMajorant_integrable damping positive).const_mul (‖r‖^2*comparisonScale cut f g phi psi p damping))
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),
      ‖comparisonIntegrand cut F f g phi psi p frequency damping r t‖≤
        (‖r‖^2*comparisonScale cut f g phi psi p damping)*laplaceMajorant damping t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (actual_affine_damped_comparison cut F f g phi psi p frequency damping r t positive small ht.le).trans_eq (by ring))
  rw [integral_const_mul] at h
  exact h.trans_eq (by unfold laplaceMass;ring)

def nonlinearRemainderScale (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ) : ℝ :=
  sourceJetRemainderScale cut f g phi psi p damping+comparisonScale cut f g phi psi p damping

theorem nonlinearRemainderScale_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ)
    (positive : 0<damping) : 0≤nonlinearRemainderScale cut f g phi psi p damping :=
  add_nonneg (sourceJetRemainderScale_nonneg cut f g phi psi p damping positive)
    (comparisonScale_nonneg cut f g phi psi p damping)

theorem finiteNonlinearLaplace_remainder (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) :
    ‖finiteNonlinearLaplace cut F f g phi psi p frequency damping r-
      finiteNonlinearLaplace cut F f g phi psi p frequency damping 0-
      r • finiteJetDerivative p F cut f g phi psi frequency damping‖≤
      (nonlinearRemainderScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2 := by
  rw [finiteNonlinearLaplace_zero]
  have identity : finiteNonlinearLaplace cut F f g phi psi p frequency damping r-
      finiteJetLaplace p F cut f g phi psi frequency damping 0-
      r • finiteJetDerivative p F cut f g phi psi frequency damping=
    (finiteNonlinearLaplace cut F f g phi psi p frequency damping r-
      finiteJetLaplace p F cut f g phi psi frequency damping r)+
    (finiteJetLaplace p F cut f g phi psi frequency damping r-
      finiteJetLaplace p F cut f g phi psi frequency damping 0-
      r • finiteJetDerivative p F cut f g phi psi frequency damping) := by abel
  rw [identity]
  exact (norm_add_le _ _).trans ((add_le_add
    (finiteNonlinearLaplace_comparison cut F f g phi psi p frequency damping r positive small)
    (finiteJetLaplace_remainder p F cut f g phi psi frequency damping r positive
      (nonlinearRadius_affine g psi p cut damping r positive small))).trans_eq
      (by unfold nonlinearRemainderScale;ring))

def nonlinearLaplaceFamily (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (frequency damping : ℝ) (positive : 0<damping) (r : ℝ) : Operator Index H where
  component F:=if |r|≤nonlinearRadius g psi p cut damping then finiteNonlinearLaplace cut F f g phi psi p frequency damping r else 0
  bounded:=⟨nonlinearTimeScale cut f g phi psi p damping*laplaceMass damping,
    mul_nonneg (nonlinearTimeScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping),fun F v=>by
      split_ifs with small
      · exact ((finiteNonlinearLaplace cut F f g phi psi p frequency damping r).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (finiteNonlinearLaplace_bound cut F f g phi psi p frequency damping r positive small) (norm_nonneg v))
      · simp only [zero_apply,norm_zero]
        exact mul_nonneg (mul_nonneg (nonlinearTimeScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping)) (norm_nonneg v)⟩

def sourceNonlinearLaplace (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (frequency damping : ℝ) (positive : 0<damping) (r : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (nonlinearLaplaceFamily cut f g phi psi p frequency damping positive r)

theorem nonlinearLaplaceFamily_actual (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (frequency damping r : ℝ) (positive : 0<damping) (small : |r|≤nonlinearRadius g psi p cut damping) :
    (nonlinearLaplaceFamily cut f g phi psi p frequency damping positive r).component F=
      ∫ t in Ioi 0,CanonicalGradedFrequency.weight frequency damping t •
        (time (compression p F+cutoff cut+matterIncrement g psi p r) (-t)*
          actualReaderCurve f g phi psi p r*time (compression p F+cutoff cut+matterIncrement g psi p r) t) :=
  if_pos small

def nonlinearLaplaceErrorFamily (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (frequency damping r : ℝ) (positive : 0<damping) (small : |r|≤nonlinearRadius g psi p cut damping) : Operator Index H where
  component F:=finiteNonlinearLaplace cut F f g phi psi p frequency damping r-
    finiteNonlinearLaplace cut F f g phi psi p frequency damping 0-
    r • finiteJetDerivative p F cut f g phi psi frequency damping
  bounded:=⟨(nonlinearRemainderScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2,
    mul_nonneg (mul_nonneg (nonlinearRemainderScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping)) (sq_nonneg _),
    fun F v=>((finiteNonlinearLaplace cut F f g phi psi p frequency damping r-
      finiteNonlinearLaplace cut F f g phi psi p frequency damping 0-
      r • finiteJetDerivative p F cut f g phi psi frequency damping).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (finiteNonlinearLaplace_remainder cut F f g phi psi p frequency damping r positive small) (norm_nonneg v))⟩

theorem nonlinear_lift_error (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (frequency damping r : ℝ) (positive : 0<damping) (small : |r|≤nonlinearRadius g psi p cut damping) :
    lift sourceFilter (nonlinearLaplaceErrorFamily cut f g phi psi p frequency damping r positive small)=
      sourceNonlinearLaplace cut f g phi psi p frequency damping positive r-
      sourceNonlinearLaplace cut f g phi psi p frequency damping positive 0-
      r • sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive := by
  apply lift_sub_smul
  intro F
  have zeroSmall : |(0:ℝ)|≤nonlinearRadius g psi p cut damping :=
    abs_zero.trans_le (nonlinearRadius_pos g psi p cut damping positive).le
  rw [nonlinearLaplaceFamily_actual cut F f g phi psi p frequency damping r positive small,
    nonlinearLaplaceFamily_actual cut F f g phi psi p frequency damping 0 positive zeroSmall]
  rfl

theorem sourceNonlinearLaplace_remainder (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (frequency damping r : ℝ) (positive : 0<damping) (small : |r|≤nonlinearRadius g psi p cut damping) :
    ‖sourceNonlinearLaplace cut f g phi psi p frequency damping positive r-
      sourceNonlinearLaplace cut f g phi psi p frequency damping positive 0-
      r • sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive‖≤
      (nonlinearRemainderScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2 := by
  rw [←nonlinear_lift_error cut f g phi psi p frequency damping r positive small]
  apply lift_bound sourceFilter _ _ (mul_nonneg
    (mul_nonneg (nonlinearRemainderScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping)) (sq_nonneg _))
  intro F
  exact finiteNonlinearLaplace_remainder cut F f g phi psi p frequency damping r positive small

theorem sourceNonlinearLaplace_parameter_derivative (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
    (frequency damping : ℝ) (positive : 0<damping) :
    HasDerivAt (sourceNonlinearLaplace cut f g phi psi p frequency damping positive)
      (sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive) 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero]
  let K:=nonlinearRemainderScale cut f g phi psi p damping*laplaceMass damping
  have convergence : Tendsto (fun r : ℝ=>K*‖r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using ((continuous_norm:Continuous (fun r:ℝ=>‖r‖)).tendsto 0).const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun r=>mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg _))) ?_ convergence
  have small : ∀ᶠ r : ℝ in 𝓝 0,|r|≤nonlinearRadius g psi p cut damping := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (nonlinearRadius_pos g psi p cut damping positive)] with r hr
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr : |r|<nonlinearRadius g psi p cut damping).le
  filter_upwards [small] with r hr
  have bound:=mul_le_mul_of_nonneg_left
    (sourceNonlinearLaplace_remainder cut f g phi psi p frequency damping r positive hr) (inv_nonneg.mpr (norm_nonneg r))
  have scalar : ‖r‖⁻¹*(K*‖r‖^2)=K*‖r‖ := by
    by_cases zero : ‖r‖=0
    · simp only [zero,inv_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · field_simp
  exact bound.trans_eq scalar

open GaussComposite GaussComposite.SourceGraph
open CanonicalPreparationCore.Completed CanonicalPreparationCreation PreparationVacuumNativeClosure
open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation

theorem original_prepared_nonlinear_laplace (x : zeroLocalizedSpace actualNativeLocalizer)
    (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer) (frequency damping : ℝ)
    (positive : 0<damping) (left right : Bool) (lc ls rc rs : Fin 2) :
    (∃ h : prepared (zeroLocalizedProfile actualNativeLocalizer x)∈GaussRadialDomain.closedY.domain,
      ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared (zeroLocalizedProfile actualNativeLocalizer x),h⟩-
        cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer x))‖≤
          (915/916:ℝ)^(n+1)*916*GaussYukawaCoefficient.bound*‖x‖) ∧
    HasDerivAt (fun r : ℝ=>SourceGraph.response
      (sourceNonlinearLaplace cut f g phi psi p frequency damping positive r) left right lc ls rc rs
      (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x))
      (SourceGraph.response (sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive) left right lc ls rc rs
        (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x)) 0 := by
  obtain ⟨h,_,bound⟩:=PreparationVacuumLocalizedYukawa.original_prepared_Y_domain x
  refine ⟨⟨h,bound⟩,?_⟩
  exact (preparationRead left right lc ls rc rs (zeroLocalizedProfile actualNativeLocalizer x)
    (zeroLocalizedProfile actualNativeLocalizer x)).hasFDerivAt.comp_hasDerivAt 0
      (sourceNonlinearLaplace_parameter_derivative cut f g phi psi p frequency damping positive)

end LowEnergy.PreparationVacuumNonlinearLaplace
