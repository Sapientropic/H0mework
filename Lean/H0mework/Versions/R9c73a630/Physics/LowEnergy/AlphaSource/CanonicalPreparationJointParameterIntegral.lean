import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSpatialFullFormFeed

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumJointFieldResponse
open SourceQuantumGaugeSliceCoordinates PreparationVacuumMixedFieldReturn
open GaussDensityCore GaussHistoryHilbert MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators

abbrev JointParameter:=Field289×SourceCoordinateSlice

section Integral
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def parameterPartial (S : JointParameter→V) (u : JointParameter) : Field289→L[ℝ] V:=
  (fderiv ℝ S u).comp (ContinuousLinearMap.inl ℝ Field289 SourceCoordinateSlice)

theorem parameterPartial_smooth (S : JointParameter→V) (u : JointParameter) (smooth : ContDiffAt ℝ ∞ S u) :
    ContDiffAt ℝ ∞ (parameterPartial S) u :=
  (smooth.fderiv_right (m:=∞) (by simp)).clm_comp contDiffAt_const

theorem parameterPartial_derivative (S : JointParameter→V) (q : Field289) (z : SourceCoordinateSlice)
    (smooth : ContDiffAt ℝ ∞ S (q,z)) : HasFDerivAt (fun p=>S (p,z)) (parameterPartial S (q,z)) q :=by
  have source:=smooth.differentiableAt (by simp) |>.hasFDerivAt
  have pair:=(hasFDerivAt_id (𝕜:=ℝ) q).prodMk (hasFDerivAt_const z q)
  exact source.comp q pair

theorem parameterPartial_zero (S : JointParameter→V) (K : Set SourceCoordinateSlice) (closed : IsClosed K)
    (zero : ∀q z,z∉K→S (q,z)=0) (q : Field289) (z : SourceCoordinateSlice) (outside : z∉K) :
    parameterPartial S (q,z)=0 :=by
  have localZero : S=ᶠ[𝓝 (q,z)] fun _=>0 :=by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (closed.isOpen_compl.mem_nhds outside)] with u hu
    exact zero u.1 u.2 hu
  rw [parameterPartial,localZero.fderiv_eq,fderiv_const_apply]
  rfl

omit [NormedSpace ℝ V] in
theorem parameter_slice_support (S : JointParameter→V) (K : Set SourceCoordinateSlice) (closed : IsClosed K)
    (zero : ∀q z,z∉K→S (q,z)=0) (q : Field289) : tsupport (fun z=>S (q,z))⊆K :=by
  apply closure_minimal _ closed
  intro z hz;by_contra outside;exact hz (zero q z outside)

theorem parameter_slice_integrable (S : JointParameter→V) (K : Set SourceCoordinateSlice) (compact : IsCompact K)
    (q : Field289) (smooth : ∀z,ContDiffAt ℝ ∞ S (q,z)) (zero : ∀p z,z∉K→S (p,z)=0) :
    Integrable (fun z=>S (q,z)) configurationMeasure :=
  (continuous_iff_continuousAt.mpr (fun z=>(smooth z).continuousAt.comp
    (continuous_const.prodMk continuous_id).continuousAt)).integrable_of_hasCompactSupport
      (compact.of_isClosed_subset isClosed_closure (parameter_slice_support S K compact.isClosed zero q))

theorem source_integral_fderivative (S : JointParameter→V) (K : Set SourceCoordinateSlice) (compact : IsCompact K)
    (R : ℝ) (positive : 0<R)
    (smooth : ∀q z,‖q‖<R→ ContDiffAt ℝ ∞ S (q,z))
    (zero : ∀q z,z∉K→S (q,z)=0) (q : Field289) (small : ‖q‖<R/2) :
    HasFDerivAt (fun p=>∫z,S (p,z) ∂configurationMeasure)
      (∫z,parameterPartial S (q,z) ∂configurationMeasure) q :=by
  have inside {p : Field289} (hp : p∈Metric.closedBall 0 (R/2)) : ‖p‖<R :=by
    rw [Metric.mem_closedBall,dist_zero_right] at hp
    linarith
  have dsmooth (p : Field289) (z : SourceCoordinateSlice) (hp : ‖p‖<R):=
    parameterPartial_smooth S (p,z) (smooth p z hp)
  have dzero:=parameterPartial_zero S K compact.isClosed zero
  have ps (p : Field289) (hp : ‖p‖<R):=parameter_slice_integrable S K compact p (smooth p · hp) zero
  have pd (p : Field289) (hp : ‖p‖<R):=
    parameter_slice_integrable (parameterPartial S) K compact p (dsmooth p · hp) dzero
  have continuous : ContinuousOn (parameterPartial S) (Metric.closedBall (0:Field289) (R/2) ×ˢ K) :=
    fun u hu=>(dsmooth u.1 u.2 (inside hu.1)).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩:=(isCompact_closedBall (0:Field289) (R/2)).prod compact |>.exists_bound_of_continuousOn continuous
  let majorant : SourceCoordinateSlice→ℝ:=K.indicator (fun _=>max 0 C)
  have mi : Integrable majorant configurationMeasure :=by
    apply (integrable_indicator_iff compact.measurableSet).mpr
    exact integrableOn_const compact.measure_lt_top.ne
  have qs : q∈Metric.ball (0:Field289) (R/2):=by simpa only [Metric.mem_ball,dist_zero_right] using small
  have domain : Metric.ball (0:Field289) (R/2)∈𝓝 q:=Metric.isOpen_ball.mem_nhds qs
  have bound : ∀ᵐz ∂configurationMeasure,∀p∈Metric.ball (0:Field289) (R/2),‖parameterPartial S (p,z)‖≤ majorant z :=by
    apply Filter.Eventually.of_forall;intro z p hp
    by_cases hz : z∈K
    · change ‖parameterPartial S (p,z)‖≤ K.indicator (fun _=>max 0 C) z
      rw [Set.indicator_of_mem hz]
      exact (hC (p,z) ⟨Metric.ball_subset_closedBall hp,hz⟩).trans (le_max_right _ _)
    · change ‖parameterPartial S (p,z)‖≤ K.indicator (fun _=>max 0 C) z
      rw [dzero p z hz,Set.indicator_of_notMem hz,norm_zero]
  have qInside : ‖q‖<R:=inside (Metric.ball_subset_closedBall qs)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le domain
    (by filter_upwards [domain] with p hp;exact (ps p (inside (Metric.ball_subset_closedBall hp))).aestronglyMeasurable)
    (ps q qInside) (pd q qInside).aestronglyMeasurable bound mi
    (Filter.Eventually.of_forall (fun z p hp=>parameterPartial_derivative S p z (smooth p z (inside (Metric.ball_subset_closedBall hp)))))

theorem source_integral_C2 (S : JointParameter→V) (K : Set SourceCoordinateSlice) (compact : IsCompact K)
    (R : ℝ) (positive : 0<R)
    (smooth : ∀q z,‖q‖<R→ ContDiffAt ℝ ∞ S (q,z))
    (zero : ∀q z,z∉K→S (q,z)=0) :
    ContDiffAt ℝ 2 (fun p=>∫z,S (p,z) ∂configurationMeasure) 0 :=by
  have d1 (p : Field289) (z : SourceCoordinateSlice) (hp : ‖p‖<R):=parameterPartial_smooth S (p,z) (smooth p z hp)
  have z1:=parameterPartial_zero S K compact.isClosed zero
  have d2 (p : Field289) (z : SourceCoordinateSlice) (hp : ‖p‖<R):=parameterPartial_smooth (parameterPartial S) (p,z) (d1 p z hp)
  have z2:=parameterPartial_zero (parameterPartial S) K compact.isClosed z1
  have ball : Metric.ball (0:Field289) (R/2)∈𝓝 (0:Field289):=Metric.ball_mem_nhds _ (by positivity)
  apply (contDiffAt_succ_iff_hasFDerivAt (n:=1)).mpr
  refine ⟨fun p=>∫z,parameterPartial S (p,z) ∂configurationMeasure,⟨Metric.ball 0 (R/2),ball,?_⟩,?_⟩
  · intro p hp
    exact source_integral_fderivative S K compact R positive smooth zero p (by simpa only [Metric.mem_ball,dist_zero_right] using hp)
  · apply (contDiffAt_succ_iff_hasFDerivAt (n:=0)).mpr
    refine ⟨fun p=>∫z,parameterPartial (parameterPartial S) (p,z) ∂configurationMeasure,⟨Metric.ball 0 (R/2),ball,?_⟩,?_⟩
    · intro p hp
      exact source_integral_fderivative (parameterPartial S) K compact R positive d1 z1 p
        (by simpa only [Metric.mem_ball,dist_zero_right] using hp)
    · apply contDiffAt_zero.mpr
      refine ⟨Metric.ball 0 (R/2),ball,?_⟩
      intro p hp
      exact (source_integral_fderivative (parameterPartial (parameterPartial S)) K compact R positive d2 z2 p
        (by simpa only [Metric.mem_ball,dist_zero_right] using hp)).continuousAt.continuousWithinAt

end Integral
end LowEnergy.PreparationVacuumJointFieldResponse
