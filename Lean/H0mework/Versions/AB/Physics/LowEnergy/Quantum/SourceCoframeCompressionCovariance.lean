import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeScaleAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceCoframeCompressionCovariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourceJointScaleBudget
open SourceCoframeScaleTransport SourceCoframeScaleAction NativeHistoryGrade
open scoped InnerProductSpace Topology ContDiff
open Filter Set
local instance labelFintype : Fintype Label := Fintype.ofFinite _

def coreTransport (t : ℝ) : diagonal.domain ≃ₗ[ℂ] diagonal.domain :=
  coreEquiv.symm.trans ((coreFlowEquiv t).trans coreEquiv)

theorem coreTransport_val (t : ℝ) (f : diagonal.domain) :
    (coreTransport t f : H)=hilbertFlow t (f : H) := by
  have he : embed (coreEquiv.symm f)=(f : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply f)
  rw [←he,hilbertFlow_on_core]
  rfl

theorem coreTransport_add (s t : ℝ) (f : diagonal.domain) :
    coreTransport s (coreTransport t f)=coreTransport (s+t) f := by
  apply Subtype.ext
  rw [coreTransport_val,coreTransport_val,coreTransport_val,hilbertFlow_add]

theorem coreTransport_zero (f : diagonal.domain) : coreTransport 0 f=f := by
  apply Subtype.ext
  rw [coreTransport_val,hilbertFlow_zero]

def mapFinsetFlow (t : ℝ) (F : Index) : Index := by
  classical
  exact F.map (coreTransport t).toEmbedding

theorem mapFinsetFlow_add (s t : ℝ) (F : Index) :
    mapFinsetFlow s (mapFinsetFlow t F)=mapFinsetFlow (s+t) F := by
  classical
  ext f
  simp only [mapFinsetFlow,Finset.mem_map]
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨y,hy,(coreTransport_add s t y).symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨coreTransport t x,⟨x,hx,rfl⟩,coreTransport_add s t x⟩

theorem mapFinsetFlow_zero (F : Index) : mapFinsetFlow 0 F=F := by
  classical
  ext x
  simp only [mapFinsetFlow,Finset.mem_map]
  change (∃ y, y∈F ∧ coreTransport 0 y=x) ↔ x∈F
  simp only [coreTransport_zero,exists_eq_right]

theorem mapFinsetFlow_mono (t : ℝ) : Monotone (mapFinsetFlow t) := by
  classical
  intro F G h
  exact Finset.map_subset_map.mpr h

theorem mapFinsetFlow_cofinal (t : ℝ) :
    Tendsto (mapFinsetFlow t) atTop atTop := by
  apply tendsto_atTop.2
  intro F
  apply eventually_atTop.2
  refine ⟨mapFinsetFlow (-t) F,fun G h => ?_⟩
  have hm := mapFinsetFlow_mono t h
  rw [mapFinsetFlow_add,add_neg_cancel,mapFinsetFlow_zero] at hm
  exact hm

theorem coreSpan_map (t : ℝ) (F : Index) :
    FiniteCoreEvolution.coreSpan diagonal (mapFinsetFlow t F)=
      (FiniteCoreEvolution.coreSpan diagonal F).map (hilbertFlow t).toLinearEquiv.toLinearMap := by
  classical
  rw [FiniteCoreEvolution.coreSpan,FiniteCoreEvolution.coreSpan,Submodule.map_span]
  congr 1
  ext x
  simp only [mapFinsetFlow,Finset.coe_map,Set.mem_image]
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨(z : H),⟨z,hz,rfl⟩,(coreTransport_val t z).symm⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨coreTransport t z,⟨z,hz,rfl⟩,coreTransport_val t z⟩

theorem core_projection_covariance (t : ℝ) (F : Index) (x : H) :
    (FiniteCoreEvolution.coreSpan diagonal (mapFinsetFlow t F)).starProjection x=
      hilbertFlow t ((FiniteCoreEvolution.coreSpan diagonal F).starProjection ((hilbertFlow t).symm x)) := by
  simpa only [←coreSpan_map] using! Submodule.starProjection_map_apply (hilbertFlow t)
    (FiniteCoreEvolution.coreSpan diagonal F) x

private theorem core_grade_commutes (t : ℝ) (g : Label) (f : QuantumTest) :
    coreFlow t (GaussCoreLabel.project g f)=GaussCoreLabel.project g (coreFlow t f) := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  rw [coreFlow_apply,GaussCoreLabel.project_apply,GaussCoreLabel.fiberPiece_apply,
    GaussCoreLabel.project_apply,GaussCoreLabel.fiberPiece_apply,coreFlow_apply]
  by_cases h : sourceLabel word=g <;> simp [h]

theorem grade_flow_commutes (t : ℝ) (g : Label) (x : H) :
    hilbertFlow t (projection g x)=projection g (hilbertFlow t x) := by
  refine embed_dense.induction_on (p := fun v : H =>
    hilbertFlow t (projection g v)=projection g (hilbertFlow t v)) x ?_ ?_
  · exact isClosed_eq ((hilbertFlow t).continuous.comp (projection g).continuous)
      ((projection g).continuous.comp (hilbertFlow t).continuous)
  · intro f
    rw [←GaussCoreLabel.embed_project,hilbertFlow_on_core,hilbertFlow_on_core,
      core_grade_commutes,GaussCoreLabel.embed_project]

theorem core_projection_transport (t : ℝ) (F : Index) (x : H) :
    (FiniteCoreEvolution.coreSpan diagonal (mapFinsetFlow t F)).starProjection (hilbertFlow t x)=
      hilbertFlow t ((FiniteCoreEvolution.coreSpan diagonal F).starProjection x) := by
  rw [core_projection_covariance,LinearIsometryEquiv.symm_apply_apply]

private def spanCore (F : Index) (x : H) : diagonal.domain :=
  ⟨(FiniteCoreEvolution.coreSpan diagonal F).starProjection x,
    FiniteCoreEvolution.coreSpan_le diagonal F
      ((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto x).property⟩

private theorem spanCore_transport (t : ℝ) (F : Index) (x : H) :
    spanCore (mapFinsetFlow t F) (hilbertFlow t x)=coreTransport t (spanCore F x) := by
  apply Subtype.ext
  rw [coreTransport_val]
  exact core_projection_transport t F x

private theorem coreTransport_test (t : ℝ) (f : diagonal.domain) :
    coreEquiv.symm (coreTransport t f)=coreFlow t (coreEquiv.symm f) := by
  change coreEquiv.symm (coreEquiv (coreFlow t (coreEquiv.symm f)))=_
  rw [coreEquiv.symm_apply_apply]

private theorem sourceCompression_apply (F : Index) (A : SourceCoframeVolumeCurrent.CoreEnd) (x : H) :
    sourceCompression F A x=∑ g : Label, projection g
      ((FiniteCoreEvolution.coreSpan diagonal F).starProjection
        (embed (A (coreEquiv.symm (spanCore F (projection g x)))))) := by
  change compress F A x=_
  simp only [compress,sum_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro g _
  rfl

private theorem ungraded_covariance (t : ℝ) (F : Index) (A : SourceCoframeVolumeCurrent.CoreEnd) (x : H) :
    (FiniteCoreEvolution.coreSpan diagonal (mapFinsetFlow t F)).starProjection
      (embed (conjugation t A
        (coreEquiv.symm (spanCore (mapFinsetFlow t F) (hilbertFlow t x)))))=
    hilbertFlow t ((FiniteCoreEvolution.coreSpan diagonal F).starProjection
      (embed (A (coreEquiv.symm (spanCore F x))))) := by
  rw [spanCore_transport,coreTransport_test,conjugation_apply,
    coreFlow_add,neg_add_cancel,coreFlow_zero,←hilbertFlow_on_core,core_projection_transport]

theorem source_compression_transport (t : ℝ) (F : Index)
    (A : SourceCoframeVolumeCurrent.CoreEnd) (x : H) :
    sourceCompression (mapFinsetFlow t F) (conjugation t A) (hilbertFlow t x)=
      hilbertFlow t (sourceCompression F A x) := by
  rw [sourceCompression_apply,sourceCompression_apply,map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [←grade_flow_commutes,ungraded_covariance,grade_flow_commutes]

theorem source_compression_conjugation (t : ℝ) (F : Index)
    (A : SourceCoframeVolumeCurrent.CoreEnd) :
    sourceCompression (mapFinsetFlow t F) (conjugation t A)=
      (hilbertFlow t).conjStarAlgEquiv (sourceCompression F A) := by
  apply ContinuousLinearMap.ext
  intro x
  have h := source_compression_transport t F A ((hilbertFlow t).symm x)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

private theorem original_compression_return (F : Index) :
    sourceCompression F diagonalAction=GaussGradedCompression.compression F := by
  have h := actual_compression_return F
  rw [scaledCompression,source_scale_one] at h
  exact h

theorem graded_compression_covariance (t : ℝ) (F : Index) :
    scaledCompression F (rate t)=
      (hilbertFlow t).conjStarAlgEquiv
        (GaussGradedCompression.compression (mapFinsetFlow (-t) F)) := by
  have h := source_compression_conjugation t (mapFinsetFlow (-t) F) diagonalAction
  simp only [mapFinsetFlow_add,add_neg_cancel,mapFinsetFlow_zero] at h
  calc
    scaledCompression F (rate t)=sourceCompression F (conjugation t diagonalAction) :=
      congrArg (sourceCompression F) (original_hamiltonian_conjugation t).symm
    _ = _ := h
    _ = _ := congrArg (hilbertFlow t).conjStarAlgEquiv (original_compression_return _)

theorem scaled_compression_selfAdjoint (t : ℝ) (F : Index) :
    IsSelfAdjoint (scaledCompression F (rate t)) := by
  rw [graded_compression_covariance]
  exact (GaussGradedCompression.compression_selfAdjoint _).map (hilbertFlow t).conjStarAlgEquiv

private theorem rate_log (r : ℝ) (hr : 0 < r) : rate ((3/2 : ℝ)*Real.log r)=r := by
  unfold rate
  have h : (2/3 : ℝ)*((3/2 : ℝ)*Real.log r)=Real.log r := by ring
  rw [h,Real.exp_log hr]

theorem positive_scaled_compression_selfAdjoint (F : Index) (r : ℝ) (hr : 0 < r) :
    IsSelfAdjoint (scaledCompression F r) := by
  have h := scaled_compression_selfAdjoint ((3/2 : ℝ)*Real.log r) F
  rwa [rate_log r hr] at h

private theorem shifted_compression_covariance (t : ℝ) (F : Index) (z : ℂ) :
    scaledCompression F (rate t)-z • 1=
      (hilbertFlow t).conjStarAlgEquiv
        (GaussGradedCompression.compression (mapFinsetFlow (-t) F)-z • 1) := by
  rw [graded_compression_covariance]
  apply ContinuousLinearMap.ext
  intro x
  simp only [sub_apply,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    smul_apply,one_apply_eq_self,map_sub,map_smul,
    LinearIsometryEquiv.apply_symm_apply]

theorem graded_resolvent_covariance (t : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0) :
    FullYSourceResolventGraphSplice.resolvent (scaledCompression F (rate t)) z=
      (hilbertFlow t).conjStarAlgEquiv
        (FullYSourceResolventGraphSplice.finiteResolvent (mapFinsetFlow (-t) F) z) := by
  let C := scaledCompression F (rate t)
  let D := GaussGradedCompression.compression (mapFinsetFlow (-t) F)
  let e := (hilbertFlow t).conjStarAlgEquiv
  have hshift : C-z • 1=e (D-z • 1) := shifted_compression_covariance t F z
  have hright : (C-z • 1)*e (FullYSourceResolventGraphSplice.resolvent D z)=1 := by
    rw [hshift,←map_mul,FullYSourceResolventGraphSplice.resolvent_right D
      (GaussGradedCompression.compression_selfAdjoint _) z hz,map_one]
  have hleft := FullYSourceResolventGraphSplice.resolvent_left C
    (scaled_compression_selfAdjoint t F) z hz
  change FullYSourceResolventGraphSplice.resolvent C z=e (FullYSourceResolventGraphSplice.resolvent D z)
  calc
    _ = FullYSourceResolventGraphSplice.resolvent C z*1 := (mul_one _).symm
    _ = FullYSourceResolventGraphSplice.resolvent C z*((C-z • 1)*
      e (FullYSourceResolventGraphSplice.resolvent D z)) := by rw [hright]
    _ = _ := by rw [←mul_assoc,hleft,one_mul]

theorem positive_scaled_resolvent_bound (F : Index) (r : ℝ) (hr : 0 < r)
    (z : ℂ) (hz : z.im≠0) :
    ‖FullYSourceResolventGraphSplice.resolvent (scaledCompression F r) z‖≤1/|z.im| :=
  FullYSourceResolventGraphSplice.resolvent_norm _
    (positive_scaled_compression_selfAdjoint F r hr) z hz

end LowEnergy.SourceCoframeCompressionCovariance
