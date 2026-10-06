import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceJointResidualEnergy
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCutoffDilationWard
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScaleJetWard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceJointScaleBudget
open Filter MeasureTheory GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceJointResidualEnergy SourceHardyRetardedTail GaussCoreDifferential GaussFockPair GaussNativeEnergy
open GaussNativeForm GaussMatterCore SourceKineticTranspose SourceDilationRemainder
open SourceHamiltonianScaleJet SourceCoframeVolumeCurrent SourceScaleJetFactor
open SourcePhysicalKineticSquare SourceEscapeCurrent FullYSourceResolventGraphSplice
open NativeHistoryGrade
open scoped InnerProductSpace
local instance labelFintype : Fintype Label := Fintype.ofFinite _

private def scaleVector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K E M L : V) (r : ℝ) : V :=
  ((r⁻¹^3 : ℝ) : ℂ) • K+(r : ℂ) • E+
    ((r⁻¹ : ℝ) : ℂ) • M+((r^3 : ℝ) : ℂ) • L

private theorem scale_vector_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K E M L : V) : scaleVector K E M L 1=K+E+M+L := by
  simp only [scaleVector,inv_one,one_pow,Complex.ofReal_one,one_smul]

private theorem scale_vector_local {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K E M L : V) :
    (-1/360 : ℂ) • scaleVector K E M L 1+(2/45 : ℂ) • scaleVector K E M L 2+
      (-27/280 : ℂ) • scaleVector K E M L 3+(16/315 : ℂ) • scaleVector K E M L 4=L := by
  unfold scaleVector
  norm_num
  module

def sourceScale (r : ℝ) : CoreEnd :=
  scaleVector (kineticAction-gaugeKinetic) (gaugeKinetic+spatialAction) matterAction localAction r

theorem source_scale_generator (r : ℝ) :
    scaleDerivative (sourceScale r)=
      ((r⁻¹^3 : ℝ) : ℂ) • ((-3 : ℂ) • (kineticAction-gaugeKinetic))+
      (r : ℂ) • (gaugeKinetic+spatialAction)+
      ((r⁻¹ : ℝ) : ℂ) • ((-1 : ℂ) • matterAction)+
      ((r^3 : ℝ) : ℂ) • ((3 : ℂ) • localAction) := by
  simp only [sourceScale,scaleVector,map_add,map_sub,map_smul,
    scale_kinetic,scale_electric,scale_matter,scale_local,scale_spatial]
  module

theorem source_scale_one : sourceScale 1=diagonalAction := by
  rw [original_action_split]
  rw [sourceScale,scale_vector_one]
  abel

/-- Four actual source weights isolate the local radius without a finite dilation surrogate. -/
theorem source_scale_local :
    (-1/360 : ℂ) • sourceScale 1+(2/45 : ℂ) • sourceScale 2+
      (-27/280 : ℂ) • sourceScale 3+(16/315 : ℂ) • sourceScale 4=localAction := by
  exact scale_vector_local _ _ _ _

private def spanInput (F : Index) (x : H) : diagonal.domain :=
  ⟨(FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto x,
    FiniteCoreEvolution.coreSpan_le diagonal F
      ((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto x).property⟩

private def finiteAction (F : Index) (A : CoreEnd) :
    FiniteCoreEvolution.coreSpan diagonal F →L[ℂ] FiniteCoreEvolution.coreSpan diagonal F :=
  (((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto).toLinearMap.comp
    (embed.comp (A.comp (coreEquiv.symm.toLinearMap.comp
      (Submodule.inclusion (FiniteCoreEvolution.coreSpan_le diagonal F)))))).toContinuousLinearMap

private def ungraded (F : Index) (A : CoreEnd) : H →L[ℂ] H :=
  (FiniteCoreEvolution.coreSpan diagonal F).subtypeL.comp
    ((finiteAction F A).comp (FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto)

private theorem ungraded_apply (F : Index) (A : CoreEnd) (x : H) :
    ungraded F A x=
      (FiniteCoreEvolution.coreSpan diagonal F).starProjection
        (embed (A (coreEquiv.symm (spanInput F x)))) := rfl

def compress (F : Index) (A : CoreEnd) : H →L[ℂ] H :=
  ∑ g : Label, (projection g).comp ((ungraded F A).comp (projection g))

private theorem compress_add (F : Index) (A B : CoreEnd) :
    compress F (A+B)=compress F A+compress F B := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [compress,sum_apply,ContinuousLinearMap.comp_apply,ungraded_apply,LinearMap.add_apply,
    map_add,Finset.sum_add_distrib,add_apply]

private theorem compress_smul (F : Index) (c : ℂ) (A : CoreEnd) :
    compress F (c • A)=c • compress F A := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [compress,sum_apply,ContinuousLinearMap.comp_apply,ungraded_apply,LinearMap.smul_apply,
    map_smul,Finset.smul_sum,smul_apply]

def sourceCompression (F : Index) : CoreEnd →ₗ[ℂ] H →L[ℂ] H where
  toFun := compress F
  map_add' := compress_add F
  map_smul' c A := by
    change compress F (c • A)=c • compress F A
    exact compress_smul F c A

def scaledCompression (F : Index) (r : ℝ) : H →L[ℂ] H := sourceCompression F (sourceScale r)

theorem actual_compression_return (F : Index) :
    scaledCompression F 1=GaussGradedCompression.compression F := by
  rw [scaledCompression,source_scale_one]
  rfl

theorem scaled_compression_weights (F : Index) (r : ℝ) :
    scaledCompression F r=
      ((r⁻¹^3 : ℝ) : ℂ) • sourceCompression F (kineticAction-gaugeKinetic)+
      (r : ℂ) • sourceCompression F (gaugeKinetic+spatialAction)+
      ((r⁻¹ : ℝ) : ℂ) • sourceCompression F matterAction+
      ((r^3 : ℝ) : ℂ) • sourceCompression F localAction := by
  simp only [scaledCompression,sourceScale,scaleVector,map_add,map_smul]

theorem scaled_compression_local (F : Index) :
    (-1/360 : ℂ) • scaledCompression F 1+(2/45 : ℂ) • scaledCompression F 2+
      (-27/280 : ℂ) • scaledCompression F 3+(16/315 : ℂ) • scaledCompression F 4=
      sourceCompression F localAction := by
  have h := congrArg (sourceCompression F) source_scale_local
  simpa only [map_add,map_smul,scaledCompression] using! h

def sourceFlux (F : Index) (A : CoreEnd) (f : QuantumTest) : H :=
  embed (A f)-sourceCompression F A (embed f)

theorem source_flux_weights (F : Index) (r : ℝ) (f : QuantumTest) :
    sourceFlux F (sourceScale r) f=
      ((r⁻¹^3 : ℝ) : ℂ) • sourceFlux F (kineticAction-gaugeKinetic) f+
      (r : ℂ) • sourceFlux F (gaugeKinetic+spatialAction) f+
      ((r⁻¹ : ℝ) : ℂ) • sourceFlux F matterAction f+
      ((r^3 : ℝ) : ℂ) • sourceFlux F localAction f := by
  simp only [sourceFlux,sourceScale,scaleVector,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
    add_apply,smul_apply]
  module

theorem source_flux_local (F : Index) (f : QuantumTest) :
    (-1/360 : ℂ) • sourceFlux F (sourceScale 1) f+(2/45 : ℂ) • sourceFlux F (sourceScale 2) f+
      (-27/280 : ℂ) • sourceFlux F (sourceScale 3) f+(16/315 : ℂ) • sourceFlux F (sourceScale 4) f=
      sourceFlux F localAction f := by
  have h := congrArg (fun A : CoreEnd => embed (A f)) source_scale_local
  have hc := congrArg (fun A : H →L[ℂ] H => A (embed f)) (scaled_compression_local F)
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul] at h
  simp only [add_apply,smul_apply,scaledCompression] at hc
  unfold sourceFlux
  change _=embed (localAction f)-sourceCompression F localAction (embed f)
  rw [←h,←hc]
  module

private theorem four_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b c d : E) :
    ‖(-1/360 : ℂ) • a+(2/45 : ℂ) • b+(-27/280 : ℂ) • c+(16/315 : ℂ) • d‖≤
      (1/360 : ℝ)*‖a‖+(2/45 : ℝ)*‖b‖+(27/280 : ℝ)*‖c‖+(16/315 : ℝ)*‖d‖ := by
  have h1 := norm_add_le ((-1/360 : ℂ) • a) ((2/45 : ℂ) • b)
  have h2 := norm_add_le ((-1/360 : ℂ) • a+(2/45 : ℂ) • b) ((-27/280 : ℂ) • c)
  have h3 := norm_add_le (((-1/360 : ℂ) • a+(2/45 : ℂ) • b)+(-27/280 : ℂ) • c)
    ((16/315 : ℂ) • d)
  norm_num [norm_smul,norm_div,norm_neg] at h1 h2 h3 ⊢
  linarith

theorem compressed_local_cost (F : Index) (x : H) :
    ‖sourceCompression F localAction x‖≤
      (1/360 : ℝ)*‖scaledCompression F 1 x‖+(2/45 : ℝ)*‖scaledCompression F 2 x‖+
      (27/280 : ℝ)*‖scaledCompression F 3 x‖+(16/315 : ℝ)*‖scaledCompression F 4 x‖ := by
  rw [←scaled_compression_local F]
  exact four_norm _ _ _ _

theorem source_radial_scale_cost (q : QuantumTest) :
    ‖embed (radialAction q)‖≤
      (1/360 : ℝ)*‖embed (inverseVolumeAction (sourceScale 1 q))‖+
      (2/45 : ℝ)*‖embed (inverseVolumeAction (sourceScale 2 q))‖+
      (27/280 : ℝ)*‖embed (inverseVolumeAction (sourceScale 3 q))‖+
      (16/315 : ℝ)*‖embed (inverseVolumeAction (sourceScale 4 q))‖ := by
  have h := congrArg (fun A : CoreEnd => embed (inverseVolumeAction (A q))) source_scale_local
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul] at h
  change ‖embed (inverseVolumeAction (localAction q))‖≤_
  rw [←h]
  exact four_norm _ _ _ _

def signedScaleInput (m ell : ℕ) (q : QuantumTest) : H := normalizer (
  (-1/360 : ℂ) • SourceRelativePowerTail.relativeTail m ell (embed (inverseVolumeAction (sourceScale 1 q)))+
  (2/45 : ℂ) • SourceRelativePowerTail.relativeTail m ell (embed (inverseVolumeAction (sourceScale 2 q)))+
  (-27/280 : ℂ) • SourceRelativePowerTail.relativeTail m ell (embed (inverseVolumeAction (sourceScale 3 q)))+
  (16/315 : ℂ) • SourceRelativePowerTail.relativeTail m ell (embed (inverseVolumeAction (sourceScale 4 q))))

theorem signed_scale_input (m ell : ℕ) (q : QuantumTest) :
    signedScaleInput m ell q=normalizer
      (SourceRelativePowerTail.relativeTail m ell (embed (radialAction q))) := by
  have h := congrArg (fun A : CoreEnd => SourceRelativePowerTail.relativeTail m ell
    (embed (inverseVolumeAction (A q)))) source_scale_local
  have he : (-1/360 : ℂ) • SourceRelativePowerTail.relativeTail m ell (embed (inverseVolumeAction (sourceScale 1 q)))+
      (2/45 : ℂ) • SourceRelativePowerTail.relativeTail m ell (embed (inverseVolumeAction (sourceScale 2 q)))+
      (-27/280 : ℂ) • SourceRelativePowerTail.relativeTail m ell (embed (inverseVolumeAction (sourceScale 3 q)))+
      (16/315 : ℂ) • SourceRelativePowerTail.relativeTail m ell (embed (inverseVolumeAction (sourceScale 4 q)))=
      SourceRelativePowerTail.relativeTail m ell (embed (radialAction q)) := by
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul] using! h
  exact congrArg normalizer he

private theorem source_time_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

theorem retained_normalizer_bound (sharp : Bool) (m ell : ℕ) (x : H) :
    ‖factor sharp m ell x‖≤(‖GaussYukawaOperator.bounded‖/sourceTime 0)*
      ‖normalizer (SourceRelativePowerTail.relativeTail m ell x)‖ := by
  have hb : ‖SourceCornerForcing.sourceVertex sharp‖=‖GaussYukawaOperator.bounded‖ := by
    cases sharp <;> simp [SourceCornerForcing.sourceVertex]
  have hc := congrArg (fun A : H →L[ℂ] H => A (SourceRelativePowerTail.relativeTail m ell x))
    (normalizer_vertex sharp).eq
  change normalizer (SourceCornerForcing.sourceVertex sharp (SourceRelativePowerTail.relativeTail m ell x))=
    SourceCornerForcing.sourceVertex sharp (normalizer (SourceRelativePowerTail.relativeTail m ell x)) at hc
  change ‖((sourceTime 0)⁻¹ : ℂ) • normalizer
    (SourceCornerForcing.sourceVertex sharp (SourceRelativePowerTail.relativeTail m ell x))‖≤_
  rw [hc,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos source_time_pos]
  have hv := (SourceCornerForcing.sourceVertex sharp).le_opNorm
    (normalizer (SourceRelativePowerTail.relativeTail m ell x))
  rw [hb] at hv
  calc
    _ ≤ (sourceTime 0)⁻¹*(‖GaussYukawaOperator.bounded‖*
        ‖normalizer (SourceRelativePowerTail.relativeTail m ell x)‖) :=
      mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr source_time_pos.le)
    _ = _ := by ring

set_option maxRecDepth 2048 in
theorem literal_joint_scale_bound (sharp : Bool) (m ell : ℕ) (q : QuantumTest) :
    ‖SourceEscapeSeedTail.actualIncrement sharp m ell (embed q)‖≤
      (‖GaussYukawaOperator.bounded‖/sourceTime 0)*‖signedScaleInput m ell q‖ := by
  have hj : scaleJet=(48 : ℂ) • localAction := source_local_from_scale_jet
  have he := actual_core_factor sharp m ell q
  rw [hj,LinearMap.smul_apply,map_smul,map_smul,map_smul,smul_smul] at he
  norm_num at he
  rw [he,signed_scale_input]
  exact retained_normalizer_bound sharp m ell (embed (radialAction q))

private theorem core_embed (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply x)

def frequencyCost (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) : ℝ :=
  ‖(k : H)‖*(1/|z.im|)*(‖GaussYukawaOperator.bounded‖/sourceTime 0)*
      ‖signedScaleInput m ell (coreEquiv.symm (sourceCore F z hz g))‖+
    ‖inner ℂ (k : H) (particular sharp m ell F z (g : H)+
      z • finiteResolvent F z (particular sharp m ell F z (g : H)))‖

set_option maxRecDepth 2048 in
theorem actual_joint_scale_bound (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g k : diagonal.domain) :
    ‖jointResidual sharp m ell F z hz g k‖≤frequencyCost sharp m ell F z hz g k := by
  let d := SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H))
  let b := particular sharp m ell F z (g : H)+z • finiteResolvent F z (particular sharp m ell F z (g : H))
  have h := SourceCornerPartition.actual_full_increment_splice sharp m ell F z hz g k
  have hj : jointResidual sharp m ell F z hz g k=
      inner ℂ (k : H) (finiteResolvent F z d)-inner ℂ (k : H) b := by
    unfold jointResidual
    dsimp only [d,b]
    linear_combination -h
  have hd := literal_joint_scale_bound sharp m ell (coreEquiv.symm (sourceCore F z hz g))
  rw [core_embed] at hd
  change ‖d‖≤_ at hd
  have hr := ((finiteResolvent F z).le_opNorm d).trans
    (mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg d))
  have hp := (norm_inner_le_norm (𝕜 := ℂ) (k : H) (finiteResolvent F z d)).trans
    (mul_le_mul_of_nonneg_left hr (norm_nonneg (k : H)))
  have hi := mul_le_mul_of_nonneg_left hd
    (mul_nonneg (norm_nonneg (k : H)) (by positivity : 0≤1/|z.im|))
  have hf : ‖inner ℂ (k : H) (finiteResolvent F z d)‖≤
      ‖(k : H)‖*(1/|z.im|)*(‖GaussYukawaOperator.bounded‖/sourceTime 0)*
        ‖signedScaleInput m ell (coreEquiv.symm (sourceCore F z hz g))‖ := by
    calc
      _ ≤ ‖(k : H)‖*(1/|z.im|)*‖d‖ := by simpa only [mul_assoc] using hp
      _ ≤ _ := by simpa only [mul_assoc] using hi
  rw [hj]
  change ‖inner ℂ (k : H) (finiteResolvent F z d)-inner ℂ (k : H) b‖≤
    ‖(k : H)‖*(1/|z.im|)*(‖GaussYukawaOperator.bounded‖/sourceTime 0)*
      ‖signedScaleInput m ell (coreEquiv.symm (sourceCore F z hz g))‖+‖inner ℂ (k : H) b‖
  linarith [norm_sub_le (inner ℂ (k : H) (finiteResolvent F z d)) (inner ℂ (k : H) b)]

/-- The same-F Gram is bounded by one signed source-scale input; its internal cross terms remain. -/
theorem actual_joint_gram_budget (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    ENNReal.ofReal (actualJointGram sharp m ell F μ (g : H) (k : H))≤
      ∫⁻ t : ℝ, ENNReal.ofReal
        ((frequencyCost sharp m ell F (SourceResolventBandLimit.line μ t)
          (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g k)^2) := by
  rw [←actual_joint_lintegral sharp m ell F μ hμ g k]
  apply lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _) (actual_joint_scale_bound sharp m ell F _ _ g k) 2

def inputSpan (F : Index) (g : diagonal.domain) : Submodule ℂ H :=
  SourceRetardedIncrement.supportSpan F ⊔ Submodule.span ℂ {(g : H)}

instance inputSpan_finite (F : Index) (g : diagonal.domain) : FiniteDimensional ℂ (inputSpan F g) := by
  unfold inputSpan
  infer_instance

theorem input_span_core (F : Index) (g : diagonal.domain) : inputSpan F g≤diagonal.domain := by
  apply sup_le
  · exact FiniteCoreEvolution.coreSpan_le diagonal (SourceRetardedIncrement.supportSet F)
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x=(g : H) := Set.mem_singleton_iff.mp hx
    rw [hx']
    exact g.property

theorem resolvent_input_span (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    finiteResolvent F z (g : H)∈inputSpan F g := by
  have hg : (g : H)∈inputSpan F g :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  have hc : GaussGradedCompression.compression F (finiteResolvent F z (g : H))∈inputSpan F g :=
    Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F _)
  have hr := congrArg (fun A : H →L[ℂ] H => A (g : H))
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F z (g : H))-
    z • finiteResolvent F z (g : H)=(g : H) at hr
  have he : z • finiteResolvent F z (g : H)=
      GaussGradedCompression.compression F (finiteResolvent F z (g : H))-(g : H) := by
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hr).symm
  have hm : z • finiteResolvent F z (g : H)∈inputSpan F g := he ▸ (inputSpan F g).sub_mem hc hg
  have hn : z≠0 := by intro h; exact hz (h ▸ rfl)
  have h := (inputSpan F g).smul_mem z⁻¹ hm
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using h

def radialRead (F : Index) (g : diagonal.domain) : H →L[ℂ] H :=
  ((embed.comp (radialAction.comp (coreEquiv.symm.toLinearMap.comp
    (Submodule.inclusion (input_span_core F g))))).toContinuousLinearMap).comp
      (inputSpan F g).orthogonalProjectionOnto

theorem radial_read_resolvent (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    radialRead F g (finiteResolvent F z (g : H))=
      embed (radialAction (coreEquiv.symm (sourceCore F z hz g))) := by
  have hp := (inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨finiteResolvent F z (g : H),resolvent_input_span F z hz g⟩
  change embed (radialAction (coreEquiv.symm
    (Submodule.inclusion (input_span_core F g)
      ((inputSpan F g).orthogonalProjectionOnto (finiteResolvent F z (g : H))))))=_
  rw [hp]
  rfl

theorem signed_input_memLp (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    MemLp (fun t : ℝ => signedScaleInput m ell
      (coreEquiv.symm (sourceCore F (SourceResolventBandLimit.line μ t)
        (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g))) 2 := by
  let A := normalizer.comp ((SourceRelativePowerTail.relativeTail m ell).comp (radialRead F g))
  let : SecondCountableTopologyEither ℝ H := ⟨Or.inl inferInstance⟩
  have hc : Continuous (fun t : ℝ => finiteResolvent F (SourceResolventBandLimit.line μ t) (g : H)) := by
    simpa only using! (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply
      (continuous_const (y := (g : H)))
  have hf : MemLp (fun t => finiteResolvent F (SourceResolventBandLimit.line μ t) (g : H)) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    simpa only [SourceResolventBandLimit.line,mul_comm (μ : ℂ) Complex.I] using!
      SourceActualResolventEnergy.actual_square_integrable F μ hμ (g : H)
  have hm : MemLp (fun t => A (finiteResolvent F (SourceResolventBandLimit.line μ t) (g : H))) 2 := by
    simpa only [Function.comp_apply] using! A.comp_memLp' hf
  have he : (fun t : ℝ => signedScaleInput m ell
      (coreEquiv.symm (sourceCore F (SourceResolventBandLimit.line μ t)
        (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g)))=
      (fun t => A (finiteResolvent F (SourceResolventBandLimit.line μ t) (g : H))) := by
    funext t
    rw [signed_scale_input]
    exact (congrArg (fun x => normalizer (SourceRelativePowerTail.relativeTail m ell x))
      (radial_read_resolvent F (SourceResolventBandLimit.line μ t)
        (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g)).symm
  rw [he]
  exact hm

private theorem hardy_body_memLp (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    MemLp (fun t : ℝ => inner ℂ (k : H)
      (particular sharp m ell F (SourceResolventBandLimit.line μ t) (g : H)+
        SourceResolventBandLimit.line μ t • finiteResolvent F (SourceResolventBandLimit.line μ t)
          (particular sharp m ell F (SourceResolventBandLimit.line μ t) (g : H)))) 2 := by
  let E := (GaussGradedCompression.compression F).comp (cutoffSolver sharp m ell)
  have he (t : ℝ) : particular sharp m ell F (SourceResolventBandLimit.line μ t) (g : H)+
        SourceResolventBandLimit.line μ t • finiteResolvent F (SourceResolventBandLimit.line μ t)
          (particular sharp m ell F (SourceResolventBandLimit.line μ t) (g : H))=
      finiteResolvent F (SourceResolventBandLimit.line μ t)
        (E (finiteResolvent F (SourceResolventBandLimit.line μ t) (g : H))) := by
    exact (congrArg (fun A : H →L[ℂ] H => A
      (particular sharp m ell F (SourceResolventBandLimit.line μ t) (g : H)))
      (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F)
        (SourceResolventBandLimit.line μ t)
        (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne'))).symm
  simp_rw [he,actual_two_leg_spectral F μ hμ,inner_sum,inner_smul_right]
  have hc : Continuous (fun t : ℝ => ∑ ij : Channel F × Channel F,
      polePair μ (channelValue F ij.1) (channelValue F ij.2) t •
        inner ℂ (k : H) (spectralLeg F E (g : H) ij)) := by
    apply continuous_finsetSum
    intro ij _
    exact ((pole_continuous μ _ hμ).mul (pole_continuous μ _ hμ)).smul continuous_const
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (finite_gram_integrable μ hμ _ _ _)

theorem frequency_cost_integrable (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    Integrable (fun t : ℝ => (frequencyCost sharp m ell F (SourceResolventBandLimit.line μ t)
      (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g k)^2) := by
  have hx := (signed_input_memLp m ell F μ hμ g).norm
  have hb := (hardy_body_memLp sharp m ell F μ hμ g k).norm
  have hm := (hx.const_smul (‖(k : H)‖*(1/|μ|)*(‖GaussYukawaOperator.bounded‖/sourceTime 0))).add hb
  have hcost : MemLp (fun t : ℝ => frequencyCost sharp m ell F (SourceResolventBandLimit.line μ t)
      (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g k) 2 := by
    simpa only [frequencyCost,SourceResolventBandLimit.line_im,smul_eq_mul] using! hm
  simpa only [Real.norm_eq_abs,sq_abs] using!
    (memLp_two_iff_integrable_sq_norm hcost.aestronglyMeasurable).mp hcost

theorem actual_joint_budget_finite (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ t : ℝ, ENNReal.ofReal
      ((frequencyCost sharp m ell F (SourceResolventBandLimit.line μ t)
        (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g k)^2))<⊤ := by
  rw [←ofReal_integral_eq_lintegral_ofReal (frequency_cost_integrable sharp m ell F μ hμ g k)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_lt_top

end LowEnergy.SourceJointScaleBudget
