import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceGaugeScaleTransport
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarDoubleEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarGaugeEndpoint
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussFockPair
open GaussDiagonalHistory GaussUnitaryHistory SourceMixedNativeReturn
open SourceCutoffDilationWard SourceRelativePowerTail SourceJointScaleBudget SourceEscapeCurrent
open SourceRetardedIncrement FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceGaugeScaleTransport
open scoped InnerProductSpace Topology

private theorem relative_commute {R : Type*} [Ring R] (a u : R) (m ell : ℕ)
    (h : Commute a u) : Commute a ((1-u)^(m+1)-(1-u)^(ell+1)) :=
  (((Commute.one_right a).sub_right h).pow_right (m+1)).sub_right
    (((Commute.one_right a).sub_right h).pow_right (ell+1))

private theorem full_core_flow (sharp : Bool) (t : ℝ) (f : QuantumTest) :
    SourceMixedNativeReturn.fullAction sharp (coreFlow t f)=
      coreFlow t (SourceMixedNativeReturn.fullAction sharp f) := by
  apply DFunLike.ext
  intro z
  cases sharp
  · change GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField z)
      ((Real.exp (18*t) : ℂ) • f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z))=
      (Real.exp (18*t) : ℂ) • GaussYukawaCoefficient.sourceMap
        (GaussNativePotential.scalarField (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z))
          (f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z))
    exact map_smul _ _ _
  · change GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z)
      ((Real.exp (18*t) : ℂ) • f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z))=
      (Real.exp (18*t) : ℂ) • GaussFullHamiltonian.adjointMap
        (GaussNativePotential.scalarField (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z))
          (f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z))
    exact map_smul _ _ _

private theorem inverse_flow (t : ℝ) :
    Commute (coreFlow t) GaussRadialDomain.inverseAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (Real.exp (18*t) : ℂ) •
    ((GaussRadialDomain.reciprocal (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z) : ℂ) •
      f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z))=
    (GaussRadialDomain.reciprocal z : ℂ) •
      ((Real.exp (18*t) : ℂ) • f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z))
  exact smul_comm _ _ _

private theorem insertion_flow (sharp : Bool) (m ell : ℕ) (t : ℝ) (f : QuantumTest) :
    SourceScalarDoubleEndpoint.fullInsertion sharp m ell (coreFlow t f)=
      coreFlow t (SourceScalarDoubleEndpoint.fullInsertion sharp m ell f) := by
  have ht := relative_commute (R := SourceCoframeVolumeCurrent.CoreEnd) (coreFlow t)
    GaussRadialDomain.inverseAction m ell (inverse_flow t)
  have he := LinearMap.congr_fun ht.eq f
  change coreFlow t (SourceMixedNativeReturn.thetaAction m ell f)=
    SourceMixedNativeReturn.thetaAction m ell (coreFlow t f) at he
  change SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (coreFlow t f))=_
  rw [←he,full_core_flow]
  rfl

/-- The literal full insertion commutes with the actual weighted whole-H gauge flow. -/
theorem actual_increment_gauge_commute (sharp : Bool) (m ell : ℕ) (t : ℝ) :
    Commute (SourceEscapeSeedTail.actualIncrement sharp m ell)
      (hilbertFlow t).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine SourceCoframeScaleTransport.embed_dense.induction_on
    (p := fun y : H => SourceEscapeSeedTail.actualIncrement sharp m ell (hilbertFlow t y)=
      hilbertFlow t (SourceEscapeSeedTail.actualIncrement sharp m ell y)) x ?_ ?_
  · exact isClosed_eq ((SourceEscapeSeedTail.actualIncrement sharp m ell).continuous.comp (hilbertFlow t).continuous)
      ((hilbertFlow t).continuous.comp (SourceEscapeSeedTail.actualIncrement sharp m ell).continuous)
  · intro f
    rw [hilbertFlow_on_core,literal_increment_core,literal_increment_core,hilbertFlow_on_core]
    have h := congrArg embed (insertion_flow sharp m ell t f)
    simpa only [SourceScalarDoubleEndpoint.fullInsertion,literal_full_return] using! h

def wholeDouble (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) : H →L[ℂ] H :=
  let C := GaussGradedCompression.compression F
  let B := SourceEscapeSeedTail.actualIncrement sharp m ell
  finiteResolvent F z*(C*(C*B-B*C)-(C*B-B*C)*C)*finiteResolvent F z

private theorem read_full (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    sourceRead F g (SourceScalarDoubleEndpoint.fullInsertion sharp m ell)=
      SourceEscapeSeedTail.actualIncrement sharp m ell*(inputSpan F g).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  let q := coreEquiv.symm (Submodule.inclusion (input_span_core F g)
    ((inputSpan F g).orthogonalProjectionOnto x))
  have h := literal_increment_core sharp m ell q
  have hf := congrArg embed (LinearMap.congr_fun (literal_full_return sharp m ell) q)
  have hq : embed q=(inputSpan F g).starProjection x :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply
      (Submodule.inclusion (input_span_core F g) ((inputSpan F g).orthogonalProjectionOnto x)))
  change embed (SourceScalarDoubleEndpoint.fullInsertion sharp m ell q)=
    SourceEscapeSeedTail.actualIncrement sharp m ell ((inputSpan F g).starProjection x)
  rw [←hq]
  exact hf.symm.trans h.symm

private theorem projection_left (F : Index) (g : diagonal.domain) :
    (inputSpan F g).starProjection*GaussGradedCompression.compression F=GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg Subtype.val ((inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨GaussGradedCompression.compression F x,
      Submodule.mem_sup_left (compression_mem_support F x)⟩)

private theorem projection_right (F : Index) (g : diagonal.domain) :
    GaussGradedCompression.compression F*(inputSpan F g).starProjection=GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have hy : GaussGradedCompression.compression F y∈inputSpan F g := Submodule.mem_sup_left (compression_mem_support F y)
  exact (GaussGradedCompression.compression_pair F y _).symm.trans
    ((Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨GaussGradedCompression.compression F y,hy⟩ x).trans
      (GaussGradedCompression.compression_pair F y x))

private theorem double_projection {R : Type*} [Ring R] (c b p : R)
    (hpc : p*c=c) (hcp : c*p=c) :
    c*(c*(b*p)-(b*p)*c)-(c*(b*p)-(b*p)*c)*c=(c*(c*b-b*c)-(c*b-b*c)*c)*p := by
  have hcpc : c*p*c=c*c := by rw [hcp]
  noncomm_ring [hpc,hcp,hcpc]

private theorem projected_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c r b p : E →L[ℂ] E) (g k : E) (hpc : p*c=c) (hcp : c*p=c) (hp : p (r g)=r g) :
    inner ℂ k (r ((c*(c*(b*p)-(b*p)*c)-(c*(b*p)-(b*p)*c)*c) (r g)))=
      inner ℂ k ((r*(c*(c*b-b*c)-(c*b-b*c)*c)*r) g) := by
  have h := congrArg (fun A : E →L[ℂ] E => A (r g)) (double_projection c b p hpc hcp)
  change _=(c*(c*b-b*c)-(c*b-b*c)*c) (p (r g)) at h
  rw [hp] at h
  exact congrArg (fun x : E => inner ℂ k (r x)) h

theorem actual_whole_return (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    SourceScalarDoubleEndpoint.doubleResponse sharp m ell F g k z=
      inner ℂ (k : H) (wholeDouble sharp m ell F z (g : H)) := by
  let C := GaussGradedCompression.compression F
  let R := finiteResolvent F z
  have h := congrArg (fun A : H →L[ℂ] H => inner ℂ (k : H)
    (R ((C*(C*A-A*C)-(C*A-A*C)*C) (R (g : H))))) (read_full sharp m ell F g)
  exact h.trans (projected_pair (E := H) C R _ _ (g : H) (k : H)
    (projection_left F g) (projection_right F g)
    (congrArg Subtype.val ((inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨R (g : H),resolvent_input_span F z hz g⟩)))

def orbitDouble (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (t : ℝ) : H →L[ℂ] H :=
  let C := compressionOrbitJet F 0 t
  let R := resolventOrbitJet F z 0 t
  let B := SourceEscapeSeedTail.actualIncrement sharp m ell
  R*(C*(C*B-B*C)-(C*B-B*C)*C)*R

private theorem fixed_conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E ≃ₗᵢ[ℂ] E) (B : E →L[ℂ] E)
    (h : Commute B U.toContinuousLinearEquiv.toContinuousLinearMap) : U.conjStarAlgEquiv B=B := by
  apply ContinuousLinearMap.ext
  intro x
  change U (B (U.symm x))=B x
  have he := congrArg (fun A : E →L[ℂ] E => A (U.symm x)) h.eq
  change B (U (U.symm x))=U (B (U.symm x)) at he
  rw [U.apply_symm_apply] at he
  exact he.symm

/-- Both moving resolvents and compressions are the actual orbit of this same full double current. -/
theorem actual_double_gauge_orbit (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (t : ℝ) :
    orbitDouble sharp m ell F z t=(hilbertFlow t).conjStarAlgEquiv (wholeDouble sharp m ell F z) := by
  have hb := fixed_conjugate (hilbertFlow t) _ (actual_increment_gauge_commute sharp m ell t)
  simp only [orbitDouble,wholeDouble,actual_moving_compression,actual_moving_resolvent F z hz,
    map_mul,map_sub,hb]

private theorem conjugate_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E ≃ₗᵢ[ℂ] E) (T : E →L[ℂ] E) (g k : E) :
    inner ℂ k (U.conjStarAlgEquiv T g)=inner ℂ (U.symm k) (T (U.symm g)) := by
  change inner ℂ k (U (T (U.symm g)))=_
  have h := U.inner_map_map (U.symm k) (T (U.symm g))
  rw [U.apply_symm_apply] at h
  exact h

private theorem inverse_core_flow (t : ℝ) (f : QuantumTest) :
    (hilbertFlow t).symm (embed f)=embed (coreFlow (-t) f) := by
  apply (hilbertFlow t).injective
  rw [LinearIsometryEquiv.apply_symm_apply,←hilbertFlow_on_core,hilbertFlow_add,add_neg_cancel,hilbertFlow_zero]

def gaugeProfile (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (g k : QuantumTest) (t : ℝ) : ℂ := inner ℂ (embed k) (orbitDouble sharp m ell F z t (embed g))

/-- The actual gauge orbit profile returns to the original fixed-F source profile. -/
theorem actual_gauge_profile (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : QuantumTest) (t : ℝ) :
    gaugeProfile sharp m ell F z g k t=
      SourceScalarDoubleEndpoint.doubleResponse sharp m ell F
        (coreEquiv (coreFlow (-t) g)) (coreEquiv (coreFlow (-t) k)) z := by
  unfold gaugeProfile
  rw [actual_double_gauge_orbit sharp m ell F z hz,conjugate_pair,inverse_core_flow,inverse_core_flow]
  have h := actual_whole_return sharp m ell F (coreEquiv (coreFlow (-t) g))
    (coreEquiv (coreFlow (-t) k)) z hz
  have hv (f : QuantumTest) : (coreEquiv f : H)=embed f := rfl
  simpa only [hv] using! h.symm

end LowEnergy.SourceScalarGaugeEndpoint
