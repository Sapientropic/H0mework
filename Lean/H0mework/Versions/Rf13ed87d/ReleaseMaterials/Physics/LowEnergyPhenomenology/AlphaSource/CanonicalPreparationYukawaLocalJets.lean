import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationYukawaCutoffField
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationLocalCurrentCarrier

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumYukawaTransport
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDensityCore GaussFockPair GaussFockWeights
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse PreparationVacuumSourceActionJets
open PreparationVacuumGradedTransport PreparationVacuumNonlinearFieldCurve CanonicalGradedSpatialSource
open CanonicalGradedLocalCurrent
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators Distributions

abbrev Fiber := FockFiber →L[ℂ] FockFiber
local instance : NormedAlgebra ℝ Fiber := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

def localCoefficient (f : Field289) (n : ℕ) (phi : Localizer) (u : Parameter) : Fiber :=
  (phi u.2:ℂ) • cutFiber n (fieldCoordinateCurve f u.1 u.2)

theorem localCoefficient_zero (f : Field289) (n : ℕ) (phi : Localizer) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport phi) : localCoefficient f n phi (r,z)=0 := by
  simp only [localCoefficient,image_eq_zero_of_notMem_tsupport outside,Complex.ofReal_zero]
  exact zero_smul ℂ (cutFiber n (fieldCoordinateCurve f r z))

theorem localCoefficient_smooth (f : Field289) (n : ℕ) (phi : Localizer) : ContDiff ℝ ∞ (localCoefficient f n phi) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases inside : u.2∈tsupport phi
  · have first:=Complex.ofRealCLM.contDiff.contDiffAt.comp u (phi.contDiff.contDiffAt.comp u contDiffAt_snd)
    have second:=(cutFiber_smooth n).contDiffAt.comp u (field_curve_smooth f u.1 ⟨u.2,phi.tsupport_subset inside⟩)
    exact first.smul second
  · apply (contDiffAt_const (c:=(0:Fiber))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isClosed_tsupport phi |>.isOpen_compl.mem_nhds inside)] with v hv
    exact localCoefficient_zero f n phi v.1 v.2 hv

def fiberPartial (A : Parameter → Fiber) (u : Parameter) : Fiber := fderiv ℝ A u (1,0)

def coefficientJet (f : Field289) (n : ℕ) (phi : Localizer) : ℕ → Parameter → Fiber :=
  Nat.rec (localCoefficient f n phi) (fun _ previous=>fiberPartial previous)

theorem coefficientJet_smooth (f : Field289) (n k : ℕ) (phi : Localizer) : ContDiff ℝ ∞ (coefficientJet f n phi k) := by
  induction k with
  | zero=>exact localCoefficient_smooth f n phi
  | succ k ih=>exact (ih.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

theorem partial_zero (A : Parameter → Fiber) (phi : Localizer)
    (zero : ∀r z,z∉tsupport phi → A (r,z)=0) (r : ℝ) (z : SourceCoordinateSlice) (outside : z∉tsupport phi) :
    fiberPartial A (r,z)=0 := by
  have same : A=ᶠ[𝓝 (r,z)] fun _=>0 := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isClosed_tsupport phi |>.isOpen_compl.mem_nhds outside)] with v hv
    exact zero v.1 v.2 hv
  rw [fiberPartial,same.fderiv_eq]
  simp

theorem coefficientJet_zero (f : Field289) (n k : ℕ) (phi : Localizer) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport phi) : coefficientJet f n phi k (r,z)=0 := by
  induction k generalizing r z with
  | zero=>exact localCoefficient_zero f n phi r z outside
  | succ k ih=>exact partial_zero _ phi (fun r z hz=>ih r z hz) r z outside

theorem coefficientJet_derivative (f : Field289) (n k : ℕ) (phi : Localizer) (r : ℝ) (z : SourceCoordinateSlice) :
    HasDerivAt (fun s=>coefficientJet f n phi k (s,z)) (coefficientJet f n phi (k+1) (r,z)) r := by
  have h:=((coefficientJet_smooth f n k phi).differentiable (by simp)).differentiableAt.hasFDerivAt (x:=(r,z))
  have generated:=h.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r z))
  convert! generated using 1

def weightBracket (w : ℕ → ℂ) : Fiber →L[ℝ] Fiber :=
  ((ContinuousLinearMap.mul ℂ Fiber (weight w))-(ContinuousLinearMap.mul ℂ Fiber).flip (weight w)).restrictScalars ℝ

theorem constraint_partial (L : Fiber →L[ℝ] Fiber) (A : Parameter → Fiber) (smooth : ContDiff ℝ ∞ A)
    (zero : ∀u,L (A u)=0) (u : Parameter) : L (fiberPartial A u)=0 := by
  have h:=L.hasFDerivAt.comp u (smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have same : (L ∘ A)=(fun _ : Parameter=>(0:Fiber)):=funext zero
  have derived:=congrArg (fun D : Parameter →L[ℝ] Fiber=>D (1,0)) h.fderiv
  rw [same] at derived
  have constant : fderiv ℝ (fun _ : Parameter=>(0:Fiber)) u=0 := (hasFDerivAt_const (0:Fiber) u).fderiv
  rw [constant] at derived
  exact derived.symm

theorem coefficientJet_number (f : Field289) (n k : ℕ) (phi : Localizer) (u : Parameter) (w : ℕ → ℂ) :
    Commute (weight w) (coefficientJet f n phi k u) := by
  induction k generalizing u with
  | zero=>exact (cutFiber_number n (fieldCoordinateCurve f u.1 u.2) w).smul_right (phi u.2:ℂ)
  | succ k ih=>
    have h:=constraint_partial (weightBracket w) (coefficientJet f n phi k) (coefficientJet_smooth f n k phi)
      (fun v=>sub_eq_zero.mpr (ih v).eq) u
    exact sub_eq_zero.mp h

def jetTest (f : Field289) (n k : ℕ) (phi : Localizer) (r : ℝ) : 𝓓(physicalChart,Fiber) where
  toFun z:=coefficientJet f n phi k (r,z)
  contDiff':=(coefficientJet_smooth f n k phi).comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport':=by
    apply phi.hasCompactSupport.of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_tsupport phi)
    intro z hz;by_contra outside;exact hz (coefficientJet_zero f n k phi r z outside)
  tsupport_subset':=by
    apply Set.Subset.trans _ phi.tsupport_subset
    apply closure_minimal _ (isClosed_tsupport phi)
    intro z hz;by_contra outside;exact hz (coefficientJet_zero f n k phi r z outside)

def jetOperator (f : Field289) (n k : ℕ) (phi : Localizer) (r : ℝ) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (fun z=>coefficientJet f n phi k (r,z))
    (fun _=>(jetTest f n k phi r).contDiff.contDiffAt)
    (fun z w=>coefficientJet_number f n k phi (r,z.val) w)
    ‖(jetTest f n k phi r : BoundedContinuousFunction SourceCoordinateSlice Fiber)‖ (by exact norm_nonneg (jetTest f n k phi r : BoundedContinuousFunction SourceCoordinateSlice Fiber))
    (fun z v=>((coefficientJet f n phi k (r,z.val)).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      ((jetTest f n k phi r : BoundedContinuousFunction SourceCoordinateSlice Fiber).norm_coe_le_norm z.val) (norm_nonneg v)))

theorem jetOperator_core (f : Field289) (n k : ℕ) (phi : Localizer) (r : ℝ) (a : QuantumTest) :
    jetOperator f n k phi r (embed a)=embed (localMultiplier (fun z=>coefficientJet f n phi k (r,z))
      (fun _=>(jetTest f n k phi r).contDiff.contDiffAt) a) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ a

theorem jetBound_exists (f : Field289) (n k : ℕ) (phi : Localizer) (center : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀r z,|r-center|≤1 → ‖coefficientJet f n phi k (r,z)‖≤C := by
  obtain ⟨C,hC⟩:=(isCompact_Icc.prod phi.hasCompactSupport).exists_bound_of_continuousOn
    ((coefficientJet_smooth f n k phi).continuous.continuousOn :
      ContinuousOn (coefficientJet f n phi k) (Icc (center-1) (center+1) ×ˢ tsupport phi))
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro r z small
  by_cases inside : z∈tsupport phi
  · have interval : r∈Icc (center-1) (center+1) := by
      have bounds:=abs_le.mp small;constructor <;>linarith
    exact (hC (r,z) ⟨interval,inside⟩).trans (le_max_right _ _)
  · rw [coefficientJet_zero f n k phi r z inside,norm_zero]
    exact le_max_left _ _

def jetBound (f : Field289) (n k : ℕ) (phi : Localizer) (center : ℝ) : ℝ :=
  (jetBound_exists f n k phi center).choose

theorem jetBound_nonnegative (f : Field289) (n k : ℕ) (phi : Localizer) (center : ℝ) :
    0≤jetBound f n k phi center := (jetBound_exists f n k phi center).choose_spec.1

theorem jetBound_controls (f : Field289) (n k : ℕ) (phi : Localizer) (center r : ℝ)
    (z : SourceCoordinateSlice) (small : |r-center|≤1) :
    ‖coefficientJet f n phi k (r,z)‖≤jetBound f n k phi center :=
  (jetBound_exists f n k phi center).choose_spec.2 r z small

theorem coefficient_remainder (f : Field289) (n k : ℕ) (phi : Localizer) (center h : ℝ)
    (small : |h|≤1) (z : SourceCoordinateSlice) :
    ‖coefficientJet f n phi k (center+h,z)-coefficientJet f n phi k (center,z)-
      h • coefficientJet f n phi (k+1) (center,z)‖≤jetBound f n (k+2) phi center*‖h‖^2 := by
  have generated:=quadratic_of_second_derivative
    (fun t=>coefficientJet f n phi k (center+t,z))
    (fun t=>coefficientJet f n phi (k+1) (center+t,z))
    (fun t=>coefficientJet f n phi (k+2) (center+t,z))
    1 (jetBound f n (k+2) phi center) zero_le_one (jetBound_nonnegative f n (k+2) phi center)
    (fun t _=>(coefficientJet_derivative f n k phi (center+t) z).comp_const_add center t)
    (fun t _=>(coefficientJet_derivative f n (k+1) phi (center+t) z).comp_const_add center t)
    (fun t ht=>jetBound_controls f n (k+2) phi center (center+t) z (by simpa only [add_sub_cancel_left] using ht)) h small
  simpa only [add_zero] using generated

theorem jetOperator_remainder (f : Field289) (n k : ℕ) (phi : Localizer) (center h : ℝ) (small : |h|≤1) :
    ‖jetOperator f n k phi (center+h)-jetOperator f n k phi center-h • jetOperator f n (k+1) phi center‖≤
      jetBound f n (k+2) phi center*‖h‖^2 := by
  let error:=fun z=>coefficientJet f n phi k (center+h,z)-coefficientJet f n phi k (center,z)-
    h • coefficientJet f n phi (k+1) (center,z)
  have smooth : ContDiff ℝ ∞ error :=
    ((jetTest f n k phi (center+h)).contDiff.sub (jetTest f n k phi center).contDiff).sub
      ((jetTest f n (k+1) phi center).contDiff.const_smul h)
  have commutes (z : physicalChart) (w : ℕ → ℂ) : Commute (weight w) (error z.val) :=
    ((coefficientJet_number f n k phi (center+h,z.val) w).sub_right
      (coefficientJet_number f n k phi (center,z.val) w)).sub_right
      (commute_real_smul _ _ (coefficientJet_number f n (k+1) phi (center,z.val) w) h)
  have nonnegative : 0≤jetBound f n (k+2) phi center*‖h‖^2 :=
    mul_nonneg (jetBound_nonnegative f n (k+2) phi center) (sq_nonneg _)
  have bound (z : physicalChart) (v : FockFiber) : ‖error z.val v‖≤(jetBound f n (k+2) phi center*‖h‖^2)*‖v‖ :=
    ((error z.val).le_opNorm v).trans (mul_le_mul_of_nonneg_right (coefficient_remainder f n k phi center h small z.val) (norm_nonneg v))
  apply core_operator_bound _ _ nonnegative
  intro a
  have readback : localMultiplier error (fun _=>smooth.contDiffAt) a=
      localMultiplier (fun z=>coefficientJet f n phi k (center+h,z)) (fun _=>(jetTest f n k phi (center+h)).contDiff.contDiffAt) a-
      localMultiplier (fun z=>coefficientJet f n phi k (center,z)) (fun _=>(jetTest f n k phi center).contDiff.contDiffAt) a-
      h • localMultiplier (fun z=>coefficientJet f n phi (k+1) (center,z)) (fun _=>(jetTest f n (k+1) phi center).contDiff.contDiffAt) a := by
    apply DFunLike.ext;intro z
    change (error z) (a z)=_
    simp only [error,sub_apply,smul_apply]
    rfl
  have estimate:=GaussBoundedMultiplier.action_bound error (fun _=>smooth.contDiffAt) commutes
    (jetBound f n (k+2) phi center*‖h‖^2) nonnegative bound a
  rw [readback,embed_sub_real,map_sub] at estimate
  simpa only [sub_apply,smul_apply,jetOperator_core] using estimate

theorem jetOperator_derivative (f : Field289) (n k : ℕ) (phi : Localizer) (center : ℝ) :
    HasDerivAt (jetOperator f n k phi) (jetOperator f n (k+1) phi center) center := by
  rw [hasDerivAt_iff_tendsto]
  let M:=jetBound f n (k+2) phi center
  have convergence : Tendsto (fun r : ℝ=>M*‖r-center‖) (𝓝 center) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ=>M*‖r-center‖) := by fun_prop
    simpa only [sub_self,norm_zero,mul_zero] using hc.tendsto center
  apply squeeze_zero' (Eventually.of_forall (fun r=>mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))) ?_ convergence
  have near : ∀ᶠr in 𝓝 center,|r-center|≤1 := by
    filter_upwards [Metric.ball_mem_nhds center (by norm_num : (0:ℝ)<1)] with r hr
    exact (by simpa only [Metric.mem_ball,Real.dist_eq] using hr : |r-center|<1).le
  filter_upwards [near] with r hr
  have bound:=mul_le_mul_of_nonneg_left (jetOperator_remainder f n k phi center (r-center) hr)
    (inv_nonneg.mpr (norm_nonneg (r-center)))
  have scalar : ‖r-center‖⁻¹*(M*‖r-center‖^2)=M*‖r-center‖ := by
    by_cases zero : ‖r-center‖=0
    · simp only [zero,inv_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · field_simp
  rw [add_sub_cancel] at bound
  exact bound.trans_eq scalar

open GaussNativePotential PreparationVacuumPreparedCurrent
open PreparationChartGuard PreparationVacuumNativeClosure GaussComposite
open scoped Manifold
open NativeHistoryGrade (Label projection)
local instance : Fintype Label:=Fintype.ofFinite _

def finiteSourceSet (p : PhysicalMomentum) (F : Index) : Set SourceCoordinateSlice :=
  tsupport actualNativeLocalizer ∪ ⋃ i : PhysicalBasisIndex p F,tsupport (bareTest p F i)

theorem finiteSourceSet_compact (p : PhysicalMomentum) (F : Index) : IsCompact (finiteSourceSet p F) :=
  actualNativeLocalizer.hasCompactSupport.union (isCompact_iUnion fun i=>(bareTest p F i).hasCompactSupport)

theorem finiteSourceSet_chart (p : PhysicalMomentum) (F : Index) : finiteSourceSet p F ⊆ physicalChart := by
  rintro z (hz|hz)
  · exact actualNativeLocalizer.tsupport_subset hz
  · obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hz
    exact (bareTest p F i).tsupport_subset hi

theorem finiteRetainer_exists (p : PhysicalMomentum) (F : Index) :
    ∃phi : Localizer,(∀z∈finiteSourceSet p F,phi z=1) ∧ (∀z,phi z∈Icc (0:ℝ) 1) := by
  obtain ⟨K,compact,covers,inside⟩:=exists_compact_between (finiteSourceSet_compact p F) physicalChart.isOpen (finiteSourceSet_chart p F)
  obtain ⟨phi,one,zero,bounded⟩:=exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,SourceCoordinateSlice)) (n:=(⊤:ℕ∞)) (finiteSourceSet_compact p F).isClosed covers
  have support : tsupport phi⊆K := by
    apply closure_minimal _ compact.isClosed
    intro z hz
    by_contra outside
    exact hz (zero z outside)
  refine ⟨⟨phi,phi.contMDiff.contDiff,compact.of_isClosed_subset isClosed_closure support,support.trans inside⟩,?_,bounded⟩
  intro z hz
  exact one.self_of_nhdsSet z hz

def finiteRetainer (p : PhysicalMomentum) (F : Index) : Localizer :=(finiteRetainer_exists p F).choose

theorem finiteRetainer_one (p : PhysicalMomentum) (F : Index) (z : SourceCoordinateSlice) (hz : z∈finiteSourceSet p F) :
    finiteRetainer p F z=1 :=(finiteRetainer_exists p F).choose_spec.1 z hz

theorem finiteRetainer_range (p : PhysicalMomentum) (F : Index) (z : SourceCoordinateSlice) :
    finiteRetainer p F z∈Icc (0:ℝ) 1 :=(finiteRetainer_exists p F).choose_spec.2 z

def retainFiber (p : PhysicalMomentum) (F : Index) (z : SourceCoordinateSlice) : Fiber :=
  (finiteRetainer p F z:ℂ) • ContinuousLinearMap.id ℂ FockFiber

theorem retainFiber_smooth (p : PhysicalMomentum) (F : Index) : ContDiff ℝ ∞ (retainFiber p F) :=
  (Complex.ofRealCLM.contDiff.comp (finiteRetainer p F).contDiff).smul contDiff_const

theorem retainFiber_number (p : PhysicalMomentum) (F : Index) (z : SourceCoordinateSlice) (w : ℕ→ℂ) :
    Commute (weight w) (retainFiber p F z) :=(Commute.one_right _).smul_right _

theorem retainFiber_bound (p : PhysicalMomentum) (F : Index) (z : SourceCoordinateSlice) (v : FockFiber) :
    ‖retainFiber p F z v‖≤(1:ℝ)*‖v‖ := by
  change ‖(finiteRetainer p F z:ℂ) • v‖≤_
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (finiteRetainer_range p F z).1]
  exact mul_le_mul_of_nonneg_right (finiteRetainer_range p F z).2 (norm_nonneg v)

def retainer (p : PhysicalMomentum) (F : Index) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (retainFiber p F) (fun _=>(retainFiber_smooth p F).contDiffAt)
    (fun z w=>retainFiber_number p F z.val w) 1 zero_le_one (fun z v=>retainFiber_bound p F z.val v)

def retainTest (p : PhysicalMomentum) (F : Index) : QuantumTest →ₗ[ℂ] QuantumTest :=
  scalarMultiplier (fun z=>(finiteRetainer p F z:ℂ)) (Complex.ofRealCLM.contDiff.comp (finiteRetainer p F).contDiff)

theorem retainer_core (p : PhysicalMomentum) (F : Index) (a : QuantumTest) :
    retainer p F (embed a)=embed (retainTest p F a) :=GaussBoundedMultiplier.extension_core _ _ _ _ _ _ a

theorem retainTest_exact (p : PhysicalMomentum) (F : Index) (a : QuantumTest)
    (support : tsupport a⊆finiteSourceSet p F) : retainTest p F a=a := by
  apply DFunLike.ext;intro z
  change (finiteRetainer p F z:ℂ) • a z=a z
  by_cases inside : z∈tsupport a
  · rw [finiteRetainer_one p F z (support inside),Complex.ofReal_one,one_smul]
  · rw [image_eq_zero_of_notMem_tsupport inside,smul_zero]

theorem retainer_basis (p : PhysicalMomentum) (F : Index) (i : PhysicalBasisIndex p F) :
    retainer p F (physicalBasis p F i).val=(physicalBasis p F i).val := by
  rw [←bareTest_embed,retainer_core,retainTest_exact]
  intro z hz
  exact Or.inr (Set.mem_iUnion.mpr ⟨i,hz⟩)

theorem retainer_projection (p : PhysicalMomentum) (F : Index) (g : Label) :
    Commute (retainer p F) (projection g) := by
  apply GaussYukawaGrade.core_ext
  intro a
  change retainer p F (projection g (embed a))=projection g (retainer p F (embed a))
  rw [←GaussCoreLabel.embed_project,retainer_core,retainer_core,←GaussCoreLabel.embed_project]
  apply congrArg embed
  apply DFunLike.ext;intro z
  change (finiteRetainer p F z:ℂ) • (GaussCoreLabel.fiberPiece g (a z))=
    GaussCoreLabel.fiberPiece g ((finiteRetainer p F z:ℂ) • a z)
  exact (map_smul _ _ _).symm

theorem retainer_frame (p : PhysicalMomentum) (F : Index) (i : Label × PhysicalBasisIndex p F) :
    retainer p F (physicalFrame p F i)=physicalFrame p F i := by
  change retainer p F (projection i.1 (physicalBasis p F i.2).val)=_
  rw [show retainer p F (projection i.1 (physicalBasis p F i.2).val)=
    projection i.1 (retainer p F (physicalBasis p F i.2).val) from
    congrArg (fun A : H →L[ℂ] H=>A (physicalBasis p F i.2).val) (retainer_projection p F i.1).eq,
    retainer_basis]
  rfl

 theorem retainer_assembly (p : PhysicalMomentum) (F : Index) (entries : PhysicalBasisIndex p F→PhysicalBasisIndex p F→ℂ) :
    retainer p F*sourceAssembly p F entries=sourceAssembly p F entries := by
  apply ContinuousLinearMap.ext;intro x
  simp only [mul_apply_eq_comp,sourceAssembly,sum_apply,smul_apply,InnerProductSpace.rankOne_apply,map_sum,map_smul,retainer_frame]

theorem retainer_sourceCut (p : PhysicalMomentum) (F : Index) (a : QuantumTest) :
    retainTest p F (sourceCut a)=sourceCut a := by
  apply DFunLike.ext;intro z
  change (finiteRetainer p F z:ℂ) • ((actualNativeLocalizer z:ℂ) • a z)=(actualNativeLocalizer z:ℂ) • a z
  by_cases inside : z∈tsupport actualNativeLocalizer
  · rw [finiteRetainer_one p F z (Or.inl inside),Complex.ofReal_one,one_smul]
  · rw [image_eq_zero_of_notMem_tsupport inside,Complex.ofReal_zero,zero_smul,smul_zero]

def retainedSpace (p : PhysicalMomentum) (F : Index) : Submodule ℂ H :=
  LinearMap.ker ((retainer p F-1).toLinearMap)

theorem retainedSpace_iff (p : PhysicalMomentum) (F : Index) (x : H) :
    x∈retainedSpace p F ↔ retainer p F x=x :=by
  change retainer p F x-x=0 ↔ _
  exact sub_eq_zero

theorem retainedSpace_closed (p : PhysicalMomentum) (F : Index) : IsClosed (retainedSpace p F:Set H) :=
  (retainer p F-1).isClosed_ker

theorem sourceCarrier_retained (p : PhysicalMomentum) (F : Index) : localCarrier≤retainedSpace p F := by
  apply Submodule.topologicalClosure_minimal _ ?_ (retainedSpace_closed p F)
  rintro x ⟨a,rfl⟩
  apply (retainedSpace_iff p F _).mpr
  change retainer p F (embed (sourceCut a))=embed (sourceCut a)
  rw [retainer_core,retainer_sourceCut]

theorem sourceLeg_retained (p : PhysicalMomentum) (F : Index) (addition : Bool) (a s : Fin 2)
    (x : sourceLocalSpace) :
    sourceLeg addition a s x∈retainedSpace p F :=sourceCarrier_retained p F (sourceLeg_mem addition a s x)

theorem retainer_cutoff (f : Field289) (n : ℕ) (p : PhysicalMomentum) (F : Index) (r : ℝ) :
    Commute (retainer p F) (fieldCutoff f n r) := by
  apply GaussYukawaGrade.core_ext;intro a
  change retainer p F (fieldCutoff f n r (embed a))=fieldCutoff f n r (retainer p F (embed a))
  rw [fieldCutoff_core,retainer_core,retainer_core,fieldCutoff_core]
  apply congrArg embed;apply DFunLike.ext;intro z
  change (finiteRetainer p F z:ℂ) • cutFiber n (fieldCoordinateCurve f r z) (a z)=
    cutFiber n (fieldCoordinateCurve f r z) ((finiteRetainer p F z:ℂ) • a z)
  exact (map_smul _ _ _).symm

theorem fieldCutoff_retained (f : Field289) (n : ℕ) (p : PhysicalMomentum) (F : Index) (r : ℝ)
    (x : H) (hx : x∈retainedSpace p F) : fieldCutoff f n r x∈retainedSpace p F := by
  apply (retainedSpace_iff p F _).mpr
  have h:=congrArg (fun A : H →L[ℂ] H=>A x) (retainer_cutoff f n p F r).eq
  change retainer p F (fieldCutoff f n r x)=fieldCutoff f n r (retainer p F x) at h
  exact h.trans (congrArg (fieldCutoff f n r) ((retainedSpace_iff p F x).mp hx))

theorem jetOperator_cutoff (f : Field289) (n : ℕ) (p : PhysicalMomentum) (F : Index) (r : ℝ) :
    jetOperator f n 0 (finiteRetainer p F) r=retainer p F*fieldCutoff f n r := by
  apply GaussYukawaGrade.core_ext;intro a
  change jetOperator f n 0 (finiteRetainer p F) r (embed a)=retainer p F (fieldCutoff f n r (embed a))
  rw [jetOperator_core,fieldCutoff_core,retainer_core]
  rfl

/-- A differentiable extension on the same Hilbert space, equal to the original
cutoff at zero and to its true field variation on the generated retained space. -/
def localY (f : Field289) (n : ℕ) (p : PhysicalMomentum) (F : Index) (r : ℝ) : H →L[ℂ] H :=
  FullYSourceCutoffVolterra.cutoff n+jetOperator f n 0 (finiteRetainer p F) r-jetOperator f n 0 (finiteRetainer p F) 0

theorem localY_zero (f : Field289) (n : ℕ) (p : PhysicalMomentum) (F : Index) :
    localY f n p F 0=FullYSourceCutoffVolterra.cutoff n :=add_sub_cancel_right _ _

theorem localY_derivative (f : Field289) (n : ℕ) (p : PhysicalMomentum) (F : Index) (r : ℝ) :
    HasDerivAt (localY f n p F) (jetOperator f n 1 (finiteRetainer p F) r) r := by
  convert! ((jetOperator_derivative f n 0 (finiteRetainer p F) r).const_add
    (FullYSourceCutoffVolterra.cutoff n)).sub_const (jetOperator f n 0 (finiteRetainer p F) 0) using 1

theorem localY_source (f : Field289) (n : ℕ) (p : PhysicalMomentum) (F : Index) (r : ℝ)
    (x : H) (hx : x∈retainedSpace p F) : localY f n p F r x=fieldCutoff f n r x := by
  have hr:=(retainedSpace_iff p F _).mp (fieldCutoff_retained f n p F r x hx)
  have h0:=(retainedSpace_iff p F _).mp (fieldCutoff_retained f n p F 0 x hx)
  rw [fieldCutoff_zero] at h0
  simp only [localY,sub_apply,add_apply,jetOperator_cutoff,mul_apply_eq_comp,hr,fieldCutoff_zero,h0,add_sub_cancel_left]

end LowEnergy.PreparationVacuumYukawaTransport
