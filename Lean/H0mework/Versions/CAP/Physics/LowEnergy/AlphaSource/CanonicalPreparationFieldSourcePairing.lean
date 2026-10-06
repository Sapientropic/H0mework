import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldSourceFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullFieldRiesz
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge GaussLiveMomentum
open GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussFockPair
open PreparationVacuumSourceActionJets PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open CanonicalGradedSpatialSource MeasureTheory Set Filter
open scoped Topology InnerProductSpace BigOperators ContDiff

structure SesqGerm (q : QuantumTest → QuantumTest → ℝ → ℂ) : Prop where
  add_left : ∀a b c,q (a+b) c=ᶠ[𝓝 0] fun r=>q a c r+q b c r
  smul_left : ∀(c:ℂ) a b,q (c • a) b=ᶠ[𝓝 0] fun r=>star c*q a b r
  add_right : ∀a b c,q a (b+c)=ᶠ[𝓝 0] fun r=>q a b r+q a c r
  smul_right : ∀(c:ℂ) a b,q a (c • b)=ᶠ[𝓝 0] fun r=>c*q a b r

namespace SesqGerm
variable {q t : QuantumTest → QuantumTest → ℝ → ℂ}

theorem add (h : SesqGerm q) (k : SesqGerm t) : SesqGerm (fun a b r=>q a b r+t a b r) := by
  constructor
  · intro a b c; filter_upwards [h.add_left a b c,k.add_left a b c] with r hr kr; rw [hr,kr]; try simp only [starRingEnd_apply]
    all_goals ring
  · intro c a b; filter_upwards [h.smul_left c a b,k.smul_left c a b] with r hr kr; rw [hr,kr]; try simp only [starRingEnd_apply]
    all_goals ring
  · intro a b c; filter_upwards [h.add_right a b c,k.add_right a b c] with r hr kr; rw [hr,kr]; try simp only [starRingEnd_apply]
    all_goals ring
  · intro c a b; filter_upwards [h.smul_right c a b,k.smul_right c a b] with r hr kr; rw [hr,kr]; try simp only [starRingEnd_apply]
    all_goals ring

theorem scale (h : SesqGerm q) (z : ℂ) : SesqGerm (fun a b r=>z*q a b r) := by
  constructor
  · intro a b c; filter_upwards [h.add_left a b c] with r hr; rw [hr]; try simp only [starRingEnd_apply]
    all_goals ring
  · intro c a b; filter_upwards [h.smul_left c a b] with r hr; rw [hr]; try simp only [starRingEnd_apply]
    all_goals ring
  · intro a b c; filter_upwards [h.add_right a b c] with r hr; rw [hr]; try simp only [starRingEnd_apply]
    all_goals ring
  · intro c a b; filter_upwards [h.smul_right c a b] with r hr; rw [hr]; try simp only [starRingEnd_apply]
    all_goals ring

theorem precomp (h : SesqGerm q) (A B : QuantumTest →ₗ[ℂ] QuantumTest) :
    SesqGerm (fun a b r=>q (A a) (B b) r) := by
  constructor
  · intro a b c; simpa only [map_add] using h.add_left (A a) (A b) (B c)
  · intro c a b; simpa only [map_smul] using h.smul_left c (A a) (B b)
  · intro a b c; simpa only [map_add] using h.add_right (A a) (B b) (B c)
  · intro c a b; simpa only [map_smul] using h.smul_right c (A a) (B b)

theorem zero : SesqGerm (fun _ _ _=>(0:ℂ)) := by
  constructor <;> intros <;> simp

theorem sum {ι : Type*} (s : Finset ι) (Q : ι → QuantumTest → QuantumTest → ℝ → ℂ)
    (h : ∀i∈s,SesqGerm (Q i)) : SesqGerm (fun a b r=>∑i∈s,Q i a b r) := by
  induction s using Finset.cons_induction with
  | empty => simpa using zero
  | cons i s hi ih =>
    simpa only [Finset.sum_cons] using (h i (by simp)).add (ih (fun j hj=>h j (by simp [hj])))
end SesqGerm

theorem fieldSample_integrable (S : SourceCoordinateSlice → SourceCoordinateSlice → ℂ) (f : Field289) (test : QuantumTest)
    (smooth : ∀r z,z∈physicalChart → fieldCoordinateCurve f r z∈physicalChart →
      ContDiffAt ℝ ∞ (fun u : Parameter=>S u.2 (fieldCoordinateCurve f u.1 u.2)) (r,z))
    (zero : ∀z x,z∉tsupport test → S z x=0) :
    ∀ᶠr in 𝓝 (0:ℝ),Integrable (fun z=>S z (fieldCoordinateCurve f r z)) configurationMeasure := by
  have near : ∀ᶠr in 𝓝 (0:ℝ),|r|<fieldRadius f test :=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f test))
  filter_upwards [near] with r hr
  have full (z : SourceCoordinateSlice) : ContDiffAt ℝ ∞ (fun u : Parameter=>S u.2 (fieldCoordinateCurve f u.1 u.2)) (r,z) := by
    by_cases hz : z∈tsupport test
    · exact smooth r z (test.tsupport_subset hz) (fieldRadius_chart f test r z hr.le hz)
    · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (isClosed_tsupport test |>.isOpen_compl.mem_nhds hz)] with u hu
      exact zero u.2 (fieldCoordinateCurve f u.1 u.2) hu
  exact (continuous_iff_continuousAt.mpr fun z=>(full z).continuousAt.comp
    (continuous_const.prodMk continuous_id).continuousAt).integrable_of_hasCompactSupport
      (test.hasCompactSupport.of_isClosed_subset isClosed_closure
        (slice_support (fun u : Parameter=>S u.2 (fieldCoordinateCurve f u.1 u.2)) (tsupport test)
          (isClosed_tsupport test) (fun r z hz=>zero z _ hz) r))

theorem integral_sesq
    (S : QuantumTest → QuantumTest → SourceCoordinateSlice → SourceCoordinateSlice → ℂ) (f : Field289)
    (al : ∀a b c z x,S (a+b) c z x=S a c z x+S b c z x)
    (sl : ∀(c:ℂ) a b z x,S (c • a) b z x=star c*S a b z x)
    (ar : ∀a b c z x,S a (b+c) z x=S a b z x+S a c z x)
    (sr : ∀(c:ℂ) a b z x,S a (c • b) z x=c*S a b z x)
    (integrable : ∀a b,∀ᶠr in 𝓝 (0:ℝ),Integrable (fun z=>S a b z (fieldCoordinateCurve f r z)) configurationMeasure) :
    SesqGerm (fun a b r=>∫z,S a b z (fieldCoordinateCurve f r z) ∂configurationMeasure) := by
  constructor
  · intro a b c; filter_upwards [integrable a c,integrable b c] with r h k
    simp only [al]; exact integral_add h k
  · intro c a b; exact Filter.Eventually.of_forall (fun r=>by simp only [sl,integral_const_mul])
  · intro a b c; filter_upwards [integrable a b,integrable a c] with r h k
    simp only [ar]; exact integral_add h k
  · intro c a b; exact Filter.Eventually.of_forall (fun r=>by simp only [sr,integral_const_mul])

theorem sampledMomentum_add (v : GaussLiveMomentum.Ambient) (a b : QuantumTest) (z x : SourceCoordinateSlice) :
    sampledMomentum v (a+b) z x=sampledMomentum v a z x+sampledMomentum v b z x := by
  unfold sampledMomentum
  rw [show (⇑(a+b):SourceCoordinateSlice→FockFiber)=(⇑a+⇑b) from rfl,
    fderiv_add (a.contDiff.differentiable (by simp)).differentiableAt (b.contDiff.differentiable (by simp)).differentiableAt]
  simp only [add_apply,Pi.add_apply,map_add,smul_add]
  abel

theorem sampledMomentum_smul (v : GaussLiveMomentum.Ambient) (c : ℂ) (a : QuantumTest) (z x : SourceCoordinateSlice) :
    sampledMomentum v (c • a) z x=c • sampledMomentum v a z x := by
  unfold sampledMomentum
  rw [show (⇑(c • a):SourceCoordinateSlice→FockFiber)=(c • ⇑a) from rfl,
    fderiv_const_smul (a.contDiff.differentiable (by simp)).differentiableAt c]
  simp only [smul_apply,Pi.smul_apply,map_smul,←smul_add]
  exact smul_comm _ _ _

theorem pairSample_add_left (x : SourceCoordinateSlice) (a b c : FockFiber) :
    pairSample x (a+b) c=pairSample x a c+pairSample x b c := by
  simp only [pairSample,WithLp.ofLp_add,Pi.add_apply,star_add,mul_add,add_mul,Finset.sum_add_distrib]

theorem pairSample_smul_left (x : SourceCoordinateSlice) (c : ℂ) (a b : FockFiber) :
    pairSample x (c • a) b=star c*pairSample x a b := by
  simp only [pairSample,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,star_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

theorem pairSample_add_right (x : SourceCoordinateSlice) (a b c : FockFiber) :
    pairSample x a (b+c)=pairSample x a b+pairSample x a c := by
  simp only [pairSample,WithLp.ofLp_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem pairSample_smul_right (x : SourceCoordinateSlice) (c : ℂ) (a b : FockFiber) :
    pairSample x a (c • b)=c*pairSample x a b := by
  simp only [pairSample,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

theorem nativeField_sesq (f : Field289) : SesqGerm (nativeFieldForm f) := by
  apply integral_sesq nativeSample f
  · intro a b c z x
    simp only [nativeSample,sampledMomentum_add,add_apply,Pi.add_apply,pairSample_add_left,Finset.sum_add_distrib]
    ring
  · intro c a b z x
    simp only [nativeSample,sampledMomentum_smul,smul_apply,Pi.smul_apply,pairSample_smul_left,←Finset.mul_sum]
    ring
  · intro a b c z x
    simp only [nativeSample,sampledMomentum_add,add_apply,Pi.add_apply,smul_add,pairSample_add_right,Finset.sum_add_distrib]
    ring
  · intro c a b z x
    simp only [nativeSample,sampledMomentum_smul,smul_apply,Pi.smul_apply,smul_comm (GaussNativeEnergy.scalarWeight x:ℂ) c,
      smul_comm (GaussNativeEnergy.gaugeWeight x _ _:ℂ) c,smul_comm (GaussNativePotential.potential x:ℂ) c,
      pairSample_smul_right,←Finset.mul_sum]
    ring
  · intro a b
    exact fieldSample_integrable (nativeSample a b) f a
      (fun r z hz hx=>nativeSample_param a b (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) Prod.snd
        (r,z) hx (field_curve_smooth f r ⟨z,hz⟩) contDiffAt_snd) (nativeSample_zero_outside a b)

theorem rowField_sesq (f : Field289) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) : SesqGerm (rowFieldForm f c) := by
  apply integral_sesq (rowSample c) f
  · intro a b d z x; exact pairSample_add_left x (a z) (b z) _
  · intro k a b z x; exact pairSample_smul_left x k (a z) _
  · intro a b d z x; simp only [rowSample,add_apply,Pi.add_apply,smul_add,pairSample_add_right]
  · intro k a b z x
    change pairSample x (a z) ((c x:ℂ) • (k • b z))=_
    rw [smul_comm (c x:ℂ) k,pairSample_smul_right]
    rfl
  · intro a b
    exact fieldSample_integrable (rowSample c a b) f a
      (fun r z hz hx=>rowSample_param c hc a b (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) Prod.snd
        (r,z) hx (field_curve_smooth f r ⟨z,hz⟩) contDiffAt_snd) (rowSample_zero_outside c a b)

theorem fiberField_sesq (f : Field289) (A : SourceCoordinateSlice → PreparationVacuumSourceFieldFamily.FiberMap)
    (hA : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) : SesqGerm (fiberFieldForm f A) := by
  apply integral_sesq (fiberSample A) f
  · intro a b c z x; exact pairSample_add_left x (a z) (b z) _
  · intro c a b z x; exact pairSample_smul_left x c (a z) _
  · intro a b c z x
    change pairSample x (a z) (A x (b z+c z))=_
    rw [map_add,pairSample_add_right]
    rfl
  · intro c a b z x
    change pairSample x (a z) (A x (c • b z))=_
    rw [map_smul,pairSample_smul_right]
    rfl
  · intro a b
    exact fieldSample_integrable (fiberSample A a b) f a
      (fun r z hz hx=>fiberSample_param A hA a b (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) Prod.snd
        (r,z) hx (field_curve_smooth f r ⟨z,hz⟩) contDiffAt_snd) (fiberSample_zero_outside A a b)

open GaussCoframeForm PreparationVacuumSourceFieldFamily PreparationVacuumActionDecomposition

theorem mixedField_sesq (f : Field289) (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) : SesqGerm (mixedFieldForm f i k c) :=
  (((rowField_sesq f c hc).precomp (GaussCoframeSpin.current k) (GaussCoframeCore.momentum i)).add
    ((rowField_sesq f c hc).precomp (GaussCoframeCore.momentum i) (GaussCoframeSpin.current k))).scale (1/2)

theorem coframeField_sesq (f : Field289) : SesqGerm (coframeFieldForm f) := by
  have kin := SesqGerm.sum Finset.univ (fun (i : Fin 6) a b r=>∑j : Fin 6,rowFieldForm f
    (GaussCoframeKinetic.coefficient i j) (GaussCoframeCore.momentum i a) (GaussCoframeCore.momentum j b) r)
    (fun i _=>SesqGerm.sum Finset.univ _ (fun j _=>(rowField_sesq f _
      (GaussCoframeKinetic.coefficient_smooth i j)).precomp (GaussCoframeCore.momentum i) (GaussCoframeCore.momentum j)))
  have cur:=(((mixedField_sesq f 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0)).add
    (mixedField_sesq f 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1))).add
    (mixedField_sesq f 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg))).add
    (mixedField_sesq f 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2))
  have spin := SesqGerm.sum Finset.univ _ (fun k (_:k∈(Finset.univ:Finset (Fin 7)))=>
    ((rowField_sesq f inverseVolume inverseVolume_smooth).precomp (GaussCoframeSpin.current k)
      (GaussCoframeSpin.current k)).scale (spinWeight k:ℂ))
  have num := (((rowField_sesq f numberCoefficient numberCoefficient_smooth).precomp number (LinearMap.id)).add
    ((rowField_sesq f numberCoefficient numberCoefficient_smooth).precomp (LinearMap.id) number)).scale (1/2)
  exact (((kin.add cur).add spin).add num).add (rowField_sesq f volumePotential volumePotential_smooth)

theorem fieldForm_sesq (f : Field289) (p : PhysicalMomentum) : SesqGerm (fieldForm f p) := by
  have h:=(((nativeField_sesq f).add (coframeField_sesq f)).add
    (fiberField_sesq f (actualFiber p) (actualFiber_smooth p))).add
    ((fiberField_sesq f retainedCoefficient retainedCoefficient_smooth).scale (-1))
  unfold fieldForm
  simpa only [neg_one_mul,sub_eq_add_neg] using h

namespace SesqGerm
variable {q : QuantumTest → QuantumTest → ℝ → ℂ} (h : SesqGerm q)
include h

theorem zero_left (b : QuantumTest) : q 0 b=ᶠ[𝓝 0] fun _=>0 := by
  simpa using h.smul_left 0 0 b

theorem zero_right (a : QuantumTest) : q a 0=ᶠ[𝓝 0] fun _=>0 := by
  simpa using h.smul_right 0 a 0

theorem sum_left {ι : Type*} (s : Finset ι) (v : ι → QuantumTest) (b : QuantumTest) :
    q (∑i∈s,v i) b=ᶠ[𝓝 0] fun r=>∑i∈s,q (v i) b r := by
  induction s using Finset.cons_induction with
  | empty => simpa using h.zero_left b
  | cons i s hi ih =>
    filter_upwards [h.add_left (v i) (∑j∈s,v j) b,ih] with r hr kr
    simpa only [Finset.sum_cons,kr] using hr

theorem sum_right {ι : Type*} (s : Finset ι) (a : QuantumTest) (v : ι → QuantumTest) :
    q a (∑i∈s,v i)=ᶠ[𝓝 0] fun r=>∑i∈s,q a (v i) r := by
  induction s using Finset.cons_induction with
  | empty => simpa using h.zero_right a
  | cons i s hi ih =>
    filter_upwards [h.add_right a (v i) (∑j∈s,v j),ih] with r hr kr
    simpa only [Finset.sum_cons,kr] using hr

theorem finite_frame {ι : Type*} [Fintype ι] (v : ι → QuantumTest) (a b : ι → ℂ) :
    q (∑i,a i • v i) (∑j,b j • v j)=ᶠ[𝓝 0]
      fun r=>∑i,∑j,star (a i)*q (v i) (v j) r*b j := by
  have each (i : ι) : q (a i • v i) (∑j,b j • v j)=ᶠ[𝓝 0]
      fun r=>∑j,star (a i)*q (v i) (v j) r*b j := by
    have pairs (j : ι) := (h.smul_left (a i) (v i) (b j • v j)).and (h.smul_right (b j) (v i) (v j))
    filter_upwards [h.sum_right Finset.univ (a i • v i) (fun j=>b j • v j),
      Filter.eventually_all.mpr pairs] with r hr hs
    rw [hr]; apply Finset.sum_congr rfl; intro j _
    rw [(hs j).1,(hs j).2]; ring
  filter_upwards [h.sum_left Finset.univ (fun i=>a i • v i) (∑j,b j • v j),
    Filter.eventually_all.mpr each] with r hr hs
  rw [hr]; exact Finset.sum_congr rfl (fun i _=>hs i)
end SesqGerm

local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

theorem formRestriction_pair_germ (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    (fun r=>inner ℂ x (formRestriction f p F r y))=ᶠ[𝓝 0]
      fieldForm f p (sourceTestApprox F x) (sourceTestApprox F y) := by
  have h:=(fieldForm_sesq f p).finite_frame (frameTest F)
    (fun i=>inner ℂ (frameVector F i) x) (fun i=>inner ℂ (frameVector F i) y)
  rw [←sourceTestApprox_frame,←sourceTestApprox_frame] at h
  filter_upwards [h] with r hr
  exact (finiteRiesz_pair F (fieldMatrix f p F r) x y).trans hr.symm

theorem paired_derivative {T : ℝ → H →L[ℂ] H} {D : H →L[ℂ] H} {r : ℝ}
    (h : HasDerivAt T D r) (x y : H) :
    HasDerivAt (fun s=>inner ℂ x (T s y)) (inner ℂ x (D y)) r := by
  have apply := ((ContinuousLinearMap.apply ℂ H y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r h
  have pair := (hasDerivAt_const r x).inner ℂ apply
  simpa using pair

def restrictionPairJets (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    TwoJets (fun r=>inner ℂ x (formRestriction f p F r y)) where
  first r:=inner ℂ x (currentRestriction f p F r y)
  second:=inner ℂ x (contactRestriction f p F y)
  derivative_near:=by
    have h := Filter.eventually_all.mpr (fun i : FrameIndex F=>Filter.eventually_all.mpr
      (fun j : FrameIndex F=>(fieldJets f p (frameTest F i) (frameTest F j)).derivative_near))
    filter_upwards [h] with r hr
    apply paired_derivative
    unfold formRestriction currentRestriction finiteRiesz fieldMatrix
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact (hr i j).smul_const (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
  second_derivative:=paired_derivative (currentRestriction_second f p F) x y

theorem currentRestriction_original_pair (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (currentRestriction f p F 0 y)=
      (fieldJets f p (sourceTestApprox F x) (sourceTestApprox F y)).first 0 := by
  exact ((restrictionPairJets f p F x y).actual.1.congr_of_eventuallyEq
    (formRestriction_pair_germ f p F x y).symm).unique
    (fieldJets f p (sourceTestApprox F x) (sourceTestApprox F y)).actual.1

theorem contactRestriction_original_pair (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (contactRestriction f p F y)=
      (fieldJets f p (sourceTestApprox F x) (sourceTestApprox F y)).second := by
  exact ((restrictionPairJets f p F x y).actual.2.congr_of_eventuallyEq
    (formRestriction_pair_germ f p F x y).deriv.symm).unique
    (fieldJets f p (sourceTestApprox F x) (sourceTestApprox F y)).actual.2

end LowEnergy.PreparationVacuumFullFieldRiesz
