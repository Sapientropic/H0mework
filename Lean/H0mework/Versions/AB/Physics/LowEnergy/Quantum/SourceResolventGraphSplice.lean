import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGraphCompactFlux
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! The original finite resolvent absorbs the compression in a graph correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.FullYSourceResolventGraphSplice
open Filter SourceFamilyHilbert SourceFamilyOperator FullYSourceGraphCompactFlux
open scoped Topology InnerProductSpace

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def resolvent (C : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  Ring.inverse (C-z • 1)

theorem resolvent_isUnit (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (C-z • 1) := by
  have h : z ∉ spectrum ℂ C := fun hs => hz (hC.im_eq_zero_of_mem_spectrum hs)
  have hu := (spectrum.notMem_iff.mp h).neg
  simpa only [Algebra.algebraMap_eq_smul_one,neg_sub] using hu

theorem resolvent_left (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (z : ℂ) (hz : z.im ≠ 0) : resolvent C z*(C-z • 1)=1 :=
  Ring.inverse_mul_cancel _ (resolvent_isUnit C hC z hz)

theorem resolvent_right (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (z : ℂ) (hz : z.im ≠ 0) : (C-z • 1)*resolvent C z=1 :=
  Ring.mul_inverse_cancel _ (resolvent_isUnit C hC z hz)

theorem resolvent_compression (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (z : ℂ) (hz : z.im ≠ 0) : resolvent C z*C=1+z • resolvent C z := by
  have h := resolvent_left C hC z hz
  rw [mul_sub,mul_smul_comm,mul_one] at h
  exact sub_eq_iff_eq_add.mp h

theorem resolvent_norm (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (z : ℂ) (hz : z.im ≠ 0) : ‖resolvent C z‖ ≤ 1/|z.im| := by
  have heta : 0 < |z.im| := abs_pos.mpr hz
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let y := resolvent C z x
  have he : C y-z • y=x := by
    have h := congrArg (fun A : E →L[ℂ] E => A x) (resolvent_right C hC z hz)
    simpa only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,y] using h
  have him : (inner ℂ y x).im = -z.im*‖y‖^2 := by
    have hr : (inner ℂ y (C y)).im=0 := hC.isSymmetric.im_inner_self_apply y
    have hyy : inner ℂ y y=(‖y‖^2 : ℝ) := by
      simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
      rfl
    rw [←he,inner_sub_right,inner_smul_right,hyy]
    simp only [Complex.sub_im,Complex.mul_im,hr,Complex.ofReal_im,Complex.ofReal_re,
      mul_zero,zero_add,zero_sub,neg_mul]
  have hb : |z.im| * ‖y‖^2 ≤ ‖y‖*‖x‖ := by
    calc
      _ = |(inner ℂ y x).im| := by
        rw [him,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg ‖y‖)]
      _ ≤ ‖inner ℂ y x‖ := Complex.abs_im_le_norm _
      _ ≤ ‖y‖*‖x‖ := norm_inner_le_norm _ _
  by_cases hy : y=0
  · change ‖y‖≤1/|z.im| * ‖x‖
    rw [hy,norm_zero]
    positivity
  · have hny : 0<‖y‖ := norm_pos_iff.mpr hy
    have h : |z.im| * ‖y‖≤‖x‖ := by nlinarith
    change ‖y‖≤1/|z.im| * ‖x‖
    rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ heta]
    simpa only [mul_comm] using h

omit [CompleteSpace E] in
theorem graph_defect_identity (C R A B A₀ B₀ : E →L[ℂ] E)
    (z : ℂ) (hR : R*C=1+z • R) (hAB : C*A₀=B₀) :
    A+z • (R*A)-R*B=(1+z • R)*(A-A₀)-R*(B-B₀) := by
  have hz : (1+z • R)*A₀=R*B₀ := by rw [←hR,mul_assoc,hAB]
  rw [mul_sub,mul_sub,hz,add_mul,one_mul,smul_mul_assoc]
  abel

omit [CompleteSpace E] in
theorem graph_defect_bound (C R A B A₀ B₀ : E →L[ℂ] E)
    (z : ℂ) (hR : R*C=1+z • R) (hAB : C*A₀=B₀) :
    ‖A+z • (R*A)-R*B‖ ≤
      (1+‖z‖*‖R‖)*‖A-A₀‖+‖R‖*‖B-B₀‖ := by
  rw [graph_defect_identity C R A B A₀ B₀ z hR hAB]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · apply (norm_mul_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖1+z • R‖ ≤ ‖(1 : E →L[ℂ] E)‖+‖z • R‖ := norm_add_le _ _
      _ ≤ 1+‖z‖*‖R‖ := by
        rw [norm_smul]
        have hn : ‖(1 : E →L[ℂ] E)‖≤1 := ContinuousLinearMap.norm_id_le
        linarith
  · exact norm_mul_le _ _

omit [CompleteSpace E] in
theorem lift_norm_congr {I : Type*} (l : Ultrafilter I) (P Q : Operator I E)
    (h : Tendsto (fun i => ‖P.component i-Q.component i‖) l (𝓝 0)) :
    lift l P=lift l Q := by
  apply SourceFamilyOperator.ext l
  intro f
  obtain ⟨M,hM,hf⟩ := f.property
  let d := act l P f-act l Q f
  have he (i : I) : value d i=(P.component i-Q.component i) (value f i) := rfl
  have hn : ‖d‖≤0 := by
    have hh : Tendsto (fun i => ‖P.component i-Q.component i‖*M) l (𝓝 0) := by
      simpa only [zero_mul] using h.mul_const M
    apply le_of_tendsto_of_tendsto (norm_tendsto l d) hh
    exact Filter.Eventually.of_forall (fun i => by
      change ‖value d i‖≤‖P.component i-Q.component i‖*M
      rw [he i]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hf i) (norm_nonneg _)))
  have hd : ((d : Family E l) : Hilbert E l)=0 := by
    apply norm_eq_zero.mp
    rw [UniformSpace.Completion.norm_coe]
    exact le_antisymm hn (norm_nonneg _)
  rw [lift_coe,lift_coe]
  apply sub_eq_zero.mp
  simpa only [d,UniformSpace.Completion.coe_sub] using hd

omit [CompleteSpace E] in
theorem remainder_algebra (R A B Y : E →L[ℂ] E) (z : ℂ)
    (h : A+z • (R*A)=R*B) :
    R*Y*R=A*R-R*(B-z • A-Y)*R := by
  have hm := congrArg (fun T : E →L[ℂ] E => T*R) h
  rw [add_mul,smul_mul_assoc] at hm
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc] at ⊢
  rw [←hm]
  abel

omit [CompleteSpace E] in
theorem lift_graph_splice {I : Type*} (l : Ultrafilter I) (R : Operator I E)
    (A B : E →L[ℂ] E) (z : ℂ)
    (hh : Tendsto (fun i => A+z • (R.component i*A)-R.component i*B) l (𝓝 0)) :
    lift l (SourceFamilyOperator.constant A)+
      z • (lift l R*lift l (SourceFamilyOperator.constant A))=
        lift l R*lift l (SourceFamilyOperator.constant B) := by
  let P := SourceFamilyOperator.add (SourceFamilyOperator.constant A)
    (comp (SourceFamilyOperator.constant (z • (1 : E →L[ℂ] E)))
      (comp R (SourceFamilyOperator.constant A)))
  let Q := comp R (SourceFamilyOperator.constant B)
  have he (i : I) : P.component i-Q.component i=
      A+z • (R.component i*A)-R.component i*B := by
    change A+(z • (1 : E →L[ℂ] E))*(R.component i*A)-R.component i*B=_
    rw [smul_mul_assoc,one_mul]
  have h := lift_norm_congr l P Q (by
    simpa only [he,norm_zero] using hh.norm)
  change lift l (SourceFamilyOperator.add _ _)=lift l (comp _ _) at h
  rw [lift_add,lift_comp,lift_comp,lift_comp,constant_smul,lift_identity] at h
  change lift l (SourceFamilyOperator.constant A)+
    (z • (1 : Hilbert E l →L[ℂ] Hilbert E l))*(lift l R*lift l (SourceFamilyOperator.constant A))=_ at h
  simpa only [smul_mul_assoc,one_mul,←ContinuousLinearMap.mul_def] using h

omit [CompleteSpace E] in
theorem lift_constant_sub {I : Type*} (l : Ultrafilter I) (A B : E →L[ℂ] E) :
    lift l (SourceFamilyOperator.constant (A-B))=
      lift l (SourceFamilyOperator.constant A)-lift l (SourceFamilyOperator.constant B) := by
  apply SourceFamilyOperator.ext l
  intro f
  rw [sub_apply,lift_coe,lift_coe,lift_coe,←UniformSpace.Completion.coe_sub]
  congr 1

omit [CompleteSpace E] in
theorem lift_remainder_splice {I : Type*} (l : Ultrafilter I) (R : Operator I E)
    (A B Y : E →L[ℂ] E) (z : ℂ)
    (h : lift l (SourceFamilyOperator.constant A)+
      z • (lift l R*lift l (SourceFamilyOperator.constant A))=
        lift l R*lift l (SourceFamilyOperator.constant B)) :
    lift l R*lift l (SourceFamilyOperator.constant Y)*lift l R=
      lift l (SourceFamilyOperator.constant A)*lift l R-
        lift l R*lift l (SourceFamilyOperator.constant (B-z • A-Y))*lift l R := by
  rw [lift_constant_sub,lift_constant_sub,constant_smul]
  exact remainder_algebra _ _ _ _ z h

end Hilbert

open GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index HistorySpace sourceFilter reader inclusion)

def finiteResolvent (F : Index) (z : ℂ) : H →L[ℂ] H :=
  resolvent (GaussGradedCompression.compression F) z

theorem finite_resolvent_norm (F : Index) (z : ℂ) (hz : z.im ≠ 0) :
    ‖finiteResolvent F z‖≤1/|z.im| :=
  resolvent_norm _ (GaussGradedCompression.compression_selfAdjoint F) z hz

theorem graph_splice_uniform (A B : H →L[ℂ] H) (approx : CoreGraphApproximation A B)
    (M μ : ℝ) (hM : 0≤M) (hμ : 0<μ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ‖z‖≤M → μ≤|z.im| →
      ‖A+z • (finiteResolvent F z*A)-finiteResolvent F z*B‖<ε := by
  let K := 2+M/μ+1/μ
  have hK : 0<K := by dsimp [K]; positivity
  let δ := ε/K
  have hδ : 0<δ := div_pos hε hK
  obtain ⟨a,ha,hb⟩ := approx δ hδ
  filter_upwards [columns_eventually_exact a] with F hF z hzm hzμ
  have hz : z.im≠0 := by intro h; simp only [h,abs_zero] at hzμ; linarith
  have hr : ‖finiteResolvent F z‖≤1/μ :=
    (finite_resolvent_norm F z hz).trans (one_div_le_one_div_of_le hμ hzμ)
  have h := graph_defect_bound (GaussGradedCompression.compression F)
    (finiteResolvent F z) A B a.action a.graphAction z
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz) hF
  have he : δ*K=ε := div_mul_cancel₀ ε (ne_of_gt hK)
  have hp : ‖z‖*‖finiteResolvent F z‖≤M*(1/μ) :=
    mul_le_mul hzm hr (norm_nonneg _) hM
  have hp₁ : 1+‖z‖*‖finiteResolvent F z‖≤1+M*(1/μ) := by linarith
  have h₁ := mul_le_mul hp₁ ha (norm_nonneg _) (by positivity : 0≤1+M*(1/μ))
  have h₂ := mul_le_mul hr hb (norm_nonneg _) (by positivity : 0≤1/μ)
  dsimp [K] at he
  simp only [div_eq_mul_inv,one_mul] at he h₁ h₂
  nlinarith

theorem graph_splice_tendsto (A B : H →L[ℂ] H) (approx : CoreGraphApproximation A B)
    (z : ℂ) (hz : z.im≠0) :
    Tendsto (fun F => A+z • (finiteResolvent F z*A)-finiteResolvent F z*B)
      sourceFilter (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [graph_splice_uniform A B approx ‖z‖ |z.im| (norm_nonneg _)
    (abs_pos.mpr hz) ε hε] with F hF
  simpa only [dist_zero_right] using hF z le_rfl le_rfl

def resolventFamily (z : ℂ) (hz : z.im≠0) : Operator Index H where
  component F := finiteResolvent F z
  bounded := ⟨1/|z.im|,by positivity,fun F x =>
    ((finiteResolvent F z).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg x))⟩

def sameResolvent (z : ℂ) (hz : z.im≠0) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (resolventFamily z hz)

theorem whole_carrier_graph_splice (A B : H →L[ℂ] H)
    (approx : CoreGraphApproximation A B) (z : ℂ) (hz : z.im≠0) :
    reader A+z • (sameResolvent z hz*reader A)=sameResolvent z hz*reader B := by
  exact lift_graph_splice sourceFilter (resolventFamily z hz) A B z
    (graph_splice_tendsto A B approx z hz)

theorem whole_carrier_remainder_splice (A B Y : H →L[ℂ] H)
    (approx : CoreGraphApproximation A B) (z : ℂ) (hz : z.im≠0) :
    sameResolvent z hz*reader Y*sameResolvent z hz=
      reader A*sameResolvent z hz-
        sameResolvent z hz*reader (B-z • A-Y)*sameResolvent z hz := by
  exact lift_remainder_splice sourceFilter (resolventFamily z hz) A B Y z
    (whole_carrier_graph_splice A B approx z hz)

#print axioms resolvent_norm
#print axioms graph_splice_uniform
#print axioms graph_splice_tendsto
#print axioms whole_carrier_graph_splice
#print axioms whole_carrier_remainder_splice
end LowEnergy.FullYSourceResolventGraphSplice
