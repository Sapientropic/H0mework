import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceTimeFamilyGraph
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceResolventGraphSplice
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Finite positive-power inequalities generate the relative tail inside the original lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceRelativePowerTail
open Filter MeasureTheory GaussCoreHilbert GaussCoreDifferential
open GaussFockPair GaussFockWeights GaussDensityCore
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)
open SourceFamilyHilbert SourceFamilyOperator
open FullYSourceCutoffNorm FullYSourceCutoffTimeGraph FullYSourceFiniteTimeIntegral
open FullYSourceTimeFamilyGraph
open scoped Topology InnerProductSpace

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positive_power_distance (Q : E →L[ℂ] E) (hQ₀ : 0 ≤ Q) (hQ₁ : Q ≤ 1)
    (x : E) {m n : ℕ} (hmn : m ≤ n) :
    ‖(Q^n) x-(Q^m) x‖^2 ≤ ‖(Q^m) x‖^2-‖(Q^n) x‖^2 := by
  have hs : ∀ x y, inner ℂ (Q x) y=inner ℂ x (Q y) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive Q).mp hQ₀).isSymmetric
  have ho := CStarAlgebra.pow_antitone hQ₀ hQ₁ (show n+m ≤ n+n by omega)
  have hp := ((ContinuousLinearMap.le_def _ _).mp ho).re_inner_nonneg_right x
  change 0 ≤ (inner ℂ x (((Q^(n+m))-(Q^(n+n))) x)).re at hp
  rw [sub_apply,inner_sub_right,Complex.sub_re] at hp
  have hn : (inner ℂ x ((Q^(n+n)) x)).re=‖(Q^n) x‖^2 := by
    rw [pow_add,mul_apply_eq_comp,←power_pair Q hs n x ((Q^n) x)]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hc : (inner ℂ ((Q^n) x) ((Q^m) x)).re=
      (inner ℂ x ((Q^(n+m)) x)).re := by
    rw [power_pair Q hs n,←mul_apply_eq_comp,←pow_add]
  rw [hn] at hp
  rw [norm_sub_sq (𝕜 := ℂ)]
  change ‖(Q^n) x‖^2-2*(inner ℂ ((Q^n) x) ((Q^m) x)).re+‖(Q^m) x‖^2 ≤ _
  rw [hc]
  linarith

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem decreasing_distance_cauchy (u : ℕ → E)
    (distance : ∀ m n, m ≤ n → ‖u n-u m‖^2 ≤ ‖u m‖^2-‖u n‖^2) : CauchySeq u := by
  have hm : Antitone (fun n => ‖u n‖^2) := by
    intro m n hmn
    have hd := distance m n hmn
    nlinarith [sq_nonneg ‖u n-u m‖]
  have hb : BddBelow (Set.range (fun n => ‖u n‖^2)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨n,rfl⟩
    exact sq_nonneg _
  have he : CauchySeq (fun n => ‖u n‖^2) := (tendsto_atTop_ciInf hm hb).cauchySeq
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp he (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hd := distance N n hn
  have hr := hN n hn
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (hm hn))] at hr
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (u n-u N)]

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem decreasing_distance_tail (u : ℕ → E)
    (distance : ∀ m n, m ≤ n → ‖u n-u m‖^2 ≤ ‖u m‖^2-‖u n‖^2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖u (m+1)-u (ell+1)‖ < ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (decreasing_distance_cauchy u distance) ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  have h := hN (m+1) (by omega) (ell+1) (by omega)
  simpa only [dist_eq_norm] using h

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
private theorem relative_tail_of_difference (u : ℕ → E) (t : ℕ → ℕ → E)
    (hd : ∀ m ell, t m ell=u (m+1)-u (ell+1))
    (distance : ∀ m n, m ≤ n → ‖u n-u m‖^2 ≤ ‖u m‖^2-‖u n‖^2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖t m ell‖ < ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := decreasing_distance_tail u distance ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  rw [hd]
  exact hN m hm ell hell
end Hilbert

open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge GaussHistoryHilbert

private theorem inverse_core_positive (f : QuantumTest) :
    0 ≤ (inner ℂ (embed f) (GaussRadialDomain.inverseRadius (embed f))).re := by
  rw [GaussRadialDomain.inverse_core]
  change 0 ≤ (sourcePair f (GaussRadialDomain.inverseAction f)).re
  rw [sourcePair_integral]
  change 0 ≤ RCLike.re (∫ z, densityPair f (GaussRadialDomain.inverseAction f) z
    ∂GaussHistoryHilbert.configurationMeasure)
  rw [←integral_re (densityPair_integrable f (GaussRadialDomain.inverseAction f))]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (GaussRadialDomain.inverseAction f) z).re
  by_cases hz : z∈physicalChart
  · have hp : 0 ≤ (densityPair f f z).re := by
      change 0 ≤ RCLike.re (inner ℂ (weight (fun N => (density N z : ℂ)) (f z)) (f z))
      rw [GaussBoundedMultiplier.weighted_square _
        (fun N => (density_pos N ⟨z,hz⟩).le)]
      exact sq_nonneg _
    have he : densityPair f (GaussRadialDomain.inverseAction f) z=
        (GaussRadialDomain.reciprocal z : ℂ)*densityPair f f z := by
      change inner ℂ (weight (fun N => complexDensity N z) (f z))
        ((GaussRadialDomain.reciprocal z : ℂ) • f z)=_
      exact inner_smul_right _ _ _
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (GaussYukawaCoefficient.radius_pos z).le) hp
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

theorem source_inverse_nonnegative : 0 ≤ GaussRadialDomain.inverseRadius := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨GaussRadialDomain.inverse_pair,?_⟩
  intro x
  change 0 ≤ RCLike.re (inner ℂ (GaussRadialDomain.inverseRadius x) x)
  rw [inner_re_symm (𝕜 := ℂ)]
  refine GaussBoundedMultiplier.core_dense.induction_on x
    (isClosed_le continuous_const
      (Complex.continuous_re.comp
        (continuous_id.inner GaussRadialDomain.inverseRadius.continuous))) ?_
  intro v
  obtain ⟨f,rfl⟩ := coreEquiv.surjective v
  exact inverse_core_positive f

def sourceComplement : H →L[ℂ] H := 1-GaussRadialDomain.inverseRadius

theorem source_complement_nonnegative : 0 ≤ sourceComplement := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨?_,?_⟩
  · intro x y
    change inner ℂ (x-GaussRadialDomain.inverseRadius x) y=
      inner ℂ x (y-GaussRadialDomain.inverseRadius y)
    rw [inner_sub_left,inner_sub_right,GaussRadialDomain.inverse_pair]
  · intro x
    have h := FullYSourceCutoffNorm.source_complement_positive (inclusion x)
    change 0 ≤ RCLike.re (inner ℂ (x-GaussRadialDomain.inverseRadius x) x)
    rw [inner_re_symm (𝕜 := ℂ)]
    change 0 ≤ (inner ℂ (inclusion x)
      (inclusion x-reader GaussRadialDomain.inverseRadius (inclusion x))).re at h
    rw [GaussUnitaryHistory.reader_inclusion,←map_sub,inclusion.inner_map_map] at h
    exact h

theorem source_complement_le_one : sourceComplement ≤ 1 := by
  rw [ContinuousLinearMap.le_def]
  have he : (1 : H →L[ℂ] H)-sourceComplement=GaussRadialDomain.inverseRadius := by
    unfold sourceComplement
    abel
  rw [he]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp source_inverse_nonnegative

def historyPower (n : ℕ) : HistorySpace →L[ℂ] HistorySpace := reader (sourceComplement^n)

def relativeTail (m ell : ℕ) : H →L[ℂ] H :=
  sourceComplement^(m+1)-sourceComplement^(ell+1)

private theorem lift_decreasing_distance {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (A : ℕ → E →L[ℂ] E)
    (hA : ∀ x m n, m ≤ n → ‖A n x-A m x‖^2 ≤ ‖A m x‖^2-‖A n x‖^2)
    (x : Hilbert E u) {m n : ℕ} (hmn : m ≤ n) :
    ‖lift u (SourceFamilyOperator.constant (A n)) x-
        lift u (SourceFamilyOperator.constant (A m)) x‖^2 ≤
      ‖lift u (SourceFamilyOperator.constant (A m)) x‖^2-
        ‖lift u (SourceFamilyOperator.constant (A n)) x‖^2 := by
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [lift_coe,lift_coe,←UniformSpace.Completion.coe_sub]
  simp only [UniformSpace.Completion.norm_coe]
  apply le_of_tendsto_of_tendsto (square_tendsto u _)
    ((square_tendsto u _).sub (square_tendsto u _))
  exact Filter.Eventually.of_forall (fun i => hA (value f i) m n hmn)

theorem history_power_distance (x : HistorySpace) {m n : ℕ} (hmn : m ≤ n) :
    ‖historyPower n x-historyPower m x‖^2 ≤ ‖historyPower m x‖^2-‖historyPower n x‖^2 :=
  lift_decreasing_distance sourceFilter (sourceComplement^·)
    (fun y _ _ h => positive_power_distance sourceComplement
      source_complement_nonnegative source_complement_le_one y h) x hmn

private theorem history_tail (x : HistorySpace) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖historyPower (m+1) x-historyPower (ell+1) x‖ < ε :=
  decreasing_distance_tail (fun n => historyPower n x)
    (fun _ _ h => history_power_distance x h)

/-- This convergence is intrinsic to the original K; the reader is never moved through a limit. -/
theorem whole_history_relative_tail (x : HistorySpace) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖reader (relativeTail m ell) x‖ < ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := history_tail x ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  have he : reader (relativeTail m ell) x=
      historyPower (m+1) x-historyPower (ell+1) x :=
    congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A x)
      (map_sub GaussYukawaInteraction.representation
        (sourceComplement^(m+1)) (sourceComplement^(ell+1)))
  rw [he]
  exact hN m hm ell hell

section L2
variable {α E : Type*} [MeasurableSpace α] (μ : Measure α)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem l2_decreasing_distance (A : ℕ → E →L[ℂ] E)
    (hA : ∀ x m n, m ≤ n → ‖A n x-A m x‖^2 ≤ ‖A m x‖^2-‖A n x‖^2)
    (ψ : Lp E 2 μ) {m n : ℕ} (hmn : m ≤ n) :
    ‖(A n).compLpL 2 μ ψ-(A m).compLpL 2 μ ψ‖^2 ≤
      ‖(A m).compLpL 2 μ ψ‖^2-‖(A n).compLpL 2 μ ψ‖^2 := by
  rw [square_integral,square_integral,square_integral,
    ←integral_sub (square_integrable μ ((A m).compLpL 2 μ ψ))
      (square_integrable μ ((A n).compLpL 2 μ ψ))]
  apply integral_mono_ae
    (square_integrable μ ((A n).compLpL 2 μ ψ-(A m).compLpL 2 μ ψ))
    ((square_integrable μ ((A m).compLpL 2 μ ψ)).sub
      (square_integrable μ ((A n).compLpL 2 μ ψ)))
  filter_upwards [Lp.coeFn_sub ((A n).compLpL 2 μ ψ) ((A m).compLpL 2 μ ψ),
    (A n).coeFn_compLpL ψ,(A m).coeFn_compLpL ψ] with t hsub hn hm
  simp only [hsub,Pi.sub_apply,hn,hm]
  exact hA (ψ t) m n hmn

private theorem compLpL_sub (A B : E →L[ℂ] E) :
    (A-B).compLpL 2 μ=A.compLpL 2 μ-B.compLpL 2 μ := by
  have he : A-B=A+(-1 : ℂ) • B := by rw [neg_one_smul,sub_eq_add_neg]
  rw [he,ContinuousLinearMap.add_compLpL,ContinuousLinearMap.smul_compLpL,neg_one_smul]
  exact (sub_eq_add_neg _ _).symm
end L2

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

def timePower (n : ℕ) : TimeSpace μ →L[ℂ] TimeSpace μ :=
  familyReader μ (sourceComplement^n)

theorem time_power_distance (ψ : TimeSpace μ) {m n : ℕ} (hmn : m ≤ n) :
    ‖timePower μ n ψ-timePower μ m ψ‖^2 ≤
      ‖timePower μ m ψ‖^2-‖timePower μ n ψ‖^2 :=
  lift_decreasing_distance sourceFilter (fun n => (sourceComplement^n).compLpL 2 μ)
    (fun v _ _ h => l2_decreasing_distance μ (sourceComplement^·)
      (fun y _ _ hj => positive_power_distance sourceComplement
        source_complement_nonnegative source_complement_le_one y hj) v h) ψ hmn

private theorem family_reader_sub (A B : H →L[ℂ] H) :
    familyReader μ (A-B)=familyReader μ A-familyReader μ B := by
  exact (congrArg
    (fun T : Lp H 2 μ →L[ℂ] Lp H 2 μ => lift sourceFilter (SourceFamilyOperator.constant T))
    (compLpL_sub μ A B)).trans
      (FullYSourceResolventGraphSplice.lift_constant_sub sourceFilter
        (A.compLpL 2 μ) (B.compLpL 2 μ))

/-- Each finite F is an L² family before the original sourceFilter is applied. -/
theorem time_space_relative_tail (ψ : TimeSpace μ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖familyReader μ (relativeTail m ell) ψ‖ < ε :=
  relative_tail_of_difference (fun n => timePower μ n ψ)
    (fun m ell => familyReader μ (relativeTail m ell) ψ)
    (fun m ell => congrArg (fun A : TimeSpace μ →L[ℂ] TimeSpace μ => A ψ)
      (family_reader_sub μ (sourceComplement^(m+1)) (sourceComplement^(ell+1))))
    (fun _ _ h => time_power_distance μ ψ h)

#print axioms source_inverse_nonnegative
#print axioms history_power_distance
#print axioms whole_history_relative_tail
#print axioms time_power_distance
#print axioms time_space_relative_tail
end LowEnergy.SourceRelativePowerTail
