import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarCoefficientTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockRadiusBoundaryFamilyTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussQuantumMultiplier
open GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum GaussFockWeights
open SourceMixedNativeReturn SourceNativeCutoffContact SourceRelativePowerTail SourceCornerForcing
open PositiveScalarWeakBudget PositiveScalarCoefficientDecay SourceLocalizedInverseFormPayment
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceCutoffSharp FullYSourceResolventGraphSplice SourceResolventBandLimit SourceHardyRetardedTail
open SourceRetardedBandCurrent MeasureTheory Filter
open SourceActualResolventEnergy SourceFamilyHilbert SourceFamilyOperator FullYSourceFiniteTimeIntegral
open FullYSourceTimeFamilyGraph FullYSourceCutoffTimeGraph
open scoped ContDiff InnerProductSpace Topology
abbrev Op := H →L[ℂ] H

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'

private theorem finite_star (F : Index) (z : ℂ) :
    finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]

private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact finite_frequency_continuous μ hμ F
  · have he : (fun w : ℝ => finiteResolvent F (actualFrequency true μ w))=
        (fun w : ℝ => (finiteResolvent F (line μ w)).adjoint) := by
      funext w
      exact finite_star F (line μ w)
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp (finite_frequency_continuous μ hμ F))

private theorem frequency_norm (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) (w : ℝ) :
    ‖finiteResolvent F (actualFrequency advanced μ w) g‖=‖finiteResolvent F (line μ w) g‖ := by
  cases advanced
  · rfl
  · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
      (by simpa only [line_im] using hμ.ne') g

private theorem whole_memLp (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    MemLp (fun w : ℝ => finiteResolvent F (actualFrequency advanced μ w) g) 2 MeasureTheory.volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (((frequency_continuous advanced μ hμ F).clm_apply continuous_const).aestronglyMeasurable)).mpr
  have hi : Integrable (fun w : ℝ => ‖finiteResolvent F (line μ w) g‖^2) MeasureTheory.volume := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using actual_square_integrable F μ hμ g
  simpa only [frequency_norm advanced μ hμ F g] using hi

private def wholeFiniteInput (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) : Lp H 2 (MeasureTheory.volume : Measure ℝ) :=
  (whole_memLp advanced μ hμ F g).toLp (fun w => finiteResolvent F (actualFrequency advanced μ w) g)

private abbrev L2H := Lp H 2 (MeasureTheory.volume : Measure ℝ)
private abbrev TH := TimeSpace (MeasureTheory.volume : Measure ℝ)
private def timeRead (A : Op) : TH →L[ℂ] TH := familyReader (MeasureTheory.volume : Measure ℝ) A

private theorem lp_one : (1 : Op).compLpL 2 (MeasureTheory.volume : Measure ℝ)=(1 : L2H →L[ℂ] L2H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [(1 : Op).coeFn_compLpL f] with w hw
  exact hw

private theorem lp_mul (A B : Op) :
    (A*B).compLpL 2 (MeasureTheory.volume : Measure ℝ)=
      A.compLpL 2 MeasureTheory.volume*B.compLpL 2 MeasureTheory.volume := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [(A*B).coeFn_compLpL f,A.coeFn_compLpL (B.compLpL 2 MeasureTheory.volume f),
    B.coeFn_compLpL f] with w hAB hA hB
  change ((A*B).compLpL 2 MeasureTheory.volume f) w=(A.compLpL 2 MeasureTheory.volume (B.compLpL 2 MeasureTheory.volume f)) w
  rw [hAB,hA,hB]
  rfl

private theorem time_one : timeRead (1 : Op)=(1 : TH →L[ℂ] TH) :=
  (congrArg (fun A : L2H →L[ℂ] L2H => lift sourceFilter (SourceFamilyOperator.constant A)) lp_one).trans
    (lift_identity sourceFilter)
private theorem time_mul (A B : Op) : timeRead (A*B)=timeRead A*timeRead B :=
  (congrArg (fun C : L2H →L[ℂ] L2H => lift sourceFilter (SourceFamilyOperator.constant C)) (lp_mul A B)).trans
    (SourceFamilyOperator.constant_mul sourceFilter _ _)
private theorem time_add (A B : Op) : timeRead (A+B)=timeRead A+timeRead B :=
  (congrArg (fun C : L2H →L[ℂ] L2H => lift sourceFilter (SourceFamilyOperator.constant C))
    (ContinuousLinearMap.add_compLpL (p := 2) (μ := MeasureTheory.volume) A B)).trans
      (SourceFamilyOperator.constant_add sourceFilter _ _)
private theorem time_smul (c : ℂ) (A : Op) : timeRead (c • A)=c • timeRead A :=
  (congrArg (fun C : L2H →L[ℂ] L2H => lift sourceFilter (SourceFamilyOperator.constant C))
    (ContinuousLinearMap.smul_compLpL (p := 2) (μ := MeasureTheory.volume) c A)).trans
      (SourceFamilyOperator.constant_smul sourceFilter c _)
private theorem time_sub (A B : Op) : timeRead (A-B)=timeRead A-timeRead B := by
  have hab : A-B=A+(-1 : ℂ) • B := by module
  exact (congrArg timeRead hab).trans ((time_add A ((-1:ℂ) • B)).trans
    ((congrArg (fun C : TH →L[ℂ] TH => timeRead A+C) (time_smul (-1) B)).trans (by module)))
private theorem time_pow (A : Op) (n : ℕ) : timeRead (A^n)=(timeRead A)^n := by
  induction n with
  | zero => simpa only [pow_zero] using time_one
  | succ n ih =>
    exact (congrArg timeRead (pow_succ A n)).trans ((time_mul (A^n) A).trans
      ((congrArg (fun B : TH →L[ℂ] TH => B*timeRead A) ih).trans (pow_succ (timeRead A) n).symm))

private theorem lp_positive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (hA : 0 ≤ A) :
    0 ≤ A.compLpL 2 (MeasureTheory.volume : Measure ℝ) := by
  have hP := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  constructor
  · intro f g
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [A.coeFn_compLpL f,A.coeFn_compLpL g] with w hf hg
    change inner ℂ ((A.compLpL 2 MeasureTheory.volume f) w) (g w)=
      inner ℂ (f w) ((A.compLpL 2 MeasureTheory.volume g) w)
    rw [hf,hg]
    exact hP.inner_left_eq_inner_right _ _
  · intro f
    change 0 ≤ (inner ℂ (A.compLpL 2 MeasureTheory.volume f) f).re
    rw [L2.inner_def]
    have hr : (∫ w : ℝ,inner ℂ ((A.compLpL 2 MeasureTheory.volume f) w) (f w)).re=
        ∫ w : ℝ,(inner ℂ ((A.compLpL 2 MeasureTheory.volume f) w) (f w)).re := by
      simpa only [RCLike.re_eq_complex_re] using
        (integral_re (L2.integrable_inner (𝕜 := ℂ) (A.compLpL 2 MeasureTheory.volume f) f)).symm
    rw [hr]
    apply integral_nonneg_of_ae
    filter_upwards [A.coeFn_compLpL f] with w hw
    rw [hw]
    exact hP.re_inner_nonneg_left _

private theorem lifted_positive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (hA : 0 ≤ A) :
    0 ≤ lift sourceFilter (SourceFamilyOperator.constant A) := by
  have hP := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  constructor
  · exact lift_pair sourceFilter (SourceFamilyOperator.constant A) (SourceFamilyOperator.constant A)
      (fun _ x y => hP.inner_left_eq_inner_right x y)
  · intro x
    change 0 ≤ (inner ℂ (lift sourceFilter (SourceFamilyOperator.constant A) x) x).re
    refine UniformSpace.Completion.induction_on x (isClosed_le continuous_const (by fun_prop)) ?_
    intro f
    rw [lift_coe,inner_coe]
    apply ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
      (pair_tendsto sourceFilter (act sourceFilter (SourceFamilyOperator.constant A) f) f))
    exact Filter.Eventually.of_forall (fun F => hP.re_inner_nonneg_left (value f F))

private theorem time_positive (A : Op) (hA : 0 ≤ A) : 0 ≤ timeRead A :=
  lifted_positive _ (lp_positive A hA)
attribute [local irreducible] timeRead

private theorem time_complement_positive : 0 ≤ timeRead sourceComplement :=
  time_positive _ source_complement_nonnegative
private theorem time_complement_le_one : timeRead sourceComplement ≤ 1 := by
  have h := time_positive (1-sourceComplement) (sub_nonneg.mpr source_complement_le_one)
  have he : timeRead (1-sourceComplement)=1-timeRead sourceComplement :=
    (time_sub 1 sourceComplement).trans (congrArg (fun A : TH →L[ℂ] TH => A-timeRead sourceComplement) time_one)
  exact sub_nonneg.mp (Eq.mp (congrArg (fun A : TH →L[ℂ] TH => (0 : TH →L[ℂ] TH) ≤ A) he) h)

private theorem inverse_complement : inverseRadius=1-sourceComplement := by unfold sourceComplement;abel
private theorem gradient_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q : E →L[ℂ] E) (n : ℕ) :
    PositiveContractionRitt.gradient Q n=(n+1 : ℂ) • (Q^n*(1-Q)) := by
  unfold PositiveContractionRitt.gradient
  have hr := RCLike.real_smul_eq_coe_smul (K := ℂ) (n+1 : ℝ) (Q^n*(1-Q))
  simpa only [RCLike.ofReal_add,RCLike.ofReal_natCast,RCLike.ofReal_one] using hr

private theorem time_inverse_complement : timeRead inverseRadius=1-timeRead sourceComplement :=
  (congrArg timeRead inverse_complement).trans ((time_sub 1 sourceComplement).trans
    (congrArg (fun A : TH →L[ℂ] TH => A-timeRead sourceComplement) time_one))

private theorem boundary_time (n : ℕ) :
    timeRead (boundaryOperator n)=PositiveContractionRitt.gradient (timeRead sourceComplement) n := by
  have hP := (time_mul inverseRadius (sourceComplement^n)).trans
    (congrArg (fun A : TH →L[ℂ] TH => timeRead inverseRadius*A) (time_pow sourceComplement n))
  have hS := congrArg (fun A : TH →L[ℂ] TH => A*(timeRead sourceComplement)^n) time_inverse_complement
  have hc : Commute (timeRead sourceComplement) (1-timeRead sourceComplement) := by
    show timeRead sourceComplement*(1-timeRead sourceComplement)=(1-timeRead sourceComplement)*timeRead sourceComplement
    simp only [sub_mul,mul_sub,one_mul,mul_one]
  have he := (time_smul (n+1 : ℂ) (inverseRadius*sourceComplement^n)).trans
    (congrArg (fun A : TH →L[ℂ] TH => (n+1 : ℂ) • A) (hP.trans (hS.trans (hc.pow_left n).eq.symm)))
  exact he.trans (gradient_complex (timeRead sourceComplement) n).symm

private theorem boundary_time_strong (x : TH) :
    Tendsto (fun n => timeRead (boundaryOperator n) x) atTop (𝓝 0) := by
  have h := PositiveContractionRitt.gradient_strong (timeRead sourceComplement)
    time_complement_positive time_complement_le_one x
  exact h.congr' (Filter.Eventually.of_forall (fun n => congrArg (fun A : TH →L[ℂ] TH => A x) (boundary_time n).symm))


private def readFamily (A : Op) (f : Family L2H sourceFilter) : Family L2H sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) f

private theorem read_family_norm (A : Op) (f : Family L2H sourceFilter) :
    ‖readFamily A f‖=‖timeRead A (f : TH)‖ := by
  unfold timeRead familyReader
  rw [lift_coe,UniformSpace.Completion.norm_coe]
  rfl

private theorem acted_integral (A : Op) (advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖A (finiteResolvent F (actualFrequency advanced μ w) g)‖^2))=
      ENNReal.ofReal (‖value (readFamily A (wholeInputFamily advanced μ hμ g)) F‖^2) := by
  have he : (fun w => ‖A (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)=ᵐ[MeasureTheory.volume]
      (fun w => ‖value (readFamily A (wholeInputFamily advanced μ hμ g)) F w‖^2) := by
    filter_upwards [A.coeFn_compLpL (wholeFiniteInput advanced μ hμ F g),
      (whole_memLp advanced μ hμ F g).coeFn_toLp] with w hA hR
    change _=‖(A.compLpL 2 MeasureTheory.volume (wholeFiniteInput advanced μ hμ F g)) w‖^2
    rw [hA]
    change _=‖A (wholeFiniteInput advanced μ hμ F g w)‖^2
    change wholeFiniteInput advanced μ hμ F g w=finiteResolvent F (actualFrequency advanced μ w) g at hR
    rw [hR]
  have hi := (square_integrable MeasureTheory.volume
    (value (readFamily A (wholeInputFamily advanced μ hμ g)) F)).congr he.symm
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)),
    integral_congr_ae he,←square_integral]

private theorem family_boundary_tail (f : Family L2H sourceFilter) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ n,N ≤ n →
      ∀ᶠ F in (sourceFilter : Filter Index),‖value (readFamily (boundaryOperator n) f) F‖^2 ≤ ε := by
  intro ε hε
  have hb : ∀ᶠ n : ℕ in atTop,‖timeRead (boundaryOperator n) (f:TH)‖^2<ε := by
    have ht := (boundary_time_strong (f:TH)).norm.pow 2
    have he : (‖(0:TH)‖:ℝ)^2<ε := by simpa only [norm_zero,zero_pow (by omega : 2≠0)] using hε
    exact ht.eventually (gt_mem_nhds he)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  refine ⟨N,fun n hn => ?_⟩
  let fB := readFamily (boundaryOperator n) f
  have hval : ‖fB‖^2<ε := by rw [read_family_norm];exact hN n hn
  filter_upwards [(square_tendsto sourceFilter fB).eventually (gt_mem_nhds hval)] with F hF
  exact hF.le

/-- The actual whole resolvent family pays every Ritt boundary at one N shared by the two frequency legs. -/
theorem actual_boundary_full_frequency_common_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ n,N ≤ n →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖boundaryOperator n
          (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := family_boundary_tail (wholeInputFamily false μ hμ g) ε hε
  obtain ⟨N₁,h₁⟩ := family_boundary_tail (wholeInputFamily true μ hμ g) ε hε
  refine ⟨max N₀ N₁,fun n hn => ?_⟩
  filter_upwards [h₀ n (by omega),h₁ n (by omega)] with F hf ht
  intro advanced
  cases advanced
  · rw [acted_integral (boundaryOperator n) false μ hμ F g]
    exact ENNReal.ofReal_le_ofReal hf
  · rw [acted_integral (boundaryOperator n) true μ hμ F g]
    exact ENNReal.ofReal_le_ofReal ht

private theorem two_square {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]

private theorem boundary_difference_integral (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖(boundaryOperator ell-boundaryOperator m)
      (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤
      ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (‖boundaryOperator ell
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2))+
      ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (‖boundaryOperator m
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) := by
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal (‖boundaryOperator m
      (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) :=
    (((boundaryOperator m).continuous.comp
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖boundaryOperator ell
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)+
      ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖boundaryOperator m
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      exact two_square _ _
    _=_ := by
      rw [lintegral_add_right _ (hm.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Both original boundary peaks are paid together on the unchanged source filter and all real frequencies. -/
theorem actual_boundary_difference_common_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖(boundaryOperator ell-boundaryOperator m)
          (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_boundary_full_frequency_common_tail μ hμ g (ε/4) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm,hN ell (hm.trans hml)] with F hf ht
  intro advanced
  have h := (boundary_difference_integral m ell advanced μ hμ F g).trans
    (add_le_add (mul_le_mul le_rfl (ht advanced) zero_le zero_le)
      (mul_le_mul le_rfl (hf advanced) zero_le zero_le))
  have he : ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4)+
      ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
      ←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact h.trans_eq he

end LowEnergy.SourceClockRadiusBoundaryFamilyTail
