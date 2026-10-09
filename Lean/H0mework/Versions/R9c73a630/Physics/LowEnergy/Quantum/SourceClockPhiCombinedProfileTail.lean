import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiZeroOrderProfile
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRittSecondGradient
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCombinedScalePressure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCombinedProfileTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussFockWeights
open GaussDensityCore FullYSourceResolventGraphSplice
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceScalarDoubleCurrent SourceScalarVirialBulk
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiRadiusResponseHessian
open SourceClockYukawaCubicCurrent SourceClockPhiRadiusResponsePositiveSource
open SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceActualResolventEnergy
open SourceRetardedBandCurrent SourceRelativePowerTail
open SourceFamilyHilbert SourceFamilyOperator FullYSourceFiniteTimeIntegral FullYSourceTimeFamilyGraph FullYSourceCutoffTimeGraph
open MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
private abbrev S : End := phiInverseAction
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev T (m ell:ℕ) : End := phiThetaAction m ell
private abbrev L2H := Lp H 2 (MeasureTheory.volume : Measure ℝ)
private abbrev TH := TimeSpace (MeasureTheory.volume : Measure ℝ)
private def timeRead (A : Op) : TH →L[ℂ] TH := familyReader (MeasureTheory.volume : Measure ℝ) A
private theorem phi_inverse_core (f:QuantumTest) : phiInverseBounded (embed f)=embed (phiInverseAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem phi_inverse_norm : ‖phiInverseBounded‖ ≤ 1 := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem phi_inverse_pair (x y:H) : inner ℂ (phiInverseBounded x) y=inner ℂ x (phiInverseBounded y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  obtain ⟨g,rfl⟩:=coreEquiv.surjective b
  change inner ℂ (phiInverseBounded (embed f)) (embed g)=inner ℂ (embed f) (phiInverseBounded (embed g))
  rw [phi_inverse_core,phi_inverse_core]
  exact (multiply_pair _ _ _ _).symm
private theorem phi_inverse_positive : 0 ≤ phiInverseBounded := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨phi_inverse_pair,?_⟩
  intro x
  change 0 ≤ (inner ℂ (phiInverseBounded x) x).re
  rw [phi_inverse_pair]
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_le continuous_const (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  change 0 ≤ (inner ℂ (embed f) (phiInverseBounded (embed f))).re
  rw [phi_inverse_core]
  change 0 ≤ (sourcePair f (phiInverseAction f)).re
  rw [sourcePair_integral]
  have hr:(∫z,densityPair f (phiInverseAction f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫z,(densityPair f (phiInverseAction f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re (densityPair_integrable f (phiInverseAction f))).symm
  rw [hr]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (phiInverseAction f) z).re
  by_cases hz:z∈physicalChart
  · have hp:0 ≤ (densityPair f f z).re := by
      change 0 ≤ RCLike.re (inner ℂ (weight (fun N=>(density N z:ℂ)) (f z)) (f z))
      rw [GaussBoundedMultiplier.weighted_square _ (fun N=>(density_pos N ⟨z,hz⟩).le)]
      exact sq_nonneg _
    have he:densityPair f (phiInverseAction f) z=(phiReciprocal z:ℂ)*densityPair f f z :=
      inner_smul_right _ _ _
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hp
  · have hf:f z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]
private def phiComplement : Op := 1-phiInverseBounded
private theorem phi_complement_positive : 0 ≤ phiComplement :=
  sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_inverse_positive).mp phi_inverse_norm)
private theorem phi_complement_le_one : phiComplement ≤ 1 := sub_le_self _ phi_inverse_positive
private def phiTail (m ell:ℕ) : Op := phiComplement^(m+1)-phiComplement^(ell+1)
private theorem phi_power_core (n:ℕ) (f:QuantumTest) :
    (phiComplement^n) (embed f)=embed (((1-phiInverseAction)^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change phiComplement ((phiComplement^n) (embed f))=embed ((1-phiInverseAction) (((1-phiInverseAction)^n) f))
    rw [ih]
    change embed (((1-phiInverseAction)^n) f)-phiInverseBounded (embed (((1-phiInverseAction)^n) f))=_
    rw [phi_inverse_core,←map_sub]
    rfl
private theorem phi_tail_core (m ell:ℕ) (f:QuantumTest) :
    phiTail m ell (embed f)=embed (phiThetaAction m ell f) := by
  simp only [phiTail,sub_apply,phi_power_core,phiThetaAction,LinearMap.sub_apply,map_sub]

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

private theorem gradient_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q : E →L[ℂ] E) (n : ℕ) :
    PositiveContractionRitt.gradient Q n=(n+1 : ℂ) • (Q^n*(1-Q)) := by
  unfold PositiveContractionRitt.gradient
  have hr := RCLike.real_smul_eq_coe_smul (K := ℂ) (n+1 : ℝ) (Q^n*(1-Q))
  simpa only [RCLike.ofReal_add,RCLike.ofReal_natCast,RCLike.ofReal_one] using hr

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


private theorem time_phi_positive : 0 ≤ timeRead phiComplement := time_positive _ phi_complement_positive
private theorem time_phi_le_one : timeRead phiComplement ≤ 1 := by
  have h := time_positive (1-phiComplement) (sub_nonneg.mpr phi_complement_le_one)
  have he : timeRead (1-phiComplement)=1-timeRead phiComplement :=
    (time_sub 1 phiComplement).trans (congrArg (fun A : TH →L[ℂ] TH=>A-timeRead phiComplement) time_one)
  exact sub_nonneg.mp (Eq.mp (congrArg (fun A : TH →L[ℂ] TH=>(0:TH →L[ℂ] TH)≤A) he) h)
private def firstBoundary (n:ℕ) : Op := (n+1:ℂ) • (phiComplement^n*(1-phiComplement))
private theorem first_time (n:ℕ):timeRead (firstBoundary n)=PositiveContractionRitt.gradient (timeRead phiComplement) n := by
  have he:= (time_smul (n+1:ℂ) (phiComplement^n*(1-phiComplement))).trans
    (congrArg (fun A:TH →L[ℂ] TH=>(n+1:ℂ) • A) ((time_mul (phiComplement^n) (1-phiComplement)).trans
      (congrArg₂ (fun A B:TH →L[ℂ] TH=>A*B) (time_pow phiComplement n)
        ((time_sub 1 phiComplement).trans (congrArg (fun A:TH →L[ℂ] TH=>A-timeRead phiComplement) time_one)))))
  exact he.trans (gradient_complex (timeRead phiComplement) n).symm
private theorem first_time_strong (x:TH):Tendsto (fun n=>timeRead (firstBoundary n) x) atTop (𝓝 0) := by
  have h:=PositiveContractionRitt.gradient_strong (timeRead phiComplement) time_phi_positive time_phi_le_one x
  exact h.congr' (Eventually.of_forall (fun n=>congrArg (fun A:TH →L[ℂ] TH=>A x) (first_time n).symm))
private theorem family_first_tail (f:Family L2H sourceFilter):
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n,N ≤ n→∀ᶠF in (sourceFilter:Filter Index),‖value (readFamily (firstBoundary n) f) F‖^2 ≤ ε := by
  intro ε hε
  have hb:∀ᶠ n:ℕ in atTop,‖timeRead (firstBoundary n) (f:TH)‖^2<ε := by
    have ht:=(first_time_strong (f:TH)).norm.pow 2
    have he:(‖(0:TH)‖:ℝ)^2<ε:=by simpa only [norm_zero,zero_pow (by omega:2≠0)] using hε
    exact ht.eventually (gt_mem_nhds he)
  obtain ⟨N,hN⟩:=eventually_atTop.mp hb
  refine ⟨N,fun n hn=>?_⟩
  let fB:=readFamily (firstBoundary n) f
  have hval:‖fB‖^2<ε := by rw [read_family_norm];exact hN n hn
  filter_upwards [(square_tendsto sourceFilter fB).eventually (gt_mem_nhds hval)] with F hF
  exact hF.le
private theorem actual_first_tail (μ:ℝ)(hμ:0<μ)(g:H):
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n,N ≤ n→∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻t:ℝ,ENNReal.ofReal (‖firstBoundary n (finiteResolvent F (actualFrequency advanced μ t) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N0,h0⟩:=family_first_tail (wholeInputFamily false μ hμ g) ε hε
  obtain ⟨N1,h1⟩:=family_first_tail (wholeInputFamily true μ hμ g) ε hε
  refine ⟨max N0 N1,fun n hn=>?_⟩
  filter_upwards [h0 n (by omega),h1 n (by omega)] with F hf ht
  intro advanced
  cases advanced
  · rw [acted_integral (firstBoundary n) false μ hμ F g]
    exact ENNReal.ofReal_le_ofReal hf
  · rw [acted_integral (firstBoundary n) true μ hμ F g]
    exact ENNReal.ofReal_le_ofReal ht
private abbrev E : End := SourceScalarVirialBulk.phiEulerAction
private abbrev R : End := phiRadiusAction
private abbrev Q : End := 1-S
private abbrev B (m ell:ℕ) : End := phiFirstPeak m ell
private abbrev C (m ell:ℕ) : End := phiSecondPeak m ell
private abbrev delta : End := S^3-S
private theorem bracket_product (X Y Z : End) : bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_sub (X Y Z : End) : bracket X (Y-Z)=bracket X Y-bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_add (X Y Z : End) : bracket X (Y+Z)=bracket X Y+bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_smul (X Y : End) (c : ℂ) : bracket X (c • Y)=c • bracket X Y := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem profile_inverse_radius : S*R=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem profile_radius_inverse : R*S=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem euler_inverse : bracket E S=delta := by
  have hr : bracket E R=R-S := original_phi_euler_radius
  have h1 : S*E*R*S=S*E := by
    calc _=S*E*(R*S) := by noncomm_ring
         _=_ := by rw [profile_radius_inverse,mul_one]
  have h2 : S*R*E*S=E*S := by rw [profile_inverse_radius,one_mul]
  have hi : bracket E S= -(S*bracket E R*S) := by
    unfold bracket
    calc _= -(S*E*R*S-S*R*E*S) := by rw [h1,h2];abel
         _=_ := by noncomm_ring
  rw [hi,hr]
  change -(S*(R-S)*S)=S^3-S
  calc _= -((S*R)*S)+S^3 := by noncomm_ring
       _=_ := by rw [profile_inverse_radius,one_mul];abel
private theorem q_delta : Commute Q delta :=
  (((Commute.one_left S).sub_left (Commute.refl S)).pow_right 3).sub_right
    ((Commute.one_left S).sub_left (Commute.refl S))
private theorem euler_q : bracket E Q= -delta := by
  rw [Q,bracket_sub,euler_inverse]
  simp only [bracket,mul_one,one_mul,sub_self,zero_sub]
private theorem euler_geometric_succ (n : ℕ) :
    bracket E (Q^(n+1))=(-(n+1:ℂ)) • (Q^n*delta) := by
  induction n with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul,one_smul,neg_smul] using euler_q
  | succ n ih =>
    have hm : (Q^n*delta)*Q=Q^(n+1)*delta := by rw [mul_assoc,←q_delta.eq,←mul_assoc,←pow_succ]
    rw [show n+1+1=(n+1)+1 from rfl,pow_succ,bracket_product,ih,euler_q]
    simp only [smul_mul_assoc,mul_neg]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module
private theorem euler_geometric (n : ℕ) : bracket E (Q^n)=(-(n:ℂ)) • (Q^(n-1)*delta) := by
  cases n with
  | zero => simp [bracket]
  | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using euler_geometric_succ n
private theorem euler_theta (m ell : ℕ) : bracket E (T m ell)=B m ell*delta := by
  change bracket E (Q^(m+1)-Q^(ell+1))=B m ell*delta
  rw [bracket_sub,euler_geometric_succ,euler_geometric_succ]
  change _=((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m)*delta
  simp only [sub_mul,smul_mul_assoc]
  module
private theorem euler_peak (m ell : ℕ) : bracket E (B m ell)=C m ell*delta := by
  change bracket E ((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m)=C m ell*delta
  rw [bracket_sub,bracket_smul,bracket_smul,euler_geometric,euler_geometric]
  change _=((m*(m+1):ℂ) • Q^(m-1)-(ell*(ell+1):ℂ) • Q^(ell-1))*delta
  simp only [sub_mul,smul_mul_assoc,smul_smul]
  module

private theorem phi_bracket (A:End):bracket Phi A=bracket E A :=
  SourceScalarAffineScaleTransport.generator_commutator A
private theorem euler_square : bracket E (S^2)=(2:ℂ) • (S*(S^3-S)) := by
  rw [pow_two,bracket_product,euler_inverse]
  noncomm_ring
  module
private def firstCore (n:ℕ):End := (n+1:ℂ) • (S*Q^n)
private def secondCore (n:ℕ):End := (n*(n+1):ℂ) • (S^2*Q^(n-1))
private def coreFirst0 (m ell:ℕ):End := (1-S^2)*(firstCore m-firstCore ell)
private def coreSecond0 (m ell:ℕ):End := (1-S^2)^2*(secondCore m-secondCore ell)+
  (1-S^2)*((3:ℂ) • S^2-1)*(firstCore m-firstCore ell)
private def coreFirst1 (m ell:ℕ):End := S*(1-S^2)*T m ell-S*coreFirst0 m ell
private def coreSecond1 (m ell:ℕ):End := S*(1-S^2)*((3:ℂ) • S^2-1)*T m ell+
  (2:ℂ) • (S*(1-S^2)*coreFirst0 m ell)-S*coreSecond0 m ell
private theorem firstCore_source (m ell:ℕ):S*B m ell=firstCore ell-firstCore m := by
  unfold B phiFirstPeak firstCore
  simp only [mul_sub,mul_smul_comm]
private theorem secondCore_source (m ell:ℕ):S^2*C m ell=secondCore m-secondCore ell := by
  unfold C phiSecondPeak secondCore
  simp only [mul_sub,mul_smul_comm]
private theorem peak_S (m ell:ℕ):Commute (B m ell) S := by
  have hQ:Commute Q S := (Commute.one_left S).sub_left (Commute.refl S)
  exact ((hQ.pow_left ell).smul_left _).sub_left ((hQ.pow_left m).smul_left _)
private theorem second_S (m ell:ℕ):Commute (C m ell) S := by
  have hQ:Commute Q S := (Commute.one_left S).sub_left (Commute.refl S)
  exact ((hQ.pow_left (m-1)).smul_left _).sub_left ((hQ.pow_left (ell-1)).smul_left _)
private theorem inverse_delta:bracket E delta=((3:ℂ) • S^2-1)*delta := by
  unfold delta
  rw [bracket_sub]
  have h3:bracket E (S^3)=(3:ℂ) • (S^2*(S^3-S)) := by
    rw [show S^3=S*(S*S) by noncomm_ring,bracket_product,bracket_product,euler_inverse]
    noncomm_ring
    module
  rw [h3,euler_inverse]
  simp only [sub_mul,one_mul,smul_mul_assoc]
private theorem source_first0 (m ell:ℕ):bracket Phi (T m ell)=coreFirst0 m ell := by
  rw [phi_bracket,euler_theta]
  have hb:=firstCore_source m ell
  unfold coreFirst0
  rw [show firstCore m-firstCore ell= -(S*B m ell) by rw [hb];abel]
  have hd:Commute (B m ell) delta := ((peak_S m ell).pow_right 3).sub_right (peak_S m ell)
  rw [hd.eq]
  unfold delta
  noncomm_ring
private theorem source_second0 (m ell:ℕ):bracket Phi (bracket Phi (T m ell))=coreSecond0 m ell := by
  rw [phi_bracket,phi_bracket,euler_theta,bracket_product,euler_peak,inverse_delta]
  have hb:=firstCore_source m ell
  have hc:=secondCore_source m ell
  unfold coreSecond0
  rw [show firstCore m-firstCore ell= -(S*B m ell) by rw [hb];abel,←hc]
  have hCdelta:Commute (C m ell) delta := ((second_S m ell).pow_right 3).sub_right (second_S m ell)
  have hBJ:Commute (B m ell) ((3:ℂ) • S^2-1) :=
    (((peak_S m ell).pow_right 2).smul_right _).sub_right (Commute.one_right _)
  have hBdelta:Commute (B m ell) delta := ((peak_S m ell).pow_right 3).sub_right (peak_S m ell)
  have hCC:(C m ell*delta)*delta=delta*delta*C m ell := by
    rw [hCdelta.eq,mul_assoc,hCdelta.eq,←mul_assoc]
  have hBB:B m ell*(((3:ℂ) • S^2-1)*delta)=((3:ℂ) • S^2-1)*delta*B m ell := by
    rw [←mul_assoc,hBJ.eq,mul_assoc,hBdelta.eq,←mul_assoc]
  rw [hCC,hBB]
  unfold delta
  noncomm_ring
  module
private theorem source_first1 (m ell:ℕ):bracket Phi (-(S*T m ell))=coreFirst1 m ell := by
  have hneg (A:End):bracket Phi (-A)= -bracket Phi A := by unfold bracket;noncomm_ring
  rw [hneg,bracket_product,phi_bracket,euler_inverse,source_first0]
  unfold coreFirst1 delta
  noncomm_ring
private theorem source_second1 (m ell:ℕ):bracket Phi (bracket Phi (-(S*T m ell)))=coreSecond1 m ell := by
  have hneg (A:End):bracket Phi (-A)= -bracket Phi A := by unfold bracket;noncomm_ring
  have hS:bracket Phi S=delta := by rw [phi_bracket,euler_inverse]
  have hdelta:bracket Phi delta=((3:ℂ) • S^2-1)*delta := by rw [phi_bracket,inverse_delta]
  have hsecondT:bracket Phi (coreFirst0 m ell)=coreSecond0 m ell := by
    rw [←source_first0]
    exact source_second0 m ell
  rw [hneg,bracket_product,hS]
  rw [hneg,bracket_add,bracket_product,bracket_product,hdelta,source_first0,hS,hsecondT]
  unfold coreSecond1 delta
  noncomm_ring
  module
private def secondBoundary (n:ℕ):Op := ((n:ℂ)*(n+1:ℂ)) • (phiComplement^(n-1)*(1-phiComplement)^2)
private theorem second_gradient_complex {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E]
    (Q:E →L[ℂ] E)(n:ℕ):
    PositiveContractionRitt.secondGradient Q n=((n:ℂ)*(n+1:ℂ)) • (Q^(n-1)*(1-Q)^2) := by
  unfold PositiveContractionRitt.secondGradient
  have h:=RCLike.real_smul_eq_coe_smul (K:=ℂ) ((n:ℝ)*(n+1:ℝ)) (Q^(n-1)*(1-Q)^2)
  simpa only [RCLike.ofReal_mul,RCLike.ofReal_add,RCLike.ofReal_natCast,RCLike.ofReal_one] using h
private theorem second_time (n:ℕ):timeRead (secondBoundary n)=PositiveContractionRitt.secondGradient (timeRead phiComplement) n := by
  have hsub:timeRead ((1:Op)-phiComplement)=(1:TH →L[ℂ] TH)-timeRead phiComplement :=
    (time_sub 1 phiComplement).trans (congrArg (fun A:TH →L[ℂ] TH=>A-timeRead phiComplement) time_one)
  have hs:timeRead (((1:Op)-phiComplement)^2)=((1:TH →L[ℂ] TH)-timeRead phiComplement)^2 :=
    (time_pow (1-phiComplement) 2).trans (congrArg (fun A:TH →L[ℂ] TH=>A^2) hsub)
  have hmul:timeRead (phiComplement^(n-1)*(1-phiComplement)^2)=
      (timeRead phiComplement)^(n-1)*((1:TH →L[ℂ] TH)-timeRead phiComplement)^2 :=
    (time_mul (phiComplement^(n-1)) ((1-phiComplement)^2)).trans
      (congrArg₂ (fun A B:TH →L[ℂ] TH=>A*B) (time_pow phiComplement (n-1)) hs)
  have h:timeRead (secondBoundary n)=((n:ℂ)*(n+1:ℂ)) •
      ((timeRead phiComplement)^(n-1)*((1:TH →L[ℂ] TH)-timeRead phiComplement)^2) :=
    (time_smul ((n:ℂ)*(n+1:ℂ)) (phiComplement^(n-1)*(1-phiComplement)^2)).trans
      (congrArg (fun A:TH →L[ℂ] TH=>((n:ℂ)*(n+1:ℂ)) • A) hmul)
  exact h.trans (second_gradient_complex (E:=TH) (timeRead phiComplement) n).symm
private theorem second_time_strong (x:TH):Tendsto (fun n=>timeRead (secondBoundary n) x) atTop (𝓝 0) := by
  have h:=PositiveContractionRitt.secondGradient_strong (timeRead phiComplement) time_phi_positive time_phi_le_one x
  exact h.congr' (Eventually.of_forall (fun n=>congrArg (fun A:TH →L[ℂ] TH=>A x) (second_time n).symm))
private def boundedF : Op := 1-phiInverseBounded^2
private def boundedJ : Op := (3:ℂ) • phiInverseBounded^2-1
private def firstLeaf0 (n:ℕ):Op := boundedF*firstBoundary n
private def firstLeaf1 (n:ℕ):Op := phiInverseBounded*boundedF*phiComplement^(n+1)-phiInverseBounded*firstLeaf0 n
private def secondLeaf0 (n:ℕ):Op := boundedF^2*secondBoundary n+boundedF*boundedJ*firstBoundary n
private def secondLeaf1 (n:ℕ):Op := phiInverseBounded*boundedF*boundedJ*phiComplement^(n+1)+
  (2:ℂ) • (phiInverseBounded*boundedF*firstLeaf0 n)-phiInverseBounded*secondLeaf0 n
private theorem firstLeaf0_time_strong (x:TH):Tendsto (fun n=>timeRead (firstLeaf0 n) x) atTop (𝓝 0) := by
  have h:=((timeRead boundedF).continuous.tendsto 0).comp (first_time_strong x)
  simp only [map_zero] at h
  simpa only [Function.comp_def,firstLeaf0,time_mul,mul_apply_eq_comp] using h
private theorem secondLeaf0_time_strong (x:TH):Tendsto (fun n=>timeRead (secondLeaf0 n) x) atTop (𝓝 0) := by
  have h0:=((timeRead (boundedF^2)).continuous.tendsto 0).comp (second_time_strong x)
  have h1:=((timeRead (boundedF*boundedJ)).continuous.tendsto 0).comp (first_time_strong x)
  simp only [map_zero] at h0 h1
  have h:=h0.add h1
  simpa only [Function.comp_def,secondLeaf0,time_add,time_mul,add_apply,mul_apply_eq_comp,add_zero] using h
private theorem mixed_stream_cauchy {V:Type*}
    [NormedAddCommGroup V][InnerProductSpace ℂ V][CompleteSpace V]
    (Q A B:V →L[ℂ] V)(hQ0:0 ≤ Q)(hQ1:Q ≤ 1)(y:V)(f h:ℕ → V)
    (hf:Tendsto f atTop (𝓝 0))(hh:Tendsto h atTop (𝓝 0)):
    CauchySeq (fun j:ℕ=>f j+(A ((Q^(j+1)) y)-B (h j))) := by
  have hq0:CauchySeq (fun j:ℕ=>(Q^j) y):=
    SourceRelativePowerTail.decreasing_distance_cauchy (E:=V)
      (fun j:ℕ=>(Q^j) y)
      (fun m n hmn=>SourceRelativePowerTail.positive_power_distance
        (E:=V) Q hQ0 hQ1 y hmn)
  have hq:CauchySeq (fun j:ℕ=>(Q^(j+1)) y) := by
    simpa only [Function.comp_def] using
      hq0.comp_tendsto (tendsto_add_atTop_nat 1)
  have ha:CauchySeq (fun j:ℕ=>A ((Q^(j+1)) y)) := by
    simpa only [Function.comp_def] using A.uniformContinuous.comp_cauchySeq hq
  have hb:CauchySeq (fun j:ℕ=>B (h j)) := by
    simpa only [Function.comp_def] using B.uniformContinuous.comp_cauchySeq hh.cauchySeq
  have hs:=hf.cauchySeq.add (ha.add hb.neg)
  convert hs using 1 <;> try rfl
  funext j
  simp only [Pi.add_apply,Pi.neg_apply,sub_eq_add_neg]

private theorem firstLeaf1_time (j:ℕ)(y:TH):
    timeRead (firstLeaf1 j) y=timeRead (phiInverseBounded*boundedF) (((timeRead phiComplement)^(j+1)) y)-
      timeRead phiInverseBounded (timeRead (firstLeaf0 j) y) := by
  have he:timeRead (firstLeaf1 j)=
      timeRead (phiInverseBounded*boundedF)*(timeRead phiComplement)^(j+1)-
      timeRead phiInverseBounded*timeRead (firstLeaf0 j) :=
    (time_sub (phiInverseBounded*boundedF*phiComplement^(j+1)) (phiInverseBounded*firstLeaf0 j)).trans
      (congrArg₂ (fun A B:TH →L[ℂ] TH=>A-B)
        ((time_mul (phiInverseBounded*boundedF) (phiComplement^(j+1))).trans
          (congrArg (fun A:TH →L[ℂ] TH=>timeRead (phiInverseBounded*boundedF)*A) (time_pow phiComplement (j+1))))
        (time_mul phiInverseBounded (firstLeaf0 j)))
  exact congrArg (fun A:TH →L[ℂ] TH=>A y) he
private theorem secondLeaf1_time (j:ℕ)(y:TH):
    timeRead (secondLeaf1 j) y=
      timeRead (phiInverseBounded*boundedF*boundedJ) (((timeRead phiComplement)^(j+1)) y)+
      (2:ℂ) • timeRead (phiInverseBounded*boundedF) (timeRead (firstLeaf0 j) y)-
      timeRead phiInverseBounded (timeRead (secondLeaf0 j) y) := by
  have h0:timeRead (phiInverseBounded*boundedF*boundedJ*phiComplement^(j+1))=
      timeRead (phiInverseBounded*boundedF*boundedJ)*(timeRead phiComplement)^(j+1) :=
    (time_mul (phiInverseBounded*boundedF*boundedJ) (phiComplement^(j+1))).trans
      (congrArg (fun A:TH →L[ℂ] TH=>timeRead (phiInverseBounded*boundedF*boundedJ)*A) (time_pow phiComplement (j+1)))
  have h1:timeRead ((2:ℂ) • (phiInverseBounded*boundedF*firstLeaf0 j))=
      (2:ℂ) • (timeRead (phiInverseBounded*boundedF)*timeRead (firstLeaf0 j)) :=
    (time_smul 2 (phiInverseBounded*boundedF*firstLeaf0 j)).trans
      (congrArg (fun A:TH →L[ℂ] TH=>(2:ℂ) • A) (time_mul (phiInverseBounded*boundedF) (firstLeaf0 j)))
  have h2:timeRead (phiInverseBounded*secondLeaf0 j)=timeRead phiInverseBounded*timeRead (secondLeaf0 j) :=
    time_mul phiInverseBounded (secondLeaf0 j)
  have he:timeRead (secondLeaf1 j)=
      timeRead (phiInverseBounded*boundedF*boundedJ)*(timeRead phiComplement)^(j+1)+
      (2:ℂ) • (timeRead (phiInverseBounded*boundedF)*timeRead (firstLeaf0 j))-
      timeRead phiInverseBounded*timeRead (secondLeaf0 j) :=
    (time_sub (phiInverseBounded*boundedF*boundedJ*phiComplement^(j+1)+(2:ℂ) • (phiInverseBounded*boundedF*firstLeaf0 j))
      (phiInverseBounded*secondLeaf0 j)).trans
      (congrArg₂ (fun A B:TH →L[ℂ] TH=>A-B)
        ((time_add (phiInverseBounded*boundedF*boundedJ*phiComplement^(j+1)) ((2:ℂ) • (phiInverseBounded*boundedF*firstLeaf0 j))).trans
          (congrArg₂ (fun A B:TH →L[ℂ] TH=>A+B) h0 h1)) h2)
  exact congrArg (fun A:TH →L[ℂ] TH=>A y) he
private theorem first_jet_stream_cauchy (x y:TH):CauchySeq
    (fun j:ℕ=>timeRead (firstLeaf0 j) x+timeRead (firstLeaf1 j) y) := by
  have h:CauchySeq (fun j:ℕ=>timeRead (firstLeaf0 j) x+
      (timeRead (phiInverseBounded*boundedF) (((timeRead phiComplement)^(j+1)) y)-
        timeRead phiInverseBounded (timeRead (firstLeaf0 j) y))) :=
    mixed_stream_cauchy (V:=TH) (timeRead phiComplement)
      (timeRead (phiInverseBounded*boundedF)) (timeRead phiInverseBounded)
      time_phi_positive time_phi_le_one y
      (fun j:ℕ=>timeRead (firstLeaf0 j) x) (fun j:ℕ=>timeRead (firstLeaf0 j) y)
      (firstLeaf0_time_strong x) (firstLeaf0_time_strong y)
  simpa only [firstLeaf1_time] using h

private theorem second_jet_stream_cauchy (x y:TH):CauchySeq
    (fun j:ℕ=>timeRead (secondLeaf0 j) x+timeRead (secondLeaf1 j) y) := by
  have h1:=((timeRead (phiInverseBounded*boundedF)).continuous.tendsto 0).comp
    (firstLeaf0_time_strong y)
  simp only [map_zero] at h1
  have hf:Tendsto (fun j:ℕ=>timeRead (secondLeaf0 j) x+(2:ℂ) •
      timeRead (phiInverseBounded*boundedF) (timeRead (firstLeaf0 j) y)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,smul_zero,add_zero] using
      (secondLeaf0_time_strong x).add (h1.const_smul (2:ℂ))
  have h:CauchySeq (fun j:ℕ=>
      (timeRead (secondLeaf0 j) x+(2:ℂ) •
        timeRead (phiInverseBounded*boundedF) (timeRead (firstLeaf0 j) y))+
      (timeRead (phiInverseBounded*boundedF*boundedJ) (((timeRead phiComplement)^(j+1)) y)-
        timeRead phiInverseBounded (timeRead (secondLeaf0 j) y))) :=
    mixed_stream_cauchy (V:=TH) (timeRead phiComplement)
      (timeRead (phiInverseBounded*boundedF*boundedJ)) (timeRead phiInverseBounded)
      time_phi_positive time_phi_le_one y
      (fun j:ℕ=>timeRead (secondLeaf0 j) x+(2:ℂ) •
        timeRead (phiInverseBounded*boundedF) (timeRead (firstLeaf0 j) y))
      (fun j:ℕ=>timeRead (secondLeaf0 j) y) hf (secondLeaf0_time_strong y)
  have he (j:ℕ):(timeRead (secondLeaf0 j) x+timeRead (secondLeaf1 j) y)=
      (timeRead (secondLeaf0 j) x+(2:ℂ) •
        timeRead (phiInverseBounded*boundedF) (timeRead (firstLeaf0 j) y))+
      (timeRead (phiInverseBounded*boundedF*boundedJ) (((timeRead phiComplement)^(j+1)) y)-
        timeRead phiInverseBounded (timeRead (secondLeaf0 j) y)) := by
    have hx:=congrArg (fun v:TH=>timeRead (secondLeaf0 j) x+v) (secondLeaf1_time j y)
    exact hx.trans (by abel)
  have heq:(fun j:ℕ=>timeRead (secondLeaf0 j) x+timeRead (secondLeaf1 j) y)=
      (fun j:ℕ=>(timeRead (secondLeaf0 j) x+(2:ℂ) • timeRead (phiInverseBounded*boundedF) (timeRead (firstLeaf0 j) y))+
        (timeRead (phiInverseBounded*boundedF*boundedJ) (((timeRead phiComplement)^(j+1)) y)-
          timeRead phiInverseBounded (timeRead (secondLeaf0 j) y))) := funext he
  exact heq.symm ▸ h

private def jetLeaf (second:Bool)(i:Fin 2)(n:ℕ):Op :=
  if second then ![secondLeaf0 n,secondLeaf1 n] i else ![firstLeaf0 n,firstLeaf1 n] i
private def jetFamily (second:Bool)(n:ℕ)(f g:Family L2H sourceFilter):Family L2H sourceFilter :=
  readFamily (jetLeaf second 0 n) f+readFamily (jetLeaf second 1 n) g
private theorem read_family_coe (A:Op)(f:Family L2H sourceFilter):
    (readFamily A f:TH)=timeRead A (f:TH) := by
  unfold readFamily timeRead familyReader
  exact (lift_coe sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) f).symm
private theorem jet_family_coe (second:Bool)(j:ℕ)(f g:Family L2H sourceFilter):
    (jetFamily second j f g:TH)=timeRead (jetLeaf second 0 j) (f:TH)+timeRead (jetLeaf second 1 j) (g:TH) :=
  (UniformSpace.Completion.coe_add (readFamily (jetLeaf second 0 j) f) (readFamily (jetLeaf second 1 j) g)).trans
    (congrArg₂ (fun x y:TH=>x+y) (read_family_coe (jetLeaf second 0 j) f) (read_family_coe (jetLeaf second 1 j) g))
private theorem jet_stream_cauchy (second:Bool)(f g:Family L2H sourceFilter):
    CauchySeq (fun n=>(jetFamily second n f g:TH)) := by
  cases second
  · have h:=first_jet_stream_cauchy (f:TH) (g:TH)
    simpa only [jet_family_coe,jetLeaf,Bool.false_eq_true,ite_false,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.head_cons] using h
  · have h:=second_jet_stream_cauchy (f:TH) (g:TH)
    simpa only [jet_family_coe,jetLeaf,ite_true,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.head_cons] using h

private theorem jet_family_difference_tail (second:Bool)(f g:Family L2H sourceFilter):
    ∀ε:ℝ,0<ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→
      ∀ᶠF in (sourceFilter:Filter Index),‖value (jetFamily second m f g-jetFamily second ell f g) F‖^2 ≤ ε := by
  intro ε hε
  have hc:CauchySeq (fun j:ℕ=>(jetFamily second j f g:TH)):=jet_stream_cauchy second f g
  obtain ⟨N,hN⟩:=Metric.cauchySeq_iff.mp hc (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨N,fun m hm ell hml=>?_⟩
  let d:=jetFamily second m f g-jetFamily second ell f g
  have hd:‖d‖^2<ε := by
    have hdist:=hN m hm ell (hm.trans hml)
    rw [dist_eq_norm] at hdist
    have hnorm:‖d‖=‖(jetFamily second m f g:TH)-(jetFamily second ell f g:TH)‖ := by
      rw [←UniformSpace.Completion.coe_sub,UniformSpace.Completion.norm_coe]
    rw [hnorm]
    have hs:=Real.sq_sqrt hε.le
    nlinarith only [hdist,hs,norm_nonneg ((jetFamily second m f g:TH)-(jetFamily second ell f g:TH)),Real.sqrt_nonneg ε]
  filter_upwards [(square_tendsto sourceFilter d).eventually (gt_mem_nhds hd)] with F hF
  exact hF.le
private theorem acted_pair_integral (A B:Op)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(F:Index)(g k:H):
    (∫⁻t:ℝ,ENNReal.ofReal (‖A (finiteResolvent F (actualFrequency advanced μ t) g)+
      B (finiteResolvent F (actualFrequency advanced μ t) k)‖^2))=
    ENNReal.ofReal (‖value (readFamily A (wholeInputFamily advanced μ hμ g)+
      readFamily B (wholeInputFamily advanced μ hμ k)) F‖^2) := by
  let r:=readFamily A (wholeInputFamily advanced μ hμ g)+readFamily B (wholeInputFamily advanced μ hμ k)
  have he:(fun t:ℝ=>‖A (finiteResolvent F (actualFrequency advanced μ t) g)+
      B (finiteResolvent F (actualFrequency advanced μ t) k)‖^2)=ᵐ[MeasureTheory.volume]
    (fun t:ℝ=>‖value r F t‖^2) := by
    filter_upwards [A.coeFn_compLpL (wholeFiniteInput advanced μ hμ F g),
      B.coeFn_compLpL (wholeFiniteInput advanced μ hμ F k),
      (whole_memLp advanced μ hμ F g).coeFn_toLp,
      (whole_memLp advanced μ hμ F k).coeFn_toLp,
      Lp.coeFn_add (A.compLpL 2 MeasureTheory.volume (wholeFiniteInput advanced μ hμ F g))
        (B.compLpL 2 MeasureTheory.volume (wholeFiniteInput advanced μ hμ F k))] with t hA hB hg hk hadd
    change _=‖(A.compLpL 2 MeasureTheory.volume (wholeFiniteInput advanced μ hμ F g)+
      B.compLpL 2 MeasureTheory.volume (wholeFiniteInput advanced μ hμ F k)) t‖^2
    rw [hadd]
    change _=‖((A.compLpL 2 MeasureTheory.volume (wholeFiniteInput advanced μ hμ F g)) t)+
      ((B.compLpL 2 MeasureTheory.volume (wholeFiniteInput advanced μ hμ F k)) t)‖^2
    rw [hA,hB]
    change wholeFiniteInput advanced μ hμ F g t=finiteResolvent F (actualFrequency advanced μ t) g at hg
    change wholeFiniteInput advanced μ hμ F k t=finiteResolvent F (actualFrequency advanced μ t) k at hk
    rw [hg,hk]
  have hi:=(square_integrable MeasureTheory.volume (value r F)).congr he.symm
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _=>sq_nonneg _)),
    integral_congr_ae he,←square_integral]
private def jetDifference (second:Bool)(i:Fin 2)(m ell:ℕ):Op := jetLeaf second i m-jetLeaf second i ell
private theorem lp_sub (A B:Op):
    (A-B).compLpL 2 (MeasureTheory.volume:Measure ℝ)=
      A.compLpL 2 (MeasureTheory.volume:Measure ℝ)-B.compLpL 2 (MeasureTheory.volume:Measure ℝ) := by
  have he:A-B=A+(-1:ℂ) • B := by module
  have hs:(A-B).compLpL 2 (MeasureTheory.volume:Measure ℝ)=
      A.compLpL 2 (MeasureTheory.volume:Measure ℝ)+(-1:ℂ) • B.compLpL 2 (MeasureTheory.volume:Measure ℝ) :=
    (congrArg (fun C:Op=>C.compLpL 2 (MeasureTheory.volume:Measure ℝ)) he).trans
      ((ContinuousLinearMap.add_compLpL (p:=2) (μ:=(MeasureTheory.volume:Measure ℝ)) A ((-1:ℂ) • B)).trans
        (congrArg (fun C:L2H →L[ℂ] L2H=>A.compLpL 2 MeasureTheory.volume+C)
          (ContinuousLinearMap.smul_compLpL (p:=2) (μ:=(MeasureTheory.volume:Measure ℝ)) (-1:ℂ) B)))
  exact hs.trans (by module)
private theorem read_family_sub (A B:Op)(f:Family L2H sourceFilter):
    readFamily (A-B) f=readFamily A f-readFamily B f := by
  apply Family.ext
  funext F
  change ((A-B).compLpL 2 MeasureTheory.volume) (value f F)=
    (A.compLpL 2 MeasureTheory.volume) (value f F)-(B.compLpL 2 MeasureTheory.volume) (value f F)
  exact congrArg (fun C:L2H →L[ℂ] L2H=>C (value f F)) (lp_sub A B)
private theorem acted_jet_integral (second:Bool)(m ell:ℕ)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(F:Index)(g k:H):
    (∫⁻t:ℝ,ENNReal.ofReal (‖jetDifference second 0 m ell (finiteResolvent F (actualFrequency advanced μ t) g)+
      jetDifference second 1 m ell (finiteResolvent F (actualFrequency advanced μ t) k)‖^2))=
    ENNReal.ofReal (‖value (jetFamily second m (wholeInputFamily advanced μ hμ g) (wholeInputFamily advanced μ hμ k)-
      jetFamily second ell (wholeInputFamily advanced μ hμ g) (wholeInputFamily advanced μ hμ k)) F‖^2) := by
  rw [acted_pair_integral (jetDifference second 0 m ell) (jetDifference second 1 m ell) advanced μ hμ F g k]
  have he:readFamily (jetDifference second 0 m ell) (wholeInputFamily advanced μ hμ g)+
    readFamily (jetDifference second 1 m ell) (wholeInputFamily advanced μ hμ k)=
    jetFamily second m (wholeInputFamily advanced μ hμ g) (wholeInputFamily advanced μ hμ k)-
    jetFamily second ell (wholeInputFamily advanced μ hμ g) (wholeInputFamily advanced μ hμ k) := by
    change readFamily (jetLeaf second 0 m-jetLeaf second 0 ell) (wholeInputFamily advanced μ hμ g)+
      readFamily (jetLeaf second 1 m-jetLeaf second 1 ell) (wholeInputFamily advanced μ hμ k)=
      (readFamily (jetLeaf second 0 m) (wholeInputFamily advanced μ hμ g)+readFamily (jetLeaf second 1 m) (wholeInputFamily advanced μ hμ k))-
      (readFamily (jetLeaf second 0 ell) (wholeInputFamily advanced μ hμ g)+readFamily (jetLeaf second 1 ell) (wholeInputFamily advanced μ hμ k))
    rw [read_family_sub,read_family_sub]
    abel
  exact congrArg (fun r:Family L2H sourceFilter=>ENNReal.ofReal (‖value r F‖^2)) he
private theorem actual_jet_difference_common_tail (μ:ℝ)(hμ:0<μ)(g k:H):
    ∀ε:ℝ,0<ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠF in (sourceFilter:Filter Index),
      ∀advanced second:Bool,
      (∫⁻t:ℝ,ENNReal.ofReal (‖jetDifference second 0 m ell (finiteResolvent F (actualFrequency advanced μ t) g)+
        jetDifference second 1 m ell (finiteResolvent F (actualFrequency advanced μ t) k)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N00,h00⟩:=jet_family_difference_tail false (wholeInputFamily false μ hμ g) (wholeInputFamily false μ hμ k) ε hε
  obtain ⟨N01,h01⟩:=jet_family_difference_tail true (wholeInputFamily false μ hμ g) (wholeInputFamily false μ hμ k) ε hε
  obtain ⟨N10,h10⟩:=jet_family_difference_tail false (wholeInputFamily true μ hμ g) (wholeInputFamily true μ hμ k) ε hε
  obtain ⟨N11,h11⟩:=jet_family_difference_tail true (wholeInputFamily true μ hμ g) (wholeInputFamily true μ hμ k) ε hε
  refine ⟨max (max N00 N01) (max N10 N11),fun m hm ell hml=>?_⟩
  filter_upwards [h00 m (by omega) ell hml,h01 m (by omega) ell hml,
    h10 m (by omega) ell hml,h11 m (by omega) ell hml] with F hf0 hf1 ht0 ht1
  intro advanced second
  rw [acted_jet_integral second m ell advanced μ hμ F g k]
  cases advanced <;> cases second
  · exact ENNReal.ofReal_le_ofReal hf0
  · exact ENNReal.ofReal_le_ofReal hf1
  · exact ENNReal.ofReal_le_ofReal ht0
  · exact ENNReal.ofReal_le_ofReal ht1
private def CoreReturn (A:Op)(a:End):Prop:=∀f:QuantumTest,A (embed f)=embed (a f)
private theorem core_mul {A B:Op}{a b:End}(ha:CoreReturn A a)(hb:CoreReturn B b):
    CoreReturn (A*B) (a*b) := by intro f;change A (B (embed f))=embed (a (b f));rw [hb,ha]
private theorem core_add {A B:Op}{a b:End}(ha:CoreReturn A a)(hb:CoreReturn B b):
    CoreReturn (A+B) (a+b) := by intro f;change A (embed f)+B (embed f)=embed (a f+b f);rw [ha,hb,map_add]
private theorem core_sub {A B:Op}{a b:End}(ha:CoreReturn A a)(hb:CoreReturn B b):
    CoreReturn (A-B) (a-b) := by intro f;change A (embed f)-B (embed f)=embed (a f-b f);rw [ha,hb,map_sub]
private theorem core_smul {A:Op}{a:End}(ha:CoreReturn A a)(c:ℂ):
    CoreReturn (c • A) (c • a) := by intro f;change c • A (embed f)=embed (c • a f);rw [ha,map_smul]
private theorem core_one:CoreReturn (1:Op) (1:End):=fun _=>rfl
private theorem core_pow {A:Op}{a:End}(ha:CoreReturn A a)(n:ℕ):CoreReturn (A^n) (a^n) := by
  induction n with
  | zero=>simpa only [pow_zero] using core_one
  | succ n ih=>simpa only [pow_succ] using core_mul ih ha
private theorem first_core_return (n:ℕ):CoreReturn (firstBoundary n) (firstCore n) := by
  have hS:(1:Op)-phiComplement=phiInverseBounded:=by unfold phiComplement;abel
  have hc:Commute Q S:=(Commute.one_left S).sub_left (Commute.refl S)
  have h:=core_smul (core_mul (phi_power_core n) phi_inverse_core) (n+1:ℂ)
  unfold firstBoundary firstCore
  rw [hS]
  simpa only [(hc.pow_left n).eq] using h
private theorem second_core_return (n:ℕ):CoreReturn (secondBoundary n) (secondCore n) := by
  have hS:(1:Op)-phiComplement=phiInverseBounded:=by unfold phiComplement;abel
  have hc:Commute Q S:=(Commute.one_left S).sub_left (Commute.refl S)
  have h:=core_smul (core_mul (phi_power_core (n-1)) (core_pow phi_inverse_core 2)) ((n:ℂ)*(n+1:ℂ))
  unfold secondBoundary secondCore
  rw [hS]
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,((hc.pow_left (n-1)).pow_right 2).eq] using h
private theorem boundedF_core:CoreReturn boundedF (1-S^2):=
  core_sub core_one (core_pow phi_inverse_core 2)
private theorem boundedJ_core:CoreReturn boundedJ ((3:ℂ) • S^2-1):=
  core_sub (core_smul (core_pow phi_inverse_core 2) 3) core_one
private def firstLeafCore0(n:ℕ):End:=(1-S^2)*firstCore n
private def firstLeafCore1(n:ℕ):End:=S*(1-S^2)*Q^(n+1)-S*firstLeafCore0 n
private def secondLeafCore0(n:ℕ):End:=(1-S^2)^2*secondCore n+(1-S^2)*((3:ℂ) • S^2-1)*firstCore n
private def secondLeafCore1(n:ℕ):End:=S*(1-S^2)*((3:ℂ) • S^2-1)*Q^(n+1)+
  (2:ℂ) • (S*(1-S^2)*firstLeafCore0 n)-S*secondLeafCore0 n
private theorem firstLeaf0_core (n:ℕ):CoreReturn (firstLeaf0 n) (firstLeafCore0 n):=
  core_mul boundedF_core (first_core_return n)
private theorem firstLeaf1_core (n:ℕ):CoreReturn (firstLeaf1 n) (firstLeafCore1 n):=
  core_sub (core_mul (core_mul phi_inverse_core boundedF_core) (phi_power_core (n+1)))
    (core_mul phi_inverse_core (firstLeaf0_core n))
private theorem secondLeaf0_core (n:ℕ):CoreReturn (secondLeaf0 n) (secondLeafCore0 n):=
  core_add (core_mul (core_pow boundedF_core 2) (second_core_return n))
    (core_mul (core_mul boundedF_core boundedJ_core) (first_core_return n))
private theorem secondLeaf1_core (n:ℕ):CoreReturn (secondLeaf1 n) (secondLeafCore1 n):=
  core_sub (core_add (core_mul (core_mul (core_mul phi_inverse_core boundedF_core) boundedJ_core) (phi_power_core (n+1)))
    (core_smul (core_mul (core_mul phi_inverse_core boundedF_core) (firstLeaf0_core n)) 2))
    (core_mul phi_inverse_core (secondLeaf0_core n))
private theorem first0_difference (m ell:ℕ):firstLeafCore0 m-firstLeafCore0 ell=coreFirst0 m ell := by
  unfold firstLeafCore0 coreFirst0
  noncomm_ring
private theorem first1_difference (m ell:ℕ):firstLeafCore1 m-firstLeafCore1 ell=coreFirst1 m ell := by
  unfold firstLeafCore1 coreFirst1
  rw [←first0_difference]
  unfold T phiThetaAction Q
  noncomm_ring
private theorem second0_difference (m ell:ℕ):secondLeafCore0 m-secondLeafCore0 ell=coreSecond0 m ell := by
  unfold secondLeafCore0 coreSecond0
  noncomm_ring
private theorem second1_difference (m ell:ℕ):secondLeafCore1 m-secondLeafCore1 ell=coreSecond1 m ell := by
  unfold secondLeafCore1 coreSecond1
  rw [←first0_difference,←second0_difference]
  unfold T phiThetaAction Q
  noncomm_ring
  module
private theorem first0_read(m ell:ℕ)(f:QuantumTest):
    jetDifference false 0 m ell (embed f)=embed (bracket Phi (T m ell) f) := by
  rw [source_first0]
  have h:=core_sub (firstLeaf0_core m) (firstLeaf0_core ell)
  change CoreReturn (jetDifference false 0 m ell) (firstLeafCore0 m-firstLeafCore0 ell) at h
  rw [first0_difference] at h
  exact h f
private theorem first1_read(m ell:ℕ)(f:QuantumTest):
    jetDifference false 1 m ell (embed f)=embed (bracket Phi (-(S*T m ell)) f) := by
  rw [source_first1]
  have h:=core_sub (firstLeaf1_core m) (firstLeaf1_core ell)
  change CoreReturn (jetDifference false 1 m ell) (firstLeafCore1 m-firstLeafCore1 ell) at h
  rw [first1_difference] at h
  exact h f
private theorem second0_read(m ell:ℕ)(f:QuantumTest):
    jetDifference true 0 m ell (embed f)=embed (bracket Phi (bracket Phi (T m ell)) f) := by
  rw [source_second0]
  have h:=core_sub (secondLeaf0_core m) (secondLeaf0_core ell)
  change CoreReturn (jetDifference true 0 m ell) (secondLeafCore0 m-secondLeafCore0 ell) at h
  rw [second0_difference] at h
  exact h f
private theorem second1_read(m ell:ℕ)(f:QuantumTest):
    jetDifference true 1 m ell (embed f)=embed (bracket Phi (bracket Phi (-(S*T m ell))) f) := by
  rw [source_second1]
  have h:=core_sub (secondLeaf1_core m) (secondLeaf1_core ell)
  change CoreReturn (jetDifference true 1 m ell) (secondLeafCore1 m-secondLeafCore1 ell) at h
  rw [second1_difference] at h
  exact h f

private abbrev RadiusSource := SourceClockRadiusAffineCutoff.phiRadiusSource
private theorem resolvent_embed (F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem core_source_embed (g:diagonal.domain):embed (coreEquiv.symm g)=(g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem radius_source_embed (g:diagonal.domain):embed (phiRadiusAction (coreEquiv.symm g))=(RadiusSource g:H) := rfl
private theorem first_read_pair (m ell:ℕ)(q h:QuantumTest):
    embed (bracket Phi (T m ell) q+bracket Phi (-(S*T m ell)) h)=
      jetDifference false 0 m ell (embed q)+jetDifference false 1 m ell (embed h) := by
  rw [map_add,first0_read,first1_read]
private theorem second_read_pair (m ell:ℕ)(q h:QuantumTest):
    embed (bracket Phi (bracket Phi (T m ell)) q+bracket Phi (bracket Phi (-(S*T m ell))) h)=
      jetDifference true 0 m ell (embed q)+jetDifference true 1 m ell (embed h) := by
  rw [map_add,second0_read,second1_read]
private theorem phaseFirst_read (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    embed (SourceClockPhiCombinedScalePressure.phaseFirst m ell F z hz g)=
      jetDifference false 0 m ell (finiteResolvent F z (g:H))+
        jetDifference false 1 m ell (finiteResolvent F z (RadiusSource g:H)) := by
  have hp:=first_read_pair m ell (resolventCore F z hz (coreEquiv.symm g))
    (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g)))
  have hq:embed (resolventCore F z hz (coreEquiv.symm g))=finiteResolvent F z (g:H) :=
    (resolvent_embed F z hz (coreEquiv.symm g)).trans (congrArg (fun x:H=>finiteResolvent F z x) (core_source_embed g))
  have hh:embed (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g)))=finiteResolvent F z (RadiusSource g:H) :=
    (resolvent_embed F z hz (phiRadiusAction (coreEquiv.symm g))).trans
      (congrArg (fun x:H=>finiteResolvent F z x) (radius_source_embed g))
  have hp2:=hp.trans (congrArg₂ (fun x y:H=>jetDifference false 0 m ell x+jetDifference false 1 m ell y) hq hh)
  simpa only [SourceClockPhiCombinedScalePressure.phaseFirst,Fin.sum_univ_two,SourceClockPhiCombinedScalePressure.phaseRow,SourceClockPhiCombinedScalePressure.phaseSeed,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using hp2
private theorem phaseSecond_read (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    embed (SourceClockPhiCombinedScalePressure.phaseSecond m ell F z hz g)=
      jetDifference true 0 m ell (finiteResolvent F z (g:H))+
        jetDifference true 1 m ell (finiteResolvent F z (RadiusSource g:H)) := by
  have hp:=second_read_pair m ell (resolventCore F z hz (coreEquiv.symm g))
    (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g)))
  have hq:embed (resolventCore F z hz (coreEquiv.symm g))=finiteResolvent F z (g:H) :=
    (resolvent_embed F z hz (coreEquiv.symm g)).trans (congrArg (fun x:H=>finiteResolvent F z x) (core_source_embed g))
  have hh:embed (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g)))=finiteResolvent F z (RadiusSource g:H) :=
    (resolvent_embed F z hz (phiRadiusAction (coreEquiv.symm g))).trans
      (congrArg (fun x:H=>finiteResolvent F z x) (radius_source_embed g))
  have hp2:=hp.trans (congrArg₂ (fun x y:H=>jetDifference true 0 m ell x+jetDifference true 1 m ell y) hq hh)
  simpa only [SourceClockPhiCombinedScalePressure.phaseSecond,Fin.sum_univ_two,SourceClockPhiCombinedScalePressure.phaseRow,SourceClockPhiCombinedScalePressure.phaseSeed,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using hp2
private theorem jet_norm_measurable (second:Bool)(m ell:ℕ)(F:Index)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Measurable (fun t:ℝ=>ENNReal.ofReal (‖jetDifference second 0 m ell (finiteResolvent F (actualFrequency advanced μ t) (g:H))+
      jetDifference second 1 m ell (finiteResolvent F (actualFrequency advanced μ t) (RadiusSource g:H))‖^2)) :=
  (((jetDifference second 0 m ell).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).add
    ((jetDifference second 1 m ell).continuous.comp
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const))).norm.pow 2 |>.measurable.ennreal_ofReal
/-- Both actual Phi profile jets, on the original two resolvent seeds, have one common source tail. -/
theorem actual_combined_profile_common_tail (μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ε:ℝ,0<ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻t:ℝ,ENNReal.ofReal (
        ‖embed (SourceClockPhiCombinedScalePressure.phaseFirst m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g)‖^2+
        ‖embed (SourceClockPhiCombinedScalePressure.phaseSecond m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_jet_difference_common_tail μ hμ (g:H) (RadiusSource g:H) (ε/2) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  simp_rw [phaseFirst_read,phaseSecond_read,ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [lintegral_add_right _ (jet_norm_measurable true m ell F advanced μ hμ g)]
  have hs:ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact (add_le_add (hF advanced false) (hF advanced true)).trans_eq hs

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_im_sq (advanced:Bool)(μ t:ℝ):
    (actualFrequency advanced μ t).im^2=μ^2 := by
  cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_sq]
/-- The complete AD contact has a common clipped error tail after retaining its true PD and PP slots. -/
theorem actual_combined_phase_common_payment (μ:ℝ)(hμ:0<μ)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ε:ℝ,0<ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻t:ℝ,ENNReal.ofReal (
        |SourceClockPhiCombinedScalePressure.combinedPhase m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g|-
        η*SourceClockPhiCombinedScalePressure.combinedPressure
          (SourceClockPhiNormalizedScalarBudget.normalizedState m ell F (actualFrequency advanced μ t)
            (frequency_nonreal advanced μ hμ t) g)-
        η*phiPositivePrice m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let A:ℝ:=32*μ^2/(3*sourceTime 0*η)
  let B:ℝ:=4*μ^2/(25*(sourceTime 0)^2*η)
  have hn:=lapse_pos
  have hA:0 ≤ A := by dsimp only [A];positivity
  have hB:0 ≤ B := by dsimp only [B];positivity
  have hC:0<A+B+1 := by linarith
  obtain ⟨N,hN⟩:=actual_combined_profile_common_tail μ hμ g (ε/(A+B+1)) (div_pos hε hC)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have hb:=hF advanced
  have hp:(∫⁻t:ℝ,ENNReal.ofReal (
        |SourceClockPhiCombinedScalePressure.combinedPhase m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g|-
        η*SourceClockPhiCombinedScalePressure.combinedPressure
          (SourceClockPhiNormalizedScalarBudget.normalizedState m ell F (actualFrequency advanced μ t)
            (frequency_nonreal advanced μ hμ t) g)-
        η*phiPositivePrice m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g)) ≤
      ENNReal.ofReal (A+B+1)*(∫⁻t:ℝ,ENNReal.ofReal (
        ‖embed (SourceClockPhiCombinedScalePressure.phaseFirst m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g)‖^2+
        ‖embed (SourceClockPhiCombinedScalePressure.phaseSecond m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g)‖^2)) := by
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro t
    dsimp only []
    rw [←ENNReal.ofReal_mul hC.le]
    apply ENNReal.ofReal_le_ofReal
    have h:= (SourceClockPhiCombinedScalePressure.actual_combined_phase_payment m ell F
      (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g η hη).2
    rw [frequency_im_sq] at h
    change _ ≤ η*SourceClockPhiCombinedScalePressure.combinedPressure _+η*phiPositivePrice m ell F _ _ g+
      A*‖embed (SourceClockPhiCombinedScalePressure.phaseFirst m ell F _ _ g)‖^2+
      B*‖embed (SourceClockPhiCombinedScalePressure.phaseSecond m ell F _ _ g)‖^2 at h
    nlinarith only [h,hA,hB,
      sq_nonneg ‖embed (SourceClockPhiCombinedScalePressure.phaseFirst m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g)‖,
      sq_nonneg ‖embed (SourceClockPhiCombinedScalePressure.phaseSecond m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g)‖]
  have he:ENNReal.ofReal (A+B+1)*ENNReal.ofReal (ε/(A+B+1))=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hC.le,mul_div_cancel₀ _ hC.ne']
  exact hp.trans ((mul_le_mul_of_nonneg_left hb (show 0 ≤ ENNReal.ofReal (A+B+1) from zero_le)).trans_eq he)

end LowEnergy.SourceClockPhiCombinedProfileTail
