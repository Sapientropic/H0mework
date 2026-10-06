import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockRadiusResponseAffine
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockRadiusBoundaryFamilyTail
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusSourceCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockRadiusAffineCutoff
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
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
open SourceClockRadiusResponseAffine GaussNativeMatter GaussNativePotential
open SourceClockPhiRadiusSourceCurrent


def scalePrice : ℝ := 2+centerPrice
private theorem center_nonnegative : 0 ≤ centerPrice := by unfold centerPrice;positivity
private theorem scale_one : 1 ≤ scalePrice := by unfold scalePrice;linarith only [center_nonnegative]
private theorem scale_positive : 0<scalePrice := lt_of_lt_of_le zero_lt_one scale_one
def scaledInverse : Op := ((scalePrice⁻¹:ℝ):ℂ) • inverseRadius
def scaledComplement : Op := 1-scaledInverse
def scaledBoundary (n : ℕ) : Op := (n+1:ℂ) • (scaledInverse*scaledComplement^n)

private theorem positive_csmul (c : ℝ) (hc : 0 ≤ c) (A : Op) (hA : 0 ≤ A) :
    0 ≤ (c:ℂ) • A :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (((ContinuousLinearMap.nonneg_iff_isPositive _).mp hA).smul_of_nonneg ((Complex.zero_le_real).mpr hc))
private theorem scaled_nonnegative : 0 ≤ scaledComplement := by
  have hi : 0 ≤ scalePrice⁻¹ := inv_nonneg.mpr scale_positive.le
  have hi1 : scalePrice⁻¹ ≤ 1 := inv_le_one_of_one_le₀ scale_one
  have he : scaledComplement=((1-scalePrice⁻¹:ℝ):ℂ) • (1:Op)+
      ((scalePrice⁻¹:ℝ):ℂ) • sourceComplement := by
    unfold scaledComplement scaledInverse sourceComplement
    push_cast
    module
  rw [he]
  exact add_nonneg (positive_csmul _ (sub_nonneg.mpr hi1) _ zero_le_one)
    (positive_csmul _ hi _ source_complement_nonnegative)
private theorem scaled_le_one : scaledComplement ≤ 1 := by
  have h : 0 ≤ scaledInverse := positive_csmul _ (inv_nonneg.mpr scale_positive.le) _ source_inverse_nonnegative
  unfold scaledComplement
  exact sub_le_self _ h

private theorem radius_lower (x : SourceCoordinateSlice) : 1 ≤ affineRadius x := by
  have h : affineRadius x^2=1+‖scalarField x‖^2/4 := Real.sq_sqrt (by positivity)
  have hp : 0 ≤ affineRadius x := Real.sqrt_nonneg _
  nlinarith only [h,hp,sq_nonneg ‖scalarField x‖]
private theorem affine_positive (x : SourceCoordinateSlice) : 0<affineRadius x := lt_of_lt_of_le zero_lt_one (radius_lower x)

private def scaledProfile (x : SourceCoordinateSlice) : ℝ := 1-reciprocal x/scalePrice
private def errorProfile (n : ℕ) (x : SourceCoordinateSlice) : ℝ :=
  affineRadius x*((1-reciprocal x)^(n+1)-(1-(affineRadius x)⁻¹)^(n+1))
private def boundaryProfile (n : ℕ) (x : SourceCoordinateSlice) : ℝ :=
  (n+1:ℝ)*(reciprocal x/scalePrice)*scaledProfile x^n

private theorem profile_nonnegative (x : SourceCoordinateSlice) : 0 ≤ scaledProfile x := by
  have hs : reciprocal x ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius x)
  have hi : reciprocal x/scalePrice ≤ 1 := (div_le_one scale_positive).mpr (hs.trans scale_one)
  exact sub_nonneg.mpr hi
private theorem profile_le_one (x : SourceCoordinateSlice) : scaledProfile x ≤ 1 := by
  have hs : 0 ≤ reciprocal x := inv_nonneg.mpr (radius_pos x).le
  exact sub_le_self _ (div_nonneg hs scale_positive.le)
private theorem boundary_nonnegative (n : ℕ) (x : SourceCoordinateSlice) : 0 ≤ boundaryProfile n x := by
  unfold boundaryProfile
  exact mul_nonneg (mul_nonneg (by positivity) (div_nonneg (inv_nonneg.mpr (radius_pos x).le) scale_positive.le))
    (pow_nonneg (profile_nonnegative x) n)

private theorem error_profile_bound (n : ℕ) (x : SourceCoordinateSlice) :
    |errorProfile n x| ≤ (centerPrice*scalePrice)*boundaryProfile n x := by
  have hr := radius_pos x
  have hp := affine_positive x
  have hs : 0 ≤ reciprocal x := inv_nonneg.mpr hr.le
  have hs1 : reciprocal x ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius x)
  have ht : 0 ≤ (affineRadius x)⁻¹ := inv_nonneg.mpr hp.le
  have ht1 : (affineRadius x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (radius_lower x)
  have hd := original_radius_center_bound x
  have hle : affineRadius x ≤ scalePrice*radius x := by
    have hh := (abs_le.mp hd).1
    unfold centerDifference at hh
    have hm := mul_le_mul_of_nonneg_left (one_le_radius x) center_nonnegative
    unfold scalePrice
    nlinarith only [hh,hm,hr]
  have hsK : reciprocal x/scalePrice ≤ (affineRadius x)⁻¹ := by
    calc
      _=1/(scalePrice*radius x) := by unfold reciprocal;field_simp
      _ ≤ (affineRadius x)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hp hle
  have hq0 : 0 ≤ 1-reciprocal x := sub_nonneg.mpr hs1
  have hq1 : 0 ≤ 1-(affineRadius x)⁻¹ := sub_nonneg.mpr ht1
  have hqm : max |1-reciprocal x| |1-(affineRadius x)⁻¹| ≤ scaledProfile x := by
    rw [abs_of_nonneg hq0,abs_of_nonneg hq1]
    apply max_le
    · have hh : reciprocal x/scalePrice ≤ reciprocal x := div_le_self hs scale_one
      exact sub_le_sub_left hh 1
    · exact sub_le_sub_left hsK 1
  have hpow := abs_pow_sub_pow_le (a:=1-reciprocal x) (b:=1-(affineRadius x)⁻¹) (n:=n+1)
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hpow
  have hcoef : affineRadius x*|(1-reciprocal x)-(1-(affineRadius x)⁻¹)| ≤ centerPrice*reciprocal x := by
    have he : affineRadius x*((1-reciprocal x)-(1-(affineRadius x)⁻¹))=(radius x-affineRadius x)*reciprocal x := by
      unfold reciprocal
      field_simp [hr.ne',hp.ne']
      ring
    calc
      _=|affineRadius x*((1-reciprocal x)-(1-(affineRadius x)⁻¹))| := by rw [abs_mul,abs_of_pos hp]
      _=|radius x-affineRadius x| *reciprocal x := by rw [he,abs_mul,abs_of_nonneg hs]
      _ ≤ _ := mul_le_mul_of_nonneg_right hd hs
  unfold errorProfile boundaryProfile
  rw [abs_mul,abs_of_pos hp]
  calc
    _ ≤ affineRadius x*(|(1-reciprocal x)-(1-(affineRadius x)⁻¹)| *(n+1:ℝ)*
      max |1-reciprocal x| |1-(affineRadius x)⁻¹|^n) := mul_le_mul_of_nonneg_left hpow hp.le
    _ = (affineRadius x*|(1-reciprocal x)-(1-(affineRadius x)⁻¹)|)*(n+1:ℝ)*
        max |1-reciprocal x| |1-(affineRadius x)⁻¹|^n := by ring
    _ ≤ (centerPrice*reciprocal x)*(n+1:ℝ)*scaledProfile x^n :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcoef (by positivity))
        (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hqm n)
        (pow_nonneg (le_max_of_le_left (abs_nonneg _)) n)
        (mul_nonneg (mul_nonneg center_nonnegative hs) (by positivity))
    _ = _ := by field_simp [scale_positive.ne']

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

private theorem time_scaled_positive : 0 ≤ timeRead scaledComplement :=
  time_positive _ scaled_nonnegative
private theorem time_scaled_le_one : timeRead scaledComplement ≤ 1 := by
  have h := time_positive (1-scaledComplement) (sub_nonneg.mpr scaled_le_one)
  have he : timeRead (1-scaledComplement)=1-timeRead scaledComplement :=
    (time_sub 1 scaledComplement).trans (congrArg (fun A : TH →L[ℂ] TH => A-timeRead scaledComplement) time_one)
  exact sub_nonneg.mp (Eq.mp (congrArg (fun A : TH →L[ℂ] TH => (0 : TH →L[ℂ] TH) ≤ A) he) h)

private theorem inverse_complement : scaledInverse=1-scaledComplement := by unfold scaledComplement;abel
private theorem gradient_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q : E →L[ℂ] E) (n : ℕ) :
    PositiveContractionRitt.gradient Q n=(n+1 : ℂ) • (Q^n*(1-Q)) := by
  unfold PositiveContractionRitt.gradient
  have hr := RCLike.real_smul_eq_coe_smul (K := ℂ) (n+1 : ℝ) (Q^n*(1-Q))
  simpa only [RCLike.ofReal_add,RCLike.ofReal_natCast,RCLike.ofReal_one] using hr

private theorem time_inverse_complement : timeRead scaledInverse=1-timeRead scaledComplement :=
  (congrArg timeRead inverse_complement).trans ((time_sub 1 scaledComplement).trans
    (congrArg (fun A : TH →L[ℂ] TH => A-timeRead scaledComplement) time_one))

private theorem boundary_time (n : ℕ) :
    timeRead (scaledBoundary n)=PositiveContractionRitt.gradient (timeRead scaledComplement) n := by
  have hP := (time_mul scaledInverse (scaledComplement^n)).trans
    (congrArg (fun A : TH →L[ℂ] TH => timeRead scaledInverse*A) (time_pow scaledComplement n))
  have hS := congrArg (fun A : TH →L[ℂ] TH => A*(timeRead scaledComplement)^n) time_inverse_complement
  have hc : Commute (timeRead scaledComplement) (1-timeRead scaledComplement) := by
    show timeRead scaledComplement*(1-timeRead scaledComplement)=(1-timeRead scaledComplement)*timeRead scaledComplement
    simp only [sub_mul,mul_sub,one_mul,mul_one]
  have he := (time_smul (n+1 : ℂ) (scaledInverse*scaledComplement^n)).trans
    (congrArg (fun A : TH →L[ℂ] TH => (n+1 : ℂ) • A) (hP.trans (hS.trans (hc.pow_left n).eq.symm)))
  exact he.trans (gradient_complex (timeRead scaledComplement) n).symm

private theorem boundary_time_strong (x : TH) :
    Tendsto (fun n => timeRead (scaledBoundary n) x) atTop (𝓝 0) := by
  have h := PositiveContractionRitt.gradient_strong (timeRead scaledComplement)
    time_scaled_positive time_scaled_le_one x
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
      ∀ᶠ F in (sourceFilter : Filter Index),‖value (readFamily (scaledBoundary n) f) F‖^2 ≤ ε := by
  intro ε hε
  have hb : ∀ᶠ n : ℕ in atTop,‖timeRead (scaledBoundary n) (f:TH)‖^2<ε := by
    have ht := (boundary_time_strong (f:TH)).norm.pow 2
    have he : (‖(0:TH)‖:ℝ)^2<ε := by simpa only [norm_zero,zero_pow (by omega : 2≠0)] using hε
    exact ht.eventually (gt_mem_nhds he)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  refine ⟨N,fun n hn => ?_⟩
  let fB := readFamily (scaledBoundary n) f
  have hval : ‖fB‖^2<ε := by rw [read_family_norm];exact hN n hn
  filter_upwards [(square_tendsto sourceFilter fB).eventually (gt_mem_nhds hval)] with F hF
  exact hF.le

/-- The actual whole resolvent family pays every Ritt boundary at one N shared by the two frequency legs. -/
theorem actual_scaled_boundary_common_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ n,N ≤ n →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖scaledBoundary n
          (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := family_boundary_tail (wholeInputFamily false μ hμ g) ε hε
  obtain ⟨N₁,h₁⟩ := family_boundary_tail (wholeInputFamily true μ hμ g) ε hε
  refine ⟨max N₀ N₁,fun n hn => ?_⟩
  filter_upwards [h₀ n (by omega),h₁ n (by omega)] with F hf ht
  intro advanced
  cases advanced
  · rw [acted_integral (scaledBoundary n) false μ hμ F g]
    exact ENNReal.ofReal_le_ofReal hf
  · rw [acted_integral (scaledBoundary n) true μ hμ F g]
    exact ENNReal.ofReal_le_ofReal ht


private theorem profile_positive (x : SourceCoordinateSlice) : 0<scaledProfile x := by
  have hs : reciprocal x ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius x)
  have hk : 1<scalePrice := by unfold scalePrice;linarith only [center_nonnegative]
  exact sub_pos.mpr ((div_lt_one scale_positive).mpr (hs.trans_lt hk))
private theorem boundary_positive (n : ℕ) (x : SourceCoordinateSlice) : 0<boundaryProfile n x := by
  unfold boundaryProfile
  exact mul_pos (mul_pos (by positivity) (div_pos (inv_pos.mpr (radius_pos x)) scale_positive))
    (pow_pos (profile_positive x) n)
private theorem affine_inverse_smooth : ContDiff ℝ ∞ (fun x : SourceCoordinateSlice => (affineRadius x)⁻¹) :=
  affine_radius_smooth.inv (fun x => (affine_positive x).ne')
private theorem profile_smooth : ContDiff ℝ ∞ scaledProfile :=
  contDiff_const.sub (reciprocal_smooth.div_const scalePrice)
private theorem error_smooth (n : ℕ) : ContDiff ℝ ∞ (errorProfile n) :=
  affine_radius_smooth.mul (((contDiff_const.sub reciprocal_smooth).pow (n+1)).sub
    ((contDiff_const.sub affine_inverse_smooth).pow (n+1)))
private theorem boundary_smooth (n : ℕ) : ContDiff ℝ ∞ (boundaryProfile n) :=
  (contDiff_const.mul (reciprocal_smooth.div_const scalePrice)).mul (profile_smooth.pow n)
private def ratioProfile (n : ℕ) (x : SourceCoordinateSlice) : ℝ := errorProfile n x/boundaryProfile n x
private theorem ratio_smooth (n : ℕ) : ContDiff ℝ ∞ (ratioProfile n) :=
  (error_smooth n).div (boundary_smooth n) (fun x => (boundary_positive n x).ne')
private theorem ratio_bound (n : ℕ) (x : SourceCoordinateSlice) : |ratioProfile n x| ≤ centerPrice*scalePrice := by
  rw [ratioProfile,abs_div,abs_of_pos (boundary_positive n x)]
  exact (div_le_iff₀ (boundary_positive n x)).mpr (error_profile_bound n x)
private def ratioFiber (n : ℕ) (x : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (ratioProfile n x:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem ratio_fiber_smooth (n : ℕ) : ContDiff ℝ ∞ (ratioFiber n) :=
  (Complex.ofRealCLM.contDiff.comp (ratio_smooth n)).smul contDiff_const
private theorem ratio_commutes (n : ℕ) (x : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (ratioFiber n x) := (Commute.one_right _).smul_right _
private theorem ratio_fiber_bound (n : ℕ) (x : SourceCoordinateSlice) (f : FockFiber) :
    ‖ratioFiber n x f‖ ≤ (centerPrice*scalePrice)*‖f‖ := by
  change ‖(ratioProfile n x:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (ratio_bound n x) (norm_nonneg f)
private def ratioAction (n : ℕ) : End := localMultiplier (ratioFiber n) (fun _ => (ratio_fiber_smooth n).contDiffAt)
private def ratioOperator (n : ℕ) : Op := GaussBoundedMultiplier.extension (ratioFiber n)
  (fun _ => (ratio_fiber_smooth n).contDiffAt) (fun x => ratio_commutes n x)
  (centerPrice*scalePrice) (mul_nonneg center_nonnegative scale_positive.le) (fun x => ratio_fiber_bound n x)
private theorem ratio_core (n : ℕ) (f : QuantumTest) : ratioOperator n (embed f)=embed (ratioAction n f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem ratio_norm (n : ℕ) : ‖ratioOperator n‖ ≤ centerPrice*scalePrice :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private def scaledInverseCore : End := ((scalePrice⁻¹:ℝ):ℂ) • inverseAction
private def scaledComplementCore : End := 1-scaledInverseCore
private def scaledBoundaryCore (n : ℕ) : End := (n+1:ℂ) • (scaledInverseCore*scaledComplementCore^n)
private theorem scaled_inverse_core (f : QuantumTest) : scaledInverse (embed f)=embed (scaledInverseCore f) := by
  simp only [scaledInverse,scaledInverseCore,smul_apply,LinearMap.smul_apply,inverse_core,map_smul]
private theorem scaled_complement_core (n : ℕ) (f : QuantumTest) :
    (scaledComplement^n) (embed f)=embed ((scaledComplementCore^n) f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change (scaledComplement^n) (embed f)-scaledInverse ((scaledComplement^n) (embed f))=
      embed ((scaledComplementCore^n) f-scaledInverseCore ((scaledComplementCore^n) f))
    rw [ih,scaled_inverse_core,map_sub]
private theorem scaled_boundary_core (n : ℕ) (f : QuantumTest) :
    scaledBoundary n (embed f)=embed (scaledBoundaryCore n f) := by
  simp only [scaledBoundary,scaledBoundaryCore,smul_apply,mul_apply_eq_comp,LinearMap.smul_apply,
    Module.End.mul_apply,scaled_complement_core,scaled_inverse_core,map_smul]
private theorem scaled_complement_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    (scaledComplementCore^n) f x=(scaledProfile x:ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((scaledComplementCore^n) f) x-((scalePrice⁻¹:ℝ):ℂ) •
      ((reciprocal x:ℂ) • (((scaledComplementCore^n) f) x))=_
    rw [ih,pow_succ',mul_smul]
    unfold scaledProfile
    push_cast
    simp only [div_eq_mul_inv]
    module
private theorem scaled_boundary_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    scaledBoundaryCore n f x=(boundaryProfile n x:ℂ) • f x := by
  change (n+1:ℂ) • (((scalePrice⁻¹:ℝ):ℂ) • ((reciprocal x:ℂ) • (((scaledComplementCore^n) f) x)))=_
  rw [scaled_complement_point]
  unfold boundaryProfile
  push_cast
  simp only [smul_smul,div_eq_mul_inv]
  congr 1
  ring

/-- The original and affine radial powers are compared on the same full Number-density carrier. -/
def radiusPowerError (n : ℕ) : Op := ratioOperator n*scaledBoundary n
private def radiusPowerErrorCore (n : ℕ) : End := multiply (errorProfile n) (fun _ => (error_smooth n).contDiffAt)
private theorem radius_power_error_core (n : ℕ) (f : QuantumTest) :
    radiusPowerError n (embed f)=embed (radiusPowerErrorCore n f) := by
  unfold radiusPowerError
  rw [mul_apply_eq_comp,scaled_boundary_core,ratio_core]
  apply congrArg embed
  apply DFunLike.ext
  intro x
  change (ratioProfile n x:ℂ) • (scaledBoundaryCore n f x)=(errorProfile n x:ℂ) • f x
  rw [scaled_boundary_point,smul_smul,←Complex.ofReal_mul]
  congr 2
  exact div_mul_cancel₀ _ (boundary_positive n x).ne'
private theorem radius_power_error_bound (n : ℕ) (x : H) :
    ‖radiusPowerError n x‖^2 ≤ (centerPrice*scalePrice)^2*‖scaledBoundary n x‖^2 := by
  have h := ((ratioOperator n).le_opNorm (scaledBoundary n x)).trans
    (mul_le_mul_of_nonneg_right (ratio_norm n) (norm_nonneg _))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (mul_pow _ _ 2)

private theorem power_error_integral (n : ℕ) (advanced : Bool) (μ : ℝ) (_hμ : 0<μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖radiusPowerError n (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤
    ENNReal.ofReal ((centerPrice*scalePrice)^2)*
      (∫⁻ w : ℝ,ENNReal.ofReal (‖scaledBoundary n (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) := by
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal ((centerPrice*scalePrice)^2)*
      ENNReal.ofReal (‖scaledBoundary n (finiteResolvent F (actualFrequency advanced μ w) g)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (radius_power_error_bound _ _)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem radius_power_error_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ n,N ≤ n →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖radiusPowerError n
          (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := 1+(centerPrice*scalePrice)^2
  have hC : 0<C := by dsimp [C];positivity
  obtain ⟨N,hN⟩ := actual_scaled_boundary_common_tail μ hμ g (ε/C) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  filter_upwards [hN n hn] with F hF
  intro advanced
  have h := (power_error_integral n advanced μ hμ F g).trans
    (mul_le_mul le_rfl (hF advanced) zero_le zero_le)
  have hc : (centerPrice*scalePrice)^2*(ε/C) ≤ ε := by
    have he : C*(ε/C)=ε := mul_div_cancel₀ _ hC.ne'
    have hq : 0 ≤ ε/C := div_nonneg hε.le hC.le
    dsimp [C] at he
    nlinarith only [he,hq]
  exact h.trans ((ENNReal.ofReal_mul (sq_nonneg _)).symm.trans_le (ENNReal.ofReal_le_ofReal hc))

private theorem two_square {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]
private theorem power_error_difference_integral (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖(radiusPowerError m-radiusPowerError ell)
      (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤
      2*(∫⁻ w : ℝ,ENNReal.ofReal (‖radiusPowerError m
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2))+
      2*(∫⁻ w : ℝ,ENNReal.ofReal (‖radiusPowerError ell
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) := by
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal (‖radiusPowerError ell
      (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) :=
    (((radiusPowerError ell).continuous.comp
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖radiusPowerError m
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)+
      ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖radiusPowerError ell
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      exact two_square _ _
    _ = _ := by
      rw [lintegral_add_right _ (hm.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      norm_num

private theorem radius_power_difference_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖(radiusPowerError m-radiusPowerError ell)
          (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := radius_power_error_tail μ hμ g (ε/4) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm,hN ell (hm.trans hml)] with F hf ht
  intro advanced
  have h := (power_error_difference_integral m ell advanced μ hμ F g).trans
    (add_le_add (mul_le_mul le_rfl (hf advanced) zero_le zero_le)
      (mul_le_mul le_rfl (ht advanced) zero_le zero_le))
  have he : (2:ENNReal)*ENNReal.ofReal (ε/4)+2*ENNReal.ofReal (ε/4)=ENNReal.ofReal ε := by
    rw [show (2:ENNReal)=ENNReal.ofReal (2:ℝ) by norm_num]
    rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact h.trans_eq he


/-- The affine cutoff is generated from the existing source rho inverse, not from a new scalar occurrence. -/
def phiThetaAction (m ell : ℕ) : End := (1-phiInverseAction)^(m+1)-(1-phiInverseAction)^(ell+1)
def phiRadiusSource (g : diagonal.domain) : diagonal.domain := coreEquiv (affineRadiusAction (coreEquiv.symm g))
def phiResponseCore (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  phiThetaAction m ell (SourceScalarDoubleCurrent.bracket affineRadiusAction
    (SourceClockYukawaCubicCurrent.resolventCore F z hz) (coreEquiv.symm g))
def phiResponseBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (μ*‖embed (phiResponseCore m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)‖^2)

private theorem inverse_phi_core (f : QuantumTest) : phiInverseBounded (embed f)=embed (phiInverseAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem inverse_phi_norm : ‖phiInverseBounded‖ ≤ 1 := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem inverse_phi_radius : phiInverseAction*affineRadiusAction=(1:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (phiReciprocal x:ℂ) • ((affineRadius x:ℂ) • f x)=f x
  simp only [phiReciprocal,phiRadius,Complex.ofReal_inv,smul_smul,
    inv_mul_cancel₀ (show (affineRadius x:ℂ)≠0 by exact_mod_cast (affine_positive x).ne'),one_smul]
private theorem source_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem core_resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (SourceClockYukawaCubicCurrent.resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold SourceClockYukawaCubicCurrent.resolventCore SourceScalarPositiveBulkWard.state
  exact source_embed _

private theorem old_power_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    (((1-inverseAction)^n) f) x=((1-reciprocal x:ℝ):ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((1-inverseAction)^n) f) x-(reciprocal x:ℂ) • ((((1-inverseAction)^n) f) x)=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module
private theorem phi_power_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    (((1-phiInverseAction)^n) f) x=((1-(affineRadius x)⁻¹:ℝ):ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((1-phiInverseAction)^n) f) x-(phiReciprocal x:ℂ) • ((((1-phiInverseAction)^n) f) x)=_
    rw [ih,pow_succ',mul_smul]
    unfold phiReciprocal phiRadius
    push_cast
    module
private theorem error_band_source (m ell : ℕ) : radiusPowerErrorCore m-radiusPowerErrorCore ell=
    affineRadiusAction*(SourceMixedNativeReturn.thetaAction m ell-phiThetaAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (errorProfile m x:ℂ) • f x-(errorProfile ell x:ℂ) • f x=
    (affineRadius x:ℂ) • ((SourceMixedNativeReturn.thetaAction m ell f) x-(phiThetaAction m ell f) x)
  unfold SourceMixedNativeReturn.thetaAction phiThetaAction
  have hs (a b : QuantumTest) : (a-b) x=a x-b x := rfl
  simp only [LinearMap.sub_apply,hs,old_power_point,phi_power_point,errorProfile]
  push_cast
  module
private theorem theta_phi_radius (m ell : ℕ) :
    Commute (SourceMixedNativeReturn.thetaAction m ell-phiThetaAction m ell) affineRadiusAction := by
  have hi : Commute inverseAction affineRadiusAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro x
    exact smul_comm (reciprocal x:ℂ) (affineRadius x:ℂ) (f x)
  have hj : Commute phiInverseAction affineRadiusAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro x
    exact smul_comm (phiReciprocal x:ℂ) (affineRadius x:ℂ) (f x)
  exact ((((Commute.one_left _).sub_left hi).pow_left (m+1)).sub_left
    (((Commute.one_left _).sub_left hi).pow_left (ell+1))).sub_left
    ((((Commute.one_left _).sub_left hj).pow_left (m+1)).sub_left
      (((Commute.one_left _).sub_left hj).pow_left (ell+1)))
private theorem error_band_core (m ell : ℕ) (f : QuantumTest) :
    (radiusPowerError m-radiusPowerError ell) (embed f)=
      embed ((radiusPowerErrorCore m-radiusPowerErrorCore ell) f) := by
  simp only [sub_apply,radius_power_error_core,LinearMap.sub_apply,map_sub]

attribute [local irreducible] phiResponseCore affineResponseCore radiusPowerErrorCore
  SourceClockYukawaCubicCurrent.resolventCore finiteResolvent phiInverseBounded

/-- Both cutoff systems return through the same two fixed affine-radius inputs and the same F. -/
theorem actual_affine_cutoff_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (affineResponseCore m ell F z hz g)=embed (phiResponseCore m ell F z hz g)+
      ((radiusPowerError m-radiusPowerError ell) (finiteResolvent F z (g:H))-
        phiInverseBounded ((radiusPowerError m-radiusPowerError ell)
          (finiteResolvent F z (phiRadiusSource g:H)))) := by
  let R : End := SourceClockYukawaCubicCurrent.resolventCore F z hz
  let D : End := SourceMixedNativeReturn.thetaAction m ell-phiThetaAction m ell
  let A : End := affineRadiusAction
  let B : End := radiusPowerErrorCore m-radiusPowerErrorCore ell
  have hd : B=A*D := error_band_source m ell
  have hc : Commute D A := theta_phi_radius m ell
  have hu : phiInverseAction*B=D := by rw [hd,←mul_assoc,inverse_phi_radius,one_mul]
  have hm : SourceMixedNativeReturn.thetaAction m ell*SourceScalarDoubleCurrent.bracket A R=
      phiThetaAction m ell*SourceScalarDoubleCurrent.bracket A R+B*R-phiInverseAction*B*R*A := by
    rw [hu,hd]
    unfold SourceScalarDoubleCurrent.bracket
    dsimp only [D] at hc ⊢
    linear_combination (norm := noncomm_ring) hc.eq*R
  have h := congrArg embed (LinearMap.congr_fun hm (coreEquiv.symm g))
  simp only [LinearMap.sub_apply,LinearMap.add_apply,Module.End.mul_apply,map_sub,map_add,
    ←inverse_phi_core] at h
  have hg : embed (R (coreEquiv.symm g))=finiteResolvent F z (g:H) := by
    rw [core_resolvent_embed,source_embed]
  have hh : embed (R (A (coreEquiv.symm g)))=finiteResolvent F z (phiRadiusSource g:H) :=
    core_resolvent_embed F z hz _
  have hB (f : QuantumTest) : embed (B f)=(radiusPowerError m-radiusPowerError ell) (embed f) :=
    (error_band_core m ell f).symm
  rw [hB,hB,hg,hh] at h
  simpa only [affineResponseCore,phiResponseCore,R,A,add_sub_assoc] using h

private theorem cutoff_point_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    ‖embed (affineResponseCore m ell F z hz g)‖^2 ≤ 2*‖embed (phiResponseCore m ell F z hz g)‖^2+
      4*‖(radiusPowerError m-radiusPowerError ell) (finiteResolvent F z (g:H))‖^2+
      4*‖(radiusPowerError m-radiusPowerError ell) (finiteResolvent F z (phiRadiusSource g:H))‖^2 := by
  rw [actual_affine_cutoff_source]
  let x := (radiusPowerError m-radiusPowerError ell) (finiteResolvent F z (g:H))
  let y := (radiusPowerError m-radiusPowerError ell) (finiteResolvent F z (phiRadiusSource g:H))
  have ha := two_square (embed (phiResponseCore m ell F z hz g)) (-(x-phiInverseBounded y))
  have hb := two_square x (phiInverseBounded y)
  have hc := (phiInverseBounded.le_opNorm y).trans
    ((mul_le_mul_of_nonneg_right inverse_phi_norm (norm_nonneg y)).trans_eq (one_mul _))
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  simp only [sub_neg_eq_add,norm_neg] at ha
  change ‖embed (phiResponseCore m ell F z hz g)+(x-phiInverseBounded y)‖^2 ≤ _
  nlinarith only [ha,hb,hc2]

/-- The full response cost pays the actual change of cutoff before invoking homogeneous source calculus. -/
theorem actual_affine_cutoff_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        affineResponseBudget m ell F μ hμ g ≤ ENNReal.ofReal ε+2*phiResponseBudget m ell F μ hμ g := by
  intro ε hε
  obtain ⟨N1,h1⟩ := radius_power_difference_tail μ hμ (g:H) (ε/(8*μ)) (by positivity)
  obtain ⟨N2,h2⟩ := radius_power_difference_tail μ hμ (phiRadiusSource g:H) (ε/(8*μ)) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hg' hh'
  have hg := hg' false
  have hh := hh' false
  simp only [actualFrequency,Bool.false_eq_true,ite_false] at hg hh
  let X := fun w : ℝ => ENNReal.ofReal (‖(radiusPowerError m-radiusPowerError ell) (finiteResolvent F (line μ w) (g:H))‖^2)
  let Y := fun w : ℝ => ENNReal.ofReal (‖(radiusPowerError m-radiusPowerError ell) (finiteResolvent F (line μ w) (phiRadiusSource g:H))‖^2)
  have hr := finite_frequency_continuous μ hμ F
  have mx : Measurable X := (((radiusPowerError m-radiusPowerError ell).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have my : Measurable Y := (((radiusPowerError m-radiusPowerError ell).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have hC : 0 ≤ 4*μ := by positivity
  have hi : affineResponseBudget m ell F μ hμ g ≤ 2*phiResponseBudget m ell F μ hμ g+
      ENNReal.ofReal (4*μ)*(∫⁻ w : ℝ,X w)+ENNReal.ofReal (4*μ)*(∫⁻ w : ℝ,Y w) := by
    unfold affineResponseBudget phiResponseBudget
    calc
      _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2*(μ*‖embed (phiResponseCore m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g)‖^2))+
          ENNReal.ofReal (4*μ)*X w+ENNReal.ofReal (4*μ)*Y w := by
        apply lintegral_mono
        intro w
        have hp := mul_le_mul_of_nonneg_left (cutoff_point_price m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g) hμ.le
        have hp' : μ*‖embed (affineResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖^2 ≤
            2*(μ*‖embed (phiResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖^2)+
            (4*μ)*‖(radiusPowerError m-radiusPowerError ell) (finiteResolvent F (line μ w) (g:H))‖^2+
            (4*μ)*‖(radiusPowerError m-radiusPowerError ell) (finiteResolvent F (line μ w) (phiRadiusSource g:H))‖^2 := by nlinarith only [hp]
        apply (ENNReal.ofReal_le_ofReal hp').trans
        dsimp only [X,Y]
        rw [←ENNReal.ofReal_mul hC,←ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
      _ = _ := by
        rw [lintegral_add_right _ (my.const_mul _),lintegral_add_right _ (mx.const_mul _)]
        simp_rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        norm_num
  have he : ENNReal.ofReal (4*μ)*ENNReal.ofReal (ε/(8*μ))+
      ENNReal.ofReal (4*μ)*ENNReal.ofReal (ε/(8*μ))=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hC,←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    norm_num
  have h := hi.trans (add_le_add (add_le_add le_rfl (mul_le_mul le_rfl hg zero_le zero_le))
    (mul_le_mul le_rfl hh zero_le zero_le))
  calc
    _ ≤ (2*phiResponseBudget m ell F μ hμ g+ENNReal.ofReal (4*μ)*ENNReal.ofReal (ε/(8*μ)))+
      ENNReal.ofReal (4*μ)*ENNReal.ofReal (ε/(8*μ)) := h
    _ = _ := by rw [add_assoc,he,add_comm]

/-- Original r_x and theta_x are retained as the sink of the completely paid affine-radius and cutoff changes. -/
theorem actual_original_radius_homogeneous_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        SourceClockYukawaQ8RadiusBudget.radiusResponseBudget m ell F μ hμ g ≤
          ENNReal.ofReal ε+4*phiResponseBudget m ell F μ hμ g := by
  intro ε hε
  obtain ⟨N1,h1⟩ := actual_original_radius_affine_budget μ hμ g (ε/2) (by positivity)
  obtain ⟨N2,h2⟩ := actual_affine_cutoff_budget μ hμ g (ε/4) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hF hG
  have h := hF.trans (add_le_add le_rfl (mul_le_mul le_rfl hG zero_le zero_le))
  have he : ENNReal.ofReal (ε/2)+(2:ENNReal)*ENNReal.ofReal (ε/4)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_ofNat,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (ε/2)+2*(ENNReal.ofReal (ε/4)+2*phiResponseBudget m ell F μ hμ g) := h
    _ = _ := by rw [mul_add,←add_assoc,he,←mul_assoc];norm_num

end LowEnergy.SourceClockRadiusAffineCutoff
