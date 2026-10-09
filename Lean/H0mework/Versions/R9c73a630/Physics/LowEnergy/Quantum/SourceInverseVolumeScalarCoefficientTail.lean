import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeScalarSignedInverseReturn
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeScalarCoefficientDecay
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceInverseVolumePositiveContractionRitt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceLocalizedInverseFormPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussQuantumMultiplier
open GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum GaussFockWeights
open SourceMixedNativeReturn SourceNativeCutoffContact SourceRelativePowerTail SourceCornerForcing
open PositiveScalarWeakBudget PositiveScalarCoefficientDecay
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceCutoffSharp
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H

/-- The original radius uses q, retaining the actual vacuum in full Y. -/
def directionWeight (a : ScalarIndex) (z : SourceCoordinateSlice) : ℝ :=
  -inner ℝ (z.2.1 : Scalar) (scalarBasis a)/(4*radius z)

private theorem direction_smooth (a : ScalarIndex) : ContDiff ℝ ∞ (directionWeight a) :=
  ((scalarCoordinate.contDiff.inner ℝ contDiff_const).neg).div
    (contDiff_const.mul radius_smooth) (fun z => mul_ne_zero (by norm_num) (radius_pos z).ne')

/-- Every native scalar direction has the same source half-bound. -/
theorem original_direction_bound (a : ScalarIndex) (z : SourceCoordinateSlice) :
    |directionWeight a z| ≤ 1/2 := by
  have hq : ‖(z.2.1 : Scalar)‖ ≤ 2*radius z := by
    have hr : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
    nlinarith [radius_pos z,norm_nonneg (z.2.1 : Scalar)]
  have hi := norm_inner_le_norm (𝕜 := ℝ) (z.2.1 : Scalar) (scalarBasis a)
  rw [Real.norm_eq_abs,scalarBasis.orthonormal.norm_eq_one a,mul_one] at hi
  rw [directionWeight,abs_div,abs_neg,abs_of_pos (mul_pos (by norm_num) (radius_pos z))]
  apply (div_le_iff₀ (mul_pos (by norm_num) (radius_pos z))).mpr
  linarith

private def directionFiber (a : ScalarIndex) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (directionWeight a z : ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem direction_fiber_smooth (a : ScalarIndex) : ContDiff ℝ ∞ (directionFiber a) :=
  (Complex.ofRealCLM.contDiff.comp (direction_smooth a)).smul contDiff_const
private theorem direction_commutes (a : ScalarIndex) (z : physicalChart) (w : ℕ → ℂ) :
    Commute (weight w) (directionFiber a z) := (Commute.one_right _).smul_right _
private theorem direction_fiber_bound (a : ScalarIndex) (z : physicalChart) (x : FockFiber) :
    ‖directionFiber a z x‖ ≤ (1/2 : ℝ)*‖x‖ := by
  change ‖(directionWeight a z : ℂ) • x‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (original_direction_bound a z) (norm_nonneg x)

def directionAction (a : ScalarIndex) : End := multiply (directionWeight a) (fun _ => (direction_smooth a).contDiffAt)
def directionOperator (a : ScalarIndex) : Op :=
  GaussBoundedMultiplier.extension (directionFiber a) (fun _ => (direction_fiber_smooth a).contDiffAt)
    (direction_commutes a) (1/2) (by norm_num) (direction_fiber_bound a)

theorem original_direction_core (a : ScalarIndex) (f : QuantumTest) :
    directionOperator a (embed f)=embed (directionAction a f) :=
  GaussBoundedMultiplier.extension_core (directionFiber a) (fun _ => (direction_fiber_smooth a).contDiffAt)
    (direction_commutes a) (1/2) (by norm_num) (direction_fiber_bound a) f

theorem original_direction_norm (a : ScalarIndex) : ‖directionOperator a‖ ≤ 1/2 :=
  GaussBoundedMultiplier.extension_norm (directionFiber a) (fun _ => (direction_fiber_smooth a).contDiffAt)
    (direction_commutes a) (1/2) (by norm_num) (direction_fiber_bound a)

/-- Both boundary peaks are kept before taking a norm. -/
theorem original_radial_derivative_peaks (a : ScalarIndex) (m ell : ℕ) (z : SourceCoordinateSlice) :
    radius z*thetaDerivative (scalarDirection a) m ell z=
      directionWeight a z*((ell+1 : ℝ)*reciprocal z*(1-reciprocal z)^ell-
        (m+1 : ℝ)*reciprocal z*(1-reciprocal z)^m) := by
  unfold thetaDerivative radialDerivative directionWeight reciprocal
  change radius z*((((ell+1 : ℕ):ℝ)*(1-(radius z)⁻¹)^ell-
    ((m+1 : ℕ):ℝ)*(1-(radius z)⁻¹)^m)*
      (-inner ℝ (z.2.1 : Scalar) (scalarBasis a)/(4*radius z^3)))=_
  push_cast
  field_simp [(radius_pos z).ne']

/-- Source boundary coefficient; this is the positive-contraction Ritt word
for the actual Q=1−1/r. -/
def boundaryOperator (n : ℕ) : Op := (n+1 : ℂ) • (inverseRadius*sourceComplement^n)
private def boundaryAction (n : ℕ) : End := (n+1 : ℂ) • (inverseAction*(1-inverseAction)^n)

private theorem complement_core (f : QuantumTest) : sourceComplement (embed f)=embed ((1-inverseAction) f) := by
  change embed f-inverseRadius (embed f)=_
  rw [inverse_core,←map_sub]
  rfl
private theorem power_core (n : ℕ) (f : QuantumTest) :
    (sourceComplement^n) (embed f)=embed (((1-inverseAction)^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change sourceComplement ((sourceComplement^n) (embed f))=_
    rw [ih,complement_core]
    rfl
private theorem boundary_core (n : ℕ) (f : QuantumTest) :
    boundaryOperator n (embed f)=embed (boundaryAction n f) := by
  simp only [boundaryOperator,boundaryAction,smul_apply,LinearMap.smul_apply,map_smul,
    mul_apply_eq_comp,Module.End.mul_apply,power_core,inverse_core]

private theorem power_at (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((1-inverseAction)^n) f z=((1-reciprocal z : ℝ)^n : ℂ) • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((1-inverseAction) (((1-inverseAction)^n) f)) z)=_
    change ((1-inverseAction)^n) f z-(reciprocal z : ℂ) • (((1-inverseAction)^n) f z)=_
    rw [ih]
    simp only [smul_smul,pow_succ,Complex.ofReal_sub,Complex.ofReal_one]
    module

private theorem boundary_at (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    boundaryAction n f z=(((n+1 : ℝ)*reciprocal z*(1-reciprocal z)^n : ℝ) : ℂ) • f z := by
  change (n+1 : ℂ) • ((reciprocal z : ℂ) • (((1-inverseAction)^n) f z))=_
  rw [power_at]
  simp only [smul_smul]
  congr 1
  push_cast
  ring

private theorem vertex_core (sharp : Bool) (f : QuantumTest) :
    sourceVertex sharp (embed f)=embed (inverseAction (fullAction sharp f)) := by
  cases sharp
  · have h := GaussRadialDomain.original_graph f
    change GaussYukawaOperator.bounded (embed f)=inverseRadius (embed (GaussYukawaOperator.originalAction f)) at h
    rw [inverse_core] at h
    exact h
  · change GaussYukawaOperator.bounded.adjoint (embed f)=_
    rw [bounded_sharp_core]
    congr 1
    apply DFunLike.ext
    intro z
    change GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z)
      ((reciprocal z : ℂ) • f z)=(reciprocal z : ℂ) • GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z) (f z)
    exact map_smul _ _ _

def boundedCoefficient (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) : Op :=
  constantBounded sharp (scalarDirection a).1*relativeTail m ell+
    directionOperator a*(boundaryOperator ell-boundaryOperator m)*sourceVertex sharp

private theorem derivative_source (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (f : QuantumTest) :
    directionAction a ((boundaryAction ell-boundaryAction m) (inverseAction (fullAction sharp f)))=
      derivativeAction a m ell (fullAction sharp f) := by
  apply DFunLike.ext
  intro z
  change (directionWeight a z : ℂ) •
    (boundaryAction ell (inverseAction (fullAction sharp f)) z-boundaryAction m (inverseAction (fullAction sharp f)) z)=_
  rw [boundary_at,boundary_at]
  change (directionWeight a z : ℂ) •
    ((((ell+1 : ℝ)*reciprocal z*(1-reciprocal z)^ell : ℝ):ℂ) •
        ((reciprocal z : ℂ) • fullAction sharp f z)-
      (((m+1 : ℝ)*reciprocal z*(1-reciprocal z)^m : ℝ):ℂ) •
        ((reciprocal z : ℂ) • fullAction sharp f z))=
    (thetaDerivative (scalarDirection a) m ell z : ℂ) • fullAction sharp f z
  simp only [←sub_smul,smul_smul]
  congr 1
  have h := original_radial_derivative_peaks a m ell z
  have hs : directionWeight a z*((ell+1 : ℝ)*reciprocal z*(1-reciprocal z)^ell-
      (m+1 : ℝ)*reciprocal z*(1-reciprocal z)^m)*reciprocal z=thetaDerivative (scalarDirection a) m ell z := by
    rw [←h,reciprocal]
    field_simp [(radius_pos z).ne']
  have ht : directionWeight a z*
      (((ell+1 : ℝ)*reciprocal z*(1-reciprocal z)^ell)*reciprocal z-
        ((m+1 : ℝ)*reciprocal z*(1-reciprocal z)^m)*reciprocal z)=thetaDerivative (scalarDirection a) m ell z := by
    nlinarith only [hs]
  exact_mod_cast ht

/-- The original joined Z has a bounded realization, keeping its genuine two
boundary peaks and both independent source branches. -/
theorem original_bounded_coefficient_core (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (f : QuantumTest) :
    boundedCoefficient sharp a m ell (embed f)=embed (coefficient sharp a m ell f) := by
  rw [boundedCoefficient,add_apply]
  simp only [mul_apply_eq_comp,sub_apply,SourceMixedNativeReturn.theta_core,constant_bounded_core,vertex_core,boundary_core]
  rw [←map_sub,original_direction_core,←map_add]
  have hd := derivative_source sharp a m ell f
  change directionAction a (boundaryAction ell (inverseAction (fullAction sharp f))-
    boundaryAction m (inverseAction (fullAction sharp f)))=derivativeAction a m ell (fullAction sharp f) at hd
  rw [hd]
  apply congrArg embed
  rw [original_coefficient_split]
  congr 1
  apply DFunLike.ext
  intro z
  rw [SourceMixedNativeReturn.thetaAction,←theta_action_polynomial]
  cases sharp
  · change sourceMap (scalarDirection a).1 ((theta m ell z : ℂ) • f z)=
      (theta m ell z : ℂ) • sourceMap (scalarDirection a).1 (f z)
    exact map_smul _ _ _
  · change GaussFullHamiltonian.adjointMap (scalarDirection a).1 ((theta m ell z : ℂ) • f z)=
      (theta m ell z : ℂ) • GaussFullHamiltonian.adjointMap (scalarDirection a).1 (f z)
    exact map_smul _ _ _


open MeasureTheory Filter SourceRetardedBandCurrent SourceActualResolventEnergy
open SourceFamilyHilbert SourceFamilyOperator FullYSourceFiniteTimeIntegral FullYSourceTimeFamilyGraph
open FullYSourceCutoffTimeGraph FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped Topology

/-- Operator duality and the frequency leg are independent choices. -/
def actualFrequency (advanced : Bool) (μ w : ℝ) : ℂ :=
  if advanced then star (line μ w) else line μ w

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

private theorem whole_input_square (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    ‖wholeFiniteInput advanced μ hμ F g‖^2=Real.pi/μ*‖g‖^2 := by
  rw [square_integral]
  have he : (fun w => ‖wholeFiniteInput advanced μ hμ F g w‖^2)=ᵐ[MeasureTheory.volume]
      (fun w => ‖finiteResolvent F (actualFrequency advanced μ w) g‖^2) := by
    filter_upwards [(whole_memLp advanced μ hμ F g).coeFn_toLp] with w hw
    exact congrArg (fun x : H => ‖x‖^2) hw
  rw [integral_congr_ae he]
  simp_rw [frequency_norm advanced μ hμ F g]
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using actual_square_integral F μ hμ g

/-- The whole frequency line is admitted before the original source filter;
its bound is generated by the actual resolvent spectral identity. -/
def wholeInputFamily (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) : Family (Lp H 2 (MeasureTheory.volume : Measure ℝ)) sourceFilter where
  val F := wholeFiniteInput advanced μ hμ F g
  property := by
    refine ⟨Real.sqrt (Real.pi/μ*‖g‖^2),Real.sqrt_nonneg _,fun F => ?_⟩
    have h := whole_input_square advanced μ hμ F g
    have hs := Real.sq_sqrt (show 0≤Real.pi/μ*‖g‖^2 by positivity)
    nlinarith [norm_nonneg (wholeFiniteInput advanced μ hμ F g),Real.sqrt_nonneg (Real.pi/μ*‖g‖^2)]

def wholeInput (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) : TimeSpace (MeasureTheory.volume : Measure ℝ) :=
  (wholeInputFamily advanced μ hμ g : TimeSpace (MeasureTheory.volume : Measure ℝ))

private def coefficientFamily (sharp : Bool) (a : ScalarIndex) (m ell : ℕ)
    (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) : Family (Lp H 2 (MeasureTheory.volume : Measure ℝ)) sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant ((boundedCoefficient sharp a m ell).compLpL 2 MeasureTheory.volume))
    (wholeInputFamily advanced μ hμ g)

private theorem coefficient_family_integral (sharp : Bool) (a : ScalarIndex) (m ell : ℕ)
    (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2))=
      ENNReal.ofReal (‖value (coefficientFamily sharp a m ell advanced μ hμ g) F‖^2) := by
  have he : (fun w => ‖boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)=ᵐ[MeasureTheory.volume]
      (fun w => ‖value (coefficientFamily sharp a m ell advanced μ hμ g) F w‖^2) := by
    filter_upwards [(boundedCoefficient sharp a m ell).coeFn_compLpL (wholeFiniteInput advanced μ hμ F g),
      (whole_memLp advanced μ hμ F g).coeFn_toLp] with w hA hR
    change _=‖((boundedCoefficient sharp a m ell).compLpL 2 MeasureTheory.volume (wholeFiniteInput advanced μ hμ F g)) w‖^2
    rw [hA]
    change _=‖boundedCoefficient sharp a m ell (wholeFiniteInput advanced μ hμ F g w)‖^2
    change wholeFiniteInput advanced μ hμ F g w=finiteResolvent F (actualFrequency advanced μ w) g at hR
    rw [hR]
  have hi := (square_integrable MeasureTheory.volume (value (coefficientFamily sharp a m ell advanced μ hμ g) F)).congr he.symm
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)),
    integral_congr_ae he,←square_integral]


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

private theorem time_norm (A : Op) : ‖timeRead A‖ ≤ ‖A‖ := by
  unfold timeRead
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  exact SourceBoundaryGram.lift_bound_explicit sourceFilter
    (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) ‖A‖ (norm_nonneg A)
    (fun _ f => ((A.compLpL 2 MeasureTheory.volume).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := MeasureTheory.volume) A) (norm_nonneg f))) x


private theorem inverse_complement : inverseRadius=1-sourceComplement := by unfold sourceComplement;abel
private theorem gradient_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q : E →L[ℂ] E) (n : ℕ) :
    PositiveContractionRitt.gradient Q n=(n+1 : ℂ) • (Q^n*(1-Q)) := by
  unfold PositiveContractionRitt.gradient
  have hr := RCLike.real_smul_eq_coe_smul (K := ℂ) (n+1 : ℝ) (Q^n*(1-Q))
  simpa only [RCLike.ofReal_add,RCLike.ofReal_natCast,RCLike.ofReal_one] using hr

private theorem boundary_gradient (n : ℕ) : boundaryOperator n=PositiveContractionRitt.gradient sourceComplement n := by
  have hc : Commute sourceComplement inverseRadius := by
    unfold sourceComplement
    show (1-inverseRadius)*inverseRadius=inverseRadius*(1-inverseRadius)
    simp only [sub_mul,mul_sub,one_mul,mul_one]
  have h := (hc.pow_left n).eq.symm
  exact (congrArg (fun A : Op => (n+1 : ℂ) • A)
    (h.trans (congrArg (fun A : Op => sourceComplement^n*A) inverse_complement))).trans
      (gradient_complex sourceComplement n).symm

/-- The source Ritt norm is uniform in n; no operator-norm convergence is claimed. -/
theorem original_boundary_norm (n : ℕ) : ‖boundaryOperator n‖ ≤ 1 := by
  rw [boundary_gradient]
  exact PositiveContractionRitt.gradient_norm sourceComplement source_complement_nonnegative source_complement_le_one n

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


/-- Parseval uses all seventy original scalar directions at the same radius. -/
theorem original_direction_square (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,(directionWeight a z)^2)=(1-(reciprocal z)^2)/4 := by
  simp only [directionWeight,div_pow,neg_sq]
  rw [←Finset.sum_div,scalarBasis.sum_sq_inner_left]
  have hr : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
  unfold reciprocal
  field_simp [(radius_pos z).ne']
  nlinarith only [hr]

private theorem direction_action_square (f : QuantumTest) :
    (∑ a : ScalarIndex,directionAction a (directionAction a f))=
      (1/4 : ℂ) • (f-inverseAction (inverseAction f)) := by
  apply DFunLike.ext
  intro z
  simp only [sum_apply]
  change (∑ a : ScalarIndex,(directionWeight a z : ℂ) • ((directionWeight a z : ℂ) • f z))=
    (1/4 : ℂ) • (f z-(reciprocal z : ℂ) • ((reciprocal z : ℂ) • f z))
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [original_direction_square]
  have he : (((1-(reciprocal z)^2)/4 : ℝ):ℂ)=(1/4 : ℂ)-(1/4 : ℂ)*(reciprocal z : ℂ)^2 := by
    push_cast
    ring
  rw [he]
  module

private theorem direction_core_energy (f : QuantumTest) :
    (∑ a : ScalarIndex,‖embed (directionAction a f)‖^2)=
      (‖embed f‖^2-‖embed (inverseAction f)‖^2)/4 := by
  have he := congrArg (sourcePair f) (direction_action_square f)
  have hp (a : ScalarIndex) : sourcePair f (directionAction a (directionAction a f))=
      sourcePair (directionAction a f) (directionAction a f) := multiply_pair _ _ _ _
  have hi : sourcePair f (inverseAction (inverseAction f))=sourcePair (inverseAction f) (inverseAction f) :=
    multiply_pair _ _ _ _
  simp only [sourcePair,map_sum,map_smul,map_sub,inner_sum,inner_smul_right,inner_sub_right] at he
  change (∑ a : ScalarIndex,sourcePair f (directionAction a (directionAction a f)))=
    (1/4 : ℂ)*(sourcePair f f-sourcePair f (inverseAction (inverseAction f))) at he
  simp_rw [hp,hi] at he
  have hr := congrArg Complex.re he
  have hquarter (z : ℂ) : ((1/4 : ℂ)*z).re=(1/4 : ℝ)*z.re := by norm_num [Complex.mul_re]
  rw [Complex.re_sum,hquarter,Complex.sub_re] at hr
  have hself (q : QuantumTest) : (sourcePair q q).re=‖embed q‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (embed q)
  simp only [hself] at hr
  exact hr.trans (by ring)

/-- The derivative coefficient Gram has no artificial factor seventy. -/
theorem original_direction_energy (x : H) :
    (∑ a : ScalarIndex,‖directionOperator a x‖^2)=(‖x‖^2-‖inverseRadius x‖^2)/4 := by
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro v
  obtain ⟨f,rfl⟩ := coreEquiv.surjective v
  change (∑ a : ScalarIndex,‖directionOperator a (embed f)‖^2)=
    (‖embed f‖^2-‖inverseRadius (embed f)‖^2)/4
  simp only [original_direction_core,inverse_core]
  exact direction_core_energy f

private theorem norm_add_square (x y : H) : ‖x+y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

/-- All seventy joined coefficients are paid by one relative tail and one
Ritt boundary difference, before any source filter or frequency integral. -/
theorem original_bounded_coefficient_energy (sharp : Bool) (m ell : ℕ) (x : H) :
    (∑ a : ScalarIndex,‖boundedCoefficient sharp a m ell x‖^2) ≤
      2*SourceScalarInverseNativeEnergy.coefficientCost sharp*‖relativeTail m ell x‖^2+
      (1/2 : ℝ)*‖(boundaryOperator ell-boundaryOperator m) (sourceVertex sharp x)‖^2 := by
  let d := (boundaryOperator ell-boundaryOperator m) (sourceVertex sharp x)
  have h (a : ScalarIndex) : ‖boundedCoefficient sharp a m ell x‖^2 ≤
      2*(‖constantBounded sharp (scalarDirection a).1 (relativeTail m ell x)‖^2+‖directionOperator a d‖^2) := by
    exact norm_add_square _ _
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ScalarIndex)) (fun a _ => h a)
  have hc : (∑ a : ScalarIndex,‖constantBounded sharp (scalarDirection a).1 (relativeTail m ell x)‖^2) ≤
      SourceScalarInverseNativeEnergy.coefficientCost sharp*‖relativeTail m ell x‖^2 := by
    rw [SourceScalarInverseNativeEnergy.coefficientCost,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    exact (pow_le_pow_left₀ (norm_nonneg _) ((constantBounded sharp (scalarBasis a)).le_opNorm (relativeTail m ell x)) 2).trans_eq (mul_pow _ _ _)
  have hd : (∑ a : ScalarIndex,‖directionOperator a d‖^2) ≤ (1/4 : ℝ)*‖d‖^2 := by
    rw [original_direction_energy]
    nlinarith [sq_nonneg ‖inverseRadius d‖]
  simp only [←Finset.mul_sum,Finset.sum_add_distrib] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left (add_le_add hc hd) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by dsimp [d];ring))

private def readFamily (A : Op) (f : Family L2H sourceFilter) : Family L2H sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) f

private theorem read_family_norm (A : Op) (f : Family L2H sourceFilter) :
    ‖readFamily A f‖=‖timeRead A (f : TH)‖ := by
  unfold timeRead familyReader
  rw [lift_coe,UniformSpace.Completion.norm_coe]
  rfl

private theorem lp_coefficient_energy (sharp : Bool) (m ell : ℕ) (f : L2H) :
    (∑ a : ScalarIndex,‖(boundedCoefficient sharp a m ell).compLpL 2 MeasureTheory.volume f‖^2) ≤
      2*SourceScalarInverseNativeEnergy.coefficientCost sharp*
        ‖(relativeTail m ell).compLpL 2 MeasureTheory.volume f‖^2+
      (1/2 : ℝ)*‖((boundaryOperator ell-boundaryOperator m)*sourceVertex sharp).compLpL 2 MeasureTheory.volume f‖^2 := by
  let T := relativeTail m ell
  let D := (boundaryOperator ell-boundaryOperator m)*sourceVertex sharp
  let Z := fun a => boundedCoefficient sharp a m ell
  have hZ (a : ScalarIndex) := square_integrable MeasureTheory.volume ((Z a).compLpL 2 MeasureTheory.volume f)
  have hT := square_integrable MeasureTheory.volume (T.compLpL 2 MeasureTheory.volume f)
  have hD := square_integrable MeasureTheory.volume (D.compLpL 2 MeasureTheory.volume f)
  calc
    _ = ∫ w : ℝ,∑ a : ScalarIndex,‖((Z a).compLpL 2 MeasureTheory.volume f) w‖^2 := by
      rw [integral_finsetSum _ (fun a _ => hZ a)]
      simp only [←square_integral]
      rfl
    _ ≤ ∫ w : ℝ,2*SourceScalarInverseNativeEnergy.coefficientCost sharp*
        ‖(T.compLpL 2 MeasureTheory.volume f) w‖^2+
        (1/2 : ℝ)*‖(D.compLpL 2 MeasureTheory.volume f) w‖^2 := by
      apply integral_mono_ae (integrable_finsetSum _ (fun a _ => hZ a))
        ((hT.const_mul _).add (hD.const_mul _))
      have hz := Filter.eventually_all.mpr (fun a : ScalarIndex => (Z a).coeFn_compLpL f)
      filter_upwards [hz,T.coeFn_compLpL f,D.coeFn_compLpL f] with w hw ht hd
      simp only [Pi.add_apply,hw,ht,hd]
      exact original_bounded_coefficient_energy sharp m ell (f w)
    _ = _ := by
      have hI := integral_add (hT.const_mul (2*SourceScalarInverseNativeEnergy.coefficientCost sharp)) (hD.const_mul (1/2 : ℝ))
      exact hI.trans (congrArg₂ (fun a b : ℝ => a+b)
        ((integral_const_mul _ _).trans (congrArg (fun v : ℝ => 2*SourceScalarInverseNativeEnergy.coefficientCost sharp*v) (square_integral MeasureTheory.volume (T.compLpL 2 MeasureTheory.volume f)).symm))
        ((integral_const_mul _ _).trans (congrArg (fun v : ℝ => (1/2 : ℝ)*v) (square_integral MeasureTheory.volume (D.compLpL 2 MeasureTheory.volume f)).symm)))

private theorem coefficient_total_integral (sharp : Bool) (m ell : ℕ)
    (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
      ‖boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2))=
      ENNReal.ofReal (∑ a : ScalarIndex,‖value (coefficientFamily sharp a m ell advanced μ hμ g) F‖^2) := by
  classical
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  rw [lintegral_finsetSum Finset.univ]
  · congr 1
    funext a
    exact coefficient_family_integral sharp a m ell advanced μ hμ F g
  · intro a _
    exact (((boundedCoefficient sharp a m ell).continuous.comp
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal

private theorem family_coefficient_tail (sharp : Bool) (f : Family L2H sourceFilter) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∑ a : ScalarIndex,‖(boundedCoefficient sharp a m ell).compLpL 2 MeasureTheory.volume (value f F)‖^2) ≤ ε := by
  intro ε hε
  let C := SourceScalarInverseNativeEnergy.coefficientCost sharp
  have hC : 0 ≤ C := by unfold C SourceScalarInverseNativeEnergy.coefficientCost;positivity
  let δ := Real.sqrt (ε/(8*(C+1)))
  have hδ : 0<δ := Real.sqrt_pos.2 (by positivity)
  have hδsq : δ^2=ε/(8*(C+1)) := Real.sq_sqrt (by positivity)
  let x : TH := (f : TH)
  let y := timeRead (sourceVertex sharp) x
  obtain ⟨NT,hNT⟩ := time_space_relative_tail MeasureTheory.volume x δ hδ
  have hb : ∀ᶠ n : ℕ in atTop,‖timeRead (boundaryOperator n) y‖<δ/2 := by
    have ht := (boundary_time_strong y).norm
    have hh := ht.eventually (gt_mem_nhds (show ‖(0 : TH)‖<δ/2 by simp only [norm_zero];positivity))
    exact hh
  obtain ⟨NB,hNB⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max NT NB,fun m hm ell hell => ?_⟩
  have hTm : ‖timeRead (relativeTail m ell) x‖<δ := by
    unfold timeRead
    exact hNT m ((le_max_left _ _).trans hm) ell hell
  have hBm := hNB m ((le_max_right _ _).trans hm)
  have hBl := hNB ell (((le_max_right _ _).trans hm).trans hell)
  let D := (boundaryOperator ell-boundaryOperator m)*sourceVertex sharp
  have hDx : timeRead D x=timeRead (boundaryOperator ell) y-timeRead (boundaryOperator m) y :=
    (congrArg (fun A : TH →L[ℂ] TH => A x) (time_mul (boundaryOperator ell-boundaryOperator m) (sourceVertex sharp))).trans
      (congrArg (fun A : TH →L[ℂ] TH => A y) (time_sub (boundaryOperator ell) (boundaryOperator m)))
  have hDm : ‖timeRead D x‖<δ := by
    rw [hDx]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hlim : 2*C*‖timeRead (relativeTail m ell) x‖^2+(1/2 : ℝ)*‖timeRead D x‖^2<ε := by
    have ht := pow_le_pow_left₀ (norm_nonneg _) hTm.le 2
    have hd := pow_le_pow_left₀ (norm_nonneg _) hDm.le 2
    have hp : 2*C*δ^2+(1/2 : ℝ)*δ^2<ε := by
      rw [hδsq]
      field_simp [show (8*(C+1):ℝ)≠0 by positivity]
      nlinarith
    exact (add_le_add (mul_le_mul_of_nonneg_left ht (by positivity))
      (mul_le_mul_of_nonneg_left hd (by norm_num))).trans_lt hp
  let fT := readFamily (relativeTail m ell) f
  let fD := readFamily D f
  have hconv := ((square_tendsto sourceFilter fT).const_mul (2*C)).add
    ((square_tendsto sourceFilter fD).const_mul (1/2 : ℝ))
  have hval : 2*C*‖fT‖^2+(1/2 : ℝ)*‖fD‖^2<ε := by
    have hT : ‖fT‖=‖timeRead (relativeTail m ell) x‖ := read_family_norm _ f
    have hD : ‖fD‖=‖timeRead D x‖ := read_family_norm _ f
    exact (congrArg₂ (fun a b : ℝ => 2*C*a^2+(1/2 : ℝ)*b^2<ε) hT hD).mpr hlim
  filter_upwards [hconv.eventually (gt_mem_nhds hval)] with F hF
  exact (lp_coefficient_energy sharp m ell (value f F)).trans hF.le

/-- The original full frequency resolvent input has a common joined-coefficient
 tail on the unchanged source filter. Both boundary peaks are paid together. -/
theorem actual_coefficient_full_frequency_tail (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
          ‖boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := family_coefficient_tail sharp (wholeInputFamily advanced μ hμ g) ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  rw [coefficient_total_integral sharp m ell advanced μ hμ F g]
  exact ENNReal.ofReal_le_ofReal hF

open SourceScalarPositiveBulkWard

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The paid Z tail is consumed by the original source states, for both
independent sharp branches and both actual frequency legs. -/
theorem actual_joined_source_tail (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
          ‖embed (PositiveScalarWeakBudget.coefficient sharp a m ell
            (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_coefficient_full_frequency_tail sharp advanced μ hμ (g : H) ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have he (w : ℝ) (a : ScalarIndex) :
      embed (PositiveScalarWeakBudget.coefficient sharp a m ell
        (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))=
        boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) (g : H)) :=
    (original_bounded_coefficient_core sharp a m ell _).symm.trans
      (congrArg (boundedCoefficient sharp a m ell) (state_embed F _ _ g))
  simpa only [he] using hF

end LowEnergy.SourceLocalizedInverseFormPayment
