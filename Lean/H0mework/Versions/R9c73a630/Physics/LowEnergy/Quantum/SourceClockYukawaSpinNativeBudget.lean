import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaSpinClosure
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaSpinJointForce
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaSpinNativeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussQuantumMultiplier
open GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum GaussFockWeights
open SourceMixedNativeReturn SourceNativeCutoffContact SourceRelativePowerTail SourceCornerForcing
open PositiveScalarWeakBudget PositiveScalarCoefficientDecay SourceLocalizedInverseFormPayment
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceCutoffSharp MeasureTheory Filter SourceRetardedBandCurrent SourceActualResolventEnergy
open SourceFamilyHilbert SourceFamilyOperator FullYSourceFiniteTimeIntegral FullYSourceTimeFamilyGraph
open FullYSourceCutoffTimeGraph FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceScalarDoubleCurrent SourceInverseNeutralSpinCurrent SourceClockYukawaSpinClosure
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] SourceMixedNativeReturn.fullAction

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


def spinBounded (j : Fin 4) : Op :=
  GaussBoundedMultiplier.extension (fun _ => quantized (GaussCoframeSpin.full (activeIndex j)))
    (fun _ => contDiffAt_const) (fun _ w => weight_commute w _)
      ‖quantized (GaussCoframeSpin.full (activeIndex j))‖ (norm_nonneg _)
        (fun _ v => ContinuousLinearMap.le_opNorm _ v)

private theorem spin_bounded_core (j : Fin 4) (f : QuantumTest) :
    spinBounded j (embed f)=embed (activeSpin j f) :=
  GaussBoundedMultiplier.extension_core (fun _ => quantized (GaussCoframeSpin.full (activeIndex j)))
    (fun _ => contDiffAt_const) (fun _ w => weight_commute w _)
      ‖quantized (GaussCoframeSpin.full (activeIndex j))‖ (norm_nonneg _)
        (fun _ v => ContinuousLinearMap.le_opNorm _ v) f

def jointCoefficient (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ) : End :=
  if h0 : mu.val=0 then coefficient sharp a m ell else
  if h1 : mu.val<5 then bracket (activeSpin ⟨mu.val-1,by omega⟩) (coefficient sharp a m ell) else
    bracket (activeSpin ⟨mu.val-5,by omega⟩) (bracket (activeSpin 3) (coefficient sharp a m ell))

def boundedJointCoefficient (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ) : Op :=
  if h0 : mu.val=0 then boundedCoefficient sharp a m ell else
  if h1 : mu.val<5 then bracket (spinBounded ⟨mu.val-1,by omega⟩) (boundedCoefficient sharp a m ell) else
    bracket (spinBounded ⟨mu.val-5,by omega⟩) (bracket (spinBounded 3) (boundedCoefficient sharp a m ell))

attribute [local irreducible] spinBounded boundedCoefficient coefficient activeSpin
  boundedJointCoefficient jointCoefficient

private theorem bracket_core (A B : Op) (a b : End)
    (ha : ∀ f, A (embed f)=embed (a f)) (hb : ∀ f,B (embed f)=embed (b f)) (f : QuantumTest) :
    bracket A B (embed f)=embed (bracket a b f) := by
  simp only [bracket,mul_apply_eq_comp,sub_apply,Module.End.mul_apply,LinearMap.sub_apply,ha,hb,map_sub]

/-- The eight native coefficients are the same actual spin-closure images of the paid joined Z. -/
theorem original_joint_coefficient_core (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ)
    (f : QuantumTest) : boundedJointCoefficient sharp mu a m ell (embed f)=
      embed (jointCoefficient sharp mu a m ell f) := by
  have hZ := original_bounded_coefficient_core sharp a m ell
  have hJ (j : Fin 4) := bracket_core (spinBounded j) (boundedCoefficient sharp a m ell)
    (activeSpin j) (coefficient sharp a m ell) (spin_bounded_core j) hZ
  have hJJ (j : Fin 4) := bracket_core (spinBounded j)
    (bracket (spinBounded 3) (boundedCoefficient sharp a m ell)) (activeSpin j)
    (bracket (activeSpin 3) (coefficient sharp a m ell)) (spin_bounded_core j) (hJ 3)
  unfold boundedJointCoefficient jointCoefficient
  split
  · exact hZ f
  · split
    · exact hJ _ f
    · exact hJJ _ f

private theorem lp_sub (A B : Op) : (A-B).compLpL 2 (MeasureTheory.volume : Measure ℝ)=
    A.compLpL 2 MeasureTheory.volume-B.compLpL 2 MeasureTheory.volume := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [(A-B).coeFn_compLpL f,A.coeFn_compLpL f,B.coeFn_compLpL f,
    Lp.coeFn_sub (A.compLpL 2 MeasureTheory.volume f) (B.compLpL 2 MeasureTheory.volume f)] with w hAB hA hB hs
  change ((A-B).compLpL 2 MeasureTheory.volume f) w=
    ((A.compLpL 2 MeasureTheory.volume f-B.compLpL 2 MeasureTheory.volume f) w)
  rw [hAB,hs]
  simp only [Pi.sub_apply,hA,hB,sub_apply]

private theorem read_value (A : Op) (f : Family L2H sourceFilter) (F : Index) :
    value (readFamily A f) F=A.compLpL 2 MeasureTheory.volume (value f F) := rfl

attribute [local irreducible] readFamily ContinuousLinearMap.compLpL

private theorem lp_bracket_apply (B A : Op) (f : L2H) :
    (bracket B A).compLpL 2 MeasureTheory.volume f=
      B.compLpL 2 MeasureTheory.volume (A.compLpL 2 MeasureTheory.volume f)-
        A.compLpL 2 MeasureTheory.volume (B.compLpL 2 MeasureTheory.volume f) := by
  have hs := lp_sub (B*A) (A*B)
  have hm := congrArg₂ (fun X Y : L2H →L[ℂ] L2H => X-Y) (lp_mul B A) (lp_mul A B)
  exact congrArg (fun T : L2H →L[ℂ] L2H => T f) (hs.trans hm)

private theorem norm_commutator_price (b a : L2H →L[ℂ] L2H) (v : L2H) :
    ‖b (a v)-a (b v)‖^2 ≤ 2*‖b‖^2*‖a v‖^2+2*‖a (b v)‖^2 := by
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (b (a v)) (a (b v))) 2
  have ho := pow_le_pow_left₀ (norm_nonneg _) (b.le_opNorm (a v)) 2
  rw [mul_pow] at ho
  nlinarith only [hn,ho,sq_nonneg (‖b (a v)‖-‖a (b v)‖)]

private def HasTail (Z : ScalarIndex → ℕ → ℕ → Op) : Prop :=
  ∀ f : Family L2H sourceFilter,∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∑ a : ScalarIndex,‖(Z a m ell).compLpL 2 MeasureTheory.volume (value f F)‖^2) ≤ ε

private theorem base_tail (sharp : Bool) : HasTail (fun a m ell => boundedCoefficient sharp a m ell) :=
  family_coefficient_tail sharp

private theorem commutator_tail (Z : ScalarIndex → ℕ → ℕ → Op) (hZ : HasTail Z) (B : Op) :
    HasTail (fun a m ell => bracket B (Z a m ell)) := by
  intro f ε hε
  let b := B.compLpL 2 (MeasureTheory.volume : Measure ℝ)
  let C : ℝ := 2*‖b‖^2+2
  have hC : 0<C := by dsimp [C];positivity
  obtain ⟨N1,h1⟩ := hZ f (ε/C) (div_pos hε hC)
  obtain ⟨N2,h2⟩ := hZ (readFamily B f) (ε/C) (div_pos hε hC)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m ((le_max_left _ _).trans hm) ell hml,
    h2 m ((le_max_right _ _).trans hm) ell hml] with F hf hg
  have hb (a : ScalarIndex) :
      ‖(bracket B (Z a m ell)).compLpL 2 MeasureTheory.volume (value f F)‖^2 ≤
        2*‖b‖^2*‖(Z a m ell).compLpL 2 MeasureTheory.volume (value f F)‖^2+
        2*‖(Z a m ell).compLpL 2 MeasureTheory.volume (value (readFamily B f) F)‖^2 := by
    have hl := congrArg (fun x : L2H => ‖x‖^2) (lp_bracket_apply B (Z a m ell) (value f F))
    have hp := norm_commutator_price b ((Z a m ell).compLpL 2 MeasureTheory.volume) (value f F)
    have hr := congrArg (fun x : L2H => 2*‖b‖^2*‖(Z a m ell).compLpL 2 MeasureTheory.volume (value f F)‖^2+
      2*‖(Z a m ell).compLpL 2 MeasureTheory.volume x‖^2) (read_value B f F).symm
    exact hl.le.trans (hp.trans_eq hr)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset ScalarIndex)) => hb a)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have he : (2*‖b‖^2+2)*(ε/C)=ε := mul_div_cancel₀ _ hC.ne'
  exact hs.trans ((add_le_add (mul_le_mul_of_nonneg_left hf (by positivity))
    (mul_le_mul_of_nonneg_left hg (by norm_num))).trans_eq (by rw [←add_mul,he]))

private theorem joint_family_tail (sharp : Bool) (mu : Fin 8) :
    HasTail (fun a m ell => boundedJointCoefficient sharp mu a m ell) := by
  have h := base_tail sharp
  have hJ (j : Fin 4) : HasTail (fun a m ell => bracket (spinBounded j) (boundedCoefficient sharp a m ell)) :=
    commutator_tail _ h (spinBounded j)
  have hJJ (j : Fin 4) : HasTail (fun a m ell => bracket (spinBounded j)
      (bracket (spinBounded 3) (boundedCoefficient sharp a m ell))) :=
    commutator_tail _ (hJ 3) (spinBounded j)
  by_cases h0 : mu.val=0
  · simpa only [boundedJointCoefficient,dif_pos h0] using h
  · by_cases h1 : mu.val<5
    · simpa only [boundedJointCoefficient,dif_neg h0,dif_pos h1] using hJ ⟨mu.val-1,by omega⟩
    · simpa only [boundedJointCoefficient,dif_neg h0,dif_neg h1] using hJJ ⟨mu.val-5,by omega⟩

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


private theorem input_ae (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    (fun w => value (wholeInputFamily advanced μ hμ g) F w)=ᵐ[MeasureTheory.volume]
      (fun w => finiteResolvent F (actualFrequency advanced μ w) g) :=
  (whole_memLp advanced μ hμ F g).coeFn_toLp

private def radialFamily (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) : Family L2H sourceFilter :=
  readFamily inverseRadius (wholeInputFamily advanced μ hμ g)-wholeInputFamily advanced μ hμ (inverseRadius g)

private theorem radial_ae (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    (fun w => value (radialFamily advanced μ hμ g) F w)=ᵐ[MeasureTheory.volume]
      (fun w => SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g) := by
  let f := value (wholeInputFamily advanced μ hμ g) F
  let b := value (wholeInputFamily advanced μ hμ (inverseRadius g)) F
  have hg := input_ae advanced μ hμ F g
  have hb := input_ae advanced μ hμ F (inverseRadius g)
  have hm := inverseRadius.coeFn_compLpL f
  have hs := Lp.coeFn_sub (inverseRadius.compLpL 2 MeasureTheory.volume f) b
  filter_upwards [hs,hm,hg,hb] with w hsw hmw hgw hbw
  have hv : value (radialFamily advanced μ hμ g) F=inverseRadius.compLpL 2 MeasureTheory.volume f-b := by
    unfold radialFamily readFamily
    rfl
  rw [hv]
  rw [hsw]
  simp only [Pi.sub_apply]
  rw [hmw]
  change inverseRadius (value (wholeInputFamily advanced μ hμ g) F w)-
    value (wholeInputFamily advanced μ hμ (inverseRadius g)) F w=_
  rw [hgw,hbw,SourceRadiusResponseDecay.actual_response_difference F _ (frequency_nonreal advanced μ hμ w)]

private theorem radial_continuous (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    Continuous (fun w : ℝ => SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g) := by
  have hc := frequency_continuous advanced μ hμ F
  have he (w : ℝ) := SourceRadiusResponseDecay.actual_response_difference F _ (frequency_nonreal advanced μ hμ w) g
  simp_rw [he]
  exact (inverseRadius.continuous.comp (hc.clm_apply continuous_const)).sub (hc.clm_apply continuous_const)

private theorem joint_row_integral (sharp advanced : Bool) (mu : Fin 8) (a : ScalarIndex)
    (μ : ℝ) (hμ : 0<μ) (F : Index) (m ell : ℕ) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖boundedJointCoefficient sharp mu a m ell
      (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g)‖^2))=
        ENNReal.ofReal (‖(boundedJointCoefficient sharp mu a m ell).compLpL 2 MeasureTheory.volume
          (value (radialFamily advanced μ hμ g) F)‖^2) := by
  let f := value (radialFamily advanced μ hμ g) F
  let Z := boundedJointCoefficient sharp mu a m ell
  have he : (fun w : ℝ => ‖Z (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g)‖^2)=ᵐ[MeasureTheory.volume]
      (fun w => ‖(Z.compLpL 2 MeasureTheory.volume f) w‖^2) := by
    filter_upwards [Z.coeFn_compLpL f,radial_ae advanced μ hμ F g] with w hZ hR
    rw [hZ]
    exact congrArg (fun x : H => ‖Z x‖^2) hR.symm
  have hi := (square_integrable MeasureTheory.volume (Z.compLpL 2 MeasureTheory.volume f)).congr he.symm
  change (∫⁻ w : ℝ,ENNReal.ofReal (‖Z (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g)‖^2))=_
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)),
    integral_congr_ae he,←square_integral]

private theorem joint_total_measurable (sharp advanced : Bool) (mu : Fin 8)
    (μ : ℝ) (hμ : 0<μ) (F : Index) (m ell : ℕ) (g : H) :
    Measurable (fun w : ℝ => ENNReal.ofReal (∑ a : ScalarIndex,‖boundedJointCoefficient sharp mu a m ell
      (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g)‖^2)) := by
  have hc : Continuous (fun w : ℝ => ∑ a : ScalarIndex,‖boundedJointCoefficient sharp mu a m ell
      (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g)‖^2) := by
    apply continuous_finsetSum
    intro a _
    exact ((boundedJointCoefficient sharp mu a m ell).continuous.comp
      (radial_continuous advanced μ hμ F g)).norm.pow 2
  exact hc.measurable.ennreal_ofReal

private theorem joint_total_integral (sharp advanced : Bool) (mu : Fin 8)
    (μ : ℝ) (hμ : 0<μ) (F : Index) (m ell : ℕ) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,‖boundedJointCoefficient sharp mu a m ell
      (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g)‖^2))=
        ENNReal.ofReal (∑ a : ScalarIndex,‖(boundedJointCoefficient sharp mu a m ell).compLpL 2 MeasureTheory.volume
          (value (radialFamily advanced μ hμ g) F)‖^2) := by
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  rw [lintegral_finsetSum Finset.univ]
  · congr 1
    funext a
    exact joint_row_integral sharp advanced mu a μ hμ F m ell g
  · intro a _
    exact (((boundedJointCoefficient sharp mu a m ell).continuous.comp
      (radial_continuous advanced μ hμ F g)).norm.pow 2).measurable.ennreal_ofReal

private theorem joint_response_tail (sharp advanced : Bool) (mu : Fin 8)
    (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,‖boundedJointCoefficient sharp mu a m ell
          (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := joint_family_tail sharp mu (radialFamily advanced μ hμ g) ε hε
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  rw [joint_total_integral sharp advanced mu μ hμ F m ell g]
  exact ENNReal.ofReal_le_ofReal hF

open SourceScalarPositiveBulkWard SourceClockYukawaRadialCoefficient SourceScalarPairedTransport

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (q : QuantumTest) :
    embed (compressionCore F q)=GaussGradedCompression.compression F (embed q) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem radial_core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (radialCore F z hz g)=SourceRadiusResponseDecay.response F z (g:H) := by
  rw [radialCore,state_embed]
  change finiteResolvent F z (embed (SourceRadiusResponseDecay.radialCurrent F (state F z hz g)))=_
  rw [SourceRadiusResponseDecay.original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←inverse_core,state_embed]
  simp only [SourceRadiusResponseDecay.response,mul_apply_eq_comp,sub_apply,map_sub]

/-- The full eight-by-seventy native coefficient on the actual corrected radial response has one source-filter cutoff. -/
theorem actual_joint_radial_coefficient_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ mu : Fin 8,∑ a : ScalarIndex,
          ‖embed (jointCoefficient sharp mu a m ell
            (radialCore F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hp (i : Bool×Bool×Fin 8) := joint_response_tail i.1 i.2.1 i.2.2 μ hμ (g:H)
    (ε/8) (div_pos hε (by norm_num))
  choose Ns hs using hp
  let N := Finset.univ.sup Ns
  refine ⟨N,fun m hm ell hml => ?_⟩
  have he : ∀ᶠ F in (sourceFilter : Filter Index),∀ i : Bool×Bool×Fin 8,
      (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,‖boundedJointCoefficient i.1 i.2.2 a m ell
        (SourceRadiusResponseDecay.response F (actualFrequency i.2.1 μ w) (g:H))‖^2)) ≤ ENNReal.ofReal (ε/8) :=
    Filter.eventually_all.mpr (fun i => hs i m ((Finset.le_sup (f := Ns) (Finset.mem_univ i)).trans hm) ell hml)
  filter_upwards [he] with F hF
  intro sharp advanced
  have hc (w : ℝ) (mu : Fin 8) (a : ScalarIndex) :
      embed (jointCoefficient sharp mu a m ell
        (radialCore F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))=
        boundedJointCoefficient sharp mu a m ell
          (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) (g:H)) := by
    rw [←original_joint_coefficient_core,radial_core_embed]
  simp only [hc]
  have hs0 (w : ℝ) (mu : Fin 8) : 0 ≤ ∑ a : ScalarIndex,‖boundedJointCoefficient sharp mu a m ell
      (SourceRadiusResponseDecay.response F (actualFrequency advanced μ w) (g:H))‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun mu _ => hs0 _ mu)]
  rw [lintegral_finsetSum Finset.univ (fun mu _ => joint_total_measurable sharp advanced mu μ hμ F m ell (g:H))]
  calc
    _ ≤ ∑ _ : Fin 8,ENNReal.ofReal (ε/8) := Finset.sum_le_sum (fun mu _ => hF (sharp,advanced,mu))
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => (div_pos hε (by norm_num)).le)]
      congr 1
      simp
      ring

open SourceClockYukawaNormalizedCurrent SourceClockYukawaTail SourceClockYukawaCubicCurrent
open SourceClockYukawaRadialNativeBudget SourceHardyRetardedTail SourceRetardedForcingTail

private theorem inverse_spin (j : Fin 4) : Commute inverseAction (activeSpin j) := by
  unfold activeSpin
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (reciprocal z:ℂ) • quantized (GaussCoframeSpin.full (activeIndex j)) (f z)=
    quantized (GaussCoframeSpin.full (activeIndex j)) ((reciprocal z:ℂ) • f z)
  exact (map_smul _ _ _).symm

private theorem inverse_coefficient (sharp : Bool) (mu : Fin 8) :
    Commute inverseAction (spinClosureCoefficient sharp mu) := by
  have hY : Commute inverseAction (fullAction sharp) := by
    unfold fullAction
    cases sharp
    · exact GaussRadialHamiltonian.original_commutes.symm
    · exact GaussRadialHamiltonian.adjoint_commutes.symm
  have hb (A B : End) (hA : Commute inverseAction A) (hB : Commute inverseAction B) :
      Commute inverseAction (bracket A B) := (hA.mul_right hB).sub_right (hB.mul_right hA)
  unfold spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient
  split
  · exact hY
  · split
    · exact hb _ _ (inverse_spin _) hY
    · exact hb _ _ (inverse_spin _) (hb _ _ (inverse_spin 3) hY)

def normalizedJoint (sharp : Bool) (mu : Fin 8) : Op :=
  if h0 : mu.val=0 then sourceB sharp else
  if h1 : mu.val<5 then bracket (spinBounded ⟨mu.val-1,by omega⟩) (sourceB sharp) else
    bracket (spinBounded ⟨mu.val-5,by omega⟩) (bracket (spinBounded 3) (sourceB sharp))

private theorem normalized_joint_core (sharp : Bool) (mu : Fin 8) (f : QuantumTest) :
    normalizedJoint sharp mu (embed f)=embed (inverseAction (spinClosureCoefficient sharp mu f)) := by
  have hs (j : Fin 4) (A : End) : bracket (activeSpin j) (inverseAction*A)=
      inverseAction*bracket (activeSpin j) A := by
    have h := (inverse_spin j).eq
    unfold bracket
    linear_combination (norm := noncomm_ring) -h*A
  have hY : ∀ f,sourceB sharp (embed f)=embed ((inverseAction*fullAction sharp) f) :=
    original_normalized_core sharp
  have hJ (j : Fin 4) (f : QuantumTest) :
      bracket (spinBounded j) (sourceB sharp) (embed f)=
        embed ((inverseAction*bracket (activeSpin j) (fullAction sharp)) f) := by
    rw [bracket_core _ _ _ _ (spin_bounded_core j) hY,hs]
  have hJJ (j : Fin 4) (f : QuantumTest) :
      bracket (spinBounded j) (bracket (spinBounded 3) (sourceB sharp)) (embed f)=
        embed ((inverseAction*bracket (activeSpin j) (bracket (activeSpin 3) (fullAction sharp))) f) := by
    rw [bracket_core _ _ _ _ (spin_bounded_core j) (hJ 3),hs]
  unfold normalizedJoint spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient
  split
  · exact hY f
  · split
    · exact hJ _ f
    · exact hJJ _ f

attribute [local irreducible] normalizedJoint inverseAction SourceClockYukawaTail.sourceB
  SourceClockYukawaSpinJointForce.currentCore SourceClockYukawaSpinJointForce.cutoffCore
  resolventCore compressionCore defectAction diagonalAction

def cutoffResponseCore (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  resolventCore F z hz (SourceClockYukawaSpinJointForce.currentCore sharp m ell F mu
    (resolventCore F z hz (coreEquiv.symm g)))

def rightNativeCoefficient (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  jointCoefficient sharp mu a m ell (radialCore F z hz g)+
    inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F z hz g)

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore
  exact state_embed F z hz (coreEquiv f)

private theorem core_inverses (F : Index) (z : ℂ) (hz : z.im≠0) :
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 ∧
      resolventCore F z hz*(compressionCore F-z • (1:End))=1 := by
  constructor
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_sub,map_smul,compression_embed,resolvent_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] using h
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      resolvent_embed,map_sub,map_smul,compression_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_left (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] using h

private theorem response_difference (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    cutoffResponseCore sharp mu m ell F z hz g=
      spinClosureCoefficient sharp mu (SourceMixedNativeReturn.thetaAction m ell (resolventCore F z hz (coreEquiv.symm g)))-
        resolventCore F z hz (SourceMixedNativeReturn.thetaAction m ell (spinClosureCoefficient sharp mu (coreEquiv.symm g))) := by
  let L : End := compressionCore F-z • 1
  let R : End := resolventCore F z hz
  let A : End := SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu
  have hi := core_inverses F z hz
  have hm (L R A : End) (hL : L*R=1) (hR : R*L=1) : R*bracket L A*R=A*R-R*A := by
    unfold bracket
    rw [mul_sub,sub_mul,←mul_assoc,←mul_assoc,hR,one_mul,mul_assoc,mul_assoc,hL,mul_one]
  have hJ : bracket L A=SourceClockYukawaSpinJointForce.currentCore sharp m ell F mu := by
    unfold SourceClockYukawaSpinJointForce.currentCore defectAction
    dsimp only [L,A]
    simp only [bracket,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    module
  have h := LinearMap.congr_fun (hm L R A hi.1 hi.2) (coreEquiv.symm g)
  rw [hJ] at h
  have ht : Commute (SourceMixedNativeReturn.thetaAction m ell) (spinClosureCoefficient sharp mu) := by
    exact ((((Commute.one_left _).sub_left (inverse_coefficient sharp mu)).pow_left _).sub_left
      (((Commute.one_left _).sub_left (inverse_coefficient sharp mu)).pow_left _))
  have ht' := LinearMap.congr_fun ht.eq (coreEquiv.symm g)
  simp only [Module.End.mul_apply] at ht'
  simpa only [cutoffResponseCore,Module.End.mul_apply,LinearMap.sub_apply,A,SourceClockYukawaSpinJointForce.cutoffCore,ht',R]
    using h

private def coefficientSource (sharp : Bool) (mu : Fin 8) (g : diagonal.domain) : diagonal.domain :=
  coreEquiv (spinClosureCoefficient sharp mu (coreEquiv.symm g))

private def normalizedColumn (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) : Op :=
  directionOperator a*inverseRadius*normalizedJoint sharp mu

private theorem derivative_core (a : ScalarIndex) (f : QuantumTest) :
    inverseDerivative a (embed f)=embed (inverseDerivativeCore a f) := by
  simp only [inverseDerivative,inverseDerivativeCore,pow_two,mul_apply_eq_comp,Module.End.mul_apply,
    inverse_core,original_direction_core]

private theorem normalized_column_core (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (f : QuantumTest) :
    normalizedColumn sharp mu a (embed f)=embed (inverseDerivativeCore a (spinClosureCoefficient sharp mu f)) := by
  simp only [normalizedColumn,inverseDerivativeCore,pow_two,mul_apply_eq_comp,Module.End.mul_apply,
    normalized_joint_core,inverse_core,original_direction_core]

attribute [local irreducible] normalizedColumn inverseDerivative inverseRadius directionOperator
  finiteResolvent GaussGradedCompression.compression

private theorem derivative_response_return (sharp : Bool) (mu : Fin 8) (a : ScalarIndex)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F z hz g))=
      normalizedColumn sharp mu a (relativeTail m ell (finiteResolvent F z (g:H)))-
        inverseDerivative a (finiteResolvent F z (relativeTail m ell (coefficientSource sharp mu g:H))) := by
  rw [←derivative_core,response_difference,map_sub]
  have hg : embed (coreEquiv.symm g)=(g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply g)
  have hY : embed (spinClosureCoefficient sharp mu (coreEquiv.symm g))=(coefficientSource sharp mu g:H) := rfl
  rw [resolvent_embed,←SourceMixedNativeReturn.theta_core,hY,map_sub]
  congr 1
  let v : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
  have hr : finiteResolvent F z (g:H)=embed v :=
    (congrArg (finiteResolvent F z) hg.symm).trans (resolvent_embed F z hz (coreEquiv.symm g)).symm
  have ht : relativeTail m ell (finiteResolvent F z (g:H))=
      embed (SourceMixedNativeReturn.thetaAction m ell v) :=
    (congrArg (relativeTail m ell) hr).trans (SourceMixedNativeReturn.theta_core m ell v)
  exact (derivative_core a (spinClosureCoefficient sharp mu (SourceMixedNativeReturn.thetaAction m ell v))).trans
    ((normalized_column_core sharp mu a (SourceMixedNativeReturn.thetaAction m ell v)).symm.trans
      (congrArg (normalizedColumn sharp mu a) ht.symm))

private def columnPrice (sharp : Bool) (mu : Fin 8) : ℝ := 2*(∑ a : ScalarIndex,‖normalizedColumn sharp mu a‖^2)
private def derivativePrice : ℝ := 2*(∑ a : ScalarIndex,‖inverseDerivative a‖^2)

attribute [local irreducible] columnPrice derivativePrice

private theorem two_square (x y : H) : ‖x-y‖^2≤2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]

private theorem derivative_response_bound (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑ a : ScalarIndex,‖embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F z hz g))‖^2) ≤
      columnPrice sharp mu*‖relativeTail m ell (finiteResolvent F z (g:H))‖^2+
      derivativePrice*‖finiteResolvent F z
        (relativeTail m ell (coefficientSource sharp mu g:H))‖^2 := by
  let x := relativeTail m ell (finiteResolvent F z (g:H))
  let y := finiteResolvent F z (relativeTail m ell (coefficientSource sharp mu g:H))
  calc
    _ ≤ ∑ a : ScalarIndex,(2*‖normalizedColumn sharp mu a‖^2*‖x‖^2+2*‖inverseDerivative a‖^2*‖y‖^2) := by
      apply Finset.sum_le_sum
      intro a _
      rw [derivative_response_return sharp mu a m ell F z hz g]
      have hx := pow_le_pow_left₀ (norm_nonneg _) ((normalizedColumn sharp mu a).le_opNorm x) 2
      have hy := pow_le_pow_left₀ (norm_nonneg _) ((inverseDerivative a).le_opNorm y) 2
      rw [mul_pow] at hx hy
      have hs := two_square (normalizedColumn sharp mu a x) (inverseDerivative a y)
      nlinarith only [hx,hy,hs]
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,columnPrice,derivativePrice]
      ring

private theorem derivative_energy_measurable (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (∑ a : ScalarIndex,
      ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g))‖^2)) := by
  simp_rw [derivative_response_return]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hc : Continuous (fun w : ℝ => ∑ a : ScalarIndex,
      ‖normalizedColumn sharp mu a (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))-
        inverseDerivative a (finiteResolvent F (line μ w)
          (relativeTail m ell (coefficientSource sharp mu g:H)))‖^2) := by
    apply continuous_finsetSum
    intro a _
    exact ((((normalizedColumn sharp mu a).continuous.comp ((relativeTail m ell).continuous.comp
      (hr.clm_apply continuous_const))).sub ((inverseDerivative a).continuous.comp
        (hr.clm_apply continuous_const))).norm.pow 2)
  exact hc.measurable.ennreal_ofReal

private theorem derivative_response_common_tail (sharp : Bool) (mu : Fin 8) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
          ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := columnPrice sharp mu+derivativePrice
  have hP : 0≤columnPrice sharp mu := by
    unfold columnPrice
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hQ : 0≤derivativePrice := by
    unfold derivativePrice
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hC : 0≤C := add_nonneg hP hQ
  let δ := ε/(C+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N₁,h₁⟩ := actual_theta_full_frequency_tail μ hμ g δ hδ
  obtain ⟨N₂,h₂⟩ := fixed_forcing_uniform_energy_tail μ hμ (1:Op)
    (coefficientSource sharp mu g:H) δ hδ
  refine ⟨max N₁ N₂,fun m hm ell hml => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hml] with F hx
  have hy := h₂ m ((le_max_right _ _).trans hm) ell hml F
  simp only [one_apply_eq_self] at hy
  let X (w : ℝ) := ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2)
  let Y (w : ℝ) := ENNReal.ofReal (‖finiteResolvent F (line μ w)
    (relativeTail m ell (coefficientSource sharp mu g:H))‖^2)
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hymeas : Measurable (fun w => ENNReal.ofReal derivativePrice*Y w) :=
    ((((hr.clm_apply continuous_const).norm.pow 2).measurable).ennreal_ofReal).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (columnPrice sharp mu)*X w+ENNReal.ofReal derivativePrice*Y w := by
      apply lintegral_mono
      intro w
      dsimp only [X,Y]
      apply (ENNReal.ofReal_le_ofReal (derivative_response_bound sharp mu m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)).trans
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ]
      exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (columnPrice sharp mu)*(∫⁻ w : ℝ,X w)+ENNReal.ofReal derivativePrice*(∫⁻ w : ℝ,Y w) := by
      rw [lintegral_add_right _ hymeas,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (columnPrice sharp mu)*ENNReal.ofReal δ+ENNReal.ofReal derivativePrice*ENNReal.ofReal δ := by gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ,←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have he : columnPrice sharp mu*δ+derivativePrice*δ=C*(ε/(C+1)) := by dsimp [C,δ];ring
      rw [he,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<C+1)).mpr
      nlinarith


/-- Frequency measurability is generated by the same actual coefficient and fixed-source resolvent words. -/
theorem actual_joint_native_energy_measurable (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (∑ mu : Fin 8,∑ a : ScalarIndex,
      ‖embed (rightNativeCoefficient sharp mu a m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)‖^2)) := by
  have he (w : ℝ) (mu : Fin 8) (a : ScalarIndex) :
      embed (rightNativeCoefficient sharp mu a m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)=
      boundedJointCoefficient sharp mu a m ell (SourceRadiusResponseDecay.response F (line μ w) (g:H))+
        (normalizedColumn sharp mu a (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))-
          inverseDerivative a (finiteResolvent F (line μ w) (relativeTail m ell (coefficientSource sharp mu g:H)))) := by
    rw [rightNativeCoefficient,map_add,←original_joint_coefficient_core,radial_core_embed,derivative_response_return]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hc : Continuous (fun w : ℝ => ∑ mu : Fin 8,∑ a : ScalarIndex,
      ‖embed (rightNativeCoefficient sharp mu a m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)‖^2) := by
    simp only [he]
    apply continuous_finsetSum
    intro mu _
    apply continuous_finsetSum
    intro a _
    exact (((boundedJointCoefficient sharp mu a m ell).continuous.comp (radial_continuous false μ hμ F (g:H))).add
      (((normalizedColumn sharp mu a).continuous.comp ((relativeTail m ell).continuous.comp
        (hr.clm_apply continuous_const))).sub ((inverseDerivative a).continuous.comp
          (hr.clm_apply continuous_const)))).norm.pow 2
  exact hc.measurable.ennreal_ofReal

private theorem derivative_all_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ mu : Fin 8,∑ a : ScalarIndex,
          ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hp (i : Bool×Fin 8) := derivative_response_common_tail i.1 i.2 μ hμ g (ε/8) (by positivity)
  choose Ns hs using hp
  let N := Finset.univ.sup Ns
  refine ⟨N,fun m hm ell hml => ?_⟩
  have he := Filter.eventually_all.mpr (fun i : Bool×Fin 8 =>
    hs i m ((Finset.le_sup (f := Ns) (Finset.mem_univ i)).trans hm) ell hml)
  filter_upwards [he] with F hF
  intro sharp
  have hn (w : ℝ) (mu : Fin 8) : 0 ≤ ∑ a : ScalarIndex,
      ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g))‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun mu _ => hn _ mu)]
  rw [lintegral_finsetSum Finset.univ (fun mu _ => derivative_energy_measurable sharp mu m ell F μ hμ g)]
  calc
    _ ≤ ∑ _ : Fin 8,ENNReal.ofReal (ε/8) := Finset.sum_le_sum (fun mu _ => hF (sharp,mu))
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => (div_pos hε (by norm_num)).le)]
      congr 1
      simp
      ring

/-- All eight actual corrected native divergences share the paid Z rS + d rA coefficient tail. -/
theorem actual_joint_native_coefficient_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ mu : Fin 8,∑ a : ScalarIndex,
          ‖embed (rightNativeCoefficient sharp mu a m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N1,h1⟩ := actual_joint_radial_coefficient_tail μ hμ g (ε/4) (by positivity)
  obtain ⟨N2,h2⟩ := derivative_all_tail μ hμ g (ε/4) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m ((le_max_left _ _).trans hm) ell hml,
    h2 m ((le_max_right _ _).trans hm) ell hml] with F hz hd
  intro sharp
  have hZ := hz sharp false
  have hD := hd sharp
  simp only [actualFrequency,Bool.false_eq_true,if_false] at hZ
  let Z (w : ℝ) := ENNReal.ofReal (∑ mu : Fin 8,∑ a : ScalarIndex,
    ‖embed (jointCoefficient sharp mu a m ell
      (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)
  let D (w : ℝ) := ENNReal.ofReal (∑ mu : Fin 8,∑ a : ScalarIndex,
    ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g))‖^2)
  have md : Measurable D := by
    have he : D=(fun w : ℝ => ∑ mu : Fin 8,ENNReal.ofReal (∑ a : ScalarIndex,
        ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g))‖^2)) := by
      funext w
      exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [he]
    exact Finset.measurable_sum Finset.univ (fun mu _ => derivative_energy_measurable sharp mu m ell F μ hμ g)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2:ℝ)*Z w+ENNReal.ofReal (2:ℝ)*D w := by
      apply lintegral_mono
      intro w
      have hb : (∑ mu : Fin 8,∑ a : ScalarIndex,‖embed (rightNativeCoefficient sharp mu a m ell F
          (line μ w) (by simpa only [line_im] using hμ.ne') g)‖^2) ≤
          2*(∑ mu : Fin 8,∑ a : ScalarIndex,‖embed (jointCoefficient sharp mu a m ell
            (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)+
          2*(∑ mu : Fin 8,∑ a : ScalarIndex,‖embed (inverseDerivativeCore a
            (cutoffResponseCore sharp mu m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2) := by
        simp only [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro mu _
        apply Finset.sum_le_sum
        intro a _
        rw [rightNativeCoefficient,map_add]
        have h := two_square
          (embed (jointCoefficient sharp mu a m ell
            (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g)))
          (-embed (inverseDerivativeCore a (cutoffResponseCore sharp mu m ell F
            (line μ w) (by simpa only [line_im] using hμ.ne') g)))
        simpa only [sub_neg_eq_add,norm_neg] using h
      apply (ENNReal.ofReal_le_ofReal hb).trans
      dsimp only [Z,D]
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
      exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,Z w)+ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,D w) := by
      rw [lintegral_add_right _ (md.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4)+ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end LowEnergy.SourceClockYukawaSpinNativeBudget
