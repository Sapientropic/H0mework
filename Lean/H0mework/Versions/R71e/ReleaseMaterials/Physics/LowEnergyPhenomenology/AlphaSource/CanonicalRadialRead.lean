import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalRadialForce
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGaugeMeasure
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparedGraph

/-! Original weighted sharp and quadratic core words. The actual canonical
seed removes the finite CAR normalization; scalar moments and derivatives
remain explicit material inputs. No arbitrary Profile is assigned a momentum
or Hamiltonian domain. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualRadial
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussLiveMomentum GaussCoreDifferential
open GaussNativePotential GaussNativeEnergy GaussCoreHilbert GaussFockPair
open CanonicalGradedFullForce GaussFullHamiltonian
open scoped ContDiff Topology RealInnerProductSpace
open GaussComposite.SourceGraph

theorem P_constant : P=(-Complex.I) • GaussCoframeCore.derivative shift := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · change P f z=(-Complex.I) • GaussCoframeCore.derivative shift f z
    rw [P_original ⟨z,hz⟩, GaussCoframeCore.derivative_apply]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz ((P f).tsupport_subset h))]
    change 0=(-Complex.I) • GaussCoframeCore.derivative shift f z
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz
      ((GaussCoframeCore.derivative shift f).tsupport_subset h)), smul_zero]

theorem Psharp_constant : Psharp=Complex.I • GaussCoframeCore.transpose shift := by
  apply LinearMap.ext
  intro h
  apply GaussCoreLabel.pair_separates
  intro f
  change sourcePair f (Psharp h)=sourcePair f (Complex.I • GaussCoframeCore.transpose shift h)
  rw [show sourcePair f (Psharp h)=sourcePair (P f) h from
    GaussNativeForm.adjoint_pair ambientDirection f h, P_constant]
  have ht := congrArg (starRingEnd ℂ) (GaussCoframeCore.derivative_pair shift h f)
  rw [GaussNativeForm.pair_conjugate, GaussNativeForm.pair_conjugate] at ht
  change inner ℂ (embed ((-Complex.I) • GaussCoframeCore.derivative shift f)) (embed h)=
    inner ℂ (embed f) (embed (Complex.I • GaussCoframeCore.transpose shift h))
  simp only [map_smul, inner_smul_left, inner_smul_right, map_neg, Complex.conj_I, neg_neg]
  exact congrArg (Complex.I*·) ht

private theorem transpose_component (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word=
      GaussDensityCore.weightedTranspose word.card v (component word f) z.val := by
  let h := GaussDensityCore.weightedTranspose word.card v (component word f)
  have row : embed (GaussCoframeCore.transpose v f) word=scalarLp word.card h := by
    rw [GaussCoframeCore.transpose_embed]
    rfl
  have ae : (fun w : physicalChart => GaussCoframeCore.transpose v f w.val word) =ᵐ[
      GaussHistoryHilbert.numberMeasure word.card] (fun w : physicalChart => h w.val) :=
    (embed_ae (GaussCoframeCore.transpose v f) word).symm.trans (row ▸ scalarLp_ae word.card h)
  have eq := MeasureTheory.Measure.eq_of_ae_eq ae
    ((component word (GaussCoframeCore.transpose v f)).continuous.comp continuous_subtype_val)
    (h.continuous.comp continuous_subtype_val)
  exact congrFun eq z

theorem shift_source_euler : shift=sourceG⁻¹ • ActualGaugeMeasure.euler GaussHistoryHilbert.sourcePoint.val := by
  ext
  all_goals simp [shift, sliceDirection, axis, ActualGaugeMeasure.euler, GaussHistoryHilbert.sourcePoint]

theorem source_ordering_coefficient : 3/sourceG=5*Real.sqrt 2 := by
  have hs : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  unfold sourceG Stage9C.Material.SpinPair.gaugeScale Stage9C.Material.SpinPair.spinScale
  field_simp
  nlinarith

theorem Psharp_source (f : QuantumTest) :
    Psharp f GaussHistoryHilbert.sourcePoint.val = P f GaussHistoryHilbert.sourcePoint.val -
      (Complex.I*(3/sourceG : ℝ)) • f GaussHistoryHilbert.sourcePoint.val := by
  rw [Psharp_constant]
  apply PiLp.ext
  intro word
  change Complex.I*GaussCoframeCore.transpose shift f GaussHistoryHilbert.sourcePoint.val word=_
  rw [transpose_component]
  have h := ActualGaugeMeasure.source_weightedTranspose word.card sourceG⁻¹ (component word f)
  rw [← shift_source_euler] at h
  rw [h]
  have componentDerivative := congrArg (fun h : GaussDensityCore.ScalarTest =>
    h GaussHistoryHilbert.sourcePoint.val) (GaussCoframeCore.component_derivative shift f word)
  change GaussCoframeCore.derivative shift f GaussHistoryHilbert.sourcePoint.val word=
    GaussDensityCore.derivative shift (component word f) GaussHistoryHilbert.sourcePoint.val at componentDerivative
  rw [GaussCoframeCore.derivative_apply, GaussDensityCore.derivative_apply] at componentDerivative
  rw [← componentDerivative]
  rw [P_original]
  change Complex.I*(-(fderiv ℝ f GaussHistoryHilbert.sourcePoint.val shift) word-
      (3*(sourceG⁻¹ : ℝ) : ℂ)*f GaussHistoryHilbert.sourcePoint.val word)=
    (-Complex.I)*(fderiv ℝ f GaussHistoryHilbert.sourcePoint.val shift) word-
      (Complex.I*(3/sourceG : ℝ))*f GaussHistoryHilbert.sourcePoint.val word
  push_cast
  ring

def symmetricP : CoreEnd := (1/2 : ℂ) • (P+Psharp)

theorem symmetricP_pair (f h : QuantumTest) :
    sourcePair f (symmetricP h)=sourcePair (symmetricP f) h := by
  have hp := P_pair f h
  have hs : sourcePair f (Psharp h)=sourcePair (P f) h := GaussNativeForm.adjoint_pair ambientDirection f h
  simp only [symmetricP, LinearMap.smul_apply, LinearMap.add_apply, sourcePair, map_add,
    map_smul, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right] at hp hs ⊢
  rw [hp, hs]
  simp only [map_div₀, map_one, map_ofNat]
  ring

theorem coordinate_momentum_force : actionForce Q P=-(LinearMap.id : CoreEnd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hg : HasDerivAt (fun r : ℝ => g (translate z r)) 1 0 := by
      simp only [g_translate]
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (g z)
    have h := scalar_force g (fun _ => g_smooth.contDiffAt) ⟨z,hz⟩ 1 hg f
    simp only [Complex.ofReal_one, neg_smul, one_smul] at h
    convert! h using 1
  · change actionForce Q P f z= -f z
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz ((actionForce Q P f).tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h)), neg_zero]

theorem Q_pair (f h : QuantumTest) : sourcePair f (Q h)=sourcePair (Q f) h :=
  GaussNativeForm.multiply_pair _ _ f h

def symmetricSquare : CoreEnd := symmetricP.comp symmetricP
def positiveMomentumSquare : CoreEnd := Psharp.comp P
def coordinateSquare : CoreEnd := Q.comp Q
def mixedWord : CoreEnd := (1/2 : ℂ) • (Q.comp symmetricP+symmetricP.comp Q)

theorem positiveMomentumSquare_read (f : QuantumTest) :
    (sourcePair f (positiveMomentumSquare f)).re=‖embed (P f)‖^2 := by
  change (sourcePair f (Psharp (P f))).re=_
  rw [show sourcePair f (Psharp (P f))=sourcePair (P f) (P f) from
    GaussNativeForm.adjoint_pair ambientDirection f (P f)]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (embed (P f))

theorem coordinateSquare_read (f : QuantumTest) :
    (sourcePair f (coordinateSquare f)).re=‖embed (Q f)‖^2 := by
  change (sourcePair f (Q (Q f))).re=_
  rw [Q_pair]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (embed (Q f))

theorem P_seedSection (f : GaussDensityCore.ScalarTest) :
    P (GaussComposite.SourceGraph.seedSection f)=GaussComposite.SourceGraph.seedSection ((-Complex.I) • GaussDensityCore.derivative shift f) := by
  rw [P_constant]
  apply DFunLike.ext
  intro z
  change (-Complex.I) • GaussCoframeCore.derivative shift (GaussComposite.SourceGraph.seedSection f) z =
    ((-Complex.I)*GaussDensityCore.derivative shift f z) • CanonicalCompletedSector.seed
  rw [GaussCoframeCore.derivative_apply, GaussDensityCore.derivative_apply]
  let M := (ContinuousLinearMap.id ℂ ℂ).smulRight CanonicalCompletedSector.seed
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z)
  have hm := (M.restrictScalars ℝ).hasFDerivAt.comp z hf
  have hd : fderiv ℝ (GaussComposite.SourceGraph.seedSection f) z shift=
      (fderiv ℝ f z shift) • CanonicalCompletedSector.seed := by
    change fderiv ℝ ((M.restrictScalars ℝ) ∘ f) z shift=_
    rw [hm.fderiv]
    rfl
  rw [hd, smul_smul]

theorem Psharp_seedSection (f : GaussDensityCore.ScalarTest) :
    Psharp (GaussComposite.SourceGraph.seedSection f)=GaussComposite.SourceGraph.seedSection
      (Complex.I • GaussDensityCore.weightedTranspose 1 shift f) := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · rw [Psharp_constant]
    apply PiLp.ext
    intro word
    change Complex.I*GaussCoframeCore.transpose shift (GaussComposite.SourceGraph.seedSection f) z word=
      (Complex.I*GaussDensityCore.weightedTranspose 1 shift f z)*CanonicalCompletedSector.seed word
    rw [transpose_component shift _ word ⟨z,hz⟩, GaussComposite.SourceGraph.seedSection_component, map_smul]
    change Complex.I*(CanonicalCompletedSector.seed word*
      GaussDensityCore.weightedTranspose word.card shift f z)=_
    by_cases hw : word.card=1
    · rw [hw]; ring
    · rw [GaussComposite.SourceGraph.seed_zero_off_one word hw]
      ring
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz
      ((Psharp (GaussComposite.SourceGraph.seedSection f)).tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz
      ((GaussComposite.SourceGraph.seedSection
        (Complex.I • GaussDensityCore.weightedTranspose 1 shift f)).tsupport_subset h))]

def symmetricScalarP : GaussDensityCore.ScalarTest →ₗ[ℂ] GaussDensityCore.ScalarTest :=
  (1/2 : ℂ) • ((-Complex.I) • GaussDensityCore.derivative shift+
    Complex.I • GaussDensityCore.weightedTranspose 1 shift)

theorem symmetricP_seedSection (f : GaussDensityCore.ScalarTest) :
    symmetricP (GaussComposite.SourceGraph.seedSection f)=
      GaussComposite.SourceGraph.seedSection (symmetricScalarP f) := by
  change (1/2 : ℂ) • (P (GaussComposite.SourceGraph.seedSection f)+
    Psharp (GaussComposite.SourceGraph.seedSection f))=_
  rw [P_seedSection,Psharp_seedSection]
  simp only [symmetricScalarP,LinearMap.smul_apply,LinearMap.add_apply,map_add,map_smul]

def coordinateScalar : GaussDensityCore.ScalarTest →ₗ[ℂ] GaussDensityCore.ScalarTest :=
  GaussDensityCore.multiply (fun z => (g z : ℂ))
    (fun _ => (Complex.ofRealCLM.contDiff.comp g_smooth).contDiffAt)

theorem Q_seedSection (f : GaussDensityCore.ScalarTest) :
    Q (GaussComposite.SourceGraph.seedSection f)=GaussComposite.SourceGraph.seedSection (coordinateScalar f) := by
  apply DFunLike.ext
  intro z
  change (g z : ℂ) • (f z • CanonicalCompletedSector.seed)=
    ((g z : ℂ)*f z) • CanonicalCompletedSector.seed
  rw [smul_smul]

theorem seed_coordinate_second (f : GaussDensityCore.ScalarTest) :
    (sourcePair (GaussComposite.SourceGraph.seedSection f) (coordinateSquare (GaussComposite.SourceGraph.seedSection f))).re=
      ‖scalarLp 1 (coordinateScalar f)‖^2 := by
  rw [coordinateSquare_read, Q_seedSection, GaussComposite.SourceGraph.seedSection_norm, GaussComposite.SourceGraph.seed_unit, one_mul]

theorem seed_momentum_second (f : GaussDensityCore.ScalarTest) :
    (sourcePair (GaussComposite.SourceGraph.seedSection f) (positiveMomentumSquare (GaussComposite.SourceGraph.seedSection f))).re=
      ‖scalarLp 1 (GaussDensityCore.derivative shift f)‖^2 := by
  rw [positiveMomentumSquare_read, P_seedSection, GaussComposite.SourceGraph.seedSection_norm, GaussComposite.SourceGraph.seed_unit, one_mul,
    GaussComposite.SourceGraph.scalarLp_smul, norm_smul, norm_neg, Complex.norm_I, one_mul]

theorem seed_symmetric_second (f : GaussDensityCore.ScalarTest) :
    (sourcePair (GaussComposite.SourceGraph.seedSection f)
      (symmetricSquare (GaussComposite.SourceGraph.seedSection f))).re=
      ‖scalarLp 1 (symmetricScalarP f)‖^2 := by
  change (sourcePair (GaussComposite.SourceGraph.seedSection f)
    (symmetricP (symmetricP (GaussComposite.SourceGraph.seedSection f)))).re=_
  rw [symmetricP_pair]
  change (inner ℂ (embed (symmetricP (GaussComposite.SourceGraph.seedSection f)))
    (embed (symmetricP (GaussComposite.SourceGraph.seedSection f)))).re=_
  have same := inner_self_eq_norm_sq (𝕜 := ℂ)
    (embed (symmetricP (GaussComposite.SourceGraph.seedSection f)))
  change (inner ℂ (embed (symmetricP (GaussComposite.SourceGraph.seedSection f)))
    (embed (symmetricP (GaussComposite.SourceGraph.seedSection f)))).re=_ at same
  rw [same, symmetricP_seedSection,
    GaussComposite.SourceGraph.seedSection_norm, GaussComposite.SourceGraph.seed_unit, one_mul]

theorem seed_mixed_read (f : GaussDensityCore.ScalarTest) :
    sourcePair (GaussComposite.SourceGraph.seedSection f)
      (mixedWord (GaussComposite.SourceGraph.seedSection f))=
    (1/2 : ℂ)*(sourcePair (GaussComposite.SourceGraph.seedSection (coordinateScalar f))
      (GaussComposite.SourceGraph.seedSection (symmetricScalarP f))+
      sourcePair (GaussComposite.SourceGraph.seedSection (symmetricScalarP f))
      (GaussComposite.SourceGraph.seedSection (coordinateScalar f))) := by
  change sourcePair (GaussComposite.SourceGraph.seedSection f) ((1/2 : ℂ) •
    (Q (symmetricP (GaussComposite.SourceGraph.seedSection f))+
      symmetricP (Q (GaussComposite.SourceGraph.seedSection f))))=_
  have expand (x y z : QuantumTest) : sourcePair x ((1/2 : ℂ) • (y+z))=
      (1/2 : ℂ)*(sourcePair x y+sourcePair x z) := by
    simp only [sourcePair,map_add,map_smul,inner_smul_right,inner_add_right]
  rw [expand,Q_pair (GaussComposite.SourceGraph.seedSection f)
    (symmetricP (GaussComposite.SourceGraph.seedSection f)),
    symmetricP_pair (GaussComposite.SourceGraph.seedSection f)
      (Q (GaussComposite.SourceGraph.seedSection f)),Q_seedSection,symmetricP_seedSection]

def yukawaDifference : CoreEnd := GaussFullHamiltonian.adjointAction-GaussYukawaOperator.originalAction
def pairRate (A : CoreEnd) : CoreEnd := Complex.I • (sharpAction.comp A-A.comp fullAction)

theorem pairRate_full (A : CoreEnd) :
    pairRate A=actionForce fullAction A+Complex.I • yukawaDifference.comp A := by
  ext f
  simp only [pairRate, actionForce, yukawaDifference, sharpAction, fullAction,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    smul_add, smul_sub]
  abel

theorem momentum_pairRate (f : QuantumTest) (z : physicalChart) :
    pairRate P f z.val =
      actionForce (GaussNativeForm.scalarKinetic+GaussNativeForm.gaugeKinetic) P f z.val+
      actionForce GaussCoframeForm.coframeAction P f z.val-matterCurrent f z.val-
      (scalarSlopePotential z.val+magneticSlopePotential z.val : ℂ) • f z.val+
      Complex.I • yukawaDifference (P f) z.val := by
  rw [pairRate_full]
  change actionForce fullAction P f z.val+Complex.I • yukawaDifference (P f) z.val=_
  rw [full_force_generated]

theorem pairRate_product (A C : CoreEnd) :
    pairRate (A.comp C)=(pairRate A).comp C+A.comp (pairRate C)-
      Complex.I • A.comp (yukawaDifference.comp C) := by
  ext f
  simp only [pairRate, yukawaDifference, sharpAction, fullAction,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    map_smul, map_sub, map_add, smul_add, smul_sub]
  abel

theorem positiveMomentumSquare_rate :
    pairRate positiveMomentumSquare=(pairRate Psharp).comp P+Psharp.comp (pairRate P)-
      Complex.I • Psharp.comp (yukawaDifference.comp P) := pairRate_product Psharp P

theorem coordinateSquare_rate :
    pairRate coordinateSquare=(pairRate Q).comp Q+Q.comp (pairRate Q)-
      Complex.I • Q.comp (yukawaDifference.comp Q) := pairRate_product Q Q

theorem pairRate_weak (A : CoreEnd) (f h : QuantumTest) :
    sourcePair f (pairRate A h)=Complex.I*
      (sourcePair (fullAction f) (A h)-sourcePair f (A (fullAction h))) := by
  change inner ℂ (embed f) (embed (Complex.I • (sharpAction (A h)-A (fullAction h))))=_
  rw [map_smul, map_sub, inner_smul_right, inner_sub_right]
  change Complex.I*(sourcePair f (sharpAction (A h))-sourcePair f (A (fullAction h)))=_
  rw [full_action_pair]

def coreJet (f : QuantumTest) (t : ℝ) : QuantumTest := f+(-Complex.I*(t : ℂ)) • fullAction f

/-- The original full generator's first core jet; no all-time domain claim
for an unbounded quadratic word is inferred from its graph-free Hilbert flow. -/
theorem coreJet_pair_derivative (A : CoreEnd) (f h : QuantumTest) :
    HasDerivAt (fun t : ℝ => sourcePair (coreJet f t) (A (coreJet h t)))
      (sourcePair f (pairRate A h)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => -Complex.I*(t : ℂ)) (-Complex.I) 0 := by
    convert! (Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x := (0 : ℝ))).const_mul (-Complex.I) using 1
    change -Complex.I=(-Complex.I)*(1 : ℂ)
    ring
  have left := (hc.smul_const (embed (fullAction f))).const_add (embed f)
  have right := (hc.smul_const (embed (A (fullAction h)))).const_add (embed (A h))
  rw [pairRate_weak]
  convert! left.inner ℂ right using 1
  · funext t
    simp only [sourcePair, coreJet, map_add, map_smul]
  · simp only [Complex.ofReal_zero, mul_zero, zero_smul, add_zero, inner_smul_left,
      inner_smul_right, map_neg, Complex.conj_I, neg_neg, sourcePair]
    ring

private theorem projected_Y_zero (f : QuantumTest) :
    GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel (GaussYukawaOperator.originalAction f)=0 := by
  have hb : CanonicalGradedCurrent.sourceProjection*GaussYukawaOperator.bounded=0 :=
    CanonicalGradedCurrent.positive_grade_left_zero _ 1
      (by simpa only [Nat.cast_one,one_smul] using GaussYukawaGrade.bounded_raises) (by omega)
  have normalized : GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel
      (GaussYukawaCoefficient.action f)=0 := by
    apply embed_injective
    rw [GaussCoreLabel.embed_project, ← GaussYukawaOperator.bounded_core, map_zero]
    exact congrArg (fun T : H →L[ℂ] H => T (embed f)) hb
  have radius : GaussCoreLabel.Commutes CanonicalGradedCurrent.sourceLabel
      GaussYukawaOperator.radiusAction := by
    intro h
    apply DFunLike.ext
    intro z
    change GaussCoreLabel.fiberPiece CanonicalGradedCurrent.sourceLabel
      (GaussYukawaCoefficient.radius z • h z)=
      GaussYukawaCoefficient.radius z • GaussCoreLabel.fiberPiece CanonicalGradedCurrent.sourceLabel (h z)
    exact (GaussCoreLabel.fiberPiece CanonicalGradedCurrent.sourceLabel).map_smul_of_tower _ _
  rw [← GaussYukawaOperator.radius_action_return, radius, normalized, map_zero]

private theorem projected_Y_pair (f h : QuantumTest) :
    sourcePair (GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f)
      (GaussYukawaOperator.originalAction h)=0 := by
  rw [← GaussCoreLabel.project_pair, projected_Y_zero]
  simp only [sourcePair,map_zero,inner_zero_right]

theorem seedSection_project (f : GaussDensityCore.ScalarTest) :
    GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel
      (GaussComposite.SourceGraph.seedSection f)=GaussComposite.SourceGraph.seedSection f := by
  apply DFunLike.ext
  intro z
  change GaussCoreLabel.fiberPiece (1,0) (f z • CanonicalCompletedSector.seed)=_
  rw [map_smul, CanonicalGradedCurrent.canonical_seed_N1_G0]
  rfl

theorem Q_blocks : GaussCoreLabel.Commutes CanonicalGradedCurrent.sourceLabel Q :=
  GaussCoreLabel.commutes_real _ _ _
theorem P_blocks : GaussCoreLabel.Commutes CanonicalGradedCurrent.sourceLabel P :=
  GaussDiagonalGrade.native_momentum _ _
theorem Psharp_blocks : GaussCoreLabel.Commutes CanonicalGradedCurrent.sourceLabel Psharp :=
  GaussDiagonalGrade.native_adjoint _ _

theorem seed_pairRate_return (A : CoreEnd)
    (preserves : GaussCoreLabel.Commutes CanonicalGradedCurrent.sourceLabel A)
    (f h : GaussDensityCore.ScalarTest) :
    sourcePair (GaussComposite.SourceGraph.seedSection f)
      (pairRate A (GaussComposite.SourceGraph.seedSection h))=
    sourcePair (GaussComposite.SourceGraph.seedSection f)
      (actionForce GaussDiagonalHistory.diagonalAction A (GaussComposite.SourceGraph.seedSection h)) := by
  let x := GaussComposite.SourceGraph.seedSection f
  let y := GaussComposite.SourceGraph.seedSection h
  have hx : GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel x=x := seedSection_project f
  have hy : GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel y=y := seedSection_project h
  have hay : GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel (A y)=A y := by rw [preserves,hy]
  have hleft : sourcePair x (adjointAction (A y))=0 := by
    rw [yukawa_pair]
    have hp := congrArg (starRingEnd ℂ) (projected_Y_pair (A y) x)
    rw [GaussNativeForm.pair_conjugate, map_zero, hay] at hp
    exact hp
  have hright : sourcePair x (A (GaussYukawaOperator.originalAction y))=0 := by
    rw [← hx, ← GaussCoreLabel.project_pair, preserves, projected_Y_zero, map_zero]
    simp only [sourcePair,map_zero,inner_zero_right]
  change sourcePair x (pairRate A y)=sourcePair x (actionForce GaussDiagonalHistory.diagonalAction A y)
  simp only [pairRate, actionForce, sharpAction, fullAction, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  simp only [sourcePair,map_smul,map_sub,map_add,inner_smul_right,inner_sub_right,inner_add_right] at hleft hright ⊢
  rw [hleft,hright]
  ring

theorem seed_coordinate_rate_return (f h : GaussDensityCore.ScalarTest) :
    sourcePair (GaussComposite.SourceGraph.seedSection f)
      (pairRate coordinateSquare (GaussComposite.SourceGraph.seedSection h))=
    sourcePair (GaussComposite.SourceGraph.seedSection f)
      (actionForce GaussDiagonalHistory.diagonalAction coordinateSquare (GaussComposite.SourceGraph.seedSection h)) :=
  seed_pairRate_return _ (GaussCoreLabel.commutes_comp _ Q_blocks Q_blocks) f h

theorem seed_momentum_rate_return (f h : GaussDensityCore.ScalarTest) :
    sourcePair (GaussComposite.SourceGraph.seedSection f)
      (pairRate positiveMomentumSquare (GaussComposite.SourceGraph.seedSection h))=
    sourcePair (GaussComposite.SourceGraph.seedSection f)
      (actionForce GaussDiagonalHistory.diagonalAction positiveMomentumSquare (GaussComposite.SourceGraph.seedSection h)) :=
  seed_pairRate_return _ (GaussCoreLabel.commutes_comp _ Psharp_blocks P_blocks) f h

end LowEnergy.ActualRadial
