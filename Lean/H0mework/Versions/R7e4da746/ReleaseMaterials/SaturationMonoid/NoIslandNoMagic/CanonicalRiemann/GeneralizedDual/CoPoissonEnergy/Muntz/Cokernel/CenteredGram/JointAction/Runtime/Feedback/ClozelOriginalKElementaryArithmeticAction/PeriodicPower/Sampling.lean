import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.ProjectionPrice
import Mathlib.Analysis.Fourier.AddCircle
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Sampling
open Complex Filter MeasureTheory Set FourierTransform
open BurnolPhysicalState OriginalRieszSource OriginalRieszSourceGreen OriginalPaPhysicalGreen
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.ProjectionPrice
open scoped Topology ENNReal InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "Eq" => burnolQuarterZeroExtension
local notation "b" => burnolRieszSingleFourierSource
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

private def circleRaw (value : BurnolL2) : AddCircle (1:ℝ)→ℂ :=
  AddCircle.liftIoc 1 (-(1/2):ℝ) (value:ℝ→ℂ)

private theorem circle_mem (value : BurnolL2) :
    MemLp (circleRaw value) 2 AddCircle.haarAddCircle := by
  have domain : MemLp (value:ℝ→ℂ) 2 (volume.restrict (Ioc (-(1/2):ℝ) (-(1/2)+1))) :=
    (Lp.memLp value).mono_measure Measure.restrict_le_self
  exact domain.memLp_liftIoc.haarAddCircle

private def circleValue (value : BurnolL2) : Lp ℂ 2 (AddCircle.haarAddCircle (T:=(1:ℝ))) :=
  (circle_mem value).toLp (circleRaw value)

def intervalSample (value : BurnolL2) (n : ℤ) : ℂ :=
  _root_.fourierCoeffOn (by norm_num : (-(1/2):ℝ)<1/2) (value:ℝ→ℂ) n

private theorem circle_coefficient (value : BurnolL2) (n : ℤ) :
    _root_.fourierBasis.repr (circleValue value) n=intervalSample value n := by
  rw [_root_.fourierBasis_repr]
  change _root_.fourierCoeff ((circle_mem value).toLp (circleRaw value)) n=_
  rw [_root_.fourierCoeff_congr_ae ((circle_mem value).coeFn_toLp)]
  change _root_.fourierCoeff (AddCircle.liftIoc 1 (-(1/2):ℝ) (value:ℝ→ℂ)) n=_
  rw [_root_.fourierCoeff_liftIoc_eq]
  norm_num only [show (-(1/2):ℝ)+1=1/2 by norm_num]
  rfl

private theorem circle_inner (left right : BurnolL2) :
    inner ℂ (circleValue left) (circleValue right)=
      ∫ x : ℝ in (-(1/2):ℝ)..(1/2:ℝ),inner ℂ (left x) (right x) := by
  rw [L2.inner_def]
  have raw : (fun x : AddCircle (1:ℝ)=>inner ℂ (circleValue left x) (circleValue right x))=ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc 1 (-(1/2):ℝ) (fun x : ℝ=>inner ℂ (left x) (right x)) := by
    filter_upwards [(circle_mem left).coeFn_toLp,(circle_mem right).coeFn_toLp] with x l r
    change inner ℂ ((circle_mem left).toLp (circleRaw left) x) ((circle_mem right).toLp (circleRaw right) x)=_
    rw [l,r]
    rfl
  rw [integral_congr_ae raw,AddCircle.integral_haarAddCircle]
  norm_num only [inv_one,one_smul]
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
  norm_num

/-- The complete period-one lattice pairing is paid by the actual Fourier Hilbert basis. -/
theorem actual_interval_cross_hasSum (left right : BurnolL2) :
    HasSum (fun n : ℤ=>star (intervalSample left n)*intervalSample right n)
      (∫ x : ℝ in (-(1/2):ℝ)..(1/2:ℝ),inner ℂ (left x) (right x)) := by
  have source:=lp.hasSum_inner (𝕜:=ℂ) (_root_.fourierBasis.repr (circleValue left))
    (_root_.fourierBasis.repr (circleValue right))
  rw [_root_.fourierBasis.repr.inner_map_map,circle_inner] at source
  apply source.congr_fun
  intro n
  rw [circle_coefficient,circle_coefficient,RCLike.inner_apply,starRingEnd_apply]
  ring

private theorem supported_interval_inner (left right : BurnolL2)
    (support : originalPhysicalCutoff (1/2) left=left) :
    (∫ x : ℝ in (-(1/2):ℝ)..(1/2:ℝ),inner ℂ (left x) (right x))=inner ℂ left right := by
  have raw:=originalPhysicalCutoff_coeFn (1/2) left
  rw [support] at raw
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ)≤1/2),←integral_Icc_eq_integral_Ioc]
  rw [L2.inner_def]
  change (∫x:ℝ in symmetricInterval (1/2),inner ℂ (left x) (right x))=_
  rw [←integral_indicator (measurableSet_symmetricInterval (1/2))]
  apply integral_congr_ae
  filter_upwards [raw] with x source
  by_cases inside : x∈symmetricInterval (1/2)
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,source,indicator_of_notMem inside]
    simp

def fourierPoint (value : BurnolL2) (frequency : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-2*Real.pi*Complex.I*(frequency:ℂ)*(x:ℂ))*value x

def fourierSample (value : BurnolL2) (n : ℤ) : ℂ := fourierPoint value n

private theorem interval_fourier_sample (value : BurnolL2)
    (support : originalPhysicalCutoff (1/2) value=value) (n : ℤ) :
    intervalSample value n=fourierSample value n := by
  rw [intervalSample,_root_.fourierCoeffOn_eq_integral]
  norm_num only [show (1/2:ℝ)-(-(1/2))=1 by norm_num,div_one,one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ)≤1/2),←integral_Icc_eq_integral_Ioc]
  have raw:=originalPhysicalCutoff_coeFn (1/2) value
  rw [support] at raw
  rw [fourierSample,fourierPoint]
  change (∫x:ℝ in symmetricInterval (1/2),_root_.fourier (-n) (x:AddCircle ((1/2:ℝ)-(-(1/2)))) • value x)=_
  rw [←integral_indicator (measurableSet_symmetricInterval (1/2))]
  apply integral_congr_ae
  filter_upwards [raw] with x source
  by_cases inside : x∈symmetricInterval (1/2)
  · rw [indicator_of_mem inside,_root_.fourier_coe_apply]
    simp only [smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  · rw [indicator_of_notMem inside,source,indicator_of_notMem inside]
    simp

theorem actual_supported_sampling (left right : BurnolL2)
    (leftSupport : originalPhysicalCutoff (1/2) left=left)
    (rightSupport : originalPhysicalCutoff (1/2) right=right) :
    HasSum (fun n : ℤ=>star (fourierSample left n)*fourierSample right n) (inner ℂ left right) := by
  have source:=actual_interval_cross_hasSum left right
  rw [supported_interval_inner left right leftSupport] at source
  apply source.congr_fun
  intro n
  rw [interval_fourier_sample left leftSupport,interval_fourier_sample right rightSupport]

def originalFourierSample (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolRadiusTruncatedFourierRaw q (b c:Hq) x

private theorem quarter_supported (state : Hq) :
    originalPhysicalCutoff (1/2) (Eq state)=Eq state := by
  simpa only [neg_zero,Real.exp_zero,mul_one,burnolMultiplicativeDilation_zero] using
    OriginalRieszFiniteColumns.intervalDilation_cutoff_self state 0 (1/2) (by norm_num)

private theorem shifted_quarter_supported (state : Hq) (h : ℝ) (bound : h≤Real.log 2) :
    originalPhysicalCutoff (1/2) (D (-h) (Eq state))=D (-h) (Eq state) := by
  apply OriginalRieszFiniteColumns.intervalDilation_cutoff_self
  have exponential : Real.exp h≤2 := by
    simpa only [Real.exp_log (by norm_num:(0:ℝ)<2)] using Real.exp_le_exp.mpr bound
  simp only [neg_neg]
  nlinarith

theorem actual_extension_fourier_point (c : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    fourierPoint (Eq (b c:Hq)) frequency=originalFourierSample c frequency := by
  unfold fourierPoint originalFourierSample burnolRadiusTruncatedFourierRaw VectorFourier.fourierIntegral
  rw [←integral_indicator (measurableSet_symmetricInterval q)]
  apply integral_congr_ae
  filter_upwards [burnolQuarterZeroExtension_coe (b c:Hq)] with x read
  rw [read]
  by_cases inside : x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,Circle.smul_def,Real.fourierChar_apply]
    simp only [smul_eq_mul,innerₗ_apply_apply,Real.inner_apply]
    congr 1
    congr 1
    push_cast
    ring
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]
    simp

private theorem sample_extension (c : BurnolCompletedMellinCoordinate) (n : ℤ) :
    fourierSample (Eq (b c:Hq)) n=originalFourierSample c n := actual_extension_fourier_point c n

theorem actual_original_lattice_self (c : BurnolCompletedMellinCoordinate) :
    HasSum (fun n : ℤ=>star (originalFourierSample c n)*originalFourierSample c n)
      (inner ℂ (b c) (b c)) := by
  have source:=actual_supported_sampling (Eq (b c:Hq)) (Eq (b c:Hq))
    (quarter_supported _) (quarter_supported _)
  rw [quarter_extension_inner] at source
  exact source.congr_fun (fun n=>by simp only [sample_extension])

/-- The real Fourier point is read after the original dilation change of variables. -/
theorem actual_dilation_fourier_point (value : BurnolL2) (h frequency : ℝ) :
    fourierPoint (D (-h) value) frequency=
      (Real.exp (h/2):ℂ)*fourierPoint value (Real.exp h*frequency) := by
  rw [fourierPoint,integral_congr_ae (by
    filter_upwards [burnolMultiplicativeDilation_coeFn (-h) value] with x source
    rw [source])]
  unfold burnolL2RawNormalizedDilation
  let f : ℝ→ℂ := fun y=>Complex.exp (-2*Real.pi*Complex.I*((Real.exp h*frequency:ℝ):ℂ)*(y:ℂ))*value y
  have inverse : Real.exp h*Real.exp (-h)=1 := by rw [←Real.exp_add];simp
  have integrand : (fun x:ℝ=>Complex.exp (-2*Real.pi*Complex.I*(frequency:ℂ)*(x:ℂ))*
      ((Real.exp (-h/2):ℂ)*value (Real.exp (-h)*x)))=
      (fun x:ℝ=>(Real.exp (-h/2):ℂ)*f (Real.exp (-h)*x)) := by
    funext x
    have exponent : -2*Real.pi*Complex.I*((Real.exp h*frequency:ℝ):ℂ)*((Real.exp (-h)*x:ℝ):ℂ)=
        -2*Real.pi*Complex.I*(frequency:ℂ)*(x:ℂ) := by
      have invC : (Real.exp h:ℂ)*(Real.exp (-h):ℂ)=1 := by exact_mod_cast inverse
      simp only [Complex.ofReal_mul]
      linear_combination (-2*Real.pi*Complex.I*(frequency:ℂ)*(x:ℂ))*invC
    dsimp only [f]
    rw [exponent]
    ring
  rw [integrand,integral_const_mul,Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr (Real.exp_pos (-h))),Complex.real_smul,←mul_assoc]
  have scalar : (Real.exp (-h/2):ℂ)*((Real.exp (-h))⁻¹:ℝ)=Real.exp (h/2) := by
    rw [←Complex.ofReal_mul,←Real.exp_neg,neg_neg,←Real.exp_add]
    congr 2
    ring
  rw [scalar]
  rfl

/-- Every integer is sampled from the same original Fourier source and its actual opposite clock. -/
theorem actual_original_lattice_pair (c d : BurnolCompletedMellinCoordinate) (h : ℝ)
    (bounded : h≤Real.log 2) :
    HasSum (fun n : ℤ=>star (originalFourierSample c n)*
      ((Real.exp (h/2):ℂ)*originalFourierSample d (Real.exp h*n)))
      (inner ℂ (F (Eq (b c:Hq))) (D h (F (Eq (b d:Hq))))) := by
  have source:=actual_supported_sampling (Eq (b c:Hq)) (D (-h) (Eq (b d:Hq)))
    (quarter_supported _) (shifted_quarter_supported _ h bounded)
  have actual:=fourierL2.inner_map_map (Eq (b c:Hq)) (D (-h) (Eq (b d:Hq)))
  rw [fourierL2_burnolMultiplicativeDilation,neg_neg] at actual
  rw [←actual] at source
  apply source.congr_fun
  intro n
  simp only [fourierSample,actual_extension_fourier_point,actual_dilation_fourier_point]

theorem actual_original_origin (c : BurnolCompletedMellinCoordinate) : originalFourierSample c 0=0 := by
  unfold originalFourierSample burnolRadiusTruncatedFourierRaw VectorFourier.fourierIntegral
  simp only [innerₗ_apply_apply,Real.inner_apply,mul_zero,neg_zero,AddChar.map_zero_eq_one,one_smul]
  have mean:=Constructor.mean_zero (b c)
  rw [Constructor.mean_integral] at mean
  linear_combination mean/2


end OriginalKElementaryArithmeticAction.PeriodicPower.Sampling
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
