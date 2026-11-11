import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Readback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.TwoPieceFourierAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRReciprocalCotestActionSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFiniteColumns
open OriginalKSourceResolventReconstruction
open OriginalWholeDebtRPowerWaveDilationSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "h" => OriginalKPairedBEulerJunctionSource.junctionShift
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "DT" => TemperedDistribution ℝ ℂ
local notation "F" => fourierL2
local notation "U" => burnolMultiplicativeDilation
local notation "Tate" => burnolTateReciprocalL2
local notation "Eq" => burnolQuarterZeroExtension
local notation "cut" => OriginalPaPhysicalGreen.originalPhysicalCutoff
local notation "step" => OriginalWholeDebtRAdjointContactSource.step
namespace ResponseRaw
export OriginalRieszFinitePairing.CoPoisson.Ward.ResponseProfile
  (uRaw vRaw u_continuous v_continuous u_read v_read u_derivative v_derivative)
end ResponseRaw
open private nativeIntegral_sub nativeIntegral_smul from
  H0mework.Versions.R7e4da746.Arithmetic.RieszColumns.Columns
open private step_euler from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
open private actual_direct_R_positive_kernel from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource
open private even_read extension_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRContactSource
open private prefix_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private nativeIntegral_quarter edgeIntegral_quarter from
  H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ColumnMass
open private realExp_cpow_halfDensity from
  H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.GapTailDilation
open private cutoff_enlarge_self radius_le_half from
  H0mework.Versions.R7e4da746.Arithmetic.RieszColumns.Half
namespace Constant
export OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual (seed seedRaw seed_coeFn)
end Constant

/-- Literal rows of the two existing signed Profile programs, before any projection. -/
def nativeInput (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  coupling0 c • Response.wholeU-coupling1 c • Response.wholeV

def sourceY (c : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  nativeIntegral (frequency c) (nativeInput c) endpoint-
    coupling1 c • edgeIntegral (barC c) endpoint

def sourceX (c : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  backwardIntegral (frequency c)
    (coupling1 c • Response.wholeU-coupling0 c • Response.wholeV) endpoint-
      coupling0 c • reverseEdgeIntegral (barC c) endpoint

def positionColumn (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (1/2 : ℂ) • (F (F (sourceX c (-h)))+F (F (sourceX c h)))
def fourierColumn (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (1/2 : ℂ) • (sourceY c (-h)+sourceY c h)

/-- This cotest keeps the actual source program's second column. -/
def reciprocalCotest (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Tate (burnolAnnulusSamplingL2 (fourierColumn c) 0)

/-- The full constant alpha belongs to the native forcing. -/
def nativeForcingInput (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  nativeInput c+coupling1 c • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed

def forcing (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (1/2 : ℂ) • cut 4 (U h (Tate (nativeForcingInput c)))

def lower : ℝ := 4*Real.exp (-h)
private def innerLower : ℝ := q*Real.exp (-h)
private def amplitude : ℂ := (1/2 : ℂ)*(Real.exp (-h/2) : ℂ)
private def nativeRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  coupling0 c*ResponseRaw.uRaw x-coupling1 c*ResponseRaw.vRaw x

private def primitiveInput (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  nativeInput c+((1-c.value)*coupling1 c) • Constant.seed
private def primitiveInputRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  nativeRaw c x+(1-c.value)*coupling1 c
private def primitive (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(1/2 : ℂ) • burnolDirectRightResolventCLM c (primitiveInput c)+
    coupling1 c • Constant.seed
private def nativePrefix (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∫ t : ℝ in 0..x, (t : ℂ)^(c.value-1)*primitiveInputRaw c t

private def thetaRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  coupling1 c-(x : ℂ)^(-c.value)*
    (∫ t : ℝ in x..q, (t : ℂ)^(c.value-1)*primitiveInputRaw c t)

private def thetaSlope (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (nativeRaw c x+coupling1 c-c.value*thetaRaw c x)/(x : ℂ)
private def reciprocalRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  amplitude/(x : ℂ)*thetaRaw c (Real.exp (-h)/x)
private def forcingRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  amplitude/(x : ℂ)*(nativeRaw c (Real.exp (-h)/x)+coupling1 c)
private def reciprocalSlope (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (frequency c*reciprocalRaw c x-forcingRaw c x-(1/2 : ℂ)*reciprocalRaw c x)/(x : ℂ)

def lowerTrace (c : BurnolCompletedMellinCoordinate) : ℂ :=
  amplitude/(lower : ℂ)*coupling1 c
def upperTrace (c : BurnolCompletedMellinCoordinate) : ℂ :=
  amplitude/4*thetaRaw c innerLower

def weight (c : BurnolCompletedMellinCoordinate) : ℂ := 2*c.value-1

def forwardContact (c : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  c.value • burnolDirectRightResolventCLM c (step radius)+(2 : ℂ) • step radius

/-- R acts only on the simpler source forcing and literal steps in this constructor. -/
def weightedField (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolDirectRightResolventCLM c (forcing c)-
    lowerTrace c • forwardContact c lower+
    upperTrace c • forwardContact c 4-(2 : ℂ) • reciprocalCotest c

def sourceA (c : BurnolCompletedMellinCoordinate) : ℂ := (star c.value-c.value)/2

def effectCotest (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  weight c • reciprocalCotest c+star (sourceA c) • weightedField c

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : barC (barC c)=c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]

private theorem input_extension (c : BurnolCompletedMellinCoordinate) :
    nativeInput c=Eq (coupling0 c • (Response.u : BurnolQuarterIntervalL2)-
      coupling1 c • (Response.v : BurnolQuarterIntervalL2)) := by
  simp only [nativeInput,Response.wholeU,Response.wholeV,map_sub,map_smul]

private theorem shift_small : |h|≤Real.log 2 := by
  simpa only [OriginalKPairedBEulerJunctionSource.junctionShift] using fixedShift_small

private theorem input_read (c : BurnolCompletedMellinCoordinate) :
    (nativeInput c : ℝ → ℂ)=ᵐ[volume] (symmetricInterval q).indicator (nativeRaw c) := by
  filter_upwards [Lp.coeFn_sub (coupling0 c • Response.wholeU) (coupling1 c • Response.wholeV),
    Lp.coeFn_smul (coupling0 c) Response.wholeU,Lp.coeFn_smul (coupling1 c) Response.wholeV,
    extension_read Response.u ResponseRaw.uRaw ResponseRaw.u_read,
    extension_read Response.v ResponseRaw.vRaw ResponseRaw.v_read] with x difference left right u v
  change (coupling0 c • Response.wholeU-coupling1 c • Response.wholeV : BurnolL2) x=_
  rw [difference,Pi.sub_apply,left,right]
  change coupling0 c*Response.wholeU x-coupling1 c*Response.wholeV x=_
  change Response.wholeU x=_ at u
  change Response.wholeV x=_ at v
  rw [u,v]
  by_cases inside : x∈symmetricInterval q
  · simp only [indicator_of_mem inside,nativeRaw]
  · simp only [indicator_of_notMem inside,mul_zero,sub_zero]

private theorem primitive_input_read (c : BurnolCompletedMellinCoordinate) :
    (primitiveInput c : ℝ → ℂ)=ᵐ[volume]
      (symmetricInterval q).indicator (primitiveInputRaw c) := by
  filter_upwards [Lp.coeFn_add (nativeInput c) (((1-c.value)*coupling1 c) • Constant.seed),
    Lp.coeFn_smul ((1-c.value)*coupling1 c) Constant.seed,input_read c,Constant.seed_coeFn]
    with x addition scalar source constant
  change (nativeInput c+((1-c.value)*coupling1 c) • Constant.seed : BurnolL2) x=_
  rw [addition,Pi.add_apply,scalar]
  change nativeInput c x+((1-c.value)*coupling1 c)*Constant.seed x=_
  rw [source,constant]
  by_cases inside : x∈symmetricInterval q
  · simp only [indicator_of_mem inside,Constant.seedRaw,if_pos (abs_le.mpr inside),
      primitiveInputRaw,mul_one]
  · simp only [indicator_of_notMem inside,Constant.seedRaw,
      if_neg (fun hx => inside (abs_le.mp hx)),mul_zero,zero_add]

private theorem primitive_input_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (primitiveInput c)=primitiveInput c := by
  have seedEven : reflectL2 Constant.seed=Constant.seed := by
    change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
    rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
    rfl
  simp only [primitiveInput,nativeInput,map_add,map_sub,map_smul,
    Response.wholeU_reflection,Response.wholeV_reflection,seedEven]

/-- Both rows are restrictions of the literal signed Profile program. -/
private theorem single_columns (c : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    singleSource c endpoint=F (F (sourceX c (-endpoint)))+F (sourceY c (-endpoint)) := by
  have inside : F (sourceX c (-endpoint))+sourceY c (-endpoint)=
      coupling1 c • profileIntegral (barC c) (-endpoint)+
        coupling0 c • fourierProfileIntegral (barC c) (-endpoint) := by
    unfold sourceX sourceY profileIntegral fourierProfileIntegral nativeInput
    rw [map_sub,map_smul,fourier_backwardIntegral,fourier_reverseEdgeIntegral]
    simp only [frequency,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,
      map_sub,map_smul,nativeIntegral_sub,nativeIntegral_smul]
    module
  have acted:=congrArg F inside
  rw [map_add] at acted
  exact acted.symm

theorem actual_columns (c : BurnolCompletedMellinCoordinate) :
    pairedSource c h=positionColumn c+F (fourierColumn c) := by
  unfold pairedSource positionColumn fourierColumn
  rw [single_columns,single_columns,neg_neg,map_smul,map_add]
  module

private theorem column_support (c : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    cut (q*Real.exp |endpoint|) (sourceX c endpoint)=sourceX c endpoint ∧
      cut (q*Real.exp |endpoint|) (sourceY c endpoint)=sourceY c endpoint := by
  have backward:=backwardIntegral_interval_cutoff_self (frequency c)
    (coupling1 c • (Response.u : BurnolQuarterIntervalL2)-
      coupling0 c • (Response.v : BurnolQuarterIntervalL2)) endpoint
  have reverse:=reverseEdgeIntegral_cutoff_self (barC c) endpoint
  change cut (q*Real.exp |endpoint|) (reverseEdgeIntegral (barC c) endpoint)=_ at reverse
  have native:=nativeIntegral_interval_cutoff_self (frequency c)
    (coupling0 c • (Response.u : BurnolQuarterIntervalL2)-
      coupling1 c • (Response.v : BurnolQuarterIntervalL2)) endpoint
  have edge:=edgeIntegral_cutoff_self (barC c) endpoint
  constructor
  · change (burnolRadiusZeroExtension _).comp (burnolRadiusRestriction _) (sourceX c endpoint)=_
    unfold sourceX
    rw [map_sub,map_smul]
    change cut _ _-coupling0 c • cut _ _=_
    simp only [map_sub,map_smul] at backward
    simp only [Response.wholeU,Response.wholeV]
    rw [backward,reverse]
  · change (burnolRadiusZeroExtension _).comp (burnolRadiusRestriction _) (sourceY c endpoint)=_
    unfold sourceY
    rw [map_sub,map_smul,input_extension]
    change cut _ _-coupling1 c • cut _ _=_
    rw [native,edge]

private theorem reflected_support (radius : ℝ) (value : BurnolL2)
    (supported : cut radius value=value) : cut radius (reflectL2 value)=reflectL2 value := by
  have restricted:=restrictToInterval_reflectL2 radius value
  change burnolRadiusRestriction radius (reflectL2 value)=
    reflectRestricted radius (burnolRadiusRestriction radius value) at restricted
  change burnolRadiusZeroExtension radius (burnolRadiusRestriction radius (reflectL2 value))=_
  rw [restricted,←burnolRadiusZeroExtension_reflect]
  exact congrArg reflectL2 supported

theorem position_supported (c : BurnolCompletedMellinCoordinate) :
    cut (1/2) (positionColumn c)=positionColumn c := by
  have source (a : ℝ) (small : |a|≤Real.log 2) : cut (1/2) (sourceX c a)=sourceX c a :=
    cutoff_enlarge_self _ _ _ (radius_le_half a small) (column_support c a).1
  have first:=reflected_support (1/2) (sourceX c (-h))
    (source (-h) (by simpa only [abs_neg] using shift_small))
  have second:=reflected_support (1/2) (sourceX c h) (source h shift_small)
  change (burnolRadiusZeroExtension _).comp (burnolRadiusRestriction _) (positionColumn c)=_
  unfold positionColumn
  rw [map_smul,map_add,fourierL2_fourierL2,fourierL2_fourierL2]
  change (1/2 : ℂ) • (cut (1/2) _+cut (1/2) _) = _
  rw [first,second]

theorem fourier_supported (c : BurnolCompletedMellinCoordinate) :
    cut (1/2) (fourierColumn c)=fourierColumn c := by
  have source (a : ℝ) (small : |a|≤Real.log 2) : cut (1/2) (sourceY c a)=sourceY c a :=
    cutoff_enlarge_self _ _ _ (radius_le_half a small) (column_support c a).2
  change (burnolRadiusZeroExtension _).comp (burnolRadiusRestriction _) (fourierColumn c)=_
  unfold fourierColumn
  rw [map_smul,map_add]
  change (1/2 : ℂ) • (cut (1/2) _+cut (1/2) _) = _
  rw [source (-h) (by simpa only [abs_neg] using shift_small),source h shift_small]

private theorem edge_primitive_R (c : BurnolCompletedMellinCoordinate) :
    edgePrimitive (barC c)=((1-c.value)/2 : ℂ) •
      burnolDirectRightResolventCLM c Constant.seed-Constant.seed := by
  have source:=OriginalKConstantSeedWholeRAction.actual_original_R_seed_whole_field c
  have same : OriginalKQuarterTailPhysicalSource.actualStarSource c=barC c := by
    cases c
    rfl
  have unit : c.value-1≠0 := by
    intro zero
    have real:=congrArg Complex.re zero
    norm_num at real
    linarith [c.belowOne]
  have factor : ((1-c.value)/2 : ℂ)*(-2/(c.value-1))=1 := by field_simp [unit];ring
  change burnolDirectRightResolventCLM c Constant.seed=_ at source
  rw [source,OriginalKConstantSeedWholeRAction.actualWholeSeedRField,same,
    smul_smul,factor,one_smul]
  exact (add_sub_cancel_right _ _).symm

private theorem primitive_source (c : BurnolCompletedMellinCoordinate) :
    primitive c=-(1/2 : ℂ) • burnolDirectRightResolventCLM c (nativeInput c)-
      coupling1 c • edgePrimitive (barC c) := by
  rw [edge_primitive_R]
  unfold primitive primitiveInput
  rw [map_add,map_smul]
  simp only [smul_add,smul_sub,smul_smul]
  module

private theorem actual_R_euler (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    GapEuler.euler (burnolDirectRightResolventCLM c value : DT)+
      frequency c • (burnolDirectRightResolventCLM c value : DT)=-(2 : ℂ) • (value : DT) := by
  have source := sourceResolvent_euler (barC c) value
  change GapEuler.euler (burnolDirectRightResolvent (c.value/2) value : DT)+
    frequency c • (burnolDirectRightResolvent (c.value/2) value : DT)=-(2 : ℂ) • (value : DT)
  simpa only [sourceResolvent,sourceRate,frequency,
    OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] using source

/-- The second row's primitive is already generated by the original R action. -/
private theorem native_integral_action (c : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    nativeIntegral (frequency c) (nativeInput c) endpoint=
      -(1/2 : ℂ) • (U endpoint (burnolDirectRightResolventCLM c (nativeInput c))-
        fullMellinTranslationCharacter c.value endpoint •
          burnolDirectRightResolventCLM c (nativeInput c)) := by
  let value := -(1/2 : ℂ) • burnolDirectRightResolventCLM c (nativeInput c)
  have source : GapEuler.euler (value : DT)+(star (barC c).value-1/2) • (value : DT)=
      (nativeInput c : DT) := by
    have native := congrArg (fun v : DT => -(1/2 : ℂ) • v)
      (actual_R_euler c (nativeInput c))
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 value)+
      (star (barC c).value-1/2) • Lp.toTemperedDistributionCLM ℂ volume 2 value=_
    simp only [value,map_smul,Lp.toTemperedDistributionCLM_apply,
      OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
    unfold frequency at native
    linear_combination (norm := module) native
  have acted := OriginalRieszFinitePairing.ColumnIntegral.action_of_euler
    (barC c) value (nativeInput c) source endpoint
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] at acted
  change U endpoint value=fullMellinTranslationCharacter c.value endpoint • value+_ at acted
  unfold value at acted
  simp only [map_smul] at acted
  unfold frequency
  linear_combination (norm := module) -acted

private theorem source_Y_action (c : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    sourceY c endpoint=U endpoint (primitive c)-
      fullMellinTranslationCharacter c.value endpoint • primitive c := by
  rw [sourceY,native_integral_action,primitive_source,edgeIntegral]
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,
    map_sub,map_smul,smul_sub,smul_smul]
  module

private theorem prefix_clipped (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    (∫ t : ℝ in 0..x,(t : ℂ)^(c.value-1)*
      (symmetricInterval q).indicator (primitiveInputRaw c) t)=nativePrefix c (min x q) := by
  have native : MemLp ((symmetricInterval q).indicator (primitiveInputRaw c)) 2 volume :=
    (Lp.memLp (primitiveInput c)).ae_eq (primitive_input_read c)
  have first (t : ℝ) (tp : 0≤t) (tq : t≤q) :
      (∫ s : ℝ in 0..t,(s : ℂ)^(c.value-1)*
        (symmetricInterval q).indicator (primitiveInputRaw c) s)=nativePrefix c t := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le tp] at hs
    change (s : ℂ)^(c.value-1)*(symmetricInterval q).indicator (primitiveInputRaw c) s=
      (s : ℂ)^(c.value-1)*primitiveInputRaw c s
    rw [indicator_of_mem (show s∈symmetricInterval q from ⟨by linarith [hs.1],hs.2.trans tq⟩)]
  by_cases inside : x≤q
  · rw [min_eq_left inside]
    exact first x positive.le inside
  · have after : q≤x := le_of_not_ge inside
    have whole := prefix_integrable c _ native x after
    have low := whole.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ)≤q),uIcc_of_le positive.le]
      exact Icc_subset_Icc le_rfl after)
    have high := whole.mono_set (by
      rw [uIcc_of_le after,uIcc_of_le positive.le]
      exact Icc_subset_Icc (by norm_num : (0 : ℝ)≤q) le_rfl)
    have tail : (∫ s : ℝ in q..x,(s : ℂ)^(c.value-1)*
        (symmetricInterval q).indicator (primitiveInputRaw c) s)=0 := by
      calc
        _=(∫ _s : ℝ in q..x,(0 : ℂ)) := by
          apply intervalIntegral.integral_congr_Ioo_of_le after
          intro s hs
          change (s : ℂ)^(c.value-1)*(symmetricInterval q).indicator (primitiveInputRaw c) s=0
          rw [indicator_of_notMem (show s∉symmetricInterval q from fun hx => hs.1.not_ge hx.2),mul_zero]
        _=0 := intervalIntegral.integral_zero
    rw [min_eq_right after,←intervalIntegral.integral_add_adjacent_intervals low high,
      first q (by norm_num) le_rfl,tail,add_zero]

private def primitiveRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ)^(-c.value)*nativePrefix c (min |x| q)+
    (if |x|≤q then coupling1 c else 0)

private theorem primitive_read (c : BurnolCompletedMellinCoordinate) :
    (primitive c : ℝ → ℂ)=ᵐ[volume] primitiveRaw c := by
  have actedEven : reflectL2 (burnolDirectRightResolventCLM c (primitiveInput c))=
      burnolDirectRightResolventCLM c (primitiveInput c) := by
    have paid:=OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_iterate_even
      c (primitiveInput c) (primitive_input_even c) 1
    exact paid
  have seedEven : reflectL2 Constant.seed=Constant.seed := by
    change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
    rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
    rfl
  have even : reflectL2 (primitive c)=primitive c := by
    simp only [primitive,map_add,map_smul,actedEven,seedEven]
  apply even_read (primitive c) (primitiveRaw c) even
    (by intro x; simp only [primitiveRaw,abs_neg])
  have actual:=actual_direct_R_positive_kernel c (primitiveInput c)
    ((symmetricInterval q).indicator (primitiveInputRaw c)) (primitive_input_read c)
  filter_upwards [actual,
    Lp.coeFn_add (-(1/2 : ℂ) • burnolDirectRightResolventCLM c (primitiveInput c))
      (coupling1 c • Constant.seed),
    Lp.coeFn_smul (-(1/2 : ℂ)) (burnolDirectRightResolventCLM c (primitiveInput c)),
    Lp.coeFn_smul (coupling1 c) Constant.seed,Constant.seed_coeFn]
    with x source addition scalar constant seed positive
  change (-(1/2 : ℂ) • burnolDirectRightResolventCLM c (primitiveInput c)+
    coupling1 c • Constant.seed : BurnolL2) x=_
  rw [addition,Pi.add_apply,scalar,constant]
  change -(1/2 : ℂ)*burnolDirectRightResolvent (c.value/2) (primitiveInput c) x+
    coupling1 c*Constant.seed x=_
  rw [source positive,prefix_clipped c x positive,seed]
  simp only [primitiveRaw,Constant.seedRaw,abs_of_pos positive]
  split_ifs <;> ring

private theorem native_raw_continuous (c : BurnolCompletedMellinCoordinate) :
    Continuous (nativeRaw c) :=
  (continuous_const.mul ResponseRaw.u_continuous).sub
    (continuous_const.mul ResponseRaw.v_continuous)

private theorem weighted_input_continuous (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0<x) :
    ContinuousAt (fun t : ℝ => (t : ℂ)^(c.value-1)*primitiveInputRaw c t) x :=
  (Complex.continuousAt_ofReal_cpow_const x (c.value-1) (Or.inr positive.ne')).mul
    ((native_raw_continuous c).continuousAt.add continuousAt_const)

private theorem theta_derivative (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0<x) : HasDerivAt (thetaRaw c) (thetaSlope c x) x := by
  let input : ℝ → ℂ := fun t => (t : ℂ)^(c.value-1)*primitiveInputRaw c t
  have regular : ContinuousOn input (Icc (min x q) (max x q)) := by
    intro t ht
    exact (weighted_input_continuous c (lt_of_lt_of_le (lt_min positive (by norm_num)) ht.1)).continuousWithinAt
  have integrable : IntervalIntegrable input volume x q := by
    exact ContinuousOn.intervalIntegrable (by simpa only [uIcc] using regular)
  have primitiveDerivative : HasDerivAt (fun t : ℝ => ∫ s : ℝ in t..q,input s) (-input x) x :=
    intervalIntegral.integral_hasDerivAt_left integrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        (fun t ht => (weighted_input_continuous c ht).continuousWithinAt) x positive)
      (weighted_input_continuous c positive)
  have power : HasDerivAt (fun t : ℝ => (t : ℂ)^(-c.value))
      (-c.value*(x : ℂ)^(-c.value-1)) x :=
    (Complex.hasStrictDerivAt_cpow_const (c := -c.value)
      (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal
  have actual:=(hasDerivAt_const x (coupling1 c)).sub (power.mul primitiveDerivative)
  change HasDerivAt (thetaRaw c)
    (0-((-c.value*(x : ℂ)^(-c.value-1)*(∫ s : ℝ in x..q,input s))+
      (x : ℂ)^(-c.value)*(-input x))) x at actual
  have slope : thetaSlope c x=0-((-c.value*(x : ℂ)^(-c.value-1)*(∫ s : ℝ in x..q,input s))+
      (x : ℂ)^(-c.value)*(-input x)) := by
    have xn : (x : ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
    have powerStep : (x : ℂ)^(-c.value-1)=(x : ℂ)^(-c.value)/(x : ℂ) := by
      apply (eq_div_iff xn).mpr
      calc
        _=(x : ℂ)^(-c.value-1)*(x : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
        _=(x : ℂ)^((-c.value-1)+1) := (Complex.cpow_add _ _ xn).symm
        _=(x : ℂ)^(-c.value) := by congr 1;ring
    have powers : (x : ℂ)^(-c.value)*(x : ℂ)^(c.value-1)=(x : ℂ)⁻¹ := by
      rw [←Complex.cpow_add _ _ xn,show -c.value+(c.value-1)=(-1 : ℂ) by ring,
        Complex.cpow_neg,Complex.cpow_one]
    have product : (x : ℂ)^(-c.value)*(-input x)= -primitiveInputRaw c x/(x : ℂ) := by
      dsimp only [input]
      rw [mul_neg,←mul_assoc,powers]
      ring
    rw [product,powerStep]
    unfold thetaSlope thetaRaw input primitiveInputRaw
    field_simp [xn]
    ring
  rwa [←slope] at actual

private theorem theta_q (c : BurnolCompletedMellinCoordinate) : thetaRaw c q=coupling1 c := by
  simp only [thetaRaw,intervalIntegral.integral_same,mul_zero,sub_zero]

private theorem theta_continuous (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0<x) : ContinuousAt (thetaRaw c) x := (theta_derivative c positive).continuousAt

private theorem theta_slope_continuous (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0<x) : ContinuousAt (thetaSlope c) x :=
  (((native_raw_continuous c).continuousAt.add continuousAt_const).sub
    (continuousAt_const.mul (theta_continuous c positive))).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr positive.ne')

private theorem prefix_theta (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0<x) (inside : x≤q) :
    nativePrefix c q=nativePrefix c x+∫ t : ℝ in x..q,(t : ℂ)^(c.value-1)*primitiveInputRaw c t := by
  have weight : IntervalIntegrable (fun t : ℝ => (t : ℂ)^(c.value-1)) volume 0 q :=
    intervalIntegral.intervalIntegrable_cpow' (by
      simp only [Complex.sub_re,Complex.one_re]
      linarith [c.rightHalf])
  have raw : Continuous (primitiveInputRaw c) := (native_raw_continuous c).add continuous_const
  have whole:=weight.mul_continuousOn raw.continuousOn
  exact (intervalIntegral.integral_add_adjacent_intervals
    (whole.mono_set (by
      rw [uIcc_of_le positive.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
      exact Icc_subset_Icc le_rfl inside))
    (whole.mono_set (by
      rw [uIcc_of_le inside,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
      exact Icc_subset_Icc positive.le le_rfl))).symm

private theorem source_Y_positive_quarter (c : BurnolCompletedMellinCoordinate) :
    cut q (sourceY c h)=sourceY c h := by
  change (burnolRadiusZeroExtension q).comp (burnolRadiusRestriction q) (sourceY c h)=_
  unfold sourceY
  rw [map_sub,map_smul,input_extension]
  change cut q (nativeIntegral _ _ h)-coupling1 c • cut q (edgeIntegral (barC c) h)=_
  rw [nativeIntegral_quarter _ _ h OriginalKPairedBEulerJunctionSource.junctionShift_pos.le,
    edgeIntegral_quarter _ h OriginalKPairedBEulerJunctionSource.junctionShift_pos.le]

private theorem source_Y_negative_read (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume,q<x → sourceY c (-h) x=
      if x≤q*Real.exp h then
        (Real.exp (-h/2) : ℂ)*thetaRaw c (Real.exp (-h)*x) else 0 := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-h)*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := Real.exp (-h)) (Real.exp_ne_zero _)
  rw [source_Y_action]
  filter_upwards [Lp.coeFn_sub (U (-h) (primitive c))
      (fullMellinTranslationCharacter c.value (-h) • primitive c),
    burnolMultiplicativeDilation_coeFn (-h) (primitive c),
    Lp.coeFn_smul (fullMellinTranslationCharacter c.value (-h)) (primitive c),
    primitive_read c,qmp.ae_eq (primitive_read c)] with x difference moved scalar direct scaled outside
  have xp : 0<x := lt_trans (by norm_num) outside
  have tp : 0<Real.exp (-h)*x := mul_pos (Real.exp_pos _) xp
  have density := realExp_cpow_halfDensity xp (star c.value) (-h)
  simp only [star_star] at density
  simp only [Function.comp_def] at scaled
  rw [difference,Pi.sub_apply,moved,scalar]
  change (Real.exp (-h/2) : ℂ)*primitive c (Real.exp (-h)*x)-
    fullMellinTranslationCharacter c.value (-h)*primitive c x=_
  rw [scaled,direct]
  simp only [primitiveRaw,abs_of_pos xp,abs_of_pos tp,min_eq_right outside.le,
    if_neg (not_le_of_gt outside)]
  have cancel : Real.exp (-h)*Real.exp h=1 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
  by_cases inside : x≤q*Real.exp h
  · have tq : Real.exp (-h)*x≤q := by
      have shifted:=mul_le_mul_of_nonneg_left inside (Real.exp_pos (-h)).le
      nlinarith [Real.exp_pos (-h)]
    rw [if_pos inside,min_eq_left tq,if_pos tq,prefix_theta c tp tq]
    unfold thetaRaw
    linear_combination (norm := ring_nf)
      (nativePrefix c (Real.exp (-h)*x)+
        (∫ t : ℝ in (Real.exp (-h)*x)..q,(t : ℂ)^(c.value-1)*primitiveInputRaw c t))*density
  · have after : q<Real.exp (-h)*x := by
      have shifted:=mul_lt_mul_of_pos_left (lt_of_not_ge inside) (Real.exp_pos (-h))
      nlinarith [Real.exp_pos (-h)]
    rw [if_neg inside,min_eq_right after.le,if_neg (not_le_of_gt after)]
    linear_combination (norm := ring_nf) density*nativePrefix c q

private theorem primitive_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (primitive c)=primitive c := by
  have acted:=OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_iterate_even
    c (primitiveInput c) (primitive_input_even c) 1
  change reflectL2 (burnolDirectRightResolventCLM c (primitiveInput c))=
    burnolDirectRightResolventCLM c (primitiveInput c) at acted
  have seedEven : reflectL2 Constant.seed=Constant.seed := by
    change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
    rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
    rfl
  simp only [primitive,map_add,map_smul,acted,seedEven]

private theorem second_column_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (fourierColumn c)=fourierColumn c := by
  have action (a : ℝ) : reflectL2 (sourceY c a)=sourceY c a := by
    rw [source_Y_action,map_sub,map_smul,reflectL2_burnolMultiplicativeDilation,primitive_even]
  simp only [fourierColumn,map_smul,map_add,action]

private def sampleRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if q< |x| ∧ |x|≤q*Real.exp h then
    amplitude*thetaRaw c (Real.exp (-h)*|x|) else 0

private theorem actual_second_sample (c : BurnolCompletedMellinCoordinate) :
    (burnolAnnulusSamplingL2 (fourierColumn c) 0 : ℝ → ℂ)=ᵐ[volume] sampleRaw c := by
  let sampled := burnolAnnulusSamplingL2 (fourierColumn c) 0
  have parity:=Lp.coeFn_compMeasurePreserving (fourierColumn c) negMeasurePreserving
  change (reflectL2 (fourierColumn c) : ℝ → ℂ)=ᵐ[volume] fun x => fourierColumn c (-x) at parity
  rw [second_column_even] at parity
  have even : reflectL2 sampled=sampled := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving sampled negMeasurePreserving,
      negMeasurePreserving.quasiMeasurePreserving.ae_eq
        (burnolAnnulusSamplingL2_coeFn (fourierColumn c) 0),
      burnolAnnulusSamplingL2_coeFn (fourierColumn c) 0,parity] with x reflected negative direct same
    change reflectL2 sampled x=sampled (-x) at reflected
    simp only [Function.comp_def] at negative
    rw [reflected,negative,direct]
    simp only [burnolAnnulusSamplingRaw,Nat.cast_zero,zero_add,one_mul]
    by_cases inside : x∈burnolSamplingAnnulus
    · rw [indicator_of_mem inside,indicator_of_mem
        (show -x∈burnolSamplingAnnulus by simpa only [burnolSamplingAnnulus,mem_ofPred_eq,abs_neg] using inside),←same]
    · rw [indicator_of_notMem inside,indicator_of_notMem
        (show -x∉burnolSamplingAnnulus by simpa only [burnolSamplingAnnulus,mem_ofPred_eq,abs_neg] using inside)]
  apply even_read sampled (sampleRaw c) even (by intro x; simp only [sampleRaw,abs_neg])
  have cutRead:=OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn q (sourceY c h)
  rw [source_Y_positive_quarter] at cutRead
  have upper : q*Real.exp h≤4 := by
    have small : h≤Real.log 2 := (le_abs_self h).trans shift_small
    have bounded:=Real.exp_le_exp.mpr small
    rw [Real.exp_log (by norm_num : (0 : ℝ)<2)] at bounded
    linarith
  filter_upwards [burnolAnnulusSamplingL2_coeFn (fourierColumn c) 0,
    Lp.coeFn_smul (1/2 : ℂ) (sourceY c (-h)+sourceY c h),
    Lp.coeFn_add (sourceY c (-h)) (sourceY c h),cutRead,source_Y_negative_read c]
    with x sampled scalar addition positivePart negativePart positive
  change burnolAnnulusSamplingL2 (fourierColumn c) 0 x=_
  rw [sampled]
  simp only [burnolAnnulusSamplingRaw,Nat.cast_zero,zero_add,one_mul,sampleRaw,abs_of_pos positive]
  by_cases outside : q<x
  · have positiveZero : sourceY c h x=0 := by
      rw [positivePart,indicator_of_notMem (show x∉symmetricInterval q from fun hx => outside.not_ge hx.2)]
    have sampleRead : fourierColumn c x=(1/2 : ℂ)*(sourceY c (-h) x+sourceY c h x) := by
      change ((1/2 : ℂ) • (sourceY c (-h)+sourceY c h) : BurnolL2) x=_
      rw [scalar]
      change (1/2 : ℂ)*(sourceY c (-h)+sourceY c h : BurnolL2) x=_
      rw [addition,Pi.add_apply]
    simp only [outside,true_and]
    by_cases inside : x≤q*Real.exp h
    · rw [indicator_of_mem (show x∈burnolSamplingAnnulus by
          change q< |x| ∧ |x|≤4
          rw [abs_of_pos positive]
          exact ⟨outside,inside.trans upper⟩),
        sampleRead,positiveZero,negativePart outside,if_pos inside]
      simp only [if_pos inside]
      unfold amplitude
      ring
    · rw [if_neg inside]
      by_cases sampleInside : x∈burnolSamplingAnnulus
      · rw [indicator_of_mem sampleInside,sampleRead,positiveZero,negativePart outside,if_neg inside]
        ring
      · exact indicator_of_notMem sampleInside _
  · rw [if_neg (not_and.mpr fun first _ => outside first),
      indicator_of_notMem (show x∉burnolSamplingAnnulus from fun hx =>
        outside (by simpa only [abs_of_pos positive] using hx.1))]

private def bandRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if lower< |x| ∧ |x|≤4 then reciprocalRaw c |x| else 0

theorem actual_reciprocal_source (c : BurnolCompletedMellinCoordinate) :
    (reciprocalCotest c : ℝ → ℂ)=ᵐ[volume] bandRaw c := by
  have sampleRead:=actual_second_sample c
  have transformed:=burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (burnolAnnulusSamplingL2 (fourierColumn c) 0))
    ((Lp.memLp (burnolAnnulusSamplingL2 (fourierColumn c) 0)).ae_eq sampleRead) sampleRead
  have read:=(burnolTateReciprocalL2_coeFn
    (burnolAnnulusSamplingL2 (fourierColumn c) 0)).trans transformed
  filter_upwards [read,volume.ae_ne (0 : ℝ),volume.ae_ne lower,volume.ae_ne (-lower),
    volume.ae_ne (4 : ℝ),volume.ae_ne (-4 : ℝ)] with x source nz nl nr n4 nr4
  change Tate (burnolAnnulusSamplingL2 (fourierColumn c) 0) x=_
  rw [source]
  have xp : 0< |x| := abs_pos.mpr nz
  have neLower : |x|≠lower := by
    intro same
    by_cases nonnegative : 0≤x
    · exact nl (by rwa [abs_of_nonneg nonnegative] at same)
    · exact nr (by rw [abs_of_neg (lt_of_not_ge nonnegative)] at same;linarith)
  have neFour : |x|≠4 := by
    intro same
    by_cases nonnegative : 0≤x
    · exact n4 (by rwa [abs_of_nonneg nonnegative] at same)
    · exact nr4 (by rw [abs_of_neg (lt_of_not_ge nonnegative)] at same;linarith)
  have inverseBand : q< |x⁻¹| ∧ |x⁻¹|≤q*Real.exp h ↔ lower< |x| ∧ |x|≤4 := by
    rw [abs_inv]
    have cancel : Real.exp h*Real.exp (-h)=1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
    constructor
    · intro inside
      have below : |x|<4 := by nlinarith [(lt_inv_comm₀ (by norm_num : (0 : ℝ)<q) xp).mp inside.1]
      have above : lower≤ |x| := by
        have prod:=mul_le_mul_of_nonneg_right inside.2 xp.le
        rw [inv_mul_cancel₀ xp.ne'] at prod
        have shifted:=mul_le_mul_of_nonneg_right prod (Real.exp_pos (-h)).le
        have cancelProduct : q*Real.exp h*|x| *Real.exp (-h)=q*|x| := by
          calc
            _=q*|x| *(Real.exp h*Real.exp (-h)) := by ring
            _=_ := by rw [cancel,mul_one]
        rw [one_mul,cancelProduct] at shifted
        unfold lower
        nlinarith
      exact ⟨lt_of_le_of_ne above neLower.symm,below.le⟩
    · intro inside
      have below : |x|<4 := lt_of_le_of_ne inside.2 neFour
      refine ⟨(lt_inv_comm₀ (by norm_num : (0 : ℝ)<q) xp).mpr (by norm_num;exact below),?_⟩
      apply (mul_le_mul_iff_right₀ xp).mp
      rw [mul_inv_cancel₀ xp.ne']
      have above:=mul_lt_mul_of_pos_left inside.1 (Real.exp_pos h)
      have lowerIdentity : Real.exp h*lower=4 := by
        unfold lower
        calc
          _=4*(Real.exp h*Real.exp (-h)) := by ring
          _=4 := by rw [cancel,mul_one]
      rw [lowerIdentity] at above
      nlinarith
  simp only [abs_inv] at inverseBand
  simp only [burnolTateReciprocalRaw,sampleRaw,abs_inv]
  simp only [inverseBand]
  unfold bandRaw
  split_ifs
  · unfold reciprocalRaw
    simp only [div_eq_mul_inv]
    ring
  · exact mul_zero _
end OriginalWholeDebtRReciprocalCotestActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
