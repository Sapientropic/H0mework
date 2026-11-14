import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Green
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKSourceResolventReconstruction
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "C" => ConstantDual.seed
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "leading" => ForcingPrimitive.leadingCoefficient
local notation "h₀" => Real.log stageZeroSonineQ

-- Suggestion indexing of these fixed-root types unfolds the full inherited receipt closure.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalCanonicalNativeEulerGreen"

/-- The actual native Euler field enters the existing full resolvent Green consumer. -/
theorem native_R_green (c d:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    (c.value-star d.value)*inner ℂ (E (nativeSmooth c:Hq)) (sourceResolvent d value)+
      star (nativeGamma c-originCoefficient c)*inner ℂ Response.wholeU (sourceResolvent d value)-
      star (nativeBeta c)*inner ℂ Response.wholeV (sourceResolvent d value)=
      2*inner ℂ (E (nativeSmooth c:Hq)) value-2*star (nativeBeta c)*inner ℂ C value-
        star d.value*star (nativeBeta c)*inner ℂ C (sourceResolvent d value) := by
  let R:=sourceResolvent d value
  have inverse:=sourceResolvent_euler d value
  have right:GapEuler.euler (R:TemperedDistribution ℝ ℂ)=
      ((-(2:ℂ) • value-sourceRate d • R:BurnolL2):TemperedDistribution ℝ ℂ) := by
    change _=Lp.toTemperedDistributionCLM ℂ volume 2 _
    simp only [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
    exact eq_sub_of_add_eq inverse
  have actual:=DilationWard.cross_balance
    (E (nativeSmooth c:Hq)-nativeBeta c • C) (E (nativeEuler c:Hq)+(nativeBeta c/2) • C)
    R (-(2:ℂ) • value-sourceRate d • R) (native_corrected_euler c) right
  unfold nativeEuler rate sourceRate at actual
  simp only [Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,map_add,map_sub,map_smul,
    inner_add_left,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    starRingEnd_apply,star_div₀,star_ofNat,star_one,star_star] at actual
  change (c.value-star d.value)*inner ℂ (E (nativeSmooth c:Hq)) R+
    star (nativeGamma c-originCoefficient c)*inner ℂ (E (Response.u:Hq)) R-
    star (nativeBeta c)*inner ℂ (E (Response.v:Hq)) R=_
  simp only [star_sub]
  linear_combination actual

/-- Resonance retains both complete seed prices and never divides a source coefficient. -/
theorem native_resonant_green (c:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    2*inner ℂ value (E (nativeSmooth c:Hq))=
      (nativeGamma c-originCoefficient c)*inner ℂ (sourceResolvent (barC c) value) Response.wholeU-
      nativeBeta c*inner ℂ (sourceResolvent (barC c) value) Response.wholeV+
      2*nativeBeta c*inner ℂ value C+
      star c.value*nativeBeta c*inner ℂ (sourceResolvent (barC c) value) C := by
  have actual:=congrArg star (native_R_green c (barC c) value)
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,sub_self,zero_mul,zero_add,
    star_sub,star_mul,star_ofNat] at actual
  simp only [star_def,inner_conj_symm,OriginalPrimitiveRankBalance.conjugateCoordinate] at actual ⊢
  linear_combination -actual

def sameNUnit (c:BurnolCompletedMellinCoordinate) (N:ℕ):BurnolL2:=
  freeUnit (star c.value) (DualSource.source N C)

/-- Every finite input is the original complete source at that same N. -/
theorem native_same_N_unit_green (c:BurnolCompletedMellinCoordinate) (N:ℕ):
    2*inner ℂ (sameNUnit c N) (E (nativeSmooth c:Hq))=
      (nativeGamma c-originCoefficient c)*inner ℂ (sourceResolvent (barC c) (sameNUnit c N)) Response.wholeU-
      nativeBeta c*inner ℂ (sourceResolvent (barC c) (sameNUnit c N)) Response.wholeV+
      2*nativeBeta c*inner ℂ (sameNUnit c N) C+
      star c.value*nativeBeta c*inner ℂ (sourceResolvent (barC c) (sameNUnit c N)) C :=
  native_resonant_green c (sameNUnit c N)

private theorem same_N_tendsto (c:BurnolCompletedMellinCoordinate):
    Tendsto (sameNUnit c) atTop (𝓝 (freeUnit (star c.value) ConstantDual.value)) := by
  have actual:=original_reverse_free_limit c
  apply actual.congr'
  filter_upwards with N
  rw [OriginalKElementaryArithmeticAction.unit_resolvent_finite,
    OriginalKElementaryArithmeticAction.FreeParameter.Riesz.actual_free_unit]
  rfl

/-- Strong convergence consumes those same finite fields with the whole Unit intact. -/
theorem native_full_unit_green (c:BurnolCompletedMellinCoordinate):
    let value:=freeUnit (star c.value) ConstantDual.value
    2*inner ℂ value (E (nativeSmooth c:Hq))=
      (nativeGamma c-originCoefficient c)*inner ℂ (sourceResolvent (barC c) value) Response.wholeU-
      nativeBeta c*inner ℂ (sourceResolvent (barC c) value) Response.wholeV+
      2*nativeBeta c*inner ℂ value C+
      star c.value*nativeBeta c*inner ℂ (sourceResolvent (barC c) value) C := by
  let value:=freeUnit (star c.value) ConstantDual.value
  have regular:Continuous (sourceResolvent (barC c)) := by
    have functions:sourceResolvent (barC c)=(fun v:BurnolL2=>(burnolDirectRightResolventCLM c) v) := by
      funext v
      change burnolDirectRightResolvent (star (barC c).value/2) v=
        burnolDirectRightResolvent (c.value/2) v
      simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
    rw [functions]
    exact (burnolDirectRightResolventCLM c).continuous
  have acted:=(regular.tendsto value).comp (same_N_tendsto c)
  have lhs:=((same_N_tendsto c).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=E (nativeSmooth c:Hq)))).const_mul 2
  have first:=(acted.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=Response.wholeU))).const_mul (nativeGamma c-originCoefficient c)
  have second:=(acted.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=Response.wholeV))).const_mul (nativeBeta c)
  have third:=((same_N_tendsto c).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=C))).const_mul (2*nativeBeta c)
  have fourth:=(acted.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=C))).const_mul (star c.value*nativeBeta c)
  exact tendsto_nhds_unique lhs ((first.sub second |>.add third |>.add fourth).congr
    (fun N=>(native_same_N_unit_green c N).symm))

private theorem seed_mean_zero (value:M):inner ℂ C (E (value:Hq))=0 := by
  change inner ℂ C (burnolQuarterRestriction.adjoint (value:Hq))=0
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (burnolQuarterRestriction (E (intervalConstant q))) (value:Hq)=0
  rw [burnolQuarterRestriction_zeroExtension]
  have source:=Constructor.mean_zero value
  unfold burnolQuarterMeanCoefficient at source
  exact (div_eq_zero_iff.mp source).resolve_right (by
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (intervalConstant_ne_zero (by norm_num : (0:ℝ)<q)))))

/-- The original joint cotest consumes the native law and removes its complete bulk pairing. -/
theorem native_cotest_green (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    2*inner ℂ (jointCotest c h) (nativeSmooth c)=
      (nativeGamma c-originCoefficient c)*inner ℂ (sourceResolvent (barC c) (E (jointCotest c h:Hq))) Response.wholeU-
      nativeBeta c*inner ℂ (sourceResolvent (barC c) (E (jointCotest c h:Hq))) Response.wholeV+
      star c.value*nativeBeta c*inner ℂ (sourceResolvent (barC c) (E (jointCotest c h:Hq))) C := by
  have actual:=native_resonant_green c (E (jointCotest c h:Hq))
  have mean:inner ℂ (E (jointCotest c h:Hq)) C=0 := by
    rw [←inner_conj_symm]
    simp only [seed_mean_zero,map_zero]
  rw [mean,mul_zero,add_zero] at actual
  have physical:inner ℂ (E (jointCotest c h:Hq)) (E (nativeSmooth c:Hq))=
      inner ℂ (jointCotest c h) (nativeSmooth c) := by
    change inner ℂ (E (jointCotest c h:Hq)) (burnolQuarterRestriction.adjoint (nativeSmooth c:Hq))=_
    rw [ContinuousLinearMap.adjoint_inner_right,burnolQuarterRestriction_zeroExtension]
    rfl
  rw [physical] at actual
  exact actual

def eulerFixedNet (c:BurnolCompletedMellinCoordinate):ℂ:=
  (pairedMellinTranslationCharacter c.value h₀-pairedMellinTranslationCharacter (star c.value) h₀)*kernelSelfSource c+
    (1/2:ℂ)*(-inner ℂ (movedTest c h₀) (freeUnit (star c.value) ConstantDual.value)+
      leading c*inner ℂ (twoClockCorrection c h₀) (centeredLogColumn c 0)-
      (1/2:ℂ)*((nativeGamma c-originCoefficient c)*inner ℂ (sourceResolvent (barC c) (E (jointCotest c h₀:Hq))) Response.wholeU-
        nativeBeta c*inner ℂ (sourceResolvent (barC c) (E (jointCotest c h₀:Hq))) Response.wholeV+
        star c.value*nativeBeta c*inner ℂ (sourceResolvent (barC c) (E (jointCotest c h₀:Hq))) C))

/-- A new source Green equation replaces the native bulk by its generated endpoint prices. -/
theorem actual_euler_fixed_net (c:BurnolCompletedMellinCoordinate):
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed.nativeFixedNet c=
      eulerFixedNet c := by
  have actual:=native_cotest_green c h₀
  unfold OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed.nativeFixedNet eulerFixedNet
  linear_combination -(1/4:ℂ)*actual

theorem actual_original_fixed_euler_consumer (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):BurnolPaBoundaryCancellationAt c zero↔eulerFixedNet c=0 := by
  rw [OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed.actual_original_fixed_native_consumer c zero,
    actual_euler_fixed_net]

/-- The independent original consumer retains its exact root, whole ledger and generated next. -/
theorem actual_original_fixed_root_consumer (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (settled:eulerFixedNet c=0):
    type_of% (burnolPaBoundaryCancellation_keeps_fixedRoot_write_next c zero
      ((actual_original_fixed_euler_consumer c zero).mpr settled)) :=
  burnolPaBoundaryCancellation_keeps_fixedRoot_write_next c zero
    ((actual_original_fixed_euler_consumer c zero).mpr settled)

end OriginalCanonicalNativeEulerGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
