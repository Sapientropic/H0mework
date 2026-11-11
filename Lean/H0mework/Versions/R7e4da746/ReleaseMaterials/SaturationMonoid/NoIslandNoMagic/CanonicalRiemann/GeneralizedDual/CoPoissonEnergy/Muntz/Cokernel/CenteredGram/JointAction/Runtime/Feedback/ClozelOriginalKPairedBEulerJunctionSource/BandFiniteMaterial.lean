import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoefficientBSelfMaterialConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteBornProjection

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.BandFiniteMaterial
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson.Ward
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open scoped InnerProductSpace Topology
namespace B
export OriginalKBFiniteCalculation
 (Value Var E sourceEnvironment constantCode uCode vCode wholeZeroMean coefficientSourceCode
  coefficientAActionCode coefficientBetaActionCode endpointRead coefficient_A_code_eval coefficient_beta_code_eval)
end B
namespace C
export OriginalKCoefficientBSelfCalculation (sourceKernelCode cotestAction cotestCode coefficientSCode)
end C
namespace Math
export BandFiniteSourcePrice
 (sourceColumn source_column_continuous forcingDensity boundarySourceRead finiteSourcePrice original_fixed_residual_finite_price)
end Math
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Fq" => burnolRadiusTruncatedFourierRaw q
local notation "T" => burnolTruncatedFourier
local notation "Eq" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction

private theorem mean_add (a b:Hq) :
    burnolQuarterMeanCoefficient (a+b)=burnolQuarterMeanCoefficient a+burnolQuarterMeanCoefficient b := by
  simp only [burnolQuarterMeanCoefficient,inner_add_right,add_div]
private theorem mean_smul (z:ℂ) (a:Hq) :
    burnolQuarterMeanCoefficient (z • a)=z*burnolQuarterMeanCoefficient a := by
  simp only [burnolQuarterMeanCoefficient,inner_smul_right]
  ring
private theorem mean_constant (z:ℂ) :
    burnolQuarterMeanCoefficient (z • intervalConstant q)=z := by
  have one:burnolQuarterMeanCoefficient (intervalConstant q)=1 := by
    rw [Constructor.mean_integral,integral_congr_ae (intervalConstant_coeFn q),integral_const,
      burnolQuarterInterval_measureReal_univ,Complex.real_smul]
    norm_num
  rw [mean_smul,one,mul_one]

/-- Scalar reads use the original constant carrier and its actual normalization. -/
def unitRead : BurnolL2 →+ ℂ where
  toFun value:=burnolQuarterMeanCoefficient (Rq value)
  map_zero':=by simp [burnolQuarterMeanCoefficient]
  map_add' left right:=by rw [map_add,mean_add]

def zeroSource : BurnolL2 →L[ℂ] M := Constructor.zeroMean.comp Rq

def smoothRaw : BurnolL2 →+ (ℝ → ℂ) where
  toFun value x:=Fq (zeroSource value:Hq) x-
    burnolQuarterMeanCoefficient (T (zeroSource value:Hq))
  map_zero':=by
    funext x
    simp only [map_zero,Submodule.coe_zero,Pi.zero_apply]
    have fourier_zero : Fq (0:Hq) x=0 := by
      simpa only [zero_smul,Pi.zero_apply,zero_mul] using
        congrFun (burnolRadiusTruncatedFourierRaw_smul (0:ℂ) (0:Hq)) x
    rw [fourier_zero]
    simp only [burnolQuarterMeanCoefficient,inner_zero_right,zero_div,sub_zero]
  map_add' left right:=by
    funext x
    simp only [map_add,Submodule.coe_add,Pi.add_apply]
    rw [burnolRadiusTruncatedFourierRaw_add,mean_add]
    dsimp only [Pi.add_apply]
    ring

private theorem smooth_continuous (value:BurnolL2) : Continuous (smoothRaw value) :=
  (burnolRadiusTruncatedFourierRaw_continuous _).sub continuous_const

private theorem source_unit (value:M) : unitRead (Eq (value:Hq)+ConstantDual.seed)=1 := by
  change burnolQuarterMeanCoefficient (Rq (Eq (value:Hq)+Eq (intervalConstant q)))=1
  rw [map_add,burnolQuarterRestriction_zeroExtension,burnolQuarterRestriction_zeroExtension,mean_add,
    Constructor.mean_zero]
  simpa only [one_smul,zero_add] using mean_constant 1

private theorem source_zero (value:M) : zeroSource (Eq (value:Hq)+ConstantDual.seed)=value := by
  change Constructor.zeroMean (Rq (Eq (value:Hq)+Eq (intervalConstant q)))=value
  rw [map_add,burnolQuarterRestriction_zeroExtension,burnolQuarterRestriction_zeroExtension,
    map_add,Constructor.zeroMean_constant,add_zero]
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr value.property

private theorem source_smooth (value:M) (x:ℝ) :
    smoothRaw (Eq (value:Hq)+ConstantDual.seed) x=burnolMeanZeroFourierRaw value x := by
  change Fq (zeroSource (Eq (value:Hq)+ConstantDual.seed):Hq) x-
    burnolQuarterMeanCoefficient (T (zeroSource (Eq (value:Hq)+ConstantDual.seed):Hq))=_
  rw [source_zero]
  rfl

/-- Both fixed source columns are generated from the original u/v and their separate means. -/
def psiProfile (i:Fin 2) : BurnolL2 →+ (ℝ → ℂ) where
  toFun value x:=if i=0 then smoothRaw value x-unitRead value else
    -smoothRaw value x+unitRead value*(Translator.ForcingMeanZero.edgeMean-Edge.raw q x)
  map_zero':=by funext x; split_ifs <;> simp
  map_add' left right:=by
    funext x
    split_ifs <;> simp only [map_add,Pi.add_apply] <;> ring

def sourceProfile (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : BurnolL2 →+ (ℝ → ℂ) where
  toFun value x:=if i=0 then
    unitRead value*((1/2:ℂ)*(x:ℂ)^(-star c.value)-GapEuler.gapMean q c)-smoothRaw value x else
    unitRead value*burnolRieszFourierForcingRaw c x+smoothRaw value x
  map_zero':=by funext x; split_ifs <;> simp
  map_add' left right:=by
    funext x
    split_ifs <;> simp only [map_add,Pi.add_apply] <;> ring

private theorem psi_continuous (i:Fin 2) (value:BurnolL2) : Continuous (psiProfile i value) := by
  fin_cases i
  · exact (smooth_continuous value).sub continuous_const
  · exact (smooth_continuous value).neg.add
      (continuous_const.mul (continuous_const.sub (Edge.raw_continuous q)))

private theorem profile_continuousAt (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (value:BurnolL2) (x:ℝ) (positive:0<x) : ContinuousAt (sourceProfile c i value) x := by
  fin_cases i
  · exact (continuousAt_const.mul ((continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const x (-star c.value) (Or.inr positive.ne'))).sub
      continuousAt_const)).sub (smooth_continuous value).continuousAt
  · exact (continuousAt_const.mul (burnolRieszFourierForcingRaw_continuousAt c positive.ne')).add
      (smooth_continuous value).continuousAt

private theorem psi_read (i:Fin 2) (x:ℝ) :
    psiProfile i (Eq (![Response.u,Response.v] i:Hq)+ConstantDual.seed) x=Math.sourceColumn i x := by
  fin_cases i
  · change smoothRaw (Eq (Response.u:Hq)+ConstantDual.seed) x -
      unitRead (Eq (Response.u:Hq)+ConstantDual.seed) = Math.sourceColumn 0 x
    simp only [Math.sourceColumn,PsiDrive.psiMean,Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [source_smooth,source_unit]
    unfold burnolMeanZeroFourierRaw
    ring
  · change -smoothRaw (Eq (Response.v:Hq)+ConstantDual.seed) x +
      unitRead (Eq (Response.v:Hq)+ConstantDual.seed) *
        (Translator.ForcingMeanZero.edgeMean - Edge.raw q x) = Math.sourceColumn 1 x
    simp only [Math.sourceColumn,PsiDrive.psiMean,Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [source_smooth,source_unit]
    unfold burnolMeanZeroFourierRaw
    ring

private theorem profile_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) :
    sourceProfile c i
      (Eq (![burnolRieszSingleFourierSource c,
        burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c)] i:Hq)+ConstantDual.seed) x=
      ![positionSource c x,burnolRieszSingleFourierSourceRaw c x] i := by
  fin_cases i
  · change unitRead (Eq (burnolRieszSingleFourierSource c:Hq)+ConstantDual.seed) *
      ((1/2:ℂ)*(x:ℂ)^(-star c.value)-GapEuler.gapMean q c) -
      smoothRaw (Eq (burnolRieszSingleFourierSource c:Hq)+ConstantDual.seed) x =
      positionSource c x
    rw [source_smooth,source_unit,one_mul]
    rfl
  · change unitRead (Eq (burnolMeanZeroTruncatedFourier
      (burnolRieszSingleFourierSource c):Hq)+ConstantDual.seed) *
      burnolRieszFourierForcingRaw c x +
      smoothRaw (Eq (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource c):Hq)+ConstantDual.seed) x =
      burnolRieszSingleFourierSourceRaw c x
    rw [source_smooth,source_unit,one_mul]
    rfl

private theorem band_positive (h:ℝ) {x:ℝ} (inside:x∈uIcc (q*Real.exp (-h)) q) : 0<x :=
  (lt_min (mul_pos (by norm_num) (Real.exp_pos _)) (by norm_num)).trans_le inside.1

/-- Integration acts on continuous canonical source profiles, never arbitrary Lp representatives. -/
def bandAction (h:ℝ) (left right:BurnolL2 →+ (ℝ → ℂ))
    (lc:∀ value x,0<x→ContinuousAt (left value) x)
    (rc:∀ value x,0<x→ContinuousAt (right value) x) :
    BurnolL2 →+ BurnolL2 →+ BurnolL2 where
  toFun a:=
    { toFun b:=(∫x:ℝ in (q*Real.exp (-h))..q,
        star (left a x)*right b (Real.exp h*x)) • ConstantDual.seed
      map_zero':=by simp
      map_add' b d:=by
        have integrable (v:BurnolL2) : IntervalIntegrable
            (fun x=>star (left a x)*right v (Real.exp h*x)) volume (q*Real.exp (-h)) q := by
          apply ContinuousOn.intervalIntegrable
          intro x hx
          exact ((lc a x (band_positive h hx)).star.mul
            ((rc v _ (mul_pos (Real.exp_pos _) (band_positive h hx))).comp
              (by fun_prop))).continuousWithinAt
        simp only [map_add,Pi.add_apply,mul_add]
        rw [intervalIntegral.integral_add (integrable b) (integrable d),add_smul] }
  map_zero':=by
    apply AddMonoidHom.ext
    intro b
    change (∫x:ℝ in (q*Real.exp (-h))..q,star (left 0 x)*right b (Real.exp h*x)) • ConstantDual.seed=0
    simp
  map_add' a d:=by
    apply AddMonoidHom.ext
    intro b
    change (∫x:ℝ in (q*Real.exp (-h))..q,star (left (a+d) x)*right b (Real.exp h*x)) • ConstantDual.seed=
      (∫x:ℝ in (q*Real.exp (-h))..q,star (left a x)*right b (Real.exp h*x)) • ConstantDual.seed+
      (∫x:ℝ in (q*Real.exp (-h))..q,star (left d x)*right b (Real.exp h*x)) • ConstantDual.seed
    have integrable (v:BurnolL2) : IntervalIntegrable
        (fun x=>star (left v x)*right b (Real.exp h*x)) volume (q*Real.exp (-h)) q := by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      exact ((lc v x (band_positive h hx)).star.mul
        ((rc b _ (mul_pos (Real.exp_pos _) (band_positive h hx))).comp
          (by fun_prop))).continuousWithinAt
    simp only [map_add,Pi.add_apply,star_add,add_mul]
    rw [intervalIntegral.integral_add (integrable a) (integrable d),add_smul]

private def linear (action:BurnolL2 →+ BurnolL2) (input:B.E) : B.E := .linear action input
private def scale (z:ℂ) (input:B.E) : B.E :=
  linear (z • ContinuousLinearMap.id ℂ BurnolL2).toLinearMap.toAddMonoidHom input
private def withUnit (input:B.E) : B.E := .add input B.constantCode
private def scalarStar (input:B.E) : B.E := scale 2 (.bilinear C.cotestAction input B.constantCode)
private def conjugateProduct (left right:B.E) : B.E := scale 2 (.bilinear C.cotestAction left right)

def psiCode (i:Fin 2) : B.E := withUnit (![B.uCode,B.vCode] i)
def sourceCode (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : B.E :=
  withUnit (![B.coefficientSourceCode c,C.coefficientSCode c] i)

def forwardBandCode (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i j:Fin 2) : B.E :=
  .bilinear (bandAction h (psiProfile i) (sourceProfile c j)
    (fun v _ _=>(psi_continuous i v).continuousAt) (profile_continuousAt c j))
    (psiCode i) (sourceCode c j)
def reverseBandCode (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i j:Fin 2) : B.E :=
  .bilinear (bandAction h (sourceProfile c i) (psiProfile j)
    (profile_continuousAt c i) (fun v _ _=>(psi_continuous j v).continuousAt))
    (sourceCode c i) (psiCode j)

def forcingIntegralCode (c:BurnolCompletedMellinCoordinate) (h:ℝ) : B.E :=
  .add (.add
    (conjugateProduct (B.coefficientAActionCode c B.constantCode)
      (.add (forwardBandCode c h 0 0) (forwardBandCode c h 1 1)))
    (conjugateProduct (B.coefficientBetaActionCode c B.constantCode)
      (.add (forwardBandCode c h 1 0) (forwardBandCode c h 0 1))))
    (.add (B.coefficientAActionCode c
      (.add (reverseBandCode c h 0 0) (reverseBandCode c h 1 1)))
      (B.coefficientBetaActionCode c
      (.add (reverseBandCode c h 0 1) (reverseBandCode c h 1 0))))

def profilePointAction (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : BurnolL2 →+ BurnolL2 :=
  (ContinuousLinearMap.toSpanSingleton ℂ ConstantDual.seed).toLinearMap.toAddMonoidHom.comp
    ((Pi.evalAddMonoidHom (fun _ : ℝ=>ℂ) x).comp (sourceProfile c i))

def boundaryCode (c:BurnolCompletedMellinCoordinate) (h:ℝ) : B.E :=
  .add (scale (q:ℂ) (.add
    (conjugateProduct (B.coefficientAActionCode c B.constantCode)
      (linear (profilePointAction c 0 (Real.exp h*q)) (sourceCode c 0)))
    (conjugateProduct (B.coefficientBetaActionCode c B.constantCode)
      (linear (profilePointAction c 1 (Real.exp h*q)) (sourceCode c 1)))))
    (scale (-(q*Real.exp (-h):ℂ)) (.add
      (conjugateProduct (linear (profilePointAction c 0 (q*Real.exp (-h))) (sourceCode c 0))
        (B.coefficientAActionCode c B.constantCode))
      (conjugateProduct (linear (profilePointAction c 1 (q*Real.exp (-h))) (sourceCode c 1))
        (B.coefficientBetaActionCode c B.constantCode))))

def finitePairCode (c:BurnolCompletedMellinCoordinate) (h:ℝ) : B.E :=
  scale ((2:ℂ)*(Real.exp (h/2):ℂ)/(c.value+star c.value-1))
    (.add (forcingIntegralCode c h) (boundaryCode c h))

/-- Both the full original K Gram and all four finite source/boundary slots are computed. -/
def evaluatorCode (c:BurnolCompletedMellinCoordinate) (h:ℝ) : B.E :=
  .add (scale (pairedMellinTranslationCharacter c.value h-pairedMellinTranslationCharacter (star c.value) h)
    (.bilinear C.cotestAction (C.sourceKernelCode c) (C.sourceKernelCode c)))
    (scale (1/2:ℂ) (scalarStar (finitePairCode c h)))





private theorem psi_code_eval (i:Fin 2) :
    (psiCode i).eval B.sourceEnvironment =
      Eq (![Response.u,Response.v] i:Hq)+ConstantDual.seed := by
  fin_cases i
  · change B.uCode.eval B.sourceEnvironment + B.constantCode.eval B.sourceEnvironment = _
    have z := OriginalKBFiniteCalculation.original_B_source_eval
    rw [z]
    rfl
  · change B.vCode.eval B.sourceEnvironment + B.constantCode.eval B.sourceEnvironment = _
    have z := OriginalKBFiniteCalculation.original_S_source_eval
    rw [z]
    rfl

private theorem source_code_eval (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (sourceCode c i).eval B.sourceEnvironment =
      Eq (![burnolRieszSingleFourierSource c,
        burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c)] i:Hq)+ConstantDual.seed := by
  fin_cases i
  · change (B.coefficientSourceCode c).eval B.sourceEnvironment + B.constantCode.eval B.sourceEnvironment = _
    rw [OriginalKCoefficientBSelfCalculation.Semantics.coefficient_b_code_eval]
    rfl
  · change (C.coefficientSCode c).eval B.sourceEnvironment + B.constantCode.eval B.sourceEnvironment = _
    rw [OriginalKCoefficientBSelfCalculation.Semantics.coefficient_sb_code_eval]
    rfl


private theorem endpoint_read (value : M) :
    B.endpointRead (Eq (value:Hq)) =
      (4 : ℂ) * inner ℂ (Constructor.endpointColumn (-q)) value := by
  change (4 : ℂ) * inner ℂ
    (burnolQuarterRestriction.adjoint (Constructor.endpointColumn (-q) : Hq))
      (burnolQuarterZeroExtension (value : Hq)) = _
  rw [ContinuousLinearMap.adjoint_inner_left, burnolQuarterRestriction_zeroExtension]
  change (4 : ℂ) * inner ℂ (Constructor.endpointColumn (-q)) value = _
  rfl

private theorem coefficient_source_eval (c:BurnolCompletedMellinCoordinate) :
    (B.coefficientSourceCode c).eval B.sourceEnvironment =
      burnolQuarterZeroExtension (burnolRieszSingleFourierSource c : Hq) := by
  exact OriginalKCoefficientBSelfCalculation.Semantics.coefficient_b_code_eval c

private theorem coefficient_A_source_eval (c:BurnolCompletedMellinCoordinate) (input:B.E) :
    (B.coefficientAActionCode c input).eval B.sourceEnvironment =
      OriginalRieszSource.Kernel.A c • input.eval B.sourceEnvironment := by
  rw [B.coefficient_A_code_eval, coefficient_source_eval]
  rw [endpoint_read (burnolRieszSingleFourierSource c)]
  rw [OriginalCommonInverseForcing.InverseEuler.endpointColumn_inner]
  simp [OriginalRieszSource.Kernel.A]
  unfold burnolRieszReturnRaw
  rfl

private theorem coefficient_beta_source_eval (c:BurnolCompletedMellinCoordinate) (input:B.E) :
    (B.coefficientBetaActionCode c input).eval B.sourceEnvironment =
      OriginalRieszSource.Kernel.beta c • input.eval B.sourceEnvironment := by
  rw [B.coefficient_beta_code_eval, coefficient_source_eval]
  have whole : B.wholeZeroMean (fourierL2
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource c : Hq))) =
      burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c) : Hq) := rfl
  rw [whole, endpoint_read]
  rw [OriginalCommonInverseForcing.InverseEuler.endpointColumn_inner]
  simp [OriginalRieszSource.Kernel.beta, burnolRieszSingleFourierSourceRaw]

private theorem forward_band_eval (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i j:Fin 2) :
    (forwardBandCode c h i j).eval B.sourceEnvironment =
      bandAction h (psiProfile i) (sourceProfile c j)
        (fun v _ _=>(psi_continuous i v).continuousAt)
        (profile_continuousAt c j)
        ((psiCode i).eval B.sourceEnvironment)
        ((sourceCode c j).eval B.sourceEnvironment) := by
  rfl

private theorem reverse_band_eval (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i j:Fin 2) :
    (reverseBandCode c h i j).eval B.sourceEnvironment =
      bandAction h (sourceProfile c i) (psiProfile j)
        (profile_continuousAt c i)
        (fun v _ _=>(psi_continuous j v).continuousAt)
        ((sourceCode c i).eval B.sourceEnvironment)
        ((psiCode j).eval B.sourceEnvironment) := by
  rfl


private theorem forward_band_read (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i j:Fin 2) :
    (forwardBandCode c h i j).eval B.sourceEnvironment =
      (∫x:ℝ in (q*Real.exp (-h))..q,
        star (Math.sourceColumn i x) * (![positionSource c (Real.exp h*x),
          burnolRieszSingleFourierSourceRaw c (Real.exp h*x)] j)) • ConstantDual.seed := by
  rw [forward_band_eval, psi_code_eval, source_code_eval]
  unfold bandAction
  change (∫x:ℝ in (q*Real.exp (-h))..q,
    star (psiProfile i (Eq (![Response.u,Response.v] i:Hq)+ConstantDual.seed) x) *
      sourceProfile c j (Eq (![burnolRieszSingleFourierSource c,
        burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c)] j:Hq)+ConstantDual.seed)
        (Real.exp h*x)) • ConstantDual.seed = _
  simp only [psi_read, profile_read]


private theorem reverse_band_read (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i j:Fin 2) :
    (reverseBandCode c h i j).eval B.sourceEnvironment =
      (∫x:ℝ in (q*Real.exp (-h))..q,
        star (![positionSource c x,burnolRieszSingleFourierSourceRaw c x] i) *
          Math.sourceColumn j (Real.exp h*x)) • ConstantDual.seed := by
  rw [reverse_band_eval, source_code_eval, psi_code_eval]
  unfold bandAction
  change (∫x:ℝ in (q*Real.exp (-h))..q,
    star (sourceProfile c i (Eq (![burnolRieszSingleFourierSource c,
      burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c)] i:Hq)+ConstantDual.seed) x) *
      psiProfile j (Eq (![Response.u,Response.v] j:Hq)+ConstantDual.seed) (Real.exp h*x)) • ConstantDual.seed = _
  simp only [profile_read, psi_read]




private theorem seed_inner : inner ℂ ConstantDual.seed ConstantDual.seed = (1/2:ℂ) := by
  have gap : burnolQuarterRestriction ConstantDual.seed =
      (1:ℂ) • intervalConstant q := by
    change burnolQuarterRestriction
      (burnolQuarterZeroExtension (intervalConstant q)) = _
    rw [burnolQuarterRestriction_zeroExtension, one_smul]
  have read := OriginalKForcingGapAction.inward_constant_contact
    ConstantDual.seed 1 gap 0 le_rfl
  rw [burnolMultiplicativeDilation_zero] at read
  convert read using 1
  norm_num

private theorem conjugate_product_eval (left right:B.E) :
    (conjugateProduct left right).eval B.sourceEnvironment =
      ((2:ℂ) * (inner ℂ (left.eval B.sourceEnvironment) (right.eval B.sourceEnvironment))) •
        ConstantDual.seed := by
  change (2:ℂ) •
      (inner ℂ (left.eval B.sourceEnvironment) (right.eval B.sourceEnvironment) •
        B.constantCode.eval B.sourceEnvironment) = _
  change (2:ℂ) •
      (inner ℂ (left.eval B.sourceEnvironment) (right.eval B.sourceEnvironment) •
        ConstantDual.seed) = _
  rw [smul_smul]

private theorem profile_point_eval (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ)
    (input:B.E) :
    (profilePointAction c i x (input.eval B.sourceEnvironment)) =
      (sourceProfile c i (input.eval B.sourceEnvironment) x) • ConstantDual.seed := by
  rfl

private theorem scale_eval (z:ℂ) (input:B.E) :
    (scale z input).eval B.sourceEnvironment = z • input.eval B.sourceEnvironment := by
  rfl

private theorem linear_eval (action:BurnolL2 →+ BurnolL2) (input:B.E) :
    (linear action input).eval B.sourceEnvironment =
      action (input.eval B.sourceEnvironment) := by
  rfl



private theorem band_term_integrable (h:ℝ) (left right:ℝ→ℂ)
    (left_cont:∀ {x:ℝ}, 0<x → ContinuousAt left x)
    (right_cont:∀ {x:ℝ}, 0<x → ContinuousAt right x) :
    IntervalIntegrable (fun x => star (left x) * right (Real.exp h*x))
      volume (q*Real.exp (-h)) q := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have px : 0<x := band_positive h hx
  have py : 0<Real.exp h*x := mul_pos (Real.exp_pos _) px
  exact ((left_cont px).star.mul
    ((right_cont py).comp (by fun_prop))).continuousWithinAt

private theorem forcing_integral_eval (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    (forcingIntegralCode c h).eval B.sourceEnvironment =
      (∫x:ℝ in (q*Real.exp (-h))..q, Math.forcingDensity c h x) • ConstantDual.seed := by
  unfold forcingIntegralCode
  change
    ((conjugateProduct (B.coefficientAActionCode c B.constantCode)
      (.add (forwardBandCode c h 0 0) (forwardBandCode c h 1 1))).eval B.sourceEnvironment +
      (conjugateProduct (B.coefficientBetaActionCode c B.constantCode)
      (.add (forwardBandCode c h 1 0) (forwardBandCode c h 0 1))).eval B.sourceEnvironment) +
    ((B.coefficientAActionCode c
      (.add (reverseBandCode c h 0 0) (reverseBandCode c h 1 1))).eval B.sourceEnvironment +
      (B.coefficientBetaActionCode c
      (.add (reverseBandCode c h 0 1) (reverseBandCode c h 1 0))).eval B.sourceEnvironment) = _
  rw [conjugate_product_eval, conjugate_product_eval,
    coefficient_A_source_eval, coefficient_beta_source_eval,
    coefficient_A_source_eval, coefficient_beta_source_eval]
  change
    (2 * inner ℂ (OriginalRieszSource.Kernel.A c • B.constantCode.eval B.sourceEnvironment)
      ((forwardBandCode c h 0 0).eval B.sourceEnvironment +
        (forwardBandCode c h 1 1).eval B.sourceEnvironment)) • ConstantDual.seed +
    (2 * inner ℂ (OriginalRieszSource.Kernel.beta c • B.constantCode.eval B.sourceEnvironment)
      ((forwardBandCode c h 1 0).eval B.sourceEnvironment +
        (forwardBandCode c h 0 1).eval B.sourceEnvironment)) • ConstantDual.seed +
    (OriginalRieszSource.Kernel.A c •
      ((reverseBandCode c h 0 0).eval B.sourceEnvironment +
        (reverseBandCode c h 1 1).eval B.sourceEnvironment) +
      OriginalRieszSource.Kernel.beta c •
      ((reverseBandCode c h 0 1).eval B.sourceEnvironment +
        (reverseBandCode c h 1 0).eval B.sourceEnvironment)) = _
  rw [forward_band_read, forward_band_read, forward_band_read, forward_band_read,
    reverse_band_read, reverse_band_read, reverse_band_read, reverse_band_read]
  rw [show B.constantCode.eval B.sourceEnvironment = ConstantDual.seed by rfl]
  simp only [inner_add_right, inner_smul_left, inner_smul_right]
  rw [seed_inner]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [← add_smul]
  ring_nf
  have h00 := band_term_integrable h (Math.sourceColumn 0)
    (positionSource c) (fun {_} _ => (Math.source_column_continuous 0).continuousAt)
    (fun {_} hx => positionSource_continuousAt c hx)
  have h11 := band_term_integrable h (Math.sourceColumn 1)
    (burnolRieszSingleFourierSourceRaw c) (fun {_} _ => (Math.source_column_continuous 1).continuousAt)
    (fun {_} hx => burnolRieszSingleFourierSourceRaw_continuousAt c hx.ne')
  have h10 := band_term_integrable h (Math.sourceColumn 1)
    (positionSource c) (fun {_} _ => (Math.source_column_continuous 1).continuousAt)
    (fun {_} hx => positionSource_continuousAt c hx)
  have h01 := band_term_integrable h (Math.sourceColumn 0)
    (burnolRieszSingleFourierSourceRaw c) (fun {_} _ => (Math.source_column_continuous 0).continuousAt)
    (fun {_} hx => burnolRieszSingleFourierSourceRaw_continuousAt c hx.ne')
  have k00 := band_term_integrable h (positionSource c) (Math.sourceColumn 0)
    (fun {_} hx => positionSource_continuousAt c hx)
    (fun {_} _ => Math.source_column_continuous 0 |>.continuousAt)
  have k11 := band_term_integrable h (burnolRieszSingleFourierSourceRaw c) (Math.sourceColumn 1)
    (fun {_} hx => burnolRieszSingleFourierSourceRaw_continuousAt c hx.ne')
    (fun {_} _ => Math.source_column_continuous 1 |>.continuousAt)
  have k01 := band_term_integrable h (positionSource c) (Math.sourceColumn 1)
    (fun {_} hx => positionSource_continuousAt c hx)
    (fun {_} _ => Math.source_column_continuous 1 |>.continuousAt)
  have k10 := band_term_integrable h (burnolRieszSingleFourierSourceRaw c) (Math.sourceColumn 0)
    (fun {_} hx => burnolRieszSingleFourierSourceRaw_continuousAt c hx.ne')
    (fun {_} _ => Math.source_column_continuous 0 |>.continuousAt)
  have h00n : IntervalIntegrable (fun x => star (Math.sourceColumn 0 x) *
      positionSource c (Real.exp h*x)) volume (Real.exp (-h)*q) q := by
    simpa [mul_comm] using h00
  have h11n : IntervalIntegrable (fun x => star (Math.sourceColumn 1 x) *
      burnolRieszSingleFourierSourceRaw c (Real.exp h*x)) volume (Real.exp (-h)*q) q := by
    simpa [mul_comm] using h11
  have h10n : IntervalIntegrable (fun x => star (Math.sourceColumn 1 x) *
      positionSource c (Real.exp h*x)) volume (Real.exp (-h)*q) q := by
    simpa [mul_comm] using h10
  have h01n : IntervalIntegrable (fun x => star (Math.sourceColumn 0 x) *
      burnolRieszSingleFourierSourceRaw c (Real.exp h*x)) volume (Real.exp (-h)*q) q := by
    simpa [mul_comm] using h01
  have k00n : IntervalIntegrable (fun x => star (positionSource c x) *
      Math.sourceColumn 0 (Real.exp h*x)) volume (Real.exp (-h)*q) q := by
    simpa [mul_comm] using k00
  have k11n : IntervalIntegrable (fun x => star (burnolRieszSingleFourierSourceRaw c x) *
      Math.sourceColumn 1 (Real.exp h*x)) volume (Real.exp (-h)*q) q := by
    simpa [mul_comm] using k11
  have k01n : IntervalIntegrable (fun x => star (positionSource c x) *
      Math.sourceColumn 1 (Real.exp h*x)) volume (Real.exp (-h)*q) q := by
    simpa [mul_comm] using k01
  have k10n : IntervalIntegrable (fun x => star (burnolRieszSingleFourierSourceRaw c x) *
      Math.sourceColumn 0 (Real.exp h*x)) volume (Real.exp (-h)*q) q := by
    simpa [mul_comm] using k10
  have h00A := h00n.mul_const (star (Kernel.A c))
  have h11A := h11n.const_mul (star (Kernel.A c))
  have h10B := h10n.mul_const (star (Kernel.beta c))
  have h01B := h01n.const_mul (star (Kernel.beta c))
  have k00A := k00n.const_mul (Kernel.A c)
  have k11A := k11n.const_mul (Kernel.A c)
  have k01B := k01n.const_mul (Kernel.beta c)
  have k10B := k10n.const_mul (Kernel.beta c)
  have i00 :
      (∫ x : ℝ in Real.exp (-h)*q..q,
        star (Math.sourceColumn 0 x) * positionSource c (Real.exp h*x)) * star (Kernel.A c) =
      ∫ x : ℝ in Real.exp (-h)*q..q,
        (star (Math.sourceColumn 0 x) * positionSource c (Real.exp h*x)) * star (Kernel.A c) := by
    rw [intervalIntegral.integral_mul_const]
  have i11 :
      star (Kernel.A c) * (∫ x : ℝ in Real.exp (-h)*q..q,
        star (Math.sourceColumn 1 x) * burnolRieszSingleFourierSourceRaw c (Real.exp h*x)) =
      ∫ x : ℝ in Real.exp (-h)*q..q,
        star (Kernel.A c) * (star (Math.sourceColumn 1 x) * burnolRieszSingleFourierSourceRaw c (Real.exp h*x)) := by
    rw [intervalIntegral.integral_const_mul]
  have i10 :
      (∫ x : ℝ in Real.exp (-h)*q..q,
        star (Math.sourceColumn 1 x) * positionSource c (Real.exp h*x)) * star (Kernel.beta c) =
      ∫ x : ℝ in Real.exp (-h)*q..q,
        (star (Math.sourceColumn 1 x) * positionSource c (Real.exp h*x)) * star (Kernel.beta c) := by
    rw [intervalIntegral.integral_mul_const]
  have i01 :
      star (Kernel.beta c) * (∫ x : ℝ in Real.exp (-h)*q..q,
        star (Math.sourceColumn 0 x) * burnolRieszSingleFourierSourceRaw c (Real.exp h*x)) =
      ∫ x : ℝ in Real.exp (-h)*q..q,
        star (Kernel.beta c) * (star (Math.sourceColumn 0 x) * burnolRieszSingleFourierSourceRaw c (Real.exp h*x)) := by
    rw [intervalIntegral.integral_const_mul]
  have j00 :
      Kernel.A c * (∫ x : ℝ in Real.exp (-h)*q..q,
        star (positionSource c x) * Math.sourceColumn 0 (Real.exp h*x)) =
      ∫ x : ℝ in Real.exp (-h)*q..q,
        Kernel.A c * (star (positionSource c x) * Math.sourceColumn 0 (Real.exp h*x)) := by
    rw [intervalIntegral.integral_const_mul]
  have j11 :
      Kernel.A c * (∫ x : ℝ in Real.exp (-h)*q..q,
        star (burnolRieszSingleFourierSourceRaw c x) * Math.sourceColumn 1 (Real.exp h*x)) =
      ∫ x : ℝ in Real.exp (-h)*q..q,
        Kernel.A c * (star (burnolRieszSingleFourierSourceRaw c x) * Math.sourceColumn 1 (Real.exp h*x)) := by
    rw [intervalIntegral.integral_const_mul]
  have j01 :
      Kernel.beta c * (∫ x : ℝ in Real.exp (-h)*q..q,
        star (positionSource c x) * Math.sourceColumn 1 (Real.exp h*x)) =
      ∫ x : ℝ in Real.exp (-h)*q..q,
        Kernel.beta c * (star (positionSource c x) * Math.sourceColumn 1 (Real.exp h*x)) := by
    rw [intervalIntegral.integral_const_mul]
  have j10 :
      Kernel.beta c * (∫ x : ℝ in Real.exp (-h)*q..q,
        star (burnolRieszSingleFourierSourceRaw c x) * Math.sourceColumn 0 (Real.exp h*x)) =
      ∫ x : ℝ in Real.exp (-h)*q..q,
        Kernel.beta c * (star (burnolRieszSingleFourierSourceRaw c x) * Math.sourceColumn 0 (Real.exp h*x)) := by
    rw [intervalIntegral.integral_const_mul]
  simp only [starRingEnd_apply]
  rw [i00, i11, i10, i01]
  simp only [smul_smul, mul_add]
  rw [j00, j11, j01, j10]
  rw [← intervalIntegral.integral_add h00A h11A,
      ← intervalIntegral.integral_add (h00A.add h11A) h10B,
      ← intervalIntegral.integral_add ((h00A.add h11A).add h10B) h01B,
      ← intervalIntegral.integral_add k00A k11A,
      ← intervalIntegral.integral_add k01B k10B]
  have hF := ((h00A.add h11A).add h10B).add h01B
  have hRA := k00A.add k11A
  have hRB := k01B.add k10B
  rw [← add_assoc]
  rw [← add_smul]
  rw [← add_smul]
  rw [← intervalIntegral.integral_add hF hRA,
      ← intervalIntegral.integral_add (hF.add hRA) hRB]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Math.forcingDensity]
  ring

private theorem profile_point_read (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) :
    profilePointAction c i x
        (Eq (![burnolRieszSingleFourierSource c,
          burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c)] i : Hq) +
          ConstantDual.seed) =
      (![positionSource c x, burnolRieszSingleFourierSourceRaw c x] i) • ConstantDual.seed := by
  change sourceProfile c i
      (Eq (![burnolRieszSingleFourierSource c,
        burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c)] i : Hq) +
        ConstantDual.seed) x • ConstantDual.seed = _
  rw [profile_read]

private theorem boundary_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (boundaryCode c h).eval B.sourceEnvironment =
      Math.boundarySourceRead c h • ConstantDual.seed := by
  unfold boundaryCode
  change (scale _ _).eval B.sourceEnvironment + (scale _ _).eval B.sourceEnvironment = _
  simp only [scale_eval]
  change
    (q:ℂ) •
        ((conjugateProduct (B.coefficientAActionCode c B.constantCode)
          (linear (profilePointAction c 0 (Real.exp h*q)) (sourceCode c 0))).eval B.sourceEnvironment +
         (conjugateProduct (B.coefficientBetaActionCode c B.constantCode)
          (linear (profilePointAction c 1 (Real.exp h*q)) (sourceCode c 1))).eval B.sourceEnvironment) +
      (-(q*Real.exp (-h):ℂ)) •
        ((conjugateProduct (linear (profilePointAction c 0 (q*Real.exp (-h))) (sourceCode c 0))
          (B.coefficientAActionCode c B.constantCode)).eval B.sourceEnvironment +
         (conjugateProduct (linear (profilePointAction c 1 (q*Real.exp (-h))) (sourceCode c 1))
          (B.coefficientBetaActionCode c B.constantCode)).eval B.sourceEnvironment) = _
  rw [conjugate_product_eval, conjugate_product_eval, conjugate_product_eval,
    conjugate_product_eval]
  simp only [linear_eval, source_code_eval,
    coefficient_A_source_eval, coefficient_beta_source_eval]
  rw [profile_point_read, profile_point_read, profile_point_read, profile_point_read]
  simp only [show B.constantCode.eval B.sourceEnvironment = ConstantDual.seed by rfl,
    inner_smul_left, inner_smul_right, seed_inner, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  unfold BandFiniteSourcePrice.boundarySourceRead
  simp only [starRingEnd_apply]
  module

/-- The source programme's finite band action is read from the actual profile AST. -/
theorem finite_pair_code_eval_stage (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (_nonnegative : 0 ≤ h) :
    (finitePairCode c h).eval B.sourceEnvironment =
      Math.finiteSourcePrice c h • ConstantDual.seed := by
  unfold finitePairCode
  change ((2:ℂ)*(Real.exp (h/2):ℂ)/(c.value+star c.value-1)) •
      ((forcingIntegralCode c h).eval B.sourceEnvironment +
        (boundaryCode c h).eval B.sourceEnvironment) = _
  rw [forcing_integral_eval, boundary_code_eval]
  unfold Math.finiteSourcePrice
  module

private theorem cotest_self_eval (c : BurnolCompletedMellinCoordinate) :
    (Expr.bilinear (s := ()) (t := ()) (r := ()) C.cotestAction
      (C.sourceKernelCode c) (C.sourceKernelCode c) : B.E).eval
        B.sourceEnvironment =
      OriginalRieszFinitePairing.kernelSelfSource c • ConstantDual.seed := by
  change inner ℂ ((C.sourceKernelCode c).eval B.sourceEnvironment)
      ((C.sourceKernelCode c).eval B.sourceEnvironment) • ConstantDual.seed = _
  rw [OriginalKCoefficientBSelfCalculation.Semantics.kernel_code_eval]
  rw [OriginalKCoefficientBFiniteAction.sourceKernel_original,
    OriginalRieszFinitePairing.original_kernel_self_source]

private theorem scalar_star_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    (scalarStar (finitePairCode c h)).eval B.sourceEnvironment =
      star (Math.finiteSourcePrice c h) • ConstantDual.seed := by
  change (2 : ℂ) •
      (inner ℂ ((finitePairCode c h).eval B.sourceEnvironment)
        (B.constantCode.eval B.sourceEnvironment) • ConstantDual.seed) = _
  rw [finite_pair_code_eval_stage c h nonnegative]
  rw [show B.constantCode.eval B.sourceEnvironment = ConstantDual.seed by rfl]
  simp only [inner_smul_left, seed_inner, smul_smul, starRingEnd_apply]
  ring

/-- The complete evaluator retains the original K self term and finite band price. -/
theorem evaluator_code_eval_stage (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (_nonnegative : 0 ≤ h) :
    (evaluatorCode c h).eval B.sourceEnvironment =
      evaluatorSource c h • ConstantDual.seed := by
  unfold evaluatorCode
  change (scale _ _).eval B.sourceEnvironment +
      (scale _ _).eval B.sourceEnvironment = _
  rw [scale_eval, scale_eval, cotest_self_eval, scalar_star_eval c h _nonnegative]
  unfold evaluatorSource
  rw [BandFiniteSourcePrice.source_pair_finite_price c h _nonnegative]
  module

end OriginalKPairedBEulerJunctionSource.BandFiniteMaterial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
