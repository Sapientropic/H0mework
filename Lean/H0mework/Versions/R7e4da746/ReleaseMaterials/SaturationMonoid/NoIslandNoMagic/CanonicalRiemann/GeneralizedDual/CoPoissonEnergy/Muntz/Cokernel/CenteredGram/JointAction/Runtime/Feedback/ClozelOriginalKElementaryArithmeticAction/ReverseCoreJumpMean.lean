import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreBalanceConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalReverseCoreJumpMean
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction OriginalKFixedBoundarySourceFibre
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open OriginalFullLossRAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2
local notation "T" => burnolTateReciprocalL2
local notation "U" => burnolMultiplicativeDilation
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

open private gamma conjugate_zero unitPrice weightedUnitCurrent unitCurrent FT unitRoot boxScale boxProgram
  boxProgram_actual box_family_integrable unitTailProgram unitTail_actual unitTail_family_integrable
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope SB_regular SB_reverse_actual complete_actual
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private slope
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantForward
open private reverseCoreRCurrent
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail

def jumpProfile (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
  Kernel.A c*ConstantDual.seedRaw x-Kernel.beta c*Constructor.fourierRaw (fun _=>1) x
def reciprocalJumpProfile (c:BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  burnolTateReciprocalRaw (fun x=>Kernel.A c*Constructor.fourierRaw (fun _=>1) x-
    Kernel.beta c*ConstantDual.seedRaw x)
def rawPair (kernel profile:ℝ→ℂ) : ℂ := ∫ x:ℝ,star (kernel x)*profile x
def dilationProfile (t:ℝ) (profile:ℝ→ℂ) (x:ℝ) : ℂ :=
  (Real.exp (t/2):ℂ)*profile (Real.exp t*x)
def scaleProfile (r:ℝ) (profile:ℝ→ℂ) (x:ℝ) : ℂ :=
  (Real.sqrt r:ℂ)*dilationProfile (-Real.log r)
    (fun x=>2*dilationProfile (Real.log q) profile x) x
def boxPrice (kernel:ℝ→ℂ) (lo hi:ℝ) (f f':ℝ→ℂ) (profile:ℝ→ℂ) : ℂ :=
  f hi*(rawPair kernel (scaleProfile hi profile)-rawPair kernel (scaleProfile lo profile))-
    ∫ u:ℝ in Ioc lo hi,f' u*(rawPair kernel (scaleProfile u profile)-rawPair kernel (scaleProfile lo profile))
def tailPrice (kernel profile:ℝ→ℂ) : ℂ :=
  -(∫ u:ℝ in Ioi 4,slope u*(rawPair kernel (scaleProfile u profile)-rawPair kernel (scaleProfile 4 profile)))
def boundaryPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (profile:ℝ→ℂ) : ℂ :=
  pairedMellinTranslationCharacter c.value h*rawPair (jumpProfile c) profile-
    (1/2:ℂ)*(rawPair (jumpProfile c) (dilationProfile h profile)+
      rawPair (jumpProfile c) (dilationProfile (-h) profile))
def unitCurrentProfile (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
  (unitPrice c)⁻¹*((2*gamma (barC c))*ConstantDual.sawtoothRaw x-2*elementaryReverseRaw (barC c) x)

private theorem jump_source (c:BurnolCompletedMellinCoordinate) :
    wholeJump c=Kernel.A c • ConstantDual.seed-Kernel.beta c • F ConstantDual.seed := by
  simp only [wholeJump,Fin.sum_univ_two,sourceCoefficients,jumpColumns,
    Matrix.cons_val_zero,Matrix.cons_val_one,smul_neg,sub_eq_add_neg]

private theorem seed_twice : F (F ConstantDual.seed)=ConstantDual.seed := by
  rw [fourierL2_fourierL2]
  change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
  rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
  rfl

private theorem jump_raw (c:BurnolCompletedMellinCoordinate) :
    (wholeJump c:ℝ→ℂ)=ᵐ[volume] jumpProfile c := by
  have first:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw (intervalConstant q)
  have raw:=Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  change (F ConstantDual.seed:ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw (intervalConstant q) at first
  rw [raw] at first
  rw [jump_source]
  filter_upwards [Lp.coeFn_sub (Kernel.A c • ConstantDual.seed) (Kernel.beta c • F ConstantDual.seed),
    Lp.coeFn_smul (Kernel.A c) ConstantDual.seed,Lp.coeFn_smul (Kernel.beta c) (F ConstantDual.seed),
    ConstantDual.seed_coeFn,first] with x difference scalarA scalarB seed fourier
  rw [difference,Pi.sub_apply,scalarA,scalarB]
  simp only [Pi.smul_apply,smul_eq_mul,seed,fourier]
  rfl

private theorem fourier_jump_raw (c:BurnolCompletedMellinCoordinate) :
    (F (wholeJump c):ℝ→ℂ)=ᵐ[volume]
      fun x=>Kernel.A c*Constructor.fourierRaw (fun _=>1) x-Kernel.beta c*ConstantDual.seedRaw x := by
  have first:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw (intervalConstant q)
  have raw:=Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  change (F ConstantDual.seed:ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw (intervalConstant q) at first
  rw [raw] at first
  rw [jump_source,map_sub,map_smul,map_smul,seed_twice]
  filter_upwards [Lp.coeFn_sub (Kernel.A c • F ConstantDual.seed) (Kernel.beta c • ConstantDual.seed),
    Lp.coeFn_smul (Kernel.A c) (F ConstantDual.seed),Lp.coeFn_smul (Kernel.beta c) ConstantDual.seed,
    ConstantDual.seed_coeFn,first] with x difference scalarA scalarB seed fourier
  rw [difference,Pi.sub_apply,scalarA,scalarB]
  simp only [Pi.smul_apply,smul_eq_mul,seed,fourier]

private theorem reciprocal_jump_raw (c:BurnolCompletedMellinCoordinate) :
    (T (F (wholeJump c)):ℝ→ℂ)=ᵐ[volume] reciprocalJumpProfile c := by
  have actual:=fourier_jump_raw c
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (F (wholeJump c)))
    ((Lp.memLp (F (wholeJump c))).ae_eq actual) actual
  filter_upwards [burnolTateReciprocalL2_coeFn (F (wholeJump c)),pulled] with x source raw
  rw [source,raw]
  rfl

private theorem FT_price (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) :
    inner ℂ (wholeJump c) (FT v)=inner ℂ (T (F (wholeJump c))) v := by
  have twice:F (F (wholeJump c))=wholeJump c := by
    simp only [jump_source,map_sub,map_smul,seed_twice]
  have actual:=fourierL2.inner_map_map (F (wholeJump c)) (T v)
  rw [twice] at actual
  exact actual.trans (OriginalRieszFiniteSynthesis.tate_pairing _ _).symm

private theorem pair_raw (kernel value:BurnolL2) (kr vr:ℝ→ℂ)
    (left:(kernel:ℝ→ℂ)=ᵐ[volume] kr) (right:(value:ℝ→ℂ)=ᵐ[volume] vr) :
    inner ℂ kernel value=rawPair kr vr := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [left,right] with x l r
  simp only [l,r,RCLike.inner_apply,starRingEnd_apply]
  ring

private theorem dilation_raw (t:ℝ) (value:BurnolL2) (raw:ℝ→ℂ)
    (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    (U t value:ℝ→ℂ)=ᵐ[volume] dilationProfile t raw := by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp t*x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
      (r:=Real.exp t) (Real.exp_ne_zero t))
  filter_upwards [burnolMultiplicativeDilation_coeFn t value,scale.ae actual] with x source read
  rw [source]
  change (Real.exp (t/2):ℂ)*value (Real.exp t*x)=_
  rw [read]
  rfl

private theorem scale_raw (r:ℝ) (value:BurnolL2) (raw:ℝ→ℂ)
    (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    (boxScale value r:ℝ→ℂ)=ᵐ[volume] scaleProfile r raw := by
  have root:(unitRoot value:ℝ→ℂ)=ᵐ[volume] fun x=>2*dilationProfile (Real.log q) raw x := by
    filter_upwards [Lp.coeFn_smul (2:ℂ) (U (Real.log q) value),
      dilation_raw (Real.log q) value raw actual] with x scalar read
    change (((2:ℂ) • U (Real.log q) value:BurnolL2):ℝ→ℂ) x=_
    rw [scalar]
    simp only [Pi.smul_apply,smul_eq_mul,read]
  filter_upwards [Lp.coeFn_smul (Real.sqrt r:ℂ) (U (-Real.log r) (unitRoot value)),
    dilation_raw (-Real.log r) (unitRoot value) _ root] with x scalar read
  change (((Real.sqrt r:ℂ) • U (-Real.log r) (unitRoot value):BurnolL2):ℝ→ℂ) x=_
  rw [scalar]
  simp only [Pi.smul_apply,smul_eq_mul,read]
  rfl

private theorem box_price (kernel value:BurnolL2) (kr vr:ℝ→ℂ)
    (left:(kernel:ℝ→ℂ)=ᵐ[volume] kr) (right:(value:ℝ→ℂ)=ᵐ[volume] vr)
    (lo hi:ℝ) (f f':ℝ→ℂ) (positive:0<lo) (regular:ContinuousOn f' (Icc lo hi)) :
    inner ℂ kernel (boxProgram lo hi f f' value)=boxPrice kr lo hi f f' vr := by
  have integral:=(innerSL ℂ kernel).integral_comp_comm
    (box_family_integrable lo hi f' positive regular value)
  simp only [innerSL_apply_apply] at integral
  unfold boxProgram boxPrice
  rw [inner_sub_right,inner_smul_right,inner_sub_right,←integral]
  simp only [inner_smul_right,inner_sub_right]
  simp_rw [pair_raw kernel _ kr _ left (scale_raw _ value vr right)]

private theorem tail_price (kernel value:BurnolL2) (kr vr:ℝ→ℂ)
    (left:(kernel:ℝ→ℂ)=ᵐ[volume] kr) (right:(value:ℝ→ℂ)=ᵐ[volume] vr) :
    inner ℂ kernel (unitTailProgram value)=tailPrice kr vr := by
  have integral:=(innerSL ℂ kernel).integral_comp_comm (unitTail_family_integrable value)
  simp only [innerSL_apply_apply] at integral
  unfold unitTailProgram tailPrice
  rw [inner_neg_right,←integral]
  simp only [inner_smul_right,inner_sub_right]
  simp_rw [pair_raw kernel _ kr _ left (scale_raw _ value vr right)]

private theorem boundary_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (value:BurnolL2)
    (raw:ℝ→ℂ) (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ (wholeJump c) (finiteBoundaryAction c h value)=boundaryPrice c h raw := by
  unfold finiteBoundaryAction boundaryPrice
  rw [inner_sub_right,inner_smul_right,inner_smul_right,inner_add_right]
  rw [pair_raw _ _ _ _ (jump_raw c) actual,
    pair_raw _ _ _ _ (jump_raw c) (dilation_raw h value raw actual),
    pair_raw _ _ _ _ (jump_raw c) (dilation_raw (-h) value raw actual)]

private theorem unitCurrent_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    (unitCurrent c zero:ℝ→ℂ)=ᵐ[volume] unitCurrentProfile c := by
  unfold unitCurrent weightedUnitCurrent
  filter_upwards [Lp.coeFn_smul (unitPrice c)⁻¹
      ((2*gamma (barC c)) • ConstantDual.value-(2:ℂ) • elementaryReverseSource (barC c) (conjugate_zero c zero)),
    Lp.coeFn_sub ((2*gamma (barC c)) • ConstantDual.value)
      ((2:ℂ) • elementaryReverseSource (barC c) (conjugate_zero c zero)),
    Lp.coeFn_smul (2*gamma (barC c)) ConstantDual.value,
    Lp.coeFn_smul (2:ℂ) (elementaryReverseSource (barC c) (conjugate_zero c zero)),
    ConstantDual.value_coeFn,elementary_reverse_raw (barC c) (conjugate_zero c zero)]
      with x outer difference scalarA scalarB y z
  rw [outer]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [difference,Pi.sub_apply,scalarA,scalarB]
  simp only [Pi.smul_apply,smul_eq_mul,y,z]
  rfl

def lossJumpPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (profile:ℝ→ℂ) : ℂ :=
  boxPrice (jumpProfile c) q (q*Real.exp h) (SBWeight c h) (SBSlope c h) profile+
    centeringMean c h 1*rawPair (jumpProfile c) profile-
    (boxPrice (reciprocalJumpProfile c) (bandLower h) 4 (positiveWeight c h 0)
        (deriv (positiveWeight c h 0)) profile+
      centeringMean c h 0*tailPrice (reciprocalJumpProfile c) profile)

def coreJumpPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  boundaryPrice c h (elementaryReverseRaw c)-(1/2:ℂ)*lossJumpPrice c h ConstantDual.sawtoothRaw

def currentJumpPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (2*gamma c)*boundaryPrice c h (elementaryReverseRaw (barC c))-
    (2*gamma (barC c))*boundaryPrice c h (elementaryReverseRaw c)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ))*lossJumpPrice c h (unitCurrentProfile c)

private theorem forward_actual (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    F (FullUnit.fullForward c h 0)=FT
      (boxProgram (bandLower h) 4 (positiveWeight c h 0) (deriv (positiveWeight c h 0))
        ConstantDual.value+centeringMean c h 0 • unitTailProgram ConstantDual.value) := by
  have regular:ContinuousOn (deriv (positiveWeight c h 0)) (Icc (bandLower h) 4) :=
    (positiveWeight_deriv_continuousOn c h 0).mono (fun _ inside=>(bandLower_pos h).trans_le inside.1)
  have wave:=boxProgram_actual (bandLower h) 4 (positiveWeight c h 0)
    (deriv (positiveWeight c h 0)) (bandLower_pos h) regular
  rw [←wave,←unitTail_actual]
  change F (FullUnit.fullForward c h 0)=F (T (T (exteriorWave c h 0)+
    centeringMean c h 0 • T ConstantForward.value))
  rw [map_add,map_smul,burnolTateReciprocalL2_involutive,burnolTateReciprocalL2_involutive]
  rfl

private theorem loss_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (value:BurnolL2)
    (raw:ℝ→ℂ) (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ (wholeJump c)
      (boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) value+
        centeringMean c h 1 • value-
        FT (boxProgram (bandLower h) 4 (positiveWeight c h 0) (deriv (positiveWeight c h 0)) value+
          centeringMean c h 0 • unitTailProgram value))=lossJumpPrice c h raw := by
  have regular:ContinuousOn (deriv (positiveWeight c h 0)) (Icc (bandLower h) 4) :=
    (positiveWeight_deriv_continuousOn c h 0).mono (fun _ inside=>(bandLower_pos h).trans_le inside.1)
  unfold lossJumpPrice
  rw [inner_sub_right,inner_add_right,inner_smul_right,FT_price,inner_add_right,inner_smul_right]
  rw [box_price _ value _ raw (jump_raw c) actual _ _ _ _ (by norm_num) (SB_regular c h).continuousOn,
    pair_raw _ value _ raw (jump_raw c) actual,
    box_price _ value _ raw (reciprocal_jump_raw c) actual _ _ _ _ (bandLower_pos h) regular,
    tail_price _ value _ raw (reciprocal_jump_raw c) actual]

theorem core_jump_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    inner ℂ (wholeJump c) (coreReverseSource c zero h)=coreJumpPrice c h := by
  unfold coreReverseSource coreJumpPrice
  rw [inner_sub_right,inner_smul_right,boundary_price c h _ _ (elementary_reverse_raw c zero),
    SB_reverse_actual c h nn,forward_actual c h,
    loss_price c h _ _ ConstantDual.value_coeFn]

theorem current_jump_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    inner ℂ (wholeJump c) (reverseCoreRCurrent c zero h)=currentJumpPrice c h := by
  rw [complete_actual c zero h nn]
  unfold completeCoreRCurrent currentJumpPrice
  rw [inner_sub_right,inner_sub_right,inner_smul_right,inner_smul_right,inner_smul_right,
    boundary_price c h _ _ (elementary_reverse_raw (barC c) (conjugate_zero c zero)),
    boundary_price c h _ _ (elementary_reverse_raw c zero),
    loss_price c h _ _ (unitCurrent_raw c zero)]

def fixedJumpProgrammePrice (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : ℂ :=
  let coefficient:=(c.value-star c.value)*gamma (barC c)
  let current:=completeCoreRCurrent c zero h
  let difference:=coreCharacterDefect c h*(reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed-
      inner ℂ (sourceKernel c) (elementarySource c))+positionLogPrice c h+
    (1/2:ℂ)*(centeringMean c h 0*inner ℂ (sourceKernel c) (F ConstantForward.value)-
      inner ℂ (sourceKernel c) (F (FullUnit.fullSource c h 0)))
  (-star (Kernel.A c)*inner ℂ (regularForcing c 0) current-
    star (Kernel.beta c)*inner ℂ (regularForcing c 1) current+
    (2*c.value-1)*inner ℂ (sourceKernel c) current-
    2*coefficient*coreJumpPrice c h-(2*c.value-1)*currentJumpPrice c h+
      2*coefficient*difference)/(2*coefficient)

theorem original_fixedResidual_jump_programme (observation:GeneratedRiemannZeroObservation)
    (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half:OriginalKCombCalculation.Half observation) :
    let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    burnolPaFixedShiftResidual c observation.mathlibZero=
      fixedJumpProgrammePrice c observation.mathlibZero (Real.log stageZeroSonineQ) := by
  let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  let h:=Real.log stageZeroSonineQ
  change burnolPaFixedShiftResidual c observation.mathlibZero=fixedJumpProgrammePrice c observation.mathlibZero h
  have read:=OriginalReverseCoreBalanceConsumer.original_fixedResidual_R_price observation nontrivial half
  change burnolPaFixedShiftResidual c observation.mathlibZero=OriginalReverseCoreBalanceConsumer.fixedRPrice c observation.mathlibZero h at read
  apply read.trans
  have nn:0≤h:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  change OriginalReverseCoreBalanceConsumer.fixedRPrice c observation.mathlibZero h=
    fixedJumpProgrammePrice c observation.mathlibZero h
  unfold OriginalReverseCoreBalanceConsumer.fixedRPrice fixedJumpProgrammePrice
  dsimp only
  rw [core_jump_source c observation.mathlibZero h nn,
    current_jump_source c observation.mathlibZero h nn,complete_actual c observation.mathlibZero h nn]
  rfl

end OriginalReverseCoreJumpMean
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
