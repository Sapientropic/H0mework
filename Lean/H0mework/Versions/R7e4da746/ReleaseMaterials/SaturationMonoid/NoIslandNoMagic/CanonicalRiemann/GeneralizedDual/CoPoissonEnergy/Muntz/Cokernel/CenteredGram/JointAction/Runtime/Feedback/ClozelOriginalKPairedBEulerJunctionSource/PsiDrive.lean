import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ResponseProfile

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.PsiDrive
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open scoped ENNReal Topology InnerProductSpace FourierTransform
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "T" => burnolTruncatedFourier
local notation "Fq" => burnolRadiusTruncatedFourierRaw q
local notation "Eq" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local instance : IsFiniteMeasure (volume.restrict (symmetricInterval q)) where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)






private theorem paired_phase_continuous : Continuous pairedPhase :=
  OriginalKPairedBEulerJunctionSource.PsiDrive.paired_phase_continuous_source

/-- The second full edge is sampled only on the actual finite quarter. -/


def psiMean (i:Fin 2) : ℂ :=
  ![1+burnolQuarterMeanCoefficient (T (Response.u:Hq)),
    -Translator.ForcingMeanZero.edgeMean-burnolQuarterMeanCoefficient (T (Response.v:Hq))] i

def psiRaw (i:Fin 2) (x:ℝ) : ℂ :=
  if |x|≤q then psiMean i else ![Fq (Response.u:Hq) x,-Fq (Response.v:Hq) x-Edge.raw q x] i

private theorem gap_regular_actual : gapRegular=Eq (intervalConstant q) := by
  unfold gapRegular burnolAmbientGapRieszVector
  rw [smul_smul,burnolIntervalConstant_norm_sq (by norm_num:(0:ℝ)<q)]
  norm_num
  rfl

private def fourierRead (x:ℝ) : Hq →ₗ[ℂ] ℂ where
  toFun:=fun state=>Fq state x
  map_add' left right:=congrFun (burnolRadiusTruncatedFourierRaw_add left right) x
  map_smul' scalar state:=congrFun (burnolRadiusTruncatedFourierRaw_smul scalar state) x

private theorem source_euler_fourier (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
    Fq (Euler.sourceEuler c:Hq) x=
      (star c.value-1/2)*Fq (burnolRieszSingleFourierSource c:Hq) x+
      Kernel.A c*Fq (Response.u:Hq) x-Kernel.beta c*Fq (Response.v:Hq) x := by
  have actual:=congrArg (fun value:M=>fourierRead x (value:Hq)) (Euler.sourceEuler_eq c)
  change fourierRead x (Euler.sourceEuler c:Hq)=fourierRead x
    ((star c.value-1/2) • (burnolRieszSingleFourierSource c:Hq)+
      Kernel.A c • (Response.u:Hq)-Kernel.beta c • (Response.v:Hq)) at actual
  simp only [map_sub,map_add,map_smul,smul_eq_mul] at actual
  exact actual

/-- The complete source Fourier kernel gives the exterior position Euler action, including its mean. -/
theorem position_outer_source (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x) :
    (x:ℂ)*positionExteriorDerivative c x+(1/2:ℂ)*burnolRieszStatePositiveOuterRaw c x+
      (star c.value-1/2)*burnolRieszStatePositiveOuterRaw c x=
      Kernel.A c*Fq (Response.u:Hq) x-
        Kernel.beta c*(Fq (Response.v:Hq) x+Edge.raw q x) := by
  have source:=Euler.source_kernel_ward c (Euler.sourceEuler c) (Euler.source_euler c) x
  rw [source_euler_fourier] at source
  rw [position_exterior_return_read]
  unfold positionExteriorDerivative burnolRieszReturnRaw burnolMeanZeroFourierRaw
  have exponent:(-(star c.value+1):ℂ)=(-star c.value)-1:=by ring
  have power:(x:ℂ)*(x:ℂ)^(-(star c.value+1))=(x:ℂ)^(-star c.value) := by
    rw [exponent,Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),Complex.cpow_one]
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  linear_combination -source-(star c.value/2)*power

namespace GapMeans
open Constructor
local notation "mean" => burnolQuarterMeanCoefficient
private theorem mean_add (a b:Hq) : mean (a+b)=mean a+mean b := by
  simp only [burnolQuarterMeanCoefficient,inner_add_right,add_div]
private theorem mean_sub (a b:Hq) : mean (a-b)=mean a-mean b := by
  simp only [burnolQuarterMeanCoefficient,inner_sub_right,sub_div]
private theorem mean_smul (z:ℂ) (a:Hq) : mean (z • a)=z*mean a := by
  simp only [burnolQuarterMeanCoefficient,inner_smul_right]
  ring
private theorem mean_one : mean (intervalConstant q)=1 := by
  rw [Constructor.mean_integral, integral_congr_ae (intervalConstant_coeFn q), integral_const,
    burnolQuarterInterval_measureReal_univ, Complex.real_smul]
  norm_num

private theorem source_ambient_ward (c:BurnolCompletedMellinCoordinate) :
    returnEulerAmbient c+T (Euler.sourceEuler c:Hq)=
      Kernel.beta c • compact (Edge.raw q) (Edge.raw_continuous q)-
        (mean (T (burnolRieszSingleFourierSource c:Hq))/2) • intervalConstant q := by
  let nativeFourier:=burnolRadiusTruncatedFourierRaw q (Euler.sourceEuler c:Hq)
  let m:=mean (T (burnolRieszSingleFourierSource c:Hq))/2
  let lhs:ℝ→ℂ:=returnEulerRaw c+nativeFourier
  let rhs:ℝ→ℂ:=Kernel.beta c • Edge.raw q-m • (fun _ : ℝ=>(1:ℂ))
  have cl:Continuous lhs := (returnEulerRaw_continuous c).add
    (burnolRadiusTruncatedFourierRaw_continuous _)
  have cr:Continuous rhs := ((Edge.raw_continuous q).const_smul (Kernel.beta c)).sub
    (continuous_const.const_smul m)
  have same:lhs=rhs := by
    funext x
    have h:=Euler.source_kernel_ward c (Euler.sourceEuler c) (Euler.source_euler c) x
    dsimp only [lhs,rhs,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_one,
      returnEulerRaw,nativeFourier,m]
    unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw
    linear_combination h
  have states:compact lhs cl=compact rhs cr :=
    ((continuous_memLp lhs cl).toLp_eq_toLp_iff (continuous_memLp rhs cr)).mpr
      (Filter.EventuallyEq.of_eq same)
  rw [compact_add _ _ (returnEulerRaw_continuous c)
    (burnolRadiusTruncatedFourierRaw_continuous _),Edge.compact_truncatedFourier] at states
  rw [compact_sub _ _ ((Edge.raw_continuous q).const_smul (Kernel.beta c))
      (continuous_const.const_smul m),
    compact_smul (Kernel.beta c) (Edge.raw q) (Edge.raw_continuous q),
    compact_smul m (fun _:ℝ=>(1:ℂ)) continuous_const,compact_one] at states
  exact states

private theorem return_mean (c:BurnolCompletedMellinCoordinate) :
    mean (returnEulerAmbient c)=burnolRieszReturnRaw c q := by
  have endpoints:burnolRieszReturnRaw c (-q)=burnolRieszReturnRaw c q :=
    burnolRieszSingleFourierReturnRaw_endpoints c
  rw [returnEulerAmbient_mean,endpoints]
  ring

private theorem source_mean (c:BurnolCompletedMellinCoordinate) :
    burnolRieszReturnRaw c q+star c.value*mean (T (burnolRieszSingleFourierSource c:Hq))+
      Kernel.A c*mean (T (Response.u:Hq))-
      Kernel.beta c*mean (T (Response.v:Hq))=
        Kernel.beta c*Translator.ForcingMeanZero.edgeMean := by
  have h:=congrArg mean (source_ambient_ward c)
  have act:=congrArg (fun a:M=>mean (T (a:Hq))) (Euler.sourceEuler_eq c)
  change mean (T (Euler.sourceEuler c:Hq))=
    mean (T (((star c.value-1/2) • (burnolRieszSingleFourierSource c:Hq)+
      Kernel.A c • (Response.u:Hq))-Kernel.beta c • (Response.v:Hq))) at act
  rw [map_sub,map_add,map_smul,map_smul,map_smul,mean_sub,mean_add,mean_smul,mean_smul,mean_smul] at act
  rw [mean_add,mean_sub,mean_smul,mean_smul,mean_one,return_mean] at h
  change burnolRieszReturnRaw c q+mean (T (Euler.sourceEuler c:Hq))=
    Kernel.beta c*Translator.ForcingMeanZero.edgeMean-
      mean (T (burnolRieszSingleFourierSource c:Hq))/2*1 at h
  linear_combination h-act

theorem position_gap_mean (c:BurnolCompletedMellinCoordinate) :
    star c.value*OriginalRieszFinitePairing.positionMean c=
      Kernel.A c*(1+mean (T (Response.u:Hq)))+
        Kernel.beta c*(-Translator.ForcingMeanZero.edgeMean-mean (T (Response.v:Hq))) := by
  rw [OriginalRieszFinitePairing.positionMean_eq]
  have h:=source_mean c
  unfold Kernel.A at h ⊢
  linear_combination -h

elab "frozenReturnAmbientWard" : term => do
  let head := `_private.H0mework.Versions.R7e4da746.Arithmetic.SonineProjection.MeanZero
  let tail := `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszSource.Constructor.return_ward_ambient
  pure (Lean.mkConst ((Lean.Name.num head 0).append tail))

private theorem return_mean_constraint (c:BurnolCompletedMellinCoordinate) :
    secondReturnRaw c q-(star c.value-1)*mean (T (returnState c:Hq))-
      Kernel.A c*mean (T (Response.v:Hq))+
      Kernel.beta c*mean (T (Response.u:Hq))=
        burnolRieszReturnRaw c q*Translator.ForcingMeanZero.edgeMean := by
  have ambient:=frozenReturnAmbientWard c
  have h:=congrArg mean ambient
  have read:=Constructor.zeroMean_read (returnEulerAmbient c)
  change (returnEuler c:Hq)=returnEulerAmbient c-mean (returnEulerAmbient c) • intervalConstant q at read
  rw [return_mean] at read
  have restore:returnEulerAmbient c=(returnEuler c:Hq)+burnolRieszReturnRaw c q • intervalConstant q := by
    rw [read]
    module
  rw [restore,map_add,map_smul,mean_add,mean_add,mean_smul,mean_sub,mean_add,mean_smul,
    mean_smul,mean_smul,mean_one,OriginalRieszSourceGreen.secondEuler_mean] at h
  have endpoints:burnolRieszReturnRaw c (-q)=burnolRieszReturnRaw c q :=
    burnolRieszSingleFourierReturnRaw_endpoints c
  rw [endpoints] at h
  have edge:=congrArg mean Edge.compact_raw
  rw [mean_sub,mean_smul,mean_add] at edge
  change Translator.ForcingMeanZero.edgeMean=(q:ℂ)*
    (mean (compact (phase q) (phaseContinuous q))+mean (compact (phase (-q)) (phaseContinuous (-q))))-
      mean (T (intervalConstant q)) at edge
  have act:=congrArg (fun a:M=>mean (T (a:Hq))) (Euler.returnEuler_eq c)
  change mean (T (returnEuler c:Hq))=
    mean (T ((-(star c.value-1/2) • (returnState c:Hq)-
      Kernel.A c • (Response.v:Hq))+Kernel.beta c • (Response.u:Hq))) at act
  rw [map_add,map_sub,map_smul,map_smul,map_smul,mean_add,mean_sub,mean_smul,mean_smul,mean_smul] at act
  linear_combination h-act-burnolRieszReturnRaw c q*edge

theorem fourier_gap_mean (c:BurnolCompletedMellinCoordinate) :
    (star c.value-1)*OriginalRieszFinitePairing.fourierMean c=
      Kernel.beta c*(1+mean (T (Response.u:Hq)))+
        Kernel.A c*(-Translator.ForcingMeanZero.edgeMean-mean (T (Response.v:Hq))) := by
  have boundary:=Translator.ForcingMeanZero.forcing_mean_boundary c
  have h:=return_mean_constraint c
  have beta:Kernel.beta c=burnolRieszFourierForcingRaw c q+secondReturnRaw c q := rfl
  unfold OriginalRieszFinitePairing.fourierMean
  unfold Translator.ForcingMeanZero.mean Translator.ForcingWhole.coefficient at boundary
  unfold Kernel.A at h ⊢
  change secondReturnRaw c q-(star c.value-1)*mean (T (returnState c:Hq))-
    (star c.value*GapEuler.gapMean q c+burnolRieszReturnRaw c q)*mean (T (Response.v:Hq))+
    Kernel.beta c*mean (T (Response.u:Hq))=
    burnolRieszReturnRaw c q*Translator.ForcingMeanZero.edgeMean at h
  change (star c.value-1)*(_+mean (T (returnState c:Hq)))=_
  linear_combination -h-boundary-beta

end GapMeans

private theorem return_euler_fourier (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
    Constructor.fourierRaw (Constructor.returnEulerRaw c) x=
      -(star c.value-1/2)*Fq (Constructor.returnState c:Hq) x-
      Kernel.A c*Fq (Response.v:Hq) x+Kernel.beta c*Fq (Response.u:Hq) x+
        burnolRieszReturnRaw c q*Fq (intervalConstant q) x := by
  have native:=congrFun (Constructor.fourierRaw_congr _ _
    (Constructor.compact_read _ (Constructor.returnEulerRaw_continuous c))) x
  change Fq (Constructor.returnEulerAmbient c) x=Constructor.fourierRaw (Constructor.returnEulerRaw c) x at native
  rw [←native]
  have read:=Constructor.zeroMean_read (Constructor.returnEulerAmbient c)
  rw [GapMeans.return_mean] at read
  change (Constructor.returnEuler c:Hq)=Constructor.returnEulerAmbient c-
    burnolRieszReturnRaw c q • intervalConstant q at read
  have restored:Constructor.returnEulerAmbient c=(Constructor.returnEuler c:Hq)+
      burnolRieszReturnRaw c q • intervalConstant q := by rw [read];module
  have source:=congrArg (fun value:M=>fourierRead x (value:Hq)) (Euler.returnEuler_eq c)
  change fourierRead x (Constructor.returnEuler c:Hq)=fourierRead x
    (-(star c.value-1/2) • (Constructor.returnState c:Hq)-
      Kernel.A c • (Response.v:Hq)+Kernel.beta c • (Response.u:Hq)) at source
  simp only [map_add,map_sub,map_smul,smul_eq_mul] at source
  change fourierRead x (Constructor.returnEulerAmbient c)=_
  rw [restored,map_add,map_smul,source]
  rfl

/-- The actual full-frequency source kernel retains both ordinary Fourier means until they cancel here. -/
theorem fourier_outer_source (c:BurnolCompletedMellinCoordinate) (x:ℝ) (nonzero:x≠0) :
    (x:ℂ)*sourceRawDerivative c x+(1/2:ℂ)*(burnolRieszSingleFourierSourceRaw c x+fourierMean c)-
      (star c.value-1/2)*(burnolRieszSingleFourierSourceRaw c x+fourierMean c)=
      Kernel.A c*(Fq (Response.v:Hq) x+Edge.raw q x)-Kernel.beta c*Fq (Response.u:Hq) x := by
  have ward:=Constructor.return_ward_fourier_source c x
  have endpoints:burnolRieszReturnRaw c (-q)=burnolRieszReturnRaw c q :=
    burnolRieszSingleFourierReturnRaw_endpoints c
  rw [return_euler_fourier,endpoints,
    Constructor.phase_symm x q,Constructor.phase_symm x (-q)] at ward
  have returned:=congrFun (Constructor.secondReturnRaw_eq_fourier c) x
  have native:=congrFun (Constructor.fourierRaw_congr _ _ (Constructor.returnState_read c)) x
  change Fq (Constructor.returnState c:Hq) x=Constructor.fourierRaw (burnolRieszReturnRaw c) x at native
  rw [←native] at returned ward
  have weighted:=sourceRaw_weighted_eq c x nonzero
  rw [weightedRaw_eq] at weighted
  change (x:ℂ)*sourceRawDerivative c x+(1/2:ℂ)*
    (burnolRieszFourierForcingRaw c x+Constructor.secondReturnRaw c x)=_ at weighted
  unfold Constructor.secondEulerRaw at weighted
  rw [Translator.ForcingMeanZero.forcingRaw_eq] at weighted
  have edge:Edge.raw q x=(q:ℂ)*(Constructor.phase q x+Constructor.phase (-q) x)-
      Fq (intervalConstant q) x := rfl
  change _=Kernel.A c*(Fq (Response.v:Hq) x+Edge.raw q x)-Kernel.beta c*Fq (Response.u:Hq) x
  change (x:ℂ)*sourceRawDerivative c x+(1/2:ℂ)*
      (burnolRieszFourierForcingRaw c x+Constructor.secondReturnRaw c x+fourierMean c)-
      (star c.value-1/2)*(burnolRieszFourierForcingRaw c x+Constructor.secondReturnRaw c x+fourierMean c)=_
  rw [Translator.ForcingMeanZero.forcingRaw_eq]
  simp only [fourierMean,Translator.ForcingMeanZero.mean,Kernel.A] at weighted ward ⊢
  dsimp only [Constructor.returnState] at returned ward
  linear_combination weighted+ward-burnolRieszReturnRaw c q*edge+(1-star c.value)*returned

private theorem extension_read (state:Hq) (raw:ℝ→ℂ)
    (read:(state:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]raw) :
    (Eq state:ℝ→ℂ)=ᵐ[volume]fun x=>if |x|≤q then raw x else 0 := by
  have localRead:∀ᵐ x:ℝ ∂volume,x∈symmetricInterval q→state x=raw x :=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp read
  filter_upwards [burnolRadiusZeroExtension_coe state,localRead] with x extended actual
  change (Eq state:BurnolL2) x=(symmetricInterval q).indicator (fun x=>state x) x at extended
  rw [extended]
  by_cases inside:|x|≤q
  · have member:x∈symmetricInterval q := by
      exact ⟨(abs_le.mp inside).1,(abs_le.mp inside).2⟩
    rw [Set.indicator_of_mem member,actual member,if_pos inside]
  · have member:x∉symmetricInterval q := by
      intro h
      exact inside (abs_le.mpr h)
    rw [Set.indicator_of_notMem member,if_neg inside]

private theorem position_field_read :
    (psiPositionField:ℝ→ℂ)=ᵐ[volume]psiRaw 0 := by
  have returned:=extension_read (Response.v:Hq) CoPoisson.Ward.ResponseProfile.vRaw
    CoPoisson.Ward.ResponseProfile.v_read
  have constant:=extension_read (intervalConstant q) (fun _=>1) (intervalConstant_coeFn q)
  filter_upwards [burnolRadiusFourierL2_zeroExtension_ae_eq_raw (Response.u:Hq),returned,constant,
    Lp.coeFn_sub (fourierL2 Response.wholeU) Response.wholeV,
    Lp.coeFn_add (fourierL2 Response.wholeU-Response.wholeV) gapRegular]
      with x fourier second one difference addition
  change (fourierL2 Response.wholeU-Response.wholeV+gapRegular:BurnolL2) x=_
  rw [addition,Pi.add_apply,difference,Pi.sub_apply]
  change (fourierL2 Response.wholeU:BurnolL2) x=Fq (Response.u:Hq) x at fourier
  rw [fourier]
  change Fq (Response.u:Hq) x-Eq (Response.v:Hq) x+gapRegular x=_
  rw [second,gap_regular_actual,one]
  change Fq (Response.u:Hq) x-(if |x|≤q then CoPoisson.Ward.ResponseProfile.vRaw x else 0)+
      (if |x|≤q then 1 else 0)=if |x|≤q then 1+burnolQuarterMeanCoefficient (T (Response.u:Hq)) else Fq (Response.u:Hq) x
  by_cases inside:|x|≤q
  · simp only [if_pos inside]
    unfold CoPoisson.Ward.ResponseProfile.vRaw burnolMeanZeroFourierRaw
    ring
  · simp only [if_neg inside]
    ring

private theorem fourier_field_read :
    (psiFourierField:ℝ→ℂ)=ᵐ[volume]fun x=>psiRaw 1 x+(q:ℂ)*phasePair x := by
  have first:=extension_read (Response.u:Hq) CoPoisson.Ward.ResponseProfile.uRaw
    CoPoisson.Ward.ResponseProfile.u_read
  filter_upwards [first,burnolRadiusFourierL2_zeroExtension_ae_eq_raw (Response.v:Hq),
    burnolRadiusFourierL2_zeroExtension_ae_eq_raw (intervalConstant q),
    Lp.coeFn_sub Response.wholeU (fourierL2 Response.wholeV),
    Lp.coeFn_add (Response.wholeU-fourierL2 Response.wholeV) (fourierL2 gapRegular)]
      with x original fourier constant difference addition
  change (Response.wholeU-fourierL2 Response.wholeV+fourierL2 gapRegular:BurnolL2) x=_
  rw [addition,Pi.add_apply,difference,Pi.sub_apply]
  change Eq (Response.u:Hq) x-fourierL2 (Eq (Response.v:Hq)) x+fourierL2 gapRegular x=_
  change (fourierL2 (Eq (Response.v:Hq)):BurnolL2) x=Fq (Response.v:Hq) x at fourier
  change (fourierL2 (Eq (intervalConstant q)):BurnolL2) x=Fq (intervalConstant q) x at constant
  rw [original,fourier,gap_regular_actual,constant]
  change (if |x|≤q then CoPoisson.Ward.ResponseProfile.uRaw x else 0)-Fq (Response.v:Hq) x+
    Fq (intervalConstant q) x=(if |x|≤q then -Translator.ForcingMeanZero.edgeMean-
      burnolQuarterMeanCoefficient (T (Response.v:Hq)) else -Fq (Response.v:Hq) x-Edge.raw q x)+
      (q:ℂ)*phasePair x
  by_cases inside:|x|≤q
  · simp only [if_pos inside]
    simp only [CoPoisson.Ward.ResponseProfile.uRaw,CoPoisson.Ward.ResponseProfile.etaRaw,
      burnolMeanZeroFourierRaw]
    have mean:CoPoisson.Ward.ResponseProfile.etaMean=Translator.ForcingMeanZero.edgeMean := rfl
    rw [mean]
    unfold Edge.raw phasePair
    dsimp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  · simp only [if_neg inside]
    unfold Edge.raw phasePair
    dsimp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring

private theorem paired_read (value:BurnolL2) (raw:ℝ→ℂ) (read:(value:ℝ→ℂ)=ᵐ[volume]raw) :
    (pairedBurnolMultiplicativeDilation junctionShift value:ℝ→ℂ)=ᵐ[volume]
      fun x=>((Real.exp (junctionShift/2):ℂ)*raw (Real.exp junctionShift*x)+
        (Real.exp (-junctionShift/2):ℂ)*raw (Real.exp (-junctionShift)*x))/2 := by
  have dilation (h:ℝ) : (burnolMultiplicativeDilation h value:ℝ→ℂ)=ᵐ[volume]
      fun x=>(Real.exp (h/2):ℂ)*raw (Real.exp h*x) := by
    have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp h*x) volume volume := by
      simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul
        (μ:=(volume:Measure ℝ)) (r:=Real.exp h) (Real.exp_ne_zero h))
    filter_upwards [burnolMultiplicativeDilation_coeFn h value,scale.ae read] with x actual source
    rw [actual]
    change (Real.exp (h/2):ℂ)*value (Real.exp h*x)=_
    rw [source]
  let left:=burnolMultiplicativeDilation junctionShift value
  let right:=burnolMultiplicativeDilation (-junctionShift) value
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (left+right),Lp.coeFn_add left right,
    dilation junctionShift,dilation (-junctionShift)] with x scalar addition first second
  change ((1/2:ℂ) • (left+right):BurnolL2) x=_
  rw [scalar]
  change (1/2:ℂ)*(left+right:BurnolL2) x=_
  rw [addition]
  change (1/2:ℂ)*(left x+right x)=_
  rw [first,second]
  ring

def pairedPsiRaw (i:Fin 2) (x:ℝ) : ℂ :=
  ((Real.exp (junctionShift/2):ℂ)*psiRaw i (Real.exp junctionShift*x)+
    (Real.exp (-junctionShift/2):ℂ)*psiRaw i (Real.exp (-junctionShift)*x))/2

theorem psi_quarter_read (i:Fin 2) :
    (psiQuarter i:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]pairedPsiRaw i := by
  fin_cases i
  · exact (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (pairedBurnolMultiplicativeDilation junctionShift psiPositionField)).trans
        (ae_restrict_of_ae (paired_read _ _ position_field_read))
  · have actual:=ae_restrict_of_ae (s:=symmetricInterval q) (paired_read _ _ fourier_field_read)
    filter_upwards [actual,LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
        (pairedBurnolMultiplicativeDilation junctionShift psiFourierField),
      Constructor.compact_read pairedPhase paired_phase_continuous,
      Lp.coeFn_sub (Rq (pairedBurnolMultiplicativeDilation junctionShift psiFourierField))
        ((q:ℂ) • Constructor.compact pairedPhase paired_phase_continuous),
      Lp.coeFn_smul (q:ℂ) (Constructor.compact pairedPhase paired_phase_continuous)]
        with x action restriction raw difference scalar
    change (Rq (pairedBurnolMultiplicativeDilation junctionShift psiFourierField)-
        (q:ℂ) • Constructor.compact pairedPhase paired_phase_continuous:Hq) x=_
    change (Rq (pairedBurnolMultiplicativeDilation junctionShift psiFourierField):Hq) x=
      pairedBurnolMultiplicativeDilation junctionShift psiFourierField x at restriction
    rw [difference,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,raw,restriction,action]
    change _=pairedPsiRaw 1 x
    unfold pairedPhase pairedPsiRaw
    ring

private theorem fourier_even (state:Hq) (fixed:reflectRestricted q state=state) (x:ℝ) :
    Fq state (-x)=Fq state x := by
  let value:=fourierL2 (Eq state)
  have even:reflectL2 value=value := by
    change reflectL2 (fourierL2 (burnolRadiusZeroExtension q state))=_
    rw [←fourierL2_reflectL2_commute,burnolRadiusZeroExtension_reflect,fixed]
    rfl
  have read:(value:ℝ→ℂ)=ᵐ[volume]Fq state:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw state
  have reflected:(fun y:ℝ=>Fq state (-y))=ᵐ[volume]Fq state := by
    filter_upwards [Lp.coeFn_compMeasurePreserving value negMeasurePreserving,
      negMeasurePreserving.quasiMeasurePreserving.ae read,read] with y reflection negative direct
    change reflectL2 value y=value (-y) at reflection
    rw [even] at reflection
    exact negative.symm.trans (reflection.symm.trans direct)
  have regular:=burnolRadiusTruncatedFourierRaw_continuous state
  exact congrFun (Measure.eq_of_ae_eq (μ:=(volume:Measure ℝ)) reflected
    (regular.comp continuous_neg) regular) x

private theorem phase_pair_even (x:ℝ) : phasePair (-x)=phasePair x := by
  have swap (r:ℝ) : Constructor.phase r (-x)=Constructor.phase (-r) x := by
    unfold Constructor.phase
    congr 2
    ring
  unfold phasePair
  rw [swap,swap,neg_neg,add_comm]

private theorem psi_raw_even (i:Fin 2) (x:ℝ) : psiRaw i (-x)=psiRaw i x := by
  unfold psiRaw
  rw [abs_neg]
  split
  · rfl
  · fin_cases i
    · exact fourier_even (Response.u:Hq) Response.u_reflection x
    · change -Fq (Response.v:Hq) (-x)-Edge.raw q (-x)= -Fq (Response.v:Hq) x-Edge.raw q x
      have edge:Edge.raw q (-x)=Edge.raw q x := by
        change (q:ℂ)*phasePair (-x)-Fq (intervalConstant q) (-x)=
          (q:ℂ)*phasePair x-Fq (intervalConstant q) x
        rw [phase_pair_even,fourier_even _ (reflectRestricted_intervalConstant q)]
      rw [fourier_even _ Response.v_reflection,edge]

private theorem paired_psi_even (i:Fin 2) (x:ℝ) : pairedPsiRaw i (-x)=pairedPsiRaw i x := by
  unfold pairedPsiRaw
  rw [mul_neg,mul_neg,psi_raw_even,psi_raw_even]

private theorem paired_psi_abs (i:Fin 2) (x:ℝ) : pairedPsiRaw i |x|=pairedPsiRaw i x := by
  by_cases positive:0≤x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive),paired_psi_even]

def sourceRate (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℂ :=
  ![star c.value-1/2,-(star c.value-1/2)] i

def psiCoupling (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  ![Kernel.A c*psiRaw 0 x+Kernel.beta c*psiRaw 1 x,
    -Kernel.A c*psiRaw 1 x-Kernel.beta c*psiRaw 0 x] i

private theorem gap_coupling (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (1/2+sourceRate c i)*originalGap c i=
      ![Kernel.A c*psiMean 0+Kernel.beta c*psiMean 1,
        -Kernel.A c*psiMean 1-Kernel.beta c*psiMean 0] i := by
  fin_cases i
  · have same:=GapMeans.position_gap_mean c
    change (1/2+(star c.value-1/2))*positionMean c=_
    change _=Kernel.A c*(1+burnolQuarterMeanCoefficient (T (Response.u:Hq)))+
      Kernel.beta c*(-Translator.ForcingMeanZero.edgeMean-burnolQuarterMeanCoefficient (T (Response.v:Hq)))
    linear_combination same
  · have same:=GapMeans.fourier_gap_mean c
    change (1/2-(star c.value-1/2))*fourierMean c=_
    change _= -Kernel.A c*(-Translator.ForcingMeanZero.edgeMean-burnolQuarterMeanCoefficient (T (Response.v:Hq)))-
      Kernel.beta c*(1+burnolQuarterMeanCoefficient (T (Response.u:Hq)))
    linear_combination -same

private theorem outer_coupling (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (outside:q<x) :
    (x:ℂ)*originalOuterSlope c i x+(1/2+sourceRate c i)*originalOuter c i x=psiCoupling c i x := by
  have pos:0<x:=by linarith
  have cut:¬|x|≤q := by rw [abs_of_pos pos];exact not_le.mpr outside
  fin_cases i
  · have same:=position_outer_source c x pos
    change (x:ℂ)*positionExteriorDerivative c x+(1/2+(star c.value-1/2))*
      burnolRieszStatePositiveOuterRaw c x=_
    change _=Kernel.A c*psiRaw 0 x+Kernel.beta c*psiRaw 1 x
    simp only [psiRaw,if_neg cut]
    change _=Kernel.A c*Fq (Response.u:Hq) x+Kernel.beta c*(-Fq (Response.v:Hq) x-Edge.raw q x)
    linear_combination same
  · have same:=fourier_outer_source c x pos.ne'
    change (x:ℂ)*sourceRawDerivative c x+(1/2-(star c.value-1/2))*
      (burnolRieszSingleFourierSourceRaw c x+fourierMean c)=_
    change _= -Kernel.A c*psiRaw 1 x-Kernel.beta c*psiRaw 0 x
    simp only [psiRaw,if_neg cut]
    change _= -Kernel.A c*(-Fq (Response.v:Hq) x-Edge.raw q x)-Kernel.beta c*Fq (Response.u:Hq) x
    linear_combination same

def pairedCouplingRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  ![Kernel.A c*pairedPsiRaw 0 x+Kernel.beta c*pairedPsiRaw 1 x,
    -Kernel.A c*pairedPsiRaw 1 x-Kernel.beta c*pairedPsiRaw 0 x] i

private theorem paired_coupling (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) :
    pairedCouplingRaw c i x=((Real.exp (junctionShift/2):ℂ)*psiCoupling c i (Real.exp junctionShift*x)+
      (Real.exp (-junctionShift/2):ℂ)*psiCoupling c i (Real.exp (-junctionShift)*x))/2 := by
  fin_cases i <;> simp [pairedCouplingRaw,psiCoupling,pairedPsiRaw] <;> ring

private theorem inner_coupling (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (small:|x|≤q) : psiCoupling c i x=(1/2+sourceRate c i)*originalGap c i := by
  have actual:=gap_coupling c i
  unfold psiCoupling
  simp only [psiRaw,if_pos small]
  exact actual.symm

private theorem drive_bulk_action_positive (c:BurnolCompletedMellinCoordinate) (i:Fin 2)
    (x:ℝ) (positive:0<x) (small:x≤q) :
    TwoPieceFourierAction.bulkRaw junctionPoint (driveInnerRaw c i) (fun _=>0)
      (driveOuterRaw c i) (driveOuterSlope c i) x+sourceRate c i*driveRaw c i x=
        pairedCouplingRaw c i x-(1/2+sourceRate c i)*sourceMean c i := by
  have inward:|Real.exp (-junctionShift)*x|≤q := by
    rw [abs_of_pos (mul_pos (Real.exp_pos _) positive)]
    have scale:Real.exp (-junctionShift)≤1:=Real.exp_le_one_iff.mpr (by linarith [junctionShift_pos])
    nlinarith [Real.exp_pos (-junctionShift)]
  rw [paired_coupling,inner_coupling c i _ inward]
  unfold TwoPieceFourierAction.bulkRaw TwoPieceFourierAction.pieceRaw driveRaw
  rw [abs_of_pos positive]
  by_cases inside:x≤junctionPoint
  · have scaled:|Real.exp junctionShift*x|≤q := by
      rw [abs_of_pos (mul_pos (Real.exp_pos _) positive)]
      have inequality:=mul_le_mul_of_nonneg_left inside (Real.exp_pos junctionShift).le
      rw [junction_scaled] at inequality
      exact inequality
    rw [if_pos inside,if_pos inside,inner_coupling c i _ scaled]
    dsimp only [driveInnerRaw]
    ring
  · have scaled:q<Real.exp junctionShift*x := by
      have inequality:=mul_lt_mul_of_pos_left (lt_of_not_ge inside) (Real.exp_pos junctionShift)
      rw [junction_scaled] at inequality
      exact inequality
    have original:=outer_coupling c i _ scaled
    rw [if_neg inside,if_neg inside]
    dsimp only [driveOuterSlope,driveOuterRaw]
    rw [Complex.ofReal_mul] at original
    linear_combination (Real.exp (junctionShift/2):ℂ)/2*original

private theorem native_add_read (a b:Hq) (f g:ℝ→ℂ)
    (ar:(a:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]f)
    (br:(b:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]g) :
    ((a+b:Hq):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]fun x=>f x+g x := by
  filter_upwards [Lp.coeFn_add a b,ar,br] with x addition first second
  rw [addition,Pi.add_apply,first,second]

private theorem native_smul_read (z:ℂ) (a:Hq) (f:ℝ→ℂ)
    (ar:(a:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]f) :
    ((z • a:Hq):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]fun x=>z*f x := by
  filter_upwards [Lp.coeFn_smul z a,ar] with x scalar raw
  rw [scalar,Pi.smul_apply,smul_eq_mul,raw]

def psiCoupledQuarter (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : Hq :=
  ![Kernel.A c • psiQuarter 0+Kernel.beta c • psiQuarter 1,
    (-Kernel.A c) • psiQuarter 1+(-Kernel.beta c) • psiQuarter 0] i

private theorem coupled_quarter_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (psiCoupledQuarter c i:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]pairedCouplingRaw c i := by
  fin_cases i
  · exact native_add_read _ _ _ _ (native_smul_read _ _ _ (psi_quarter_read 0))
      (native_smul_read _ _ _ (psi_quarter_read 1))
  · convert native_add_read _ _ _ _ (native_smul_read (-Kernel.A c) _ _ (psi_quarter_read 1))
      (native_smul_read (-Kernel.beta c) _ _ (psi_quarter_read 0)) using 1
    · rfl
    · funext x
      change -Kernel.A c*pairedPsiRaw 1 x-Kernel.beta c*pairedPsiRaw 0 x=
        -Kernel.A c*pairedPsiRaw 1 x+-Kernel.beta c*pairedPsiRaw 0 x
      ring

elab "frozenDriveBulkRead" : term => do
  let head:=`_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
  let tail:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedBEulerJunctionSource.drive_bulk_read
  pure (Lean.mkConst ((Lean.Name.num head 0).append tail))

elab "frozenDriveRawRead" : term => do
  let head:=`_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
  let tail:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedBEulerJunctionSource.drive_raw_read
  pure (Lean.mkConst ((Lean.Name.num head 0).append tail))

/-- This is the full ordinary-quarter Euler drive; its actual mean is retained before centering. -/
theorem drive_Psi_full_action (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    driveBulk c i+sourceRate c i • (sourceDrive c i:Hq)=psiCoupledQuarter c i+
      (-(1/2+sourceRate c i)*sourceMean c i) • intervalConstant q := by
  have left:=native_add_read _ _ _ _ (frozenDriveBulkRead c i)
    (native_smul_read (sourceRate c i) _ _ (frozenDriveRawRead c i))
  have right:=native_add_read _ _ _ _ (coupled_quarter_read c i)
    (native_smul_read (-(1/2+sourceRate c i)*sourceMean c i) _ _ (intervalConstant_coeFn q))
  apply Lp.ext
  filter_upwards [left,right,ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x leftRead rightRead member nonzero
  rw [leftRead,rightRead]
  have actual:=drive_bulk_action_positive c i |x| (abs_pos.mpr nonzero) (abs_le.mpr member)
  unfold pairedCouplingRaw at actual ⊢
  rw [paired_psi_abs,paired_psi_abs] at actual
  simpa only [TwoPieceFourierAction.bulkRaw,TwoPieceFourierAction.pieceRaw,driveRaw,abs_abs,
    mul_one,sub_eq_add_neg,neg_mul] using actual

def psiCoupledColumn (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
  ![Kernel.A c • psiColumn 0+Kernel.beta c • psiColumn 1,
    (-Kernel.A c) • psiColumn 1+(-Kernel.beta c) • psiColumn 0] i

/-- The actual two centering means disappear only after the same native drive has been centered. -/
theorem drive_Psi_action (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    driveEuler c i+sourceRate c i • sourceDrive c i=psiCoupledColumn c i := by
  have actual:=congrArg Constructor.zeroMean (drive_Psi_full_action c i)
  rw [map_add,map_smul,map_add,map_smul,Constructor.zeroMean_constant,smul_zero,add_zero] at actual
  have fixed:Constructor.zeroMean (sourceDrive c i:Hq)=sourceDrive c i :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [fixed] at actual
  change driveEuler c i+sourceRate c i • sourceDrive c i=Constructor.zeroMean (psiCoupledQuarter c i) at actual
  rw [actual]
  fin_cases i <;> simp [psiCoupledQuarter,psiCoupledColumn,psiColumn,map_add,map_smul]

/-- The same two fixed native Psi columns are solved once by the original complete B inverse. -/

theorem psi_B_first : psiU+S psiV=psiColumn 0 :=
  burnolMeanZeroBlock_first_equation (psiColumn 0,psiColumn 1)
theorem psi_B_second : psiV+S psiU=psiColumn 1 := by
  rw [add_comm]
  exact burnolMeanZeroBlock_second_equation (psiColumn 0,psiColumn 1)


private theorem contact_B_first (c:BurnolCompletedMellinCoordinate) :
    contactU c-S (contactV c)=sourceContact c 1 := by
  have read:=congrArg (fun op:M→L[ℂ]M=>op (sourceContact c 1+S (sourceContact c 0)))
    burnolMeanZeroBlockInverse_right
  change contactU c-S (S (contactU c))=sourceContact c 1+S (sourceContact c 0) at read
  unfold contactV
  rw [map_add]
  linear_combination (norm:=module) read

private theorem contact_B_second (c:BurnolCompletedMellinCoordinate) :
    contactV c-S (contactU c)=sourceContact c 0 := by unfold contactV;module

private theorem minus_pair_unique (a b d e:M) (first:a-S b=d-S e) (second:b-S a=e-S d) :
    a=d ∧ b=e := by
  have next:=congrArg S second
  rw [map_sub,map_sub] at next
  have combined:burnolMeanZeroOneMinusSquare a=burnolMeanZeroOneMinusSquare d := by
    change a-S (S a)=d-S (S d)
    linear_combination (norm:=module) first+next
  have recover:=congrArg burnolMeanZeroBlockInverse combined
  change (burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare) a=
    (burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare) d at recover
  have inverse:burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare=1:=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  rw [inverse] at recover
  change a=d at recover
  constructor
  · exact recover
  · rw [recover] at second
    exact sub_left_inj.mp second

/-- Full actual paired B Euler fields are generated by fixed Psi columns and the two true contact columns. -/
theorem source_B_Psi_action (c:BurnolCompletedMellinCoordinate) :
    sourceEulerBulk c 0+(star c.value-1/2) • sourceFirst c=
      Kernel.A c • psiU+Kernel.beta c • psiV-contactU c ∧
    sourceEulerBulk c 1-(star c.value-1/2) • sourceSecond c=
      (-Kernel.A c) • psiV+(-Kernel.beta c) • psiU-contactV c := by
  let rate:=star c.value-1/2
  let a:=sourceEulerBulk c 0+rate • sourceFirst c
  let b:=sourceEulerBulk c 1-rate • sourceSecond c
  let d:=Kernel.A c • psiU+Kernel.beta c • psiV-contactU c
  let e:=(-Kernel.A c) • psiV+(-Kernel.beta c) • psiU-contactV c
  have first:a-S b=psiCoupledColumn c 0-sourceContact c 1 := by
    calc
      _=(sourceEulerBulk c 0-S (sourceEulerBulk c 1))+rate • (sourceFirst c+S (sourceSecond c)) := by
        dsimp only [a,b]
        rw [map_sub,map_smul]
        module
      _=(driveEuler c 0+rate • sourceDrive c 0)-sourceContact c 1 := by
        rw [source_B_euler_first,source_B_first]
        module
      _=_ := drive_Psi_action c 0 ▸ rfl
  have second:b-S a=psiCoupledColumn c 1-sourceContact c 0 := by
    calc
      _=(sourceEulerBulk c 1-S (sourceEulerBulk c 0))-rate • (sourceSecond c+S (sourceFirst c)) := by
        dsimp only [a,b]
        rw [map_add,map_smul]
        module
      _=(driveEuler c 1+sourceRate c 1 • sourceDrive c 1)-sourceContact c 0 := by
        rw [source_B_euler_second]
        have source:sourceSecond c+S (sourceFirst c)=sourceDrive c 1 := by rw [add_comm];exact source_B_second c
        rw [source]
        change _=driveEuler c 1+(-rate) • sourceDrive c 1-sourceContact c 0
        module
      _=_ := drive_Psi_action c 1 ▸ rfl
  have forward:d-S e=psiCoupledColumn c 0-sourceContact c 1 := by
    dsimp only [d,e]
    rw [map_sub,map_add,map_smul,map_smul]
    calc
      _=Kernel.A c • (psiU+S psiV)+Kernel.beta c • (psiV+S psiU)-
        (contactU c-S (contactV c)) := by module
      _=_ := by rw [psi_B_first,psi_B_second,contact_B_first];rfl
  have backward:e-S d=psiCoupledColumn c 1-sourceContact c 0 := by
    dsimp only [d,e]
    rw [map_sub,map_add,map_smul,map_smul]
    calc
      _=(-Kernel.A c) • (psiV+S psiU)+(-Kernel.beta c) • (psiU+S psiV)-
        (contactV c-S (contactU c)) := by module
      _=_ := by rw [psi_B_second,psi_B_first,contact_B_second];rfl
  exact minus_pair_unique a b d e (first.trans forward.symm) (second.trans backward.symm)

/-- Both ordinary bulk means are the actual endpoint/internal-jump charge, not omitted projection data. -/
theorem source_B_Psi_full_action (c:BurnolCompletedMellinCoordinate) :
    sourceBulk c 0+(star c.value-1/2) • (sourceFirst c:Hq)=
      ((Kernel.A c • psiU+Kernel.beta c • psiV-contactU c:M):Hq)+
        (sourceTrace c 0-((junctionPoint/q:ℝ):ℂ)*sourceJump c 0) • intervalConstant q ∧
    sourceBulk c 1-(star c.value-1/2) • (sourceSecond c:Hq)=
      (((-Kernel.A c) • psiV+(-Kernel.beta c) • psiU-contactV c:M):Hq)+
        (sourceTrace c 1-((junctionPoint/q:ℝ):ℂ)*sourceJump c 1) • intervalConstant q := by
  have actual:=source_B_Psi_action c
  have first:=congrArg (fun value:M=>(value:Hq)) actual.1
  have second:=congrArg (fun value:M=>(value:Hq)) actual.2
  have read0:=Constructor.zeroMean_read (sourceBulk c 0)
  have read1:=Constructor.zeroMean_read (sourceBulk c 1)
  rw [source_bulk_mean] at read0 read1
  change (sourceEulerBulk c 0:Hq)=_ at read0
  change (sourceEulerBulk c 1:Hq)=_ at read1
  constructor
  · change (sourceEulerBulk c 0:Hq)+(star c.value-1/2) • (sourceFirst c:Hq)=_ at first
    rw [read0] at first
    linear_combination (norm:=module) first
  · change (sourceEulerBulk c 1:Hq)-(star c.value-1/2) • (sourceSecond c:Hq)=_ at second
    rw [read1] at second
    linear_combination (norm:=module) second

/-- This consumes the original mixed Green law with the generated fixed Psi forcing, retaining its complex rate and both charges. -/
theorem actual_paired_Psi_euler_action (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (star (star c.value-1/2)-sourceRate c i)*
        inner ℂ (burnolRieszSingleFourierSource c) (sourceDrive c i)+
      star (Kernel.A c)*inner ℂ Response.u (sourceDrive c i)-
      star (Kernel.beta c)*inner ℂ Response.u (sourceDrive c (![1,0] i))+
      inner ℂ (burnolRieszSingleFourierSource c)
        (psiCoupledColumn c i-sourceContact c (![1,0] i))=pairedJunctionFlux c i := by
  have actual:=actual_paired_B_euler_action c i
  have generated:driveEuler c i=psiCoupledColumn c i-sourceRate c i • sourceDrive c i :=
    eq_sub_of_add_eq (drive_Psi_action c i)
  rw [generated,inner_sub_right,inner_sub_right,inner_smul_right] at actual
  change star (star c.value-1/2)*inner ℂ (burnolRieszSingleFourierSource c) (sourceDrive c i)+
    star (Kernel.A c)*inner ℂ Response.u (sourceDrive c i)-
    star (Kernel.beta c)*inner ℂ Response.u (sourceDrive c (![1,0] i))+
    (inner ℂ (burnolRieszSingleFourierSource c) (psiCoupledColumn c i)-
      sourceRate c i*inner ℂ (burnolRieszSingleFourierSource c) (sourceDrive c i)-
      inner ℂ (burnolRieszSingleFourierSource c) (sourceContact c (![1,0] i)))=_ at actual
  rw [inner_sub_right]
  linear_combination actual

end OriginalKPairedBEulerJunctionSource.PsiDrive
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
