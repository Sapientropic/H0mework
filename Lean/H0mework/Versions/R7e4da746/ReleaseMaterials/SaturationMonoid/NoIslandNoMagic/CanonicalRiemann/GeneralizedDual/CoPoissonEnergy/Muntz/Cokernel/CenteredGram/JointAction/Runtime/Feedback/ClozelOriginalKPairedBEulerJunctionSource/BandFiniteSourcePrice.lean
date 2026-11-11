import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.PsiDrive

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
namespace PD
export PsiDrive (position_outer_source fourier_outer_source psiMean)
end PD
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Fq" => burnolRadiusTruncatedFourierRaw q

def sourceColumn (i:Fin 2) (x:ℝ) : ℂ :=
  ![Fq (Response.u:Hq) x-PD.psiMean 0,
    -Fq (Response.v:Hq) x-Edge.raw q x-PD.psiMean 1] i

theorem source_column_continuous (i:Fin 2) : Continuous (sourceColumn i) := by
  fin_cases i
  · exact (burnolRadiusTruncatedFourierRaw_continuous _).sub continuous_const
  · exact ((burnolRadiusTruncatedFourierRaw_continuous _).neg.sub
      (Edge.raw_continuous q)).sub continuous_const

private theorem position_hasDerivAt (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x) :
    HasDerivAt (positionSource c) (positionExteriorDerivative c x) x := by
  have generated:=(((burnolMellinTailPower_hasDerivAt (star c.value) positive).const_mul
    (1/2:ℂ)).sub_const (GapEuler.gapMean q c)).sub (burnolRieszReturnRaw_hasDerivAt c x)
  exact generated

theorem position_source_euler (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x) :
    (x:ℂ)*positionExteriorDerivative c x+(1/2:ℂ)*positionSource c x+
      (star c.value-1/2)*positionSource c x=
      Kernel.A c*sourceColumn 0 x+Kernel.beta c*sourceColumn 1 x := by
  have source:=PD.position_outer_source c x positive
  have mean:=PsiDrive.GapMeans.position_gap_mean c
  simp only [positionSource_eq_outer_sub_mean]
  simp only [sourceColumn,PsiDrive.psiMean,Matrix.cons_val_zero,Matrix.cons_val_one]
  linear_combination source-mean

theorem fourier_source_euler (c:BurnolCompletedMellinCoordinate) (x:ℝ) (nonzero:x≠0) :
    (x:ℂ)*sourceRawDerivative c x+(1/2:ℂ)*burnolRieszSingleFourierSourceRaw c x-
      (star c.value-1/2)*burnolRieszSingleFourierSourceRaw c x=
      -Kernel.A c*sourceColumn 1 x-Kernel.beta c*sourceColumn 0 x := by
  have source:=PD.fourier_outer_source c x nonzero
  have mean:=PsiDrive.GapMeans.fourier_gap_mean c
  simp only [sourceColumn,PsiDrive.psiMean,Matrix.cons_val_zero,Matrix.cons_val_one]
  linear_combination source+mean

def forcingDensity (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  star (Kernel.A c)*(star (sourceColumn 0 x)*positionSource c (Real.exp h*x)+
    star (sourceColumn 1 x)*burnolRieszSingleFourierSourceRaw c (Real.exp h*x))+
  star (Kernel.beta c)*(star (sourceColumn 1 x)*positionSource c (Real.exp h*x)+
    star (sourceColumn 0 x)*burnolRieszSingleFourierSourceRaw c (Real.exp h*x))+
  Kernel.A c*(star (positionSource c x)*sourceColumn 0 (Real.exp h*x)+
    star (burnolRieszSingleFourierSourceRaw c x)*sourceColumn 1 (Real.exp h*x))+
  Kernel.beta c*(star (positionSource c x)*sourceColumn 1 (Real.exp h*x)+
    star (burnolRieszSingleFourierSourceRaw c x)*sourceColumn 0 (Real.exp h*x))

def sourceFlux (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  (x:ℂ)*(star (positionSource c x)*positionSource c (Real.exp h*x)-
    star (burnolRieszSingleFourierSourceRaw c x)*burnolRieszSingleFourierSourceRaw c (Real.exp h*x))

private theorem flux_derivative (c:BurnolCompletedMellinCoordinate) (h x:ℝ) (positive:0<x) :
    HasDerivAt (sourceFlux c h)
      (forcingDensity c h x-(c.value+star c.value-1)*sourceProduct c h x) x := by
  have moved:=mul_pos (Real.exp_pos h) positive
  have position:=position_hasDerivAt c x positive
  have fourier:=sourceRaw_hasDerivAt c x positive.ne'
  have scale:HasDerivAt (fun y:ℝ=>Real.exp h*y) (Real.exp h) x := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id x).const_mul (Real.exp h)
  have positionMoved:HasDerivAt (fun y:ℝ=>positionSource c (Real.exp h*y))
      ((Real.exp h:ℂ)*positionExteriorDerivative c (Real.exp h*x)) x := by
    simpa only [Function.comp_def,Complex.real_smul] using!
      (position_hasDerivAt c _ moved).scomp x scale
  have fourierMoved:HasDerivAt (fun y:ℝ=>burnolRieszSingleFourierSourceRaw c (Real.exp h*y))
      ((Real.exp h:ℂ)*sourceRawDerivative c (Real.exp h*x)) x := by
    simpa only [Function.comp_def,Complex.real_smul] using!
      (sourceRaw_hasDerivAt c _ moved.ne').scomp x scale
  have cast:HasDerivAt (fun y:ℝ=>(y:ℂ)) 1 x := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x:=x))
  have generated:=cast.mul ((position.star.mul positionMoved).sub (fourier.star.mul fourierMoved))
  convert! generated using 1
  have px:=position_source_euler c x positive
  have py:=position_source_euler c _ moved
  have bx:=fourier_source_euler c x positive.ne'
  have by_:=fourier_source_euler c _ moved.ne'
  have cpx:=congrArg star px
  have cbx:=congrArg star bx
  have sx:star (x:ℂ)=(x:ℂ):=Complex.conj_ofReal x
  simp only [star_add,star_sub,star_mul,star_neg,star_star,star_div₀,star_ofNat,star_one,sx] at cpx cbx
  unfold forcingDensity sourceProduct
  dsimp only [Pi.sub_apply,Pi.mul_apply]
  simp only [Complex.ofReal_mul] at py by_
  linear_combination
    -(star (positionSource c x))*py-(positionSource c (Real.exp h*x))*cpx+
    (star (burnolRieszSingleFourierSourceRaw c x))*by_+
    (burnolRieszSingleFourierSourceRaw c (Real.exp h*x))*cbx

private theorem forcing_continuousAt (c:BurnolCompletedMellinCoordinate) (h x:ℝ) (positive:0<x) :
    ContinuousAt (forcingDensity c h) x := by
  have p:ContinuousAt (positionSource c) x:=positionSource_continuousAt c positive
  have b:ContinuousAt (burnolRieszSingleFourierSourceRaw c) x:=
    burnolRieszSingleFourierSourceRaw_continuousAt c positive.ne'
  have scale:ContinuousAt (fun y:ℝ=>Real.exp h*y) x:=by fun_prop
  have mp:ContinuousAt (fun y:ℝ=>positionSource c (Real.exp h*y)) x:=
    (positionSource_continuousAt c (mul_pos (Real.exp_pos h) positive)).comp scale
  have mb:ContinuousAt (fun y:ℝ=>burnolRieszSingleFourierSourceRaw c (Real.exp h*y)) x:=
    (burnolRieszSingleFourierSourceRaw_continuousAt c (mul_pos (Real.exp_pos h) positive).ne').comp scale
  have f:ContinuousAt (sourceColumn 0) x:=(source_column_continuous 0).continuousAt
  have g:ContinuousAt (sourceColumn 1) x:=(source_column_continuous 1).continuousAt
  have mf:ContinuousAt (fun y:ℝ=>sourceColumn 0 (Real.exp h*y)) x:=
    (source_column_continuous 0).continuousAt.comp scale
  have mg:ContinuousAt (fun y:ℝ=>sourceColumn 1 (Real.exp h*y)) x:=
    (source_column_continuous 1).continuousAt.comp scale
  unfold forcingDensity
  fun_prop

theorem position_source_trace (c:BurnolCompletedMellinCoordinate) :
    positionSource c q= -Kernel.A c := by
  rw [positionSource_eq_outer_sub_mean]
  exact Kernel.position_jump c

def boundarySourceRead (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (q:ℂ)*(star (Kernel.A c)*positionSource c (Real.exp h*q)+
    star (Kernel.beta c)*burnolRieszSingleFourierSourceRaw c (Real.exp h*q))-
  (q*Real.exp (-h):ℂ)*(star (positionSource c (q*Real.exp (-h)))*Kernel.A c+
    star (burnolRieszSingleFourierSourceRaw c (q*Real.exp (-h)))*Kernel.beta c)

theorem source_flux_boundary (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    -sourceFlux c h q+sourceFlux c h (q*Real.exp (-h))=boundarySourceRead c h := by
  have shifted:Real.exp h*(q*Real.exp (-h))=q := by
    calc
      _ =q*(Real.exp h*Real.exp (-h)):=by ring
      _ =q:=by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  unfold sourceFlux boundarySourceRead
  simp only [shifted,position_source_trace,star_neg,Kernel.beta]
  push_cast
  ring

def finiteSourcePrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (2:ℂ)*(Real.exp (h/2):ℂ)*
    ((∫x:ℝ in (q*Real.exp (-h))..q,forcingDensity c h x)+boundarySourceRead c h)/
      (c.value+star c.value-1)

theorem source_pair_finite_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h) :
    sourcePairRead c h=finiteSourcePrice c h := by
  have ppos:0<q*Real.exp (-h):=mul_pos (by norm_num) (Real.exp_pos _)
  have bounds:q*Real.exp (-h)≤q:=by
    calc
      _ ≤ q*1:=mul_le_mul_of_nonneg_left ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr nonnegative)) (by norm_num)
      _ =q:=mul_one _
  have pos:∀x∈Icc (q*Real.exp (-h)) q,0<x:=fun x hx=>ppos.trans_le hx.1
  have fcont:ContinuousOn (forcingDensity c h) (Icc (q*Real.exp (-h)) q):=
    fun x hx=>(forcing_continuousAt c h x (pos x hx)).continuousWithinAt
  have pcont:ContinuousOn (sourceProduct c h) (Icc (q*Real.exp (-h)) q):=
    fun x hx=>(sourceProduct_continuousAt c h (pos x hx)).continuousWithinAt
  have fint:IntervalIntegrable (forcingDensity c h) volume (q*Real.exp (-h)) q :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le bounds] using fcont)
  have pint:IntervalIntegrable (sourceProduct c h) volume (q*Real.exp (-h)) q :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le bounds] using pcont)
  have fluxcont:ContinuousOn (sourceFlux c h) (Icc (q*Real.exp (-h)) q):=
    fun x hx=>(flux_derivative c h x (pos x hx)).continuousAt.continuousWithinAt
  have gen:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le bounds fluxcont
    (fun x hx=>flux_derivative c h x (ppos.trans hx.1))
    (fint.sub (pint.const_mul (c.value+star c.value-1)))
  rw [intervalIntegral.integral_sub fint (pint.const_mul _),intervalIntegral.integral_const_mul] at gen
  have nonzero:c.value+star c.value-1≠0:=OriginalRieszSourceGreen.source_cross_parameter_ne_zero c c
  unfold sourcePairRead finiteSourcePrice
  apply (eq_div_iff nonzero).mpr
  rw [←source_flux_boundary c h]
  linear_combination -(2:ℂ)*(Real.exp (h/2):ℂ)*gen

theorem original_evaluator_finite_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h) :
    evaluatorSource c h=
      (pairedMellinTranslationCharacter c.value h-pairedMellinTranslationCharacter (star c.value) h)*
        kernelSelfSource c+(1/2:ℂ)*star (finiteSourcePrice c h) := by
  rw [evaluatorSource,source_pair_finite_price c h nonnegative]

theorem original_fixed_residual_finite_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) :
    -burnolPaFixedShiftResidual c zero=
      (pairedMellinTranslationCharacter c.value (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star c.value) (Real.log stageZeroSonineQ))*
        kernelSelfSource c+(1/2:ℂ)*star (finiteSourcePrice c (Real.log stageZeroSonineQ)) := by
  have nonnegative:0≤Real.log stageZeroSonineQ := by
    apply Real.log_nonneg
    change 1≤Real.sqrt 3
    exact Real.one_le_sqrt.mpr (by norm_num)
  exact (fixed_residual_source c zero).trans (original_evaluator_finite_price c _ nonnegative)

theorem zero_shift_override (c:BurnolCompletedMellinCoordinate) : finiteSourcePrice c 0=0 := by
  rw [←source_pair_finite_price c 0 le_rfl,sourcePairRead_zero]

theorem boundary_fee_kept (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    finiteSourcePrice c h-
      ((2:ℂ)*(Real.exp (h/2):ℂ)*(∫x:ℝ in (q*Real.exp (-h))..q,forcingDensity c h x)/
        (c.value+star c.value-1))=
      (2:ℂ)*(Real.exp (h/2):ℂ)*boundarySourceRead c h/(c.value+star c.value-1) := by
  unfold finiteSourcePrice
  ring

theorem forcing_fee_kept (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    finiteSourcePrice c h-
      ((2:ℂ)*(Real.exp (h/2):ℂ)*boundarySourceRead c h/(c.value+star c.value-1))=
      (2:ℂ)*(Real.exp (h/2):ℂ)*(∫x:ℝ in (q*Real.exp (-h))..q,forcingDensity c h x)/
        (c.value+star c.value-1) := by
  unfold finiteSourcePrice
  ring

end OriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
