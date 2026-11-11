import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeTrace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.StockEnergy

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.WholeUnitGreen
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward OriginalKElementaryArithmeticAction.WholeTrace
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "D"=>burnolMultiplicativeDilation
local notation "C"=>ConstantDual.seed

private theorem raw_interval (X:BurnolL2) (f:ℝ→ℂ) (read:(X:ℝ→ℂ)=ᵐ[volume] f)
    (s t:ℝ) : IntervalIntegrable (fun x=>star (f x)) volume s t := by
  rw [intervalIntegrable_iff']
  apply ((Complex.conjCLE.toContinuousLinearMap).integrable_comp
    (integrableOn_Lp_of_measure_ne_top X (by norm_num) isCompact_uIcc.measure_ne_top)).congr
  filter_upwards [ae_restrict_of_ae read] with x hx
  exact congrArg star hx

private theorem channel_mass (X:BurnolL2) (f:ℝ→ℂ) (read:(X:ℝ→ℂ)=ᵐ[volume] f)
    (a:ℝ) (positive:0<a) :
    inner ℂ X (ContinuousChannels.channel 1 a C)=∫x:ℝ in (-q/a)..(q/a),star (f x) := by
  have actual:(fun x:ℝ=>inner ℂ (X x) (ContinuousChannels.channel 1 a C x))=ᵐ[volume]
      (Icc (-q/a) (q/a)).indicator (fun x=>star (f x)) := by
    filter_upwards [read,DualSourceRaw.channel_coeFn C ConstantDual.seedRaw
      ConstantDual.seed_coeFn a positive] with x source unit
    rw [source,unit]
    have member:(x∈Icc (-q/a) (q/a))↔|a*x|≤q := by
      rw [neg_div,mem_Icc,←abs_le,abs_mul,abs_of_pos positive,mul_comm a |x|,
        ←le_div_iff₀ positive]
    by_cases inside:x∈Icc (-q/a) (q/a)
    · rw [indicator_of_mem inside,ConstantDual.seedRaw,if_pos (member.mp inside)]
      simp [RCLike.inner_apply]
    · rw [indicator_of_notMem inside,ConstantDual.seedRaw,if_neg (fun h=>inside (member.mpr h))]
      simp
  rw [L2.inner_def,integral_congr_ae actual,integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le
      (div_le_div_of_nonneg_right (by norm_num : -q≤q) positive.le)]

def shiftedRaw (h:ℝ) (f:ℝ→ℂ) (x:ℝ) : ℂ :=
  (Real.exp (h/2):ℂ)*f (Real.exp h*x)

private theorem shifted_read (X:BurnolL2) (f:ℝ→ℂ) (read:(X:ℝ→ℂ)=ᵐ[volume] f) (h:ℝ) :
    (D h X:ℝ→ℂ)=ᵐ[volume] shiftedRaw h f := by
  have scale:=Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
    (r:=Real.exp h) (Real.exp_ne_zero h)
  filter_upwards [burnolMultiplicativeDilation_coeFn h X,scale.ae read] with x actual source
  rw [actual]
  change (Real.exp (h/2):ℂ)*X (Real.exp h*x)=_
  simp only [smul_eq_mul] at source
  rw [source]
  rfl

private theorem orbit_mass (X:BurnolL2) (f:ℝ→ℂ) (read:(X:ℝ→ℂ)=ᵐ[volume] f)
    (a:ℝ) (positive:0<a) (t:ℝ) :
    inner ℂ (D t X) (ContinuousChannels.channel 1 a C)=
      (Real.exp (-t/2):ℂ)*(∫x:ℝ in (-(q/a)*Real.exp t)..((q/a)*Real.exp t),star (f x)) := by
  rw [channel_mass _ _ (shifted_read X f read t) a positive]
  have point (x:ℝ):star (shiftedRaw t f x)=(Real.exp (t/2):ℂ)*star (f (Real.exp t*x)) := by
    simp only [shiftedRaw,star_mul,Complex.star_def,Complex.conj_ofReal]
    ring
  simp_rw [point]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left (fun x:ℝ=>star (f x)) (Real.exp_ne_zero t),
    Complex.real_smul]
  have coefficient:(Real.exp (t/2):ℂ)*(Real.exp t:ℂ)⁻¹=(Real.exp (-t/2):ℂ) := by
    rw [←Complex.ofReal_inv,←Complex.ofReal_mul,←div_eq_mul_inv,←Real.exp_sub]
    congr 2
    ring
  rw [←mul_assoc,Complex.ofReal_inv,coefficient]
  congr 2 <;> ring

private theorem orbit_mass_derivative (X:BurnolL2) (f:ℝ→ℂ)
    (read:(X:ℝ→ℂ)=ᵐ[volume] f) (measured:StronglyMeasurable f)
    (a:ℝ) (pos:ContinuousAt f (q/a)) (neg:ContinuousAt f (-q/a)) :
    HasDerivAt (fun t:ℝ=>(Real.exp (-t/2):ℂ)*
      (∫x:ℝ in (-(q/a)*Real.exp t)..((q/a)*Real.exp t),star (f x)))
      (-(1/2:ℂ)*(∫x:ℝ in (-q/a)..(q/a),star (f x))+
        (q/a:ℝ)*(star (f (q/a))+star (f (-q/a)))) 0 := by
  let r:=q/a
  have first:=intervalIntegral.integral_hasDerivAt_right (raw_interval X f read 0 r)
    measured.star.stronglyMeasurableAtFilter pos.star
  have last:=intervalIntegral.integral_hasDerivAt_right (raw_interval X f read 0 (-r))
    measured.star.stronglyMeasurableAtFilter (by simpa only [r,neg_div] using neg.star)
  have grow:HasDerivAt (fun t:ℝ=>r*Real.exp t) r 0 := by
    simpa only [Real.exp_zero,mul_one] using (Real.hasDerivAt_exp (0:ℝ)).const_mul r
  have shrink:HasDerivAt (fun t:ℝ=>-r*Real.exp t) (-r) 0 := by
    simpa only [Real.exp_zero,mul_one] using (Real.hasDerivAt_exp (0:ℝ)).const_mul (-r)
  have plus:=first.scomp_of_eq 0 grow (by simp)
  have minus:=last.scomp_of_eq 0 shrink (by simp)
  have factor:HasDerivAt (fun t:ℝ=>(Real.exp (-t/2):ℂ)) (-(1/2:ℂ)) 0 := by
    have realPart:=(((hasDerivAt_id (0:ℝ)).neg).div_const 2).exp
    have actual:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 realPart
    convert! actual using 1
    norm_num
  have combined:=factor.mul (plus.sub minus)
  have split (t:ℝ) :
      (∫x:ℝ in 0..(r*Real.exp t),star (f x))-(∫x:ℝ in 0..(-r*Real.exp t),star (f x))=
      ∫x:ℝ in (-r*Real.exp t)..(r*Real.exp t),star (f x) :=
    intervalIntegral.integral_interval_sub_left (raw_interval X f read 0 _) (raw_interval X f read 0 _)
  change HasDerivAt (fun t:ℝ=>(Real.exp (-t/2):ℂ)*
    ((∫x:ℝ in 0..(r*Real.exp t),star (f x))-(∫x:ℝ in 0..(-r*Real.exp t),star (f x)))) _ 0 at combined
  simp only [Pi.sub_apply,Function.comp_apply,neg_zero,zero_div,Real.exp_zero,mul_one,Complex.ofReal_one,one_mul,
    Complex.real_smul] at combined
  have functions:(fun t:ℝ=>(Real.exp (-t/2):ℂ)*
      ((∫x:ℝ in 0..(r*Real.exp t),star (f x))-(∫x:ℝ in 0..(-r*Real.exp t),star (f x))))=
      fun t=>(Real.exp (-t/2):ℂ)*(∫x:ℝ in (-r*Real.exp t)..(r*Real.exp t),star (f x)) := by
    funext t
    rw [split]
  rw [functions] at combined
  convert! combined using 1
  rw [intervalIntegral.integral_interval_sub_left (raw_interval X f read 0 r) (raw_interval X f read 0 (-r))]
  simp only [r,neg_div,Complex.ofReal_neg]
  ring

/-- Endpoints and the original interval mass are one complete edge read. -/
def edge (f:ℝ→ℂ) (a:ℝ) : ℂ :=
  (q/a:ℝ)*(star (f (q/a))+star (f (-q/a)))-∫x:ℝ in (-q/a)..(q/a),star (f x)

private theorem unit_edge (X V:BurnolL2) (f:ℝ→ℂ) (read:(X:ℝ→ℂ)=ᵐ[volume] f)
    (measured:StronglyMeasurable f) (domain:HasDerivAt (fun t:ℝ=>D t X) V 0)
    (a:ℝ) (positive:0<a) (pos:ContinuousAt f (q/a)) (neg:ContinuousAt f (-q/a)) :
    inner ℂ V (ContinuousChannels.channel 1 a C)-
      (1/2:ℂ)*inner ℂ X (ContinuousChannels.channel 1 a C)=edge f a := by
  have actual:=domain.inner ℂ (hasDerivAt_const (0:ℝ) (ContinuousChannels.channel 1 a C))
  simp only [burnolMultiplicativeDilation_zero,inner_zero_right] at actual
  have computed:=orbit_mass_derivative X f read measured a pos neg
  have same:(fun t:ℝ=>inner ℂ (D t X) (ContinuousChannels.channel 1 a C))=
      fun t=>(Real.exp (-t/2):ℂ)*(∫x:ℝ in (-(q/a)*Real.exp t)..((q/a)*Real.exp t),star (f x)) :=
    funext (orbit_mass X f read a positive)
  rw [same] at actual
  have equality:=actual.unique computed
  rw [channel_mass X f read a positive,edge]
  linear_combination equality

def edgeProgramme (f:ℝ→ℂ) (M:ℕ) : ℂ :=
  (∑m∈Finset.Ico 1 M,edge f m)-∫a:ℝ in Ioc 0 (M:ℝ),edge f a

private theorem finite_unit_edge (X V:BurnolL2) (f:ℝ→ℂ) (read:(X:ℝ→ℂ)=ᵐ[volume] f)
    (measured:StronglyMeasurable f) (domain:HasDerivAt (fun t:ℝ=>D t X) V 0)
    (continuous:∀x:ℝ,x≠0→ContinuousAt f x) (M:ℕ) :
    inner ℂ V (DualSource.source M C)-(1/2:ℂ)*inner ℂ X (DualSource.source M C)=edgeProgramme f M := by
  let functional:BurnolL2→L[ℂ]ℂ:=innerSL ℂ V-(1/2:ℂ) • innerSL ℂ X
  have channel (a:ℝ) (positive:0<a) : functional (ContinuousChannels.channel 1 a C)=edge f a :=
    unit_edge X V f read measured domain a positive
      (continuous _ (div_ne_zero (by norm_num) positive.ne'))
      (continuous _ (div_ne_zero (by norm_num) positive.ne'))
  change functional (DualSource.source M C)=_
  rw [DualSource.source,map_sub,map_sum,
    ←functional.integral_comp_comm (ContinuousChannels.channel_integrable 1 M C)]
  unfold edgeProgramme
  congr 1
  · exact Finset.sum_congr rfl (fun m hm=>channel m (by exact_mod_cast (Finset.mem_Ico.mp hm).1))
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact channel a ha.1

/-- Both arguments are the literal full finite source; no point cotest is supplied. -/
theorem actual_unit_edge (c:BurnolCompletedMellinCoordinate) (N M:ℕ) :
    inner ℂ (velocity c N) (DualSource.source M C)-
      (1/2:ℂ)*inner ℂ (value c N) (DualSource.source M C)=edgeProgramme (countedRaw c N) M :=
  finite_unit_edge _ _ _ (counted_read c N) (counted_continuous c N).stronglyMeasurable
    (actual_derivative c N) (fun _ _=>(counted_continuous c N).continuousAt) M

local notation "J"=>burnolTateReciprocalL2
open OriginalKFixedBoundarySourceFibre
open private tate_inner boundary_tate from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.StockEnergy

private theorem shifted_derivative (X V:BurnolL2)
    (domain:HasDerivAt (fun t:ℝ=>D t X) V 0) (h:ℝ) :
    HasDerivAt (fun t:ℝ=>D t (D h X)) (D h V) 0 := by
  have actual:=((D h).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 domain
  convert! actual using 1
  funext t
  change D t (D h X)=D h (D t X)
  simp only [burnolMultiplicativeDilation_add]
  rw [add_comm]

private theorem flip_dilation (h:ℝ) (X Y:BurnolL2) :
    inner ℂ (D (-h) X) Y=inner ℂ X (D h Y) := by
  have actual:=(D (-h)).inner_map_eq_flip X Y
  rwa [←burnolMultiplicativeDilation_neg_eq_symm,neg_neg] at actual

private theorem shifted_unit_edge (X V:BurnolL2) (f:ℝ→ℂ) (read:(X:ℝ→ℂ)=ᵐ[volume] f)
    (measured:StronglyMeasurable f) (domain:HasDerivAt (fun t:ℝ=>D t X) V 0)
    (continuous:∀x:ℝ,x≠0→ContinuousAt f x) (h:ℝ) (M:ℕ) :
    inner ℂ V (D h (DualSource.source M C))-(1/2:ℂ)*inner ℂ X (D h (DualSource.source M C))=
      edgeProgramme (shiftedRaw (-h) f) M := by
  have measuredShift:StronglyMeasurable (shiftedRaw (-h) f) := by
    unfold shiftedRaw
    exact stronglyMeasurable_const.mul (measured.comp_measurable (by fun_prop))
  have regular:∀x:ℝ,x≠0→ContinuousAt (shiftedRaw (-h) f) x := by
    intro x hx
    have point:=continuous (Real.exp (-h)*x) (mul_ne_zero (Real.exp_ne_zero _) hx)
    unfold shiftedRaw
    exact continuousAt_const.mul (ContinuousAt.comp (f:=fun y:ℝ=>Real.exp (-h)*y)
      (g:=f) point (by fun_prop))
  have actual:=finite_unit_edge (D (-h) X) (D (-h) V) (shiftedRaw (-h) f)
    (shifted_read X f read (-h)) measuredShift (shifted_derivative X V domain (-h)) regular M
  simpa only [flip_dilation] using actual

private theorem tate_derivative (X V:BurnolL2)
    (domain:HasDerivAt (fun t:ℝ=>D t X) V 0) :
    HasDerivAt (fun t:ℝ=>D t (J X)) (-J V) 0 := by
  have mapped:=(burnolTateReciprocalL2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 domain
  have reversed:=mapped.scomp_of_eq (0:ℝ) ((hasDerivAt_id (0:ℝ)).neg) (by simp)
  convert! reversed using 1
  · funext h
    exact burnolTateReciprocalL2_dilation_inverse h X
  · simp only [neg_one_smul]
    rfl

private theorem tate_pair (X Y:BurnolL2) : inner ℂ (J X) Y=inner ℂ X (J Y) := by
  have actual:=tate_inner X (J Y)
  rwa [burnolTateReciprocalL2_involutive] at actual

private theorem tate_read (X:BurnolL2) (f:ℝ→ℂ) (read:(X:ℝ→ℂ)=ᵐ[volume] f) :
    (J X:ℝ→ℂ)=ᵐ[volume] burnolTateReciprocalRaw f := by
  have member:MemLp f 2 volume:=(memLp_congr_ae read).mp (Lp.memLp X)
  have transported:=burnolTateReciprocalRaw_ae_congr (Lp.memLp X) member read
  filter_upwards [burnolTateReciprocalL2_coeFn X,transported] with x actual source
  exact actual.trans source

private theorem tate_measured (f:ℝ→ℂ) (measured:StronglyMeasurable f) :
    StronglyMeasurable (burnolTateReciprocalRaw f) := by
  unfold burnolTateReciprocalRaw
  exact ((continuous_abs.measurable.complex_ofReal.inv).stronglyMeasurable).mul
    (measured.comp_measurable measurable_inv)

private theorem tate_continuous (f:ℝ→ℂ) (continuous:Continuous f) (x:ℝ) (nonzero:x≠0) :
    ContinuousAt (burnolTateReciprocalRaw f) x := by
  have weight:ContinuousAt (fun y:ℝ=>((|y|:ℝ):ℂ)⁻¹) x := by
    apply ContinuousAt.inv₀ (by fun_prop)
    exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)
  exact weight.mul (continuous.continuousAt.comp (continuousAt_inv₀ nonzero))

def edgeAt (f:ℝ→ℂ) (h:ℝ) (M:ℕ) : ℂ := edgeProgramme (shiftedRaw (-h) f) M

/-- Both feet use the very same full X_N and its original Euler effect. -/
theorem actual_two_unit_edges (c:BurnolCompletedMellinCoordinate) (N M:ℕ) (h:ℝ) :
    (inner ℂ (velocity c N) (D h (DualSource.source M C))-
      (1/2:ℂ)*inner ℂ (value c N) (D h (DualSource.source M C))=edgeAt (countedRaw c N) h M) ∧
    (inner ℂ (velocity c N) (J (D h (DualSource.source M C)))+
      (1/2:ℂ)*inner ℂ (value c N) (J (D h (DualSource.source M C)))=
        -edgeAt (burnolTateReciprocalRaw (countedRaw c N)) h M) := by
  constructor
  · exact shifted_unit_edge _ _ _ (counted_read c N) (counted_continuous c N).stronglyMeasurable
      (actual_derivative c N) (fun _ _=>(counted_continuous c N).continuousAt) h M
  · have actual:=shifted_unit_edge (J (value c N)) (-J (velocity c N))
      (burnolTateReciprocalRaw (countedRaw c N)) (tate_read _ _ (counted_read c N))
      (tate_measured _ (counted_continuous c N).stronglyMeasurable)
      (tate_derivative _ _ (actual_derivative c N))
      (tate_continuous _ (counted_continuous c N)) h M
    rw [inner_neg_left,tate_pair,tate_pair] at actual
    change _=-edgeProgramme (shiftedRaw (-h) (burnolTateReciprocalRaw (countedRaw c N))) M
    linear_combination -actual

def boundaryEdge (c:BurnolCompletedMellinCoordinate) (h:ℝ) (f:ℝ→ℂ) (M:ℕ) : ℂ :=
  pairedMellinTranslationCharacter c.value h*edgeAt f 0 M-
    (1/2:ℂ)*(edgeAt f h M+edgeAt f (-h) M)

theorem actual_two_boundary_edges (c:BurnolCompletedMellinCoordinate) (N M:ℕ) (h:ℝ) :
    (inner ℂ (velocity c N) (finiteBoundaryAction c h (DualSource.source M C))-
      (1/2:ℂ)*inner ℂ (value c N) (finiteBoundaryAction c h (DualSource.source M C))=
        boundaryEdge c h (countedRaw c N) M) ∧
    (inner ℂ (velocity c N) (J (finiteBoundaryAction c h (DualSource.source M C)))+
      (1/2:ℂ)*inner ℂ (value c N) (J (finiteBoundaryAction c h (DualSource.source M C)))=
        -boundaryEdge c h (burnolTateReciprocalRaw (countedRaw c N)) M) := by
  have base:=actual_two_unit_edges c N M 0
  rw [burnolMultiplicativeDilation_zero] at base
  have plus:=actual_two_unit_edges c N M h
  have minus:=actual_two_unit_edges c N M (-h)
  unfold finiteBoundaryAction boundaryEdge
  simp only [map_sub,map_add,map_smul,inner_sub_right,inner_smul_right,inner_add_right]
  constructor
  · linear_combination pairedMellinTranslationCharacter c.value h*base.1-(1/2:ℂ)*(plus.1+minus.1)
  · linear_combination pairedMellinTranslationCharacter c.value h*base.2-(1/2:ℂ)*(plus.2+minus.2)

/-- The complete unit stock and its companion mass consume the same counted graph, with both J signs. -/
theorem actual_stock_green (c:BurnolCompletedMellinCoordinate) (N:ℕ) (h:ℝ) :
    inner ℂ (velocity c N) (finiteBoundaryAction c h
      (Kernel.A c • DualSource.source N C-Kernel.beta c • J (DualSource.source N C)))-
    (1/2:ℂ)*inner ℂ (value c N) (finiteBoundaryAction c h
      (Kernel.A c • DualSource.source N C+Kernel.beta c • J (DualSource.source N C)))=
    Kernel.A c*boundaryEdge c h (countedRaw c N) N+
      Kernel.beta c*boundaryEdge c h (burnolTateReciprocalRaw (countedRaw c N)) N := by
  have actual:=actual_two_boundary_edges c N N h
  have add (X Y:BurnolL2):finiteBoundaryAction c h (X+Y)=
      finiteBoundaryAction c h X+finiteBoundaryAction c h Y := by simp only [finiteBoundaryAction,map_add,smul_add];module
  have sub (X Y:BurnolL2):finiteBoundaryAction c h (X-Y)=
      finiteBoundaryAction c h X-finiteBoundaryAction c h Y := by simp only [finiteBoundaryAction,map_sub,smul_sub];module
  have scalar (a:ℂ) (X:BurnolL2):finiteBoundaryAction c h (a • X)=a • finiteBoundaryAction c h X := by
    simp only [finiteBoundaryAction,map_smul,smul_smul];module
  simp only [sub,add,scalar,←boundary_tate,inner_sub_right,inner_add_right,inner_smul_right]
  linear_combination Kernel.A c*actual.1-Kernel.beta c*actual.2

end OriginalKElementaryArithmeticAction.WholeUnitGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
