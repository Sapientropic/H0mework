import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.CoefficientJet
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Response
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Whole
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.SourceJet
open Complex Filter MeasureTheory Set
open OriginalRieszSource OriginalRieszSourceGreen
open scoped Topology InnerProductSpace BigOperators
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Q" => Constructor.zeroMean
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- Literal finite logarithmic weight on the original scale inventory. -/
def scaleWeight (s:ℂ) (j:ℕ) (r:ℝ) : ℂ :=
  (-(Real.log r:ℂ))^j * Complex.exp ((Real.log r:ℂ)*(-s))

private theorem scaleWeight_continuous (s:ℂ) (j:ℕ) (b:ℝ) :
    ContinuousOn (scaleWeight s j) (Icc 1 b) := by
  intro r inside
  have positive:0<r := lt_of_lt_of_le zero_lt_one inside.1
  have logCont:ContinuousAt (fun t:ℝ=>(Real.log t:ℂ)) r :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log positive.ne')
  exact ((logCont.neg.pow j).mul ((logCont.mul_const (-s)).cexp)).continuousWithinAt

private theorem scaleWeight_integrable (s:ℂ) (j:ℕ) (b:ℝ) :
    IntegrableOn (scaleWeight s j) (Ioc 1 b) :=
  (scaleWeight_continuous s j b).integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem scaleWeight_derivative (s:ℂ) (j:ℕ) (r:ℝ) :
    HasDerivAt (fun z:ℂ=>scaleWeight z j r) (scaleWeight s (j+1) r) s := by
  have source:=((((hasDerivAt_id s).neg).const_mul (Real.log r:ℂ)).cexp).const_mul
    ((-(Real.log r:ℂ))^j)
  apply source.congr_deriv
  dsimp only [scaleWeight,Pi.neg_apply,id_eq]
  rw [pow_succ]
  ring

/-- Finite-interval differentiation pays each log weight on the actual 1..b inventory. -/
private theorem scaleIntegral_derivative (s:ℂ) (j:ℕ) (b:ℝ) :
    HasDerivAt (fun z:ℂ=>∫r:ℝ in Ioc 1 b,scaleWeight z j r)
      (∫r:ℝ in Ioc 1 b,scaleWeight s (j+1) r) s := by
  let region:Set (ℂ×ℝ):=Metric.closedBall s 1 ×ˢ Icc 1 b
  have continuous:ContinuousOn (fun p:ℂ×ℝ=>scaleWeight p.1 (j+1) p.2) region := by
    intro p inside
    have positive:0<p.2:=lt_of_lt_of_le zero_lt_one inside.2.1
    have logCont:ContinuousAt (fun p:ℂ×ℝ=>(Real.log p.2:ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_log positive.ne').comp continuous_snd.continuousAt)
    exact ((logCont.neg.pow (j+1)).mul
      ((logCont.mul continuous_fst.continuousAt.neg).cexp)).continuousWithinAt
  obtain ⟨bound,majorant⟩:=((isCompact_closedBall s 1).prod isCompact_Icc).exists_bound_of_continuousOn continuous
  have aeInside:∀ᵐr:ℝ ∂volume.restrict (Ioc 1 b),r∈Icc 1 b :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun _ h=>Ioc_subset_Icc_self h)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.closedBall_mem_nhds s (by norm_num:0<(1:ℝ)))
    (Filter.Eventually.of_forall (fun z=>(scaleWeight_integrable z j b).aestronglyMeasurable))
    (scaleWeight_integrable s j b) (scaleWeight_integrable s (j+1) b).aestronglyMeasurable
    (aeInside.mono (fun r hr z hz=>majorant (z,r) ⟨hz,hr⟩))
    (show Integrable (fun _:ℝ=>bound) (volume.restrict (Ioc 1 b)) from integrable_const _)
    (Filter.Eventually.of_forall (fun r z _=>scaleWeight_derivative z j r))).2

private theorem scaleIntegral_jets (s:ℂ) (j:ℕ) (b:ℝ) :
    iteratedDeriv j (fun z:ℂ=>∫r:ℝ in Ioc 1 b,scaleWeight z 0 r) s=
      ∫r:ℝ in Ioc 1 b,scaleWeight s j r := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have functions:(iteratedDeriv j (fun z:ℂ=>∫r:ℝ in Ioc 1 b,scaleWeight z 0 r))=
      (fun z:ℂ=>∫r:ℝ in Ioc 1 b,scaleWeight z j r) := funext ih
    rw [functions,(scaleIntegral_derivative s j b).deriv]

private theorem scaleWeight_cpow (s:ℂ) (j:ℕ) (r:ℝ) (positive:0<r) :
    scaleWeight s j r=(-Complex.log (r:ℂ))^j*(r:ℂ)^(-s) := by
  rw [scaleWeight,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr positive.ne'),
    Complex.ofReal_log positive.le]

open private inverse_jet from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.CoefficientJet

/-- Complete finite normalization, including the entire lower endpoint contribution. -/
theorem scaleIntegral_source (s:ℂ) (notOne:s≠1) (j N:ℕ) :
    (∫r:ℝ in Ioc 1 ((N+1:ℕ):ℝ),scaleWeight s j r)=
      CoefficientJet.normalizationJet s j N-(j.factorial:ℂ)/(1-s)^(j+1) := by
  have large:(1:ℝ)≤((N+1:ℕ):ℝ):=by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have source (z:ℂ) (apart:z≠1) :
      (∫r:ℝ in Ioc 1 ((N+1:ℕ):ℝ),scaleWeight z 0 r)=
        ((N+1:ℕ):ℂ)^(1-z)/(1-z)-1/(1-z) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr=>by
      rw [scaleWeight_cpow z 0 r (lt_of_lt_of_le zero_lt_one hr.1.le),pow_zero,one_mul]),
      ←intervalIntegral.integral_of_le large,integral_cpow]
    · simp only [show -z+1=1-z by ring,Complex.ofReal_natCast,Complex.ofReal_one,one_cpow,sub_div]
    · right
      constructor
      · intro equality
        apply apart
        linear_combination -equality
      · rw [uIcc_of_le large]
        intro inside
        exact not_le.mpr zero_lt_one inside.1
  have near:(fun z:ℂ=>∫r:ℝ in Ioc 1 ((N+1:ℕ):ℝ),scaleWeight z 0 r)=ᶠ[𝓝 s]
      fun z:ℂ=>((N+1:ℕ):ℂ)^(1-z)/(1-z)-1/(1-z) :=
    (eventually_ne_nhds notOne).mono (fun z hz=>source z hz)
  have actual:=near.iteratedDeriv_eq j
  rw [scaleIntegral_jets,iteratedDeriv_fun_sub,CoefficientJet.normalization_source s notOne,
    inverse_jet s notOne] at actual
  · exact actual
  · have nz:((N+1:ℕ):ℂ)≠0:=by exact_mod_cast Nat.succ_ne_zero N
    apply AnalyticAt.contDiffAt
    apply AnalyticAt.div
    · simp only [Complex.cpow_def_of_ne_zero nz]
      fun_prop
    · fun_prop
    · exact sub_ne_zero.mpr notOne.symm
  · exact (analyticAt_const.div (analyticAt_const.sub analyticAt_id)
      (sub_ne_zero.mpr notOne.symm)).contDiffAt
run_cmd IO.eprintln "source jet: finite normalization integral keeps all endpoint terms"

/-- Actual bounded source operations generate the log-power column, with its ordinary mean. -/
def logCoefficient (j k:ℕ) : ℂ :=
  (j.choose k:ℂ)*(Real.log q:ℂ)^(j-k)*(-1:ℂ)^k*(k.factorial:ℂ)
def rawColumn (a:BurnolCompletedMellinCoordinate) (j:ℕ) : Hq :=
  ∑k∈Finset.range (j+1),logCoefficient j k • dividedLogColumn a k
def column (a:BurnolCompletedMellinCoordinate) (j:ℕ) : M := Q (rawColumn a j)
def first (a:BurnolCompletedMellinCoordinate) (j:ℕ) : M := BI (column a j)
def second (a:BurnolCompletedMellinCoordinate) (j:ℕ) : M := -S (first a j)
def rawProfile (a:BurnolCompletedMellinCoordinate) (j:ℕ) (x:ℝ) : ℂ :=
  SingularCounting.powerRaw a x*(Real.log |x|:ℂ)^j

private theorem rawColumn_sum_profile (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    (rawColumn a j:ℝ→ℂ)=ᵐ[μq]
      fun x=>∑k∈Finset.range (j+1),logCoefficient j k * dividedLogRaw a k x := by
  have terms:∀k:ℕ,((logCoefficient j k • dividedLogColumn a k:Hq):ℝ→ℂ)=ᵐ[μq]
      fun x=>logCoefficient j k*dividedLogRaw a k x := by
    intro k
    filter_upwards [Lp.coeFn_smul (logCoefficient j k) (dividedLogColumn a k),dividedLogColumn_profile a k]
      with x scaled raw
    rw [scaled,Pi.smul_apply,smul_eq_mul,raw]
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (j+1))
    (fun k=>logCoefficient j k • dividedLogColumn a k),(ae_all_iff.mpr terms)] with x sumAt termAt
  rw [rawColumn,sumAt]
  apply Finset.sum_congr rfl
  intro k _
  exact termAt k

/-- The source-generated column is exactly power times log^j on the original quarter window. -/
theorem rawColumn_profile (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    (rawColumn a j:ℝ→ℂ)=ᵐ[μq] rawProfile a j := by
  filter_upwards [rawColumn_sum_profile a j,ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x source nonzero
  rw [source]
  have logEquation:(Real.log |x|:ℂ)=(Real.log q:ℂ)-(Real.log (q/|x|):ℂ) := by
    rw [Real.log_div (by norm_num:q≠0) (abs_ne_zero.mpr nonzero),Complex.ofReal_sub]
    ring
  unfold rawProfile
  rw [logEquation,sub_eq_add_neg,add_comm (Real.log q:ℂ),add_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k member
  have factorial:(k.factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero k
  unfold logCoefficient dividedLogRaw
  rw [neg_pow]
  field_simp
  ring

theorem source_blocks (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    first a j+S (second a j)=column a j ∧ S (first a j)+second a j=0 := by
  constructor
  · change BI (column a j)+S (-S (BI (column a j)))=_
    rw [map_neg,←sub_eq_add_neg]
    change (burnolMeanZeroOneMinusSquare*BI) (column a j)=_
    rw [burnolMeanZeroBlockInverse_right]
    rfl
  · exact add_neg_cancel _


open private window_preserved counting_integrable projectedSource_eq
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting
open private fourier_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
open private forward_sub from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Response

private theorem sum_profile {ι:Type*} [Countable ι] (indices:Finset ι) (scalars:ι→ℂ) (values:ι→Hq)
    (raw:ι→ℝ→ℂ) (represents:∀i∈indices,(values i:ℝ→ℂ)=ᵐ[μq] raw i) :
    ((∑i∈indices,scalars i • values i:Hq):ℝ→ℂ)=ᵐ[μq]
      fun x=>∑i∈indices,scalars i*raw i x := by
  have terms:∀i∈indices,((scalars i • values i:Hq):ℝ→ℂ)=ᵐ[μq] fun x=>scalars i*raw i x := by
    intro i hi
    filter_upwards [Lp.coeFn_smul (scalars i) (values i),represents i hi] with x scaled actual
    rw [scaled,Pi.smul_apply,smul_eq_mul,actual]
  filter_upwards [Lp.coeFn_fun_finsetSum indices (fun i=>scalars i • values i),
    (ae_all_iff.mpr (fun i=>ae_all_iff.mpr (terms i)))] with x sumAt termsAt
  rw [sumAt]
  apply Finset.sum_congr rfl
  intro i hi
  exact termsAt i hi

private theorem raw_scaling (a:BurnolCompletedMellinCoordinate) (j:ℕ)
    (r x:ℝ) (large:1≤r) (inside:x∈symmetricInterval q) (nonzero:x≠0) :
    InverseAction.countingRaw r (rawProfile a j) x=
      ∑i∈Finset.range (j+1),(j.choose i:ℂ)*scaleWeight (star a.value) i r*rawProfile a (j-i) x := by
  have positive:0<r:=zero_lt_one.trans_le large
  have rNonzero:(r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr positive.ne'
  have powerNonzero:(r:ℂ)^star a.value≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl rNonzero)
  have power:(r:ℂ)⁻¹*SingularCounting.powerRaw a (x/r)=
      (r:ℂ)^(-star a.value)*SingularCounting.powerRaw a x := by
    unfold SingularCounting.powerRaw
    rw [abs_div,abs_of_pos positive,Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (abs_nonneg x) positive.le,
      Complex.cpow_sub _ _ rNonzero,Complex.cpow_one,Complex.cpow_neg]
    field_simp [rNonzero,powerNonzero]
  have logs:(Real.log |x/r|:ℂ)=(Real.log |x|:ℂ)-(Real.log r:ℂ) := by
    rw [abs_div,abs_of_pos positive,Real.log_div (abs_ne_zero.mpr nonzero) positive.ne',Complex.ofReal_sub]
  unfold InverseAction.countingRaw
  rw [indicator_of_mem (window_preserved r x large inside)]
  unfold rawProfile
  rw [←mul_assoc,power,logs,sub_eq_add_neg,add_comm (Real.log |x|:ℂ),add_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [scaleWeight_cpow _ _ _ positive]
  rw [Complex.ofReal_log positive.le]
  ring

/-- The actual counting operation acts on every generated log column by the finite binomial law. -/
theorem counting_rawColumn (a:BurnolCompletedMellinCoordinate) (j:ℕ) (r:ℝ) (large:1≤r) :
    InverseAction.countingWindow r (rawColumn a j)=
      ∑i∈Finset.range (j+1),((j.choose i:ℂ)*scaleWeight (star a.value) i r) • rawColumn a (j-i) := by
  apply Lp.ext
  filter_upwards [InverseAction.countingWindow_raw r (zero_lt_one.trans_le large)
    (rawColumn a j) (rawProfile a j) (rawColumn_profile a j),
    sum_profile (Finset.range (j+1))
      (fun i=>(j.choose i:ℂ)*scaleWeight (star a.value) i r) (fun i=>rawColumn a (j-i))
      (fun i=>rawProfile a (j-i)) (fun i _=>rawColumn_profile a (j-i)),
    ae_restrict_mem (measurableSet_symmetricInterval q),ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
    with x lhs rhs inside nonzero
  rw [lhs,rhs]
  exact raw_scaling a j r x large inside nonzero

theorem counting_column (a:BurnolCompletedMellinCoordinate) (j:ℕ) (r:ℝ) (large:1≤r) :
    InverseAction.centeredCounting r (column a j)=
      ∑i∈Finset.range (j+1),((j.choose i:ℂ)*scaleWeight (star a.value) i r) • column a (j-i) := by
  have split:InverseAction.countingWindow r (column a j:Hq)=
      InverseAction.countingWindow r (rawColumn a j)-burnolQuarterMeanCoefficient (rawColumn a j) •
        InverseAction.countingWindow r (intervalConstant q) := by
    rw [column,Constructor.zeroMean_read]
    simp only [InverseAction.countingWindow,map_sub,map_smul,smul_sub,smul_smul]
    module
  unfold InverseAction.centeredCounting
  rw [split,counting_rawColumn a j r large,SingularCounting.counting_constant r large,
    map_sub,map_sum,map_smul,map_smul,Constructor.zeroMean_constant,smul_zero,smul_zero,sub_zero]
  simp only [map_smul,column]

/-- The complete 0..1 compensation is generated from the same log column and its genuine mean. -/
def logSource (a:BurnolCompletedMellinCoordinate) (j:ℕ) : M :=
  (∑i∈Finset.range (j+1),((j.choose i:ℂ)*(i.factorial:ℂ)/(1-star a.value)^(i+1)) • column a (j-i))-
    ∫r:ℝ in Ioc 0 1,InverseAction.centeredCounting r (column a j)

def countedPower (a:BurnolCompletedMellinCoordinate) (j N:ℕ) : M :=
  (∑i∈Finset.range (j+1),((j.choose i:ℂ)*CoefficientJet.jet i N (star a.value)) • column a (j-i))+
    logSource a j

/-- Same finite integers, same whole normalization interval, and all lower log-power columns. -/
theorem counted_column (a:BurnolCompletedMellinCoordinate) (j N:ℕ) :
    CenteredCountingDual.forward (N+1) (column a j)=countedPower a j N := by
  have large:(1:ℝ)≤((N+1:ℕ):ℝ):=by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have integrable:=counting_integrable ((N+1:ℕ):ℝ) (column a j)
  have split:(∫r:ℝ in Ioc 0 ((N+1:ℕ):ℝ),InverseAction.centeredCounting r (column a j))=
      (∫r:ℝ in Ioc 0 1,InverseAction.centeredCounting r (column a j))+
      ∫r:ℝ in Ioc 1 ((N+1:ℕ):ℝ),InverseAction.centeredCounting r (column a j) := by
    rw [←Ioc_union_Ioc_eq_Ioc zero_le_one large]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (integrable.mono_set (Ioc_subset_Ioc le_rfl large))
      (integrable.mono_set (Ioc_subset_Ioc zero_le_one le_rfl))
  have notOne:star a.value≠1:=by
    intro equality
    have re:=congrArg Complex.re equality
    simp only [Complex.star_def,Complex.conj_re,Complex.one_re] at re
    linarith [a.belowOne]
  have largeIntegral:(∫r:ℝ in Ioc 1 ((N+1:ℕ):ℝ),InverseAction.centeredCounting r (column a j))=
      ∑i∈Finset.range (j+1),((j.choose i:ℂ)*
        (CoefficientJet.normalizationJet (star a.value) i N-(i.factorial:ℂ)/(1-star a.value)^(i+1))) • column a (j-i) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr=>counting_column a j r hr.1.le),integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_smul_const,integral_const_mul,scaleIntegral_source _ notOne]
    · intro i _
      exact ((scaleWeight_integrable (star a.value) i ((N+1:ℕ):ℝ)).const_mul (j.choose i:ℂ)).smul_const (column a (j-i))
  have integers:(∑n∈Finset.Ico 1 (N+1),InverseAction.centeredCounting n (column a j))=
      ∑i∈Finset.range (j+1),((j.choose i:ℂ)*
        (∑n∈Finset.Ico 1 (N+1),scaleWeight (star a.value) i n)) • column a (j-i) := by
    have expand:(∑n∈Finset.Ico 1 (N+1),InverseAction.centeredCounting n (column a j))=
        ∑n∈Finset.Ico 1 (N+1),∑i∈Finset.range (j+1),
          ((j.choose i:ℂ)*scaleWeight (star a.value) i n) • column a (j-i) := by
      apply Finset.sum_congr rfl
      intro n member
      exact counting_column a j n (by exact_mod_cast (Finset.mem_Ico.mp member).1)
    rw [expand]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum,Finset.sum_smul]
  change SingularCounting.projectedSource (N+1) (column a j)=_
  rw [projectedSource_eq,split,largeIntegral,integers]
  unfold countedPower logSource
  have scalars:∀i∈Finset.range (j+1),
      (j.choose i:ℂ)*(∑n∈Finset.Ico 1 (N+1),scaleWeight (star a.value) i n)-
        (j.choose i:ℂ)*(CoefficientJet.normalizationJet (star a.value) i N-(i.factorial:ℂ)/(1-star a.value)^(i+1))=
      (j.choose i:ℂ)*CoefficientJet.jet i N (star a.value)+
        (j.choose i:ℂ)*(i.factorial:ℂ)/(1-star a.value)^(i+1) := by
    intro i _
    rw [CoefficientJet.jet_source _ notOne]
    unfold CoefficientJet.rawJet
    have actual:(∑n∈Finset.Ico 1 (N+1),scaleWeight (star a.value) i n)=
        ∑n∈Finset.Ico 1 (N+1),(-Complex.log (n:ℂ))^i*(n:ℂ)^(-star a.value) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact scaleWeight_cpow _ _ _ (by exact_mod_cast lt_of_lt_of_le zero_lt_one (Finset.mem_Ico.mp hn).1)
    rw [actual]
    ring
  have difference :
      (∑i∈Finset.range (j+1),((j.choose i:ℂ)*(∑n∈Finset.Ico 1 (N+1),scaleWeight (star a.value) i n)) • column a (j-i))-
      (∑i∈Finset.range (j+1),((j.choose i:ℂ)*(CoefficientJet.normalizationJet (star a.value) i N-(i.factorial:ℂ)/(1-star a.value)^(i+1))) • column a (j-i))=
      (∑i∈Finset.range (j+1),((j.choose i:ℂ)*CoefficientJet.jet i N (star a.value)) • column a (j-i))+
      (∑i∈Finset.range (j+1),((j.choose i:ℂ)*(i.factorial:ℂ)/(1-star a.value)^(i+1)) • column a (j-i)) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←sub_smul,←add_smul,scalars i hi]
  linear_combination (norm:=module) difference

/-- The finite-source fields are generated before the fixed K/B read is applied. -/
def resolvedFirst (a:BurnolCompletedMellinCoordinate) (j N:ℕ) : M :=
  BI (countedPower a j N+S (oppositeSource (N+1) (first a j))+rankSource (S (first a j)))
def resolvedSecond (a:BurnolCompletedMellinCoordinate) (j N:ℕ) : M :=
  -S (resolvedFirst a j N)-oppositeSource (N+1) (first a j)


private theorem power_conjugate (r:ℝ) (positive:0<r) (z:ℂ) :
    star ((r:ℂ)^(star z))=(r:ℂ)^z := by
  have arg:(r:ℂ).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_ne_zero.symm
  simpa only [Complex.star_def,Complex.conj_ofReal,Complex.conj_conj] using
    congrArg (star:ℂ→ℂ) (Complex.cpow_conj (r:ℂ) z arg)

private theorem finite_conjugate (s:ℂ) (N:ℕ) :
    star (CoefficientJet.finite N (star s))=CoefficientJet.finite N s := by
  unfold CoefficientJet.finite FiniteForcing.coefficient
  rw [star_sub,star_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    rw [show -star s=star (-s) by simp only [star_neg]]
    exact power_conjugate n (by exact_mod_cast lt_of_lt_of_le zero_lt_one (Finset.mem_Ico.mp hn).1) (-s)
  · rw [star_div₀,show 1-star s=star (1-s) by simp only [star_sub,star_one],star_star]
    congr 1
    exact power_conjugate ((N+1:ℕ):ℝ) (by positivity) (1-s)

private theorem iterated_conjugate (f:ℂ→ℂ) (j:ℕ) :
    iteratedDeriv j (fun z:ℂ=>star (f (star z)))=fun z=>star (iteratedDeriv j f (star z)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ,ih,iteratedDeriv_succ]
    simpa only [Function.comp_def,Complex.star_def] using
      (deriv_star_conj (𝕜:=ℂ) (F:=ℂ) (f:=iteratedDeriv j f))

/-- The actual observer coefficient has the original bar direction at every order. -/
theorem jet_conjugate (s:ℂ) (j N:ℕ) :
    star (CoefficientJet.jet j N (star s))=CoefficientJet.jet j N s := by
  have source:=congrFun (iterated_conjugate (CoefficientJet.finite N) j) s
  have functions:(fun z:ℂ=>star (CoefficientJet.finite N (star z)))=CoefficientJet.finite N :=
    funext (fun z=>finite_conjugate z N)
  rw [functions] at source
  exact source.symm

private theorem first_even (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    reflectRestricted q (first a j:Hq)=first a j := by
  have fields:first a j=∑k∈Finset.range (j+1),logCoefficient j k • logBFirst a k := by
    simp only [first,column,rawColumn,map_sum,map_smul,logBFirst,centeredLogColumn]
  rw [fields]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact congrArg (fun state:M=>(state:Hq)) (OriginalKFiniteOrderRelease.UnitPowerJordanAction.log_B_even a k)
private theorem second_reflection (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    reflectRestricted q (second a j:Hq)=second a j := by
  have even:=fourier_even (first a j) (first_even a j)
  change reflectRestricted q ((-S (first a j):M):Hq)=((-S (first a j):M):Hq)
  simpa only [Submodule.coe_neg,map_neg] using congrArg Neg.neg even

/-- The original forward commutator and the full opposite source solve both counted B blocks. -/
theorem resolved_actual (a:BurnolCompletedMellinCoordinate) (j N:ℕ) :
    resolvedFirst a j N=CenteredCountingDual.forward (N+1) (first a j) ∧
    resolvedSecond a j N=CenteredCountingDual.reverse (N+1) (second a j) := by
  have source:=(source_blocks a j).1
  change first a j+S (-S (first a j))=column a j at source
  simp only [map_neg,←sub_eq_add_neg] at source
  have counted:=congrArg (CenteredCountingDual.forward (N+1)) source
  rw [forward_sub,counted_column] at counted
  have rank:=CountingJointEnergy.commutator (N+1) (by omega) (S (first a j))
    (fourier_even _ (first_even a j))
  have opposite:=oppositeSource_action (N+1) (first a j) (first_even a j)
  have schur:burnolMeanZeroOneMinusSquare (CenteredCountingDual.forward (N+1) (first a j))=
      countedPower a j N+S (oppositeSource (N+1) (first a j))+rankSource (S (first a j)) := by
    change CenteredCountingDual.forward (N+1) (first a j)-S (S (CenteredCountingDual.forward (N+1) (first a j)))=_
    rw [opposite,map_sub]
    change _=countedPower a j N+
      (S (CenteredCountingDual.reverse (N+1) (S (first a j)))-S (S (CenteredCountingDual.forward (N+1) (first a j))))+
      CountingJointEnergy.contact (S (first a j))
    linear_combination (norm:=module) counted+rank
  have inverse:BI*burnolMeanZeroOneMinusSquare=1:=Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  have solved:=congrArg BI schur
  change (BI*burnolMeanZeroOneMinusSquare) (CenteredCountingDual.forward (N+1) (first a j))=resolvedFirst a j N at solved
  rw [inverse] at solved
  have firstRead:resolvedFirst a j N=CenteredCountingDual.forward (N+1) (first a j):=solved.symm
  refine ⟨firstRead,?_⟩
  rw [resolvedSecond,firstRead,opposite]
  change _=CenteredCountingDual.reverse (N+1) (-S (first a j))
  simp only [CenteredCountingDual.reverse,Submodule.coe_neg,map_neg,CountingDual.dual_eq_adjoint]
  module

theorem resolved_blocks (a:BurnolCompletedMellinCoordinate) (j N:ℕ) :
    resolvedFirst a j N+S (resolvedSecond a j N)=countedPower a j N+rankSource (S (first a j)) ∧
    S (resolvedFirst a j N)+resolvedSecond a j N= -oppositeSource (N+1) (first a j) := by
  have inverseRead:=congrArg (fun op:M→L[ℂ]M=>op
    (countedPower a j N+S (oppositeSource (N+1) (first a j))+rankSource (S (first a j))))
    burnolMeanZeroBlockInverse_right
  change resolvedFirst a j N-S (S (resolvedFirst a j N))=
    countedPower a j N+S (oppositeSource (N+1) (first a j))+rankSource (S (first a j)) at inverseRead
  constructor
  · rw [resolvedSecond,map_sub,map_neg]
    linear_combination (norm:=module) inverseRead
  · rw [resolvedSecond]
    module

open private first_B_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private second_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.OutsideQuarterAction

/-- Source-only arithmetic pair; both original B equations are consumed after generation. -/
def countedRead (a:BurnolCompletedMellinCoordinate) (j N:ℕ) (value:BurnolL2) : ℂ :=
  inner ℂ (resolvedFirst a j N) (burnolAmbientMeanZeroFourier value)+
  inner ℂ (resolvedSecond a j N) (burnolAmbientMeanZeroPosition value)-
  inner ℂ (logSource a j+rankSource (S (first a j))) (burnolAmbientMeanZeroSecondCorrection value)+
  inner ℂ (oppositeSource (N+1) (first a j)) (burnolAmbientMeanZeroFirstCorrection value)

theorem counted_read_source (a:BurnolCompletedMellinCoordinate) (j N:ℕ) (value:BurnolL2) :
    countedRead a j N value=∑i∈Finset.range (j+1),
      (j.choose i:ℂ)*CoefficientJet.jet i N a.value*
        inner ℂ (column a (j-i)) (burnolAmbientMeanZeroSecondCorrection value) := by
  let b:=burnolAmbientMeanZeroFirstCorrection value
  let d:=burnolAmbientMeanZeroSecondCorrection value
  have first:=burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs value)
  have second:=burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs value)
  change b+S d=burnolAmbientMeanZeroPosition value at first
  change S b+d=burnolAmbientMeanZeroFourier value at second
  have bp:reflectRestricted q (b:Hq)=b:=congrArg (fun state:M=>(state:Hq)) (first_B_even value)
  have dp:reflectRestricted q (d:Hq)=d:=congrArg (fun state:M=>(state:Hq)) (second_even value)
  have read:inner ℂ (resolvedFirst a j N) (burnolAmbientMeanZeroFourier value)+
      inner ℂ (resolvedSecond a j N) (burnolAmbientMeanZeroPosition value)=
      inner ℂ (resolvedFirst a j N+S (resolvedSecond a j N)) d+
      inner ℂ (S (resolvedFirst a j N)+resolvedSecond a j N) b := by
    rw [←first,←second,inner_add_right,inner_add_right,inner_add_left,inner_add_left,
      meanZero_fourier_pairing_of_reflection _ _ dp,meanZero_fourier_pairing_of_reflection _ _ bp]
    ring
  unfold countedRead
  rw [read,(resolved_blocks a j N).1,(resolved_blocks a j N).2,countedPower,
    inner_add_left,inner_add_left,inner_neg_left]
  have weighted:inner ℂ
      (∑i∈Finset.range (j+1),((j.choose i:ℂ)*CoefficientJet.jet i N (star a.value)) • column a (j-i)) d=
      ∑i∈Finset.range (j+1),(j.choose i:ℂ)*CoefficientJet.jet i N a.value*inner ℂ (column a (j-i)) d := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    have scaled:=inner_smul_left (𝕜:=ℂ) (column a (j-i)) d
      ((j.choose i:ℂ)*CoefficientJet.jet i N (star a.value))
    rw [scaled,starRingEnd_apply,star_mul,star_natCast,jet_conjugate]
    ring
  rw [weighted]
  dsimp only [b,d]
  rw [inner_add_left]
  ring

/-- The actual whole finite wave preserves its two mean fields and original spatial outside. -/
def wholeWave (a:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  burnolQuarterZeroExtension (first a j:Hq)+fourierL2 (burnolQuarterZeroExtension (second a j:Hq))
def wholeParticle (a:BurnolCompletedMellinCoordinate) (j N:ℕ) : BurnolL2 :=
  fourierL2.symm (FiniteForcing.source (N+1) (wholeWave a j))
def wholeInventory (a:BurnolCompletedMellinCoordinate) (j N:ℕ) (value:BurnolL2) : ℂ :=
  star (2*CountingEnergy.head (N+1) (first a j))*inner ℂ (fourierL2.symm ConstantDual.seed) value+
  star (2*inner ℂ CenteredCountingDual.logarithm (second a j))*inner ℂ ConstantDual.seed value+
  inner ℂ (fourierL2.symm (CountingEnergy.outside (N+1) (first a j))) value

theorem complete_counted_read (a:BurnolCompletedMellinCoordinate) (j N:ℕ) (value:BurnolL2) :
    inner ℂ (wholeParticle a j N) value=
      countedRead a j N value+
      inner ℂ (logSource a j+rankSource (S (first a j))) (burnolAmbientMeanZeroSecondCorrection value)-
      inner ℂ (oppositeSource (N+1) (first a j)) (burnolAmbientMeanZeroFirstCorrection value)+
      wholeInventory a j N value := by
  have actual:=complete_two_foot_read (N+1) (by omega) (first a j) (second a j)
    (first_even a j) (second_reflection a j) value
  rw [←(resolved_actual a j N).1,←(resolved_actual a j N).2] at actual
  unfold wholeParticle wholeWave countedRead wholeInventory
  linear_combination actual
run_cmd IO.eprintln "source jet: full finite Schur/whole inventory retains all lower columns, means, rank and outside"
end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.SourceJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env=>Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CountedSchur.SourceJet"
