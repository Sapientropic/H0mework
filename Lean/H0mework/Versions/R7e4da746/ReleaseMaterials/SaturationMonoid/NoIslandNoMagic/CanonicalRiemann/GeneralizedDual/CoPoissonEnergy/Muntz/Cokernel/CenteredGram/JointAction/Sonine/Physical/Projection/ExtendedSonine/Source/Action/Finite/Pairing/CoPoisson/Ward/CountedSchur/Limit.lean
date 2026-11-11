import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Kernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Response
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open Complex Filter MeasureTheory Set
open OriginalRieszSource OriginalPaPhysicalGreen
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "D" => burnolMultiplicativeDilation
local notation "cut" => originalPhysicalCutoff
open private sqrt_exp from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseAction


private theorem phase_norm (frequency a:ℝ) : ‖Constructor.phase frequency a‖=1 := Circle.norm_coe _

private theorem phase_lipschitz (frequency x y:ℝ) :
    ‖Constructor.phase frequency y-Constructor.phase frequency x‖≤(2*Real.pi*|frequency|)*|y-x| := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s:=univ) (f':=fun a=>-2*(Real.pi:ℂ)*Complex.I*(frequency:ℂ)*Constructor.phase frequency a)
    (fun a _=>(Constructor.phase_derivative frequency a).hasDerivWithinAt)
    (fun a _=>?_) (convex_univ) (mem_univ x) (mem_univ y)
  simp only [norm_mul,norm_neg,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_I,mul_one,phase_norm]
  exact le_rfl

private theorem phase_sum_error (frequency:ℝ) (k:ℕ) :
    ‖(∑ n∈Finset.Icc 1 k,Constructor.phase frequency n)-∫a:ℝ in (0:ℝ)..k,Constructor.phase frequency a‖≤
      (2*Real.pi*|frequency|)*k := by
  have continuous:=Constructor.phaseContinuous frequency
  induction k with
  | zero => simp
  | succ k previous =>
    have adjacent: (∫a:ℝ in (0:ℝ)..k,Constructor.phase frequency a)+
        (∫a:ℝ in (k:ℝ)..(k+1:ℝ),Constructor.phase frequency a)=
        ∫a:ℝ in (0:ℝ)..(k+1:ℝ),Constructor.phase frequency a :=
      intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable _ _) (continuous.intervalIntegrable _ _)
    have cell:‖Constructor.phase frequency (k+1)-∫a:ℝ in (k:ℝ)..(k+1:ℝ),Constructor.phase frequency a‖≤
        2*Real.pi*|frequency| := by
      have difference:Constructor.phase frequency (k+1)-(∫a:ℝ in (k:ℝ)..(k+1:ℝ),Constructor.phase frequency a)=
          ∫a:ℝ in (k:ℝ)..(k+1:ℝ),Constructor.phase frequency (k+1)-Constructor.phase frequency a := by
        rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (continuous.intervalIntegrable _ _),
          intervalIntegral.integral_const]
        simp
      rw [difference]
      have bounded:=intervalIntegral.norm_integral_le_of_norm_le_const
        (a:=(k:ℝ)) (b:=(k+1:ℝ)) (C:=2*Real.pi*|frequency|)
        (f:=fun a=>Constructor.phase frequency (k+1)-Constructor.phase frequency a) (fun a inside=>by
          rw [uIoc_of_le (by linarith)] at inside
          calc
            _≤(2*Real.pi*|frequency|)*|(k+1:ℝ)-a|:=phase_lipschitz frequency a (k+1)
            _≤(2*Real.pi*|frequency|)*1:=mul_le_mul_of_nonneg_left
              (by rw [abs_of_nonneg (by linarith [inside.2])];linarith [inside.1]) (by positivity)
            _=_:=mul_one _)
      simpa using bounded
    rw [Finset.sum_Icc_succ_top (by omega),Nat.cast_add,Nat.cast_one,←adjacent]
    have decompose:(∑ n∈Finset.Icc 1 k,Constructor.phase frequency n)+Constructor.phase frequency (k+1)-
        ((∫a:ℝ in (0:ℝ)..k,Constructor.phase frequency a)+(∫a:ℝ in (k:ℝ)..(k+1:ℝ),Constructor.phase frequency a))=
        ((∑ n∈Finset.Icc 1 k,Constructor.phase frequency n)-∫a:ℝ in (0:ℝ)..k,Constructor.phase frequency a)+
        (Constructor.phase frequency (k+1)-∫a:ℝ in (k:ℝ)..(k+1:ℝ),Constructor.phase frequency a) := by ring
    rw [decompose]
    exact (norm_add_le _ _).trans (by nlinarith [previous,cell])

/-- Original strict n<N inventory and the full integral from zero. -/
def weightedCut (N:ℕ) (x frequency:ℝ) : ℂ :=
  (∑ n∈Finset.Ico 1 N,Constructor.phase frequency n*ConstantDual.seedRaw ((n:ℝ)*x))-
    ∫a:ℝ in Ioc 0 (N:ℝ),Constructor.phase frequency a*ConstantDual.seedRaw (a*x)

def weightedLimit (x frequency:ℝ) : ℂ :=
  (∑ n∈Finset.Icc 1 ⌊q/|x|⌋₊,Constructor.phase frequency n)-
    ∫a:ℝ in (0:ℝ)..(q/|x|),Constructor.phase frequency a

private theorem weightedCut_read (N:ℕ) (x frequency:ℝ) (nonzero:x≠0) :
    weightedCut N x frequency=
      (∑ n∈Finset.Icc 1 (min ⌊q/|x|⌋₊ (N-1)),Constructor.phase frequency n)-
        ∫a:ℝ in (0:ℝ)..(min (N:ℝ) (q/|x|)),Constructor.phase frequency a := by
  have incidence (n:ℕ) (positive:1≤n) : |(n:ℝ)*x|≤q ↔ n≤⌊q/|x|⌋₊ := by
    rw [Nat.le_floor_iff' (by omega),abs_mul,abs_of_nonneg (Nat.cast_nonneg n),
      le_div_iff₀ (abs_pos.mpr nonzero)]
  have indices:(Finset.Ico 1 N).filter (fun n:ℕ=>|(n:ℝ)*x|≤q)=
      Finset.Icc 1 (min ⌊q/|x|⌋₊ (N-1)) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Ico,Finset.mem_Icc,le_min_iff]
    constructor
    · rintro ⟨⟨positive,upper⟩,member⟩
      exact ⟨positive,(incidence n positive).mp member,by omega⟩
    · rintro ⟨positive,upper,cutoff⟩
      exact ⟨⟨positive,by omega⟩,(incidence n positive).mpr upper⟩
  have integer:(∑n∈Finset.Ico 1 N,Constructor.phase frequency n*ConstantDual.seedRaw ((n:ℝ)*x))=
      ∑n∈Finset.Icc 1 (min ⌊q/|x|⌋₊ (N-1)),Constructor.phase frequency n := by
    simp only [ConstantDual.seedRaw,mul_ite,mul_one,mul_zero,←Finset.sum_filter,indices]
  have source:(fun a:ℝ=>Constructor.phase frequency a*ConstantDual.seedRaw (a*x))=ᵐ[volume.restrict (Ioc 0 (N:ℝ))]
      (Ioc 0 (q/|x|)).indicator (Constructor.phase frequency) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    have native:|a*x|≤q ↔ a∈Ioc 0 (q/|x|) := by
      rw [abs_mul,abs_of_pos inside.1,mem_Ioc,and_iff_right inside.1,
        le_div_iff₀ (abs_pos.mpr nonzero)]
    by_cases included:a∈Ioc 0 (q/|x|)
    · rw [ConstantDual.seedRaw,if_pos (native.mpr included),indicator_of_mem included,mul_one]
    · rw [ConstantDual.seedRaw,if_neg (fun h=>included (native.mp h)),indicator_of_notMem included,mul_zero]
  rw [weightedCut,integer,integral_congr_ae source,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,Ioc_inter_Ioc,max_self,min_comm (q/|x|) (N:ℝ),
    ←intervalIntegral.integral_of_le (by positivity:0≤min (N:ℝ) (q/|x|))]

/-- Paid unit endpoint discrepancy retains the exact inclusive floor and strict source cutoff. -/
theorem weightedCut_bound (N:ℕ) (x frequency:ℝ) (nonzero:x≠0) :
    ‖weightedCut N x frequency‖≤2*Real.pi*|frequency| *(q/|x|)+1 := by
  let k:=min ⌊q/|x|⌋₊ (N-1)
  let u:=min (N:ℝ) (q/|x|)
  have distance:|u-(k:ℝ)|≤1 := by
    have paid:‖((k:ℂ)-(u:ℂ))‖≤1:=(ConstantDual.finite_bounds N x).1
    rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_sub_comm] at paid
    exact paid
  have cutoff:(k:ℝ)≤q/|x|:=le_trans (by exact_mod_cast min_le_left ⌊q/|x|⌋₊ (N-1))
    (Nat.floor_le (by positivity))
  have continuous:=Constructor.phaseContinuous frequency
  have adjacent: (∫a:ℝ in (0:ℝ)..k,Constructor.phase frequency a)+
      (∫a:ℝ in (k:ℝ)..u,Constructor.phase frequency a)=∫a:ℝ in (0:ℝ)..u,Constructor.phase frequency a :=
    intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable _ _) (continuous.intervalIntegrable _ _)
  have tail:‖∫a:ℝ in (k:ℝ)..u,Constructor.phase frequency a‖≤1 := by
    exact (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun a _=>(phase_norm frequency a).le)).trans (by simpa using distance)
  rw [weightedCut_read N x frequency nonzero]
  change ‖(∑n∈Finset.Icc 1 k,Constructor.phase frequency n)-∫a:ℝ in (0:ℝ)..u,Constructor.phase frequency a‖≤_
  rw [←adjacent,sub_add_eq_sub_sub]
  have scaled : (2*Real.pi*|frequency|)*(k:ℝ)≤(2*Real.pi*|frequency|)*(q/|x|) :=
    mul_le_mul_of_nonneg_left cutoff (by positivity)
  exact ((norm_sub_le _ _).trans (add_le_add (phase_sum_error frequency k) tail)).trans
    (by nlinarith [scaled])

theorem weightedCut_eventually (x frequency:ℝ) (nonzero:x≠0) :
    ∀ᶠ N:ℕ in atTop,weightedCut N x frequency=weightedLimit x frequency := by
  filter_upwards [eventually_gt_atTop ⌊q/|x|⌋₊] with N after
  have before:q/|x|<(N:ℝ):=(Nat.lt_floor_add_one (q/|x|)).trans_le (by exact_mod_cast after)
  rw [weightedCut_read N x frequency nonzero,min_eq_left (by omega:⌊q/|x|⌋₊≤N-1),min_eq_right before.le]
  rfl

def finiteKernel (N:ℕ) (x y:ℝ) : ℂ := weightedCut N x (x*y)-weightedCut N y (x*y)
def limitKernel (x y:ℝ) : ℂ := weightedLimit x (x*y)-weightedLimit y (x*y)

theorem finiteKernel_eventually (x y:ℝ) (nonzeroX:x≠0) (nonzeroY:y≠0) :
    ∀ᶠ N:ℕ in atTop,finiteKernel N x y=limitKernel x y := by
  filter_upwards [weightedCut_eventually x (x*y) nonzeroX,weightedCut_eventually y (x*y) nonzeroY]
    with N first second
  exact congrArg₂ (·-·) first second

theorem finiteKernel_bound (N:ℕ) (x y:ℝ) (insideX:x∈symmetricInterval q)
    (insideY:y∈symmetricInterval q) (nonzeroX:x≠0) (nonzeroY:y≠0) :
    ‖finiteKernel N x y‖≤2+4*Real.pi*q^2 := by
  have first:=weightedCut_bound N x (x*y) nonzeroX
  have second:=weightedCut_bound N y (x*y) nonzeroY
  have xBound:=abs_le.mpr insideX
  have yBound:=abs_le.mpr insideY
  have firstScale:|x*y| *(q/|x|)=q*|y| := by rw [abs_mul];field_simp [abs_ne_zero.mpr nonzeroX]
  have secondScale:|x*y| *(q/|y|)=q*|x| := by rw [abs_mul];field_simp [abs_ne_zero.mpr nonzeroY]
  rw [mul_assoc (2*Real.pi),firstScale] at first
  rw [mul_assoc (2*Real.pi),secondScale] at second
  exact (norm_sub_le _ _).trans (by nlinarith [Real.pi_pos])


local instance : IsFiniteMeasure μq :=
  ⟨lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)⟩

private theorem weightedCut_measurable (N:ℕ) :
    Measurable (fun p:ℝ×ℝ=>weightedCut N p.1 p.2) := by
  have phaseJoint : Measurable (fun p:(ℝ×ℝ)×ℝ=>Constructor.phase p.1.2 p.2) := by
    unfold Constructor.phase
    fun_prop
  have seedJoint := ConstantDual.seedRaw_measurable.comp
    (show Measurable (fun p:(ℝ×ℝ)×ℝ=>p.2*p.1.1) by fun_prop)
  have normalization : Measurable (fun p:ℝ×ℝ=>∫a:ℝ in Ioc 0 (N:ℝ),
      Constructor.phase p.2 a*ConstantDual.seedRaw (a*p.1)) :=
    (phaseJoint.mul seedJoint).stronglyMeasurable.integral_prod_right'.measurable
  apply Measurable.sub _ normalization
  apply Finset.measurable_sum
  intro n _
  have phaseFixed : Measurable (fun p:ℝ×ℝ=>Constructor.phase p.2 n) := by
    unfold Constructor.phase
    fun_prop
  exact phaseFixed.mul (ConstantDual.seedRaw_measurable.comp (by fun_prop))

private theorem mixed_measurable (f:ℝ→ℝ→ℂ) (measured:Measurable (fun p:ℝ×ℝ=>f p.1 p.2)) :
    Measurable (fun p:ℝ×ℝ=>f p.1 (p.1*p.2)-f p.2 (p.1*p.2)) := by
  have first:=measured.comp (show Measurable (fun p:ℝ×ℝ=>(p.1,p.1*p.2)) from
    measurable_fst.prodMk (measurable_fst.mul measurable_snd))
  have second:=measured.comp (show Measurable (fun p:ℝ×ℝ=>(p.2,p.1*p.2)) from
    measurable_snd.prodMk (measurable_fst.mul measurable_snd))
  exact first.sub second

private theorem finiteKernel_measurable (N:ℕ) :
    Measurable (fun p:ℝ×ℝ=>finiteKernel N p.1 p.2) :=
  mixed_measurable (weightedCut N) (weightedCut_measurable N)

/-- Axis values are chosen only as an AE representative; the finite source itself is not changed. -/
private def cleanKernel (N:ℕ) (x y:ℝ) : ℂ := if x=0 ∨ y=0 then 0 else finiteKernel N x y
private def cleanLimitKernel (x y:ℝ) : ℂ := if x=0 ∨ y=0 then 0 else limitKernel x y
private def kernelBound : ℝ := 2+4*Real.pi*q^2

private theorem kernelBound_pos : 0<kernelBound := by unfold kernelBound;positivity

private theorem cleanKernel_measurable (N:ℕ) :
    Measurable (fun p:ℝ×ℝ=>cleanKernel N p.1 p.2) := by
  unfold cleanKernel
  exact Measurable.ite ((measurableSet_eq_fun measurable_fst measurable_const).union
    (measurableSet_eq_fun measurable_snd measurable_const)) measurable_const (finiteKernel_measurable N)

private theorem cleanKernel_eventually (x y:ℝ) :
    ∀ᶠ N:ℕ in atTop,cleanKernel N x y=cleanLimitKernel x y := by
  by_cases axis:x=0 ∨ y=0
  · exact Eventually.of_forall (fun _=>by simp only [cleanKernel,cleanLimitKernel,if_pos axis])
  · filter_upwards [finiteKernel_eventually x y (fun h=>axis (Or.inl h)) (fun h=>axis (Or.inr h))]
      with N same
    simpa only [cleanKernel,cleanLimitKernel,if_neg axis] using same

private theorem cleanLimitKernel_measurable : Measurable (fun p:ℝ×ℝ=>cleanLimitKernel p.1 p.2) := by
  apply measurable_of_tendsto_metrizable cleanKernel_measurable
  apply tendsto_pi_nhds.mpr
  intro p
  exact tendsto_const_nhds.congr' ((cleanKernel_eventually p.1 p.2).mono (fun _ h=>h.symm))

private theorem cleanKernel_bound (N:ℕ) (x y:ℝ) (insideX:x∈symmetricInterval q)
    (insideY:y∈symmetricInterval q) : ‖cleanKernel N x y‖≤kernelBound := by
  by_cases axis:x=0 ∨ y=0
  · simp only [cleanKernel,if_pos axis,norm_zero]
    exact kernelBound_pos.le
  · rw [cleanKernel,if_neg axis]
    exact finiteKernel_bound N x y insideX insideY (fun h=>axis (Or.inl h)) (fun h=>axis (Or.inr h))

private theorem cleanLimitKernel_bound (x y:ℝ) (insideX:x∈symmetricInterval q)
    (insideY:y∈symmetricInterval q) : ‖cleanLimitKernel x y‖≤kernelBound := by
  obtain ⟨N,same⟩:=(cleanKernel_eventually x y).exists
  rw [←same]
  exact cleanKernel_bound N x y insideX insideY

private def kernelRow (N:ℕ) (state:Hq) (x:ℝ) : ℂ :=
  ∫y:ℝ,cleanKernel N x y*state y ∂μq
private def kernelRowLimit (state:Hq) (x:ℝ) : ℂ :=
  ∫y:ℝ,cleanLimitKernel x y*state y ∂μq
private def rowBound (state:Hq) : ℝ := kernelBound*(∫y:ℝ,‖state y‖ ∂μq)

private theorem state_integrable (state:Hq) : Integrable (state:ℝ→ℂ) μq :=
  MemLp.integrable (by norm_num) (Lp.memLp state)

private theorem kernelRow_measurable (N:ℕ) (state:Hq) : Measurable (kernelRow N state) :=
  ((cleanKernel_measurable N).mul ((Lp.stronglyMeasurable state).measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

private theorem kernelRowLimit_measurable (state:Hq) : Measurable (kernelRowLimit state) :=
  (cleanLimitKernel_measurable.mul ((Lp.stronglyMeasurable state).measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

private theorem kernelRow_bound (N:ℕ) (state:Hq) (x:ℝ) (inside:x∈symmetricInterval q) :
    ‖kernelRow N state x‖≤rowBound state := by
  have bound:=norm_integral_le_of_norm_le ((state_integrable state).norm.const_mul kernelBound)
    (f:=fun y=>cleanKernel N x y*state y) (by
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y inY
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (cleanKernel_bound N x y inside inY) (norm_nonneg _))
  simpa only [kernelRow,rowBound,integral_const_mul] using bound

private theorem kernelRowLimit_bound (state:Hq) (x:ℝ) (inside:x∈symmetricInterval q) :
    ‖kernelRowLimit state x‖≤rowBound state := by
  have bound:=norm_integral_le_of_norm_le ((state_integrable state).norm.const_mul kernelBound)
    (f:=fun y=>cleanLimitKernel x y*state y) (by
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y inY
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (cleanLimitKernel_bound x y inside inY) (norm_nonneg _))
  simpa only [kernelRowLimit,rowBound,integral_const_mul] using bound

private theorem kernelRow_tendsto (state:Hq) (x:ℝ) (inside:x∈symmetricInterval q) :
    Tendsto (fun N=>kernelRow N state x) atTop (𝓝 (kernelRowLimit state x)) := by
  apply tendsto_integral_of_dominated_convergence (fun y=>kernelBound*‖state y‖)
    (F:=fun N y=>cleanKernel N x y*state y) (f:=fun y=>cleanLimitKernel x y*state y)
    (fun N=>((cleanKernel_measurable N).comp (measurable_const.prodMk measurable_id)).mul
      (Lp.stronglyMeasurable state).measurable |>.aestronglyMeasurable)
    ((state_integrable state).norm.const_mul kernelBound)
  · intro N
    filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y inY
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (cleanKernel_bound N x y inside inY) (norm_nonneg _)
  · filter_upwards with y
    exact (tendsto_const_nhds.congr' ((cleanKernel_eventually x y).mono (fun _ h=>h.symm))).mul_const (state y)

private theorem kernelRow_memLp (N:ℕ) (state:Hq) : MemLp (kernelRow N state) 2 μq :=
  MemLp.of_bound (kernelRow_measurable N state).aestronglyMeasurable (rowBound state)
    ((ae_restrict_mem (measurableSet_symmetricInterval q)).mono (fun x inside=>kernelRow_bound N state x inside))

private theorem kernelRowLimit_memLp (state:Hq) : MemLp (kernelRowLimit state) 2 μq :=
  MemLp.of_bound (kernelRowLimit_measurable state).aestronglyMeasurable (rowBound state)
    ((ae_restrict_mem (measurableSet_symmetricInterval q)).mono (fun x inside=>kernelRowLimit_bound state x inside))

private def kernelValue (N:ℕ) (state:Hq) : Hq := (kernelRow_memLp N state).toLp (kernelRow N state)
def crossLimit (state:Hq) : Hq := (kernelRowLimit_memLp state).toLp (kernelRowLimit state)

private theorem kernelValue_tendsto (state:Hq) : Tendsto (fun N=>kernelValue N state) atTop (𝓝 (crossLimit state)) := by
  have squareLimit:Tendsto (fun N=>∫x:ℝ,‖kernelRow N state x-kernelRowLimit state x‖^2 ∂μq) atTop (𝓝 0) := by
    have limit:=tendsto_integral_of_dominated_convergence (μ:=μq) (fun _:ℝ=>4*(rowBound state)^2)
      (F:=fun N x=>‖kernelRow N state x-kernelRowLimit state x‖^2) (f:=fun _=>(0:ℝ))
      (fun N=>(((kernelRow_measurable N state).sub (kernelRowLimit_measurable state)).norm.pow_const 2).aestronglyMeasurable)
      (integrable_const _) ?_ ?_
    · simpa using limit
    · intro N
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have bound:‖kernelRow N state x-kernelRowLimit state x‖≤2*rowBound state :=
        (norm_sub_le _ _).trans (by linarith [kernelRow_bound N state x inside,kernelRowLimit_bound state x inside])
      nlinarith [norm_nonneg (kernelRow N state x-kernelRowLimit state x)]
    · filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
      simpa using ((kernelRow_tendsto state x inside).sub (tendsto_const_nhds (x:=kernelRowLimit state x))).norm.pow 2
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun N=>kernelRow N state)
    (fun N=>kernelRow_memLp N state) (kernelRowLimit state) (kernelRowLimit_memLp state)).mpr
  have rootLimit:=squareLimit.rpow_const (p:=(2:ℝ)⁻¹) (Or.inr (by norm_num))
  have limit:=ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using rootLimit)
  convert limit using 1
  · ext N
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((kernelRow_memLp N state).sub (kernelRowLimit_memLp state))]
    simp
  · simp

private theorem quarter_integral_read (μ:Measure ℝ) [SFinite μ]
    (family:ℝ→Hq) (integrable:Integrable family μ) (raw:ℝ×ℝ→ℂ)
    (measured:Measurable raw)
    (reads:∀ᵐ a ∂μ,(family a:ℝ→ℂ)=ᵐ[μq] fun x=>raw (a,x)) :
    ((∫a,family a ∂μ:Hq):ℝ→ℂ)=ᵐ[μq] fun x=>∫a,raw (a,x) ∂μ := by
  classical
  let extended:ℝ×ℝ→ℂ:=fun p=>(symmetricInterval q).indicator (fun x=>raw (p.1,x)) p.2
  have joint:Measurable extended := by
    change Measurable (fun p:ℝ×ℝ=>if p.2∈symmetricInterval q then raw p else 0)
    exact Measurable.ite ((measurableSet_symmetricInterval q).preimage measurable_snd) measured measurable_const
  have sourceReads:∀ᵐ a ∂μ,(E (family a):ℝ→ℂ)=ᵐ[volume] fun x=>extended (a,x) := by
    filter_upwards [reads] with a source
    have localRead:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp source
    filter_upwards [burnolQuarterZeroExtension_coe (family a),localRead] with x extension actual
    rw [extension]
    by_cases inside:x∈symmetricInterval q
    · simp only [extended,indicator_of_mem inside,actual inside]
    · simp only [extended,indicator_of_notMem inside]
  have source:=source_l2_bochner_coeFn μ (fun a=>E (family a)) ((E).integrable_comp integrable)
    extended joint sourceReads
  rw [(E).integral_comp_comm integrable] at source
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (E (∫a,family a ∂μ)),
    ae_restrict_of_ae source,ae_restrict_mem (measurableSet_symmetricInterval q)]
    with x restricted actual inside
  change Rq (E (∫a,family a ∂μ)) x=E (∫a,family a ∂μ) x at restricted
  rw [burnolQuarterRestriction_zeroExtension] at restricted
  rw [restricted,actual]
  apply integral_congr_ae
  filter_upwards with a
  exact indicator_of_mem inside _

private def cellKernel (a x y:ℝ) : ℂ :=
  Constructor.phase (x*y) a*(ConstantDual.seedRaw (a*x)-ConstantDual.seedRaw (a*y))

private theorem seed_norm (x:ℝ) : ‖ConstantDual.seedRaw x‖≤1 := by
  unfold ConstantDual.seedRaw
  split <;> norm_num

private theorem cellKernel_bound (a x y:ℝ) : ‖cellKernel a x y‖≤2 := by
  rw [cellKernel,norm_mul,phase_norm,one_mul]
  exact (norm_sub_le _ _).trans (by linarith [seed_norm (a*x),seed_norm (a*y)])

private theorem cellKernel_measurable : Measurable (fun p:ℝ×(ℝ×ℝ)=>cellKernel p.1 p.2.1 p.2.2) := by
  have phaseJoint:Measurable (fun p:ℝ×(ℝ×ℝ)=>Constructor.phase (p.2.1*p.2.2) p.1) := by
    unfold Constructor.phase
    fun_prop
  exact phaseJoint.mul ((ConstantDual.seedRaw_measurable.comp (by fun_prop)).sub
    (ConstantDual.seedRaw_measurable.comp (by fun_prop)))

private theorem cell_state_integrable (a x:ℝ) (state:Hq) :
    Integrable (fun y=>cellKernel a x y*state y) μq := by
  apply ((state_integrable state).norm.const_mul 2).mono'
  · exact ((cellKernel_measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
      (Lp.stronglyMeasurable state).measurable).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (cellKernel_bound a x y) (norm_nonneg _)

private theorem phase_state_integrable (a x:ℝ) (state:Hq) :
    Integrable (fun y=>Constructor.phase (a*x) y*state y) μq := by
  apply (state_integrable state).norm.mono'
  · exact ((Constructor.phaseContinuous (a*x)).measurable.mul (Lp.stronglyMeasurable state).measurable).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul,phase_norm,one_mul]

private theorem crossRaw_cell (a:ℝ) (positive:0<a) (state:Hq) (x:ℝ) :
    crossRaw a state x=∫y:ℝ,cellKernel a x y*state y ∂μq := by
  have phaseRead (y:ℝ):Constructor.phase (a*x) y=Constructor.phase (x*y) a := by
    unfold Constructor.phase
    rw [show -((a*x)*y)= -((x*y)*a) by ring]
  have incidence (y:ℝ):|a*y|≤q ↔ y∈symmetricInterval (q/a) := by
    rw [symmetricInterval,mem_Icc,←abs_le,abs_mul,abs_of_pos positive,le_div_iff₀ positive]
    rw [mul_comm a]
  have first:=phase_state_integrable a x state
  have second:Integrable (fun y=>Constructor.phase (a*x) y*((symmetricInterval (q/a)).indicator state) y) μq := by
    apply (state_integrable state).norm.mono'
    · exact ((Constructor.phaseContinuous (a*x)).measurable.mul
        ((Lp.stronglyMeasurable state).measurable.indicator (measurableSet_symmetricInterval (q/a)))).aestronglyMeasurable
    · filter_upwards with y
      rw [norm_mul,phase_norm,one_mul]
      exact norm_indicator_le_norm_self _ _
  rw [crossRaw_integral]
  by_cases inside:x∈symmetricInterval (q/a)
  · rw [indicator_of_mem inside,intervalIntegral.integral_of_le (by norm_num:(-q:ℝ)≤q),
      intervalIntegral.integral_of_le (by norm_num:(-q:ℝ)≤q),←integral_Icc_eq_integral_Ioc,
      ←integral_Icc_eq_integral_Ioc]
    change (∫y:ℝ,Constructor.phase (a*x) y*state y ∂μq)-
      (∫y:ℝ,Constructor.phase (a*x) y*((symmetricInterval (q/a)).indicator state) y ∂μq)=_
    rw [←integral_sub first second]
    apply integral_congr_ae
    filter_upwards with y
    by_cases inner:y∈symmetricInterval (q/a)
    · simp only [cellKernel,ConstantDual.seedRaw,if_pos ((incidence x).mpr inside),
        if_pos ((incidence y).mpr inner),indicator_of_mem inner,sub_self,mul_zero,zero_mul]
    · simp only [cellKernel,ConstantDual.seedRaw,if_pos ((incidence x).mpr inside),
        if_neg (fun h=>inner ((incidence y).mp h)),indicator_of_notMem inner,sub_zero,mul_zero,
        mul_one,phaseRead]
  · rw [indicator_of_notMem inside,zero_sub,intervalIntegral.integral_of_le (by norm_num:(-q:ℝ)≤q),
      ←integral_Icc_eq_integral_Ioc,←integral_neg]
    apply integral_congr_ae
    filter_upwards with y
    by_cases inner:y∈symmetricInterval (q/a)
    · simp only [cellKernel,ConstantDual.seedRaw,if_neg (fun h=>inside ((incidence x).mp h)),
        if_pos ((incidence y).mpr inner),indicator_of_mem inner,zero_sub,mul_neg,mul_one,
        neg_mul,phaseRead]
    · simp only [cellKernel,ConstantDual.seedRaw,if_neg (fun h=>inside ((incidence x).mp h)),
        if_neg (fun h=>inner ((incidence y).mp h)),indicator_of_notMem inner,sub_self,mul_zero,zero_mul,neg_zero]

private theorem scale_finite (N:ℕ) : IsFiniteMeasure (volume.restrict (Ioc 0 (N:ℝ))) :=
  ⟨by rw [Measure.restrict_apply_univ];exact measure_Ioc_lt_top⟩

private theorem weighted_scale_integrable (N:ℕ) (x frequency:ℝ) :
    IntegrableOn (fun a=>Constructor.phase frequency a*ConstantDual.seedRaw (a*x)) (Ioc 0 (N:ℝ)) := by
  let : IsFiniteMeasure (volume.restrict (Ioc 0 (N:ℝ))) := scale_finite N
  apply (integrable_const (1:ℝ)).mono'
  · exact ((Constructor.phaseContinuous frequency).measurable.mul
      (ConstantDual.seedRaw_measurable.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with a
    rw [norm_mul,phase_norm,one_mul]
    exact seed_norm _

private theorem finiteKernel_cells (N:ℕ) (x y:ℝ) :
    finiteKernel N x y=(∑n∈Finset.Ico 1 N,cellKernel n x y)-
      ∫a:ℝ in Ioc 0 (N:ℝ),cellKernel a x y := by
  unfold finiteKernel weightedCut cellKernel
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,integral_sub (weighted_scale_integrable N x (x*y))
    (weighted_scale_integrable N y (x*y))]
  ring

private theorem cell_state_joint_integrable (N:ℕ) (x:ℝ) (state:Hq) :
    Integrable (fun p:ℝ×ℝ=>cellKernel p.1 x p.2*state p.2)
      ((volume.restrict (Ioc 0 (N:ℝ))).prod μq) := by
  let : IsFiniteMeasure (volume.restrict (Ioc 0 (N:ℝ))) := scale_finite N
  apply (((state_integrable state).norm.const_mul 2).comp_snd (volume.restrict (Ioc 0 (N:ℝ)))).mono'
  · exact ((cellKernel_measurable.comp (measurable_fst.prodMk
      (measurable_const.prodMk measurable_snd))).mul
      ((Lp.stronglyMeasurable state).measurable.comp measurable_snd)).aestronglyMeasurable
  · filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (cellKernel_bound p.1 x p.2) (norm_nonneg _)

private theorem raw_row_source (N:ℕ) (state:Hq) (x:ℝ) :
    (∑n∈Finset.Ico 1 N,∫y:ℝ,cellKernel n x y*state y ∂μq)-
      (∫a:ℝ in Ioc 0 (N:ℝ),∫y:ℝ,cellKernel a x y*state y ∂μq)=
      ∫y:ℝ,finiteKernel N x y*state y ∂μq := by
  have sumIntegrable:∀n∈Finset.Ico 1 N,Integrable (fun y=>cellKernel n x y*state y) μq :=
    fun n _=>cell_state_integrable n x state
  have joint:=cell_state_joint_integrable N x state
  rw [integral_integral_swap joint,←integral_finsetSum _ sumIntegrable,
    ←integral_sub (integrable_finsetSum _ sumIntegrable) joint.integral_prod_right]
  apply integral_congr_ae
  filter_upwards with y
  rw [finiteKernel_cells,sub_mul,Finset.sum_mul,integral_mul_const]

private theorem source_row_measurable (kernel:ℝ×(ℝ×ℝ)→ℂ)
    (measured:Measurable kernel) (value:ℝ→ℂ) (valueMeasured:Measurable value) :
    Measurable (fun p:ℝ×ℝ=>∫y:ℝ,kernel (p.1,(p.2,y))*value y ∂μq) := by
  have reordered:=measured.comp (show Measurable (fun p:(ℝ×ℝ)×ℝ=>(p.1.1,(p.1.2,p.2))) from
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact (reordered.mul (valueMeasured.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

private theorem cell_row_joint_measurable (state:Hq) :
    Measurable (fun p:ℝ×ℝ=>∫y:ℝ,cellKernel p.1 p.2 y*state y ∂μq) :=
  source_row_measurable (fun p=>cellKernel p.1 p.2.1 p.2.2) cellKernel_measurable
    state (Lp.stronglyMeasurable state).measurable

private theorem crossSource_kernelRow (N:ℕ) (state:Hq) :
    (crossSource N state:ℝ→ℂ)=ᵐ[μq] kernelRow N state := by
  have normalization:=quarter_integral_read (volume.restrict (Ioc 0 (N:ℝ)))
    (fun a=>crossWindow a state) (crossWindow_integrable N state)
    (fun p:ℝ×ℝ=>∫y:ℝ,cellKernel p.1 p.2 y*state y ∂μq)
    (cell_row_joint_measurable state) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
      filter_upwards [crossWindow_raw a inside.1 state] with x source
      exact source.trans (crossRaw_cell a inside.1 state x))
  have channels:∀ᵐ x:ℝ ∂μq,∀n:{n:ℕ//n∈Finset.Ico 1 N},
      crossWindow n state x=∫y:ℝ,cellKernel n x y*state y ∂μq := by
    apply ae_all_iff.mpr
    intro n
    have positive:0<(n:ℝ):=by exact_mod_cast (Finset.mem_Ico.mp n.property).1
    filter_upwards [crossWindow_raw n positive state] with x source
    exact source.trans (crossRaw_cell n positive state x)
  filter_upwards [Lp.coeFn_sub (∑n∈Finset.Ico 1 N,crossWindow n state)
      (∫a:ℝ in Ioc 0 (N:ℝ),crossWindow a state),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n=>crossWindow n state),normalization,channels,
    ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x difference summed average channel nonzero
  change ((∑n∈Finset.Ico 1 N,crossWindow n state)-∫a:ℝ in Ioc 0 (N:ℝ),crossWindow a state:Hq) x=_
  rw [difference,Pi.sub_apply,summed,average]
  have finite:(∑n∈Finset.Ico 1 N,crossWindow n state x)=
      ∑n∈Finset.Ico 1 N,∫y:ℝ,cellKernel n x y*state y ∂μq :=
    Finset.sum_congr rfl (fun n inside=>channel ⟨n,inside⟩)
  rw [finite,raw_row_source]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with y nonzeroY
  simp only [cleanKernel,if_neg (not_or.mpr ⟨nonzero,nonzeroY⟩)]

/-- The strong limit is consumed by the original source, not assigned to an equal-valued replacement. -/
theorem crossSource_tendsto (state:Hq) : Tendsto (fun N=>crossSource N state) atTop (𝓝 (crossLimit state)) := by
  have actual (N:ℕ):crossSource N state=kernelValue N state := by
    apply Lp.ext
    exact (crossSource_kernelRow N state).trans (kernelRow_memLp N state).coeFn_toLp.symm
  simp_rw [actual]
  exact kernelValue_tendsto state


local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Q" => Constructor.zeroMean
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "sinc" => CenteredCountingDual.constantFourier
local notation "h" => NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn
local notation "hSecond" => NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource.hPowerBSecond
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def countedUnitLimit : M := Q (Rq ConstantDual.value)

theorem countedUnit_tendsto : Tendsto countedUnit atTop (𝓝 countedUnitLimit) := by
  exact (((Q).comp Rq).continuous.tendsto ConstantDual.value).comp ConstantDual.original_tendsto

def oppositeLimit (state:M) : M :=
  Q (crossLimit (state:Hq))-(2*inner ℂ sinc state) • countedUnitLimit+
    (2*inner ℂ countedUnitLimit state) • sinc

theorem oppositeSource_tendsto (state:M) :
    Tendsto (fun N=>oppositeSource N state) atTop (𝓝 (oppositeLimit state)) := by
  have crossed:=((Q).continuous.tendsto (crossLimit (state:Hq))).comp (crossSource_tendsto (state:Hq))
  have unit:=countedUnit_tendsto
  exact (crossed.sub (unit.const_smul (2*inner ℂ sinc state))).add
    (((unit.inner tendsto_const_nhds).const_mul 2).smul_const sinc)

def firstLimit (coordinate:BurnolCompletedMellinCoordinate) : M :=
  BI (logSource coordinate+S (oppositeLimit (h coordinate))+rankSource (S (h coordinate)))

def secondLimit (coordinate:BurnolCompletedMellinCoordinate) : M :=
  -S (firstLimit coordinate)-oppositeLimit (h coordinate)

/-- The original zero-qualified power source, explicit crossing limit, and old rank source generate both counted feet. -/
theorem resolvedFirst_tendsto (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N=>resolvedFirst N coordinate) atTop (𝓝 (firstLimit coordinate)) := by
  have power:Tendsto (fun N=>powerSource N coordinate) atTop (𝓝 (logSource coordinate)) := by
    apply (original_zero_power_limit coordinate zero).congr'
    filter_upwards [eventually_ge_atTop 1] with N positive
    exact actual_power_source N (by omega) coordinate
  have opposite:=((S).continuous.tendsto (oppositeLimit (h coordinate))).comp (oppositeSource_tendsto (h coordinate))
  exact ((BI).continuous.tendsto _).comp ((power.add opposite).add_const (rankSource (S (h coordinate))))

theorem resolvedSecond_tendsto (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N=>resolvedSecond N coordinate) atTop (𝓝 (secondLimit coordinate)) := by
  exact (((S).continuous.tendsto _).comp (resolvedFirst_tendsto coordinate zero)).neg.sub
    (oppositeSource_tendsto (h coordinate))

/-- These are the literal original finite counting outputs on h and -S h; the strong limit is not an input. -/
theorem actual_counted_feet_tendsto (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N=>CenteredCountingDual.forward N (h coordinate)) atTop (𝓝 (firstLimit coordinate)) ∧
    Tendsto (fun N=>CenteredCountingDual.reverse N (hSecond coordinate)) atTop (𝓝 (secondLimit coordinate)) := by
  constructor
  · apply (resolvedFirst_tendsto coordinate zero).congr'
    filter_upwards [eventually_ge_atTop 1] with N positive
    exact resolvedFirst_actual N (by omega) coordinate
  · apply (resolvedSecond_tendsto coordinate zero).congr'
    filter_upwards [eventually_ge_atTop 1] with N positive
    exact resolvedSecond_actual N (by omega) coordinate

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
