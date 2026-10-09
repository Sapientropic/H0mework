import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYLiteralDynamicDefect
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCutoffSharpCore
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicSourceNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussNativeForm GaussNativePotential GaussRadialDomain GaussYukawaOperator GaussYukawaCoefficient
open GaussDensityCore GaussFockWeights GaussBoundedMultiplier
open GaussUnitaryHistory FullYDynamicSource FullYSourceCutoffVolterra FullYSourceCutoffSharp
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] sourcePair embed diagonalAction originalAction GaussFullHamiltonian.adjointAction

/-- A finite source subspace generates its own radius bound; no support cover is supplied. -/
theorem finite_source_radius(S:Submodule ℂ QuantumTest)[FiniteDimensional ℂ S]:
    ∃R:ℝ,1≤R ∧ ∀q:S,∀z:SourceCoordinateSlice,q.val z≠0 → radius z≤R:=by
  classical
  let b:=Module.finBasis ℂ S
  have hb(i:Fin (Module.finrank ℂ S)):
      ∃R:ℝ,1≤R ∧ ∀z:SourceCoordinateSlice,(b i).val z≠0 → radius z≤R:=by
    obtain ⟨R,hR⟩:=(b i).val.hasCompactSupport.bddAbove_image radius_smooth.continuous.continuousOn
    refine ⟨max 1 R,le_max_left _ _,fun z hz=>?_⟩
    exact (hR (Set.mem_image_of_mem radius (subset_tsupport _ hz))).trans (le_max_right _ _)
  choose B hB hbound using hb
  let R:=1+∑i:Fin (Module.finrank ℂ S),B i
  have hBi(i:Fin (Module.finrank ℂ S)):B i≤R:=by
    have hi:B i≤∑j:Fin (Module.finrank ℂ S),B j:=
      Finset.single_le_sum (fun j _=>(zero_le_one.trans (hB j))) (Finset.mem_univ i)
    dsimp only [R]
    linarith
  have hsum:0≤∑i:Fin (Module.finrank ℂ S),B i:=
    Finset.sum_nonneg (fun i _=>zero_le_one.trans (hB i))
  refine ⟨R,by dsimp only [R];linarith,?_⟩
  intro q z hz
  by_contra hr
  have hg(i:Fin (Module.finrank ℂ S)):(b i).val z=0:=by
    by_contra hn
    exact hr ((hbound i z hn).trans (hBi i))
  let ev:S→ₗ[ℂ]FockFiber:={
    toFun:=fun q=>q.val z
    map_add':=fun q r=>by simp only [Submodule.coe_add,add_apply]
    map_smul':=fun c q=>by simp only [Submodule.coe_smul,smul_apply,RingHom.id_apply] }
  have he:ev=0:=by
    apply b.ext
    intro i
    exact hg i
  exact hz (LinearMap.congr_fun he q)

private theorem multiply_local_bound(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest)(C:ℝ)(hC:0≤C)
    (h:∀z:SourceCoordinateSlice,f z≠0 → |c z|≤C):
    ‖embed (multiply c hc f)‖≤C*‖embed f‖:=by
  let g:=multiply c hc f
  have hp(z:SourceCoordinateSlice):RCLike.re (densityPair g g z)≤C^2*RCLike.re (densityPair f f z):=by
    by_cases hf:f z=0
    · have hg:g z=0:=by simp only [g,multiply_apply,hf,smul_zero]
      simp only [densityPair,hg,hf,map_zero,inner_zero_left,map_zero,mul_zero,le_refl]
    · have hz:z∈physicalChart:=f.tsupport_subset (subset_tsupport _ hf)
      have pos:0≤RCLike.re (densityPair f f z):=by
        change 0≤RCLike.re (inner ℂ (weight (fun N=>(density N z:ℂ)) (f z)) (f z))
        rw [weighted_square (fun N=>density N z) (fun N=>(density_pos N ⟨z,hz⟩).le)]
        exact sq_nonneg _
      have hs:(c z)^2≤C^2:=by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (c z)) (h z hf) 2
      have he:RCLike.re (densityPair g g z)=(c z)^2*RCLike.re (densityPair f f z):=by
        simp only [densityPair,g,multiply_apply,map_smul,inner_smul_left,inner_smul_right,
          Complex.conj_ofReal,←mul_assoc]
        rw [←pow_two,←Complex.ofReal_pow]
        exact RCLike.re_ofReal_mul _ _
      rw [he]
      exact mul_le_mul_of_nonneg_right hs pos
  have hs:‖embed g‖^2≤C^2*‖embed f‖^2:=by
    calc
      _=∫z,RCLike.re (densityPair g g z) ∂GaussHistoryHilbert.configurationMeasure:=norm_square_integral g
      _≤∫z,C^2*RCLike.re (densityPair f f z) ∂GaussHistoryHilbert.configurationMeasure:=
        integral_mono (densityPair_integrable g g).re ((densityPair_integrable f f).re.const_mul _) hp
      _=_:=by rw [integral_const_mul,←norm_square_integral]
  nlinarith [norm_nonneg (embed g),mul_nonneg hC (norm_nonneg (embed f))]

def radialTailCore(n:ℕ):End:=multiply (fun z=>(1-reciprocal z)^n)
  (fun _=>((contDiff_const.sub reciprocal_smooth).pow n).contDiffAt)
private theorem tail_core(n:ℕ)(f:QuantumTest):
    ((1-inverseRadius)^n) (embed f)=embed (radialTailCore n f):=by
  induction n generalizing f with
  | zero =>
    apply congrArg embed
    apply DFunLike.ext
    intro z
    simp only [radialTailCore,multiply_apply,pow_zero,Complex.ofReal_one,one_smul]
  | succ n ih =>
    rw [pow_succ']
    change (1-inverseRadius) (((1-inverseRadius)^n) (embed f))=_
    rw [ih]
    simp only [sub_apply,one_apply_eq_self,inverse_core,←map_sub]
    apply congrArg embed
    apply DFunLike.ext
    intro z
    simp only [radialTailCore,inverseAction,sub_apply,multiply_apply]
    rw [smul_smul,←sub_smul,pow_succ']
    congr 1
    push_cast
    ring

def cutoffBranch(sharp:Bool)(n:ℕ):H→L[ℂ]H:=if sharp then (cutoff n).adjoint else cutoff n
private theorem recurrence_residual {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
    (S B:E→L[ℂ]E)(K:ℕ→E→L[ℂ]E)(h0:K 0=B)
    (hstep:∀n,K (n+1)=B+(1-S)*K n)(x y:E)(hg:B x=S y)(n:ℕ):
    y-K n x=((1-S)^(n+1)) y:=by
  induction n with
  | zero =>
    rw [h0,hg,pow_one]
    simp only [sub_apply,one_apply_eq_self]
  | succ n ih =>
    rw [hstep,add_apply,mul_apply_eq_comp,hg,pow_succ']
    change y-(S y+(1-S) (K n x))=(1-S) (((1-S)^(n+1)) y)
    rw [←ih]
    simp only [sub_apply,one_apply_eq_self,map_sub]
    abel
private theorem original_graph_residual(n:ℕ)(f:QuantumTest):
    embed (originalAction f)-cutoff n (embed f)=((1-inverseRadius)^(n+1)) (embed (originalAction f)):=
  recurrence_residual inverseRadius bounded cutoff rfl (fun _=>rfl) _ _ (original_graph f) n
private theorem tail_pair(n:ℕ)(f g:QuantumTest):
    sourcePair f (radialTailCore n g)=sourcePair (radialTailCore n f) g:=
  multiply_pair _ _ f g
private theorem tail_sharp_commute(n:ℕ)(f:QuantumTest):
    GaussFullHamiltonian.adjointAction (radialTailCore n f)=
      radialTailCore n (GaussFullHamiltonian.adjointAction f):=by
  apply DFunLike.ext
  intro z
  unfold GaussFullHamiltonian.adjointAction radialTailCore
  change GaussFullHamiltonian.adjointMap (scalarField z)
    ((((1-reciprocal z)^n:ℝ):ℂ) • f z) = _
  exact map_smul _ _ _

private theorem embed_pair_ext(x y:H)(h:∀g:QuantumTest,inner ℂ (embed g) x=inner ℂ (embed g) y):x=y:=by
  apply core_dense.eq_of_inner_right ℂ
  intro a
  let g:QuantumTest:=coreEquiv.symm a
  have hg:embed g=(a:H):=congrArg Subtype.val (coreEquiv.apply_symm_apply a)
  exact (congrArg (fun u:H=>inner ℂ u x) hg).symm.trans
    ((h g).trans (congrArg (fun u:H=>inner ℂ u y) hg))

theorem cutoff_core_residual(sharp:Bool)(n:ℕ)(f:QuantumTest):
    embed (sourceY sharp f)-cutoffBranch sharp n (embed f)=
      embed (radialTailCore (n+1) (sourceY sharp f)):=by
  cases sharp
  · exact (original_graph_residual n f).trans (tail_core (n+1) (originalAction f))
  · change embed (GaussFullHamiltonian.adjointAction f)-(cutoff n).adjoint (embed f)=_
    apply embed_pair_ext
    intro g
    have hY:inner ℂ (embed g) (embed (GaussFullHamiltonian.adjointAction f))=
        inner ℂ (embed (originalAction g)) (embed f):=by
      simpa only [sourcePair] using GaussFullHamiltonian.yukawa_pair g f
    have hp:= (tail_pair (n+1) (originalAction g) f).symm.trans
      ((GaussFullHamiltonian.yukawa_pair g (radialTailCore (n+1) f)).symm.trans
        (congrArg (sourcePair g) (tail_sharp_commute (n+1) f)))
    calc
      inner ℂ (embed g) (embed (GaussFullHamiltonian.adjointAction f)-(cutoff n).adjoint (embed f))=
          inner ℂ (embed (originalAction g)-cutoff n (embed g)) (embed f):=by
        simp only [inner_sub_left,inner_sub_right]
        exact congrArg₂ (·-·) hY (ContinuousLinearMap.adjoint_inner_right (cutoff n) (embed g) (embed f))
      _=inner ℂ (embed (radialTailCore (n+1) (originalAction g))) (embed f):=
        congrArg (fun v:H=>inner ℂ v (embed f)) ((original_graph_residual n g).trans (tail_core (n+1) (originalAction g)))
      _=inner ℂ (embed g) (embed (radialTailCore (n+1) (GaussFullHamiltonian.adjointAction f))):=by
        simpa only [sourcePair] using hp

private theorem radial_tail_bound(R:ℝ)(hR:1≤R)(f:QuantumTest)
    (hf:∀z:SourceCoordinateSlice,f z≠0 → radius z≤R)(n:ℕ):
    ‖embed (radialTailCore n f)‖≤(1-R⁻¹)^n*‖embed f‖:=by
  have hρ:0≤1-R⁻¹:=sub_nonneg.mpr (inv_le_one_of_one_le₀ hR)
  apply multiply_local_bound _ _ f _ (pow_nonneg hρ n)
  intro z hz
  have hq:0≤1-reciprocal z:=sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_radius z))
  rw [abs_of_nonneg (pow_nonneg hq n)]
  apply pow_le_pow_left₀ hq
  exact sub_le_sub_left (inv_anti₀ (radius_pos z) (hf z hz)) 1

/-- The actual source image generates a common geometric cutoff price for its entire carrier. -/
theorem finite_source_cutoff_price(sharp:Bool)(S:Submodule ℂ QuantumTest)[FiniteDimensional ℂ S]:
    ∃ρ:ℝ,0≤ρ ∧ ρ<1 ∧ ∀n:ℕ,∀q:S,
      ‖embed (sourceY sharp q.val)-cutoffBranch sharp n (embed q.val)‖≤
        ρ^(n+1)*‖embed (sourceY sharp q.val)‖:=by
  obtain ⟨R,hR,hbound⟩:=finite_source_radius (S.map (sourceY sharp))
  refine ⟨1-R⁻¹,sub_nonneg.mpr (inv_le_one_of_one_le₀ hR),by
    have hi:0<R⁻¹:=inv_pos.mpr (zero_lt_one.trans_le hR)
    linarith,?_⟩
  intro n q
  rw [cutoff_core_residual]
  exact radial_tail_bound R hR (sourceY sharp q.val)
    (hbound ⟨sourceY sharp q.val,Submodule.mem_map.mpr ⟨q.val,q.property,rfl⟩⟩) (n+1)

private def sourceYReader(F:Index)(sharp:Bool)(f:QuantumTest):sourceSpace F sharp f→L[ℂ]H:=
  (embed.comp ((sourceY sharp).comp ((sourceOrbit F sharp f).subtype.comp
    (sourceEquiv F sharp f).symm.toLinearMap))).toContinuousLinearMap
theorem source_y_time_continuous(F:Index)(sharp:Bool)(f:QuantumTest):
    Continuous (fun t:ℝ=>embed (sourceY sharp (literalCoreTime F sharp f t))):=by
  let A:=sourceGenerator F sharp f
  let x:=sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩
  have ht:Continuous (fun t:ℝ=>SourceFiniteUnitary.time A t x):=
    continuous_iff_continuousAt.mpr (fun t=>(SourceFiniteUnitary.time_derivative A t x).continuousAt)
  exact (sourceYReader F sharp f).continuous.comp ht

def dynamicCutoffError(F:Index)(sharp:Bool)(f:QuantumTest)(n:ℕ)(t:ℝ):ℝ:=
  ‖embed (sourceY sharp (literalCoreTime F sharp f t))-
    cutoffBranch sharp n (embed (literalCoreTime F sharp f t))‖
def dynamicYCost(F:Index)(sharp:Bool)(f:QuantumTest)(a b:ℝ):ℝ:=
  ∫t in a..b,‖embed (sourceY sharp (literalCoreTime F sharp f t))‖

theorem actual_dynamic_cutoff_geometric(F:Index)(sharp:Bool)(f:QuantumTest):
    ∃ρ:ℝ,0≤ρ ∧ ρ<1 ∧ ∀n:ℕ,∀t:ℝ,dynamicCutoffError F sharp f n t≤
      ρ^(n+1)*‖embed (sourceY sharp (literalCoreTime F sharp f t))‖:=by
  obtain ⟨ρ,hρ,hρ1,h⟩:=finite_source_cutoff_price sharp (sourceOrbit F sharp f)
  refine ⟨ρ,hρ,hρ1,fun n t=>?_⟩
  exact h n ((sourceEquiv F sharp f).symm
    (SourceFiniteUnitary.time (sourceGenerator F sharp f) t
      (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩)))

theorem dynamic_cutoff_error_continuous(F:Index)(sharp:Bool)(f:QuantumTest)(n:ℕ):
    Continuous (dynamicCutoffError F sharp f n):=by
  have ht:Continuous (fun t:ℝ=>embed (literalCoreTime F sharp f t)):=
    continuous_iff_continuousAt.mpr (fun t=>(literal_core_time_derivative F sharp f t).continuousAt)
  exact ((source_y_time_continuous F sharp f).sub ((cutoffBranch sharp n).continuous.comp ht)).norm

/-- Every polynomial cutoff loss is paid on the actual uncut source trajectory, on either time orientation. -/
theorem actual_dynamic_cutoff_weighted_L1_return(F:Index)(sharp:Bool)(f:QuantumTest)
    (a b:ℝ)(hab:a≤b)(k:ℕ):
    (∀n:ℕ,IntervalIntegrable (dynamicCutoffError F sharp f n) volume a b) ∧
      Tendsto (fun n:ℕ=>((n+1:ℕ):ℝ)^k*(∫t in a..b,dynamicCutoffError F sharp f n t)) atTop (𝓝 0):=by
  have hI(n:ℕ):IntervalIntegrable (dynamicCutoffError F sharp f n) volume a b:=
    (dynamic_cutoff_error_continuous F sharp f n).intervalIntegrable a b
  refine ⟨hI,?_⟩
  obtain ⟨ρ,hρ,hρ1,h⟩:=actual_dynamic_cutoff_geometric F sharp f
  have hb(n:ℕ):(∫t in a..b,dynamicCutoffError F sharp f n t)≤ρ^(n+1)*dynamicYCost F sharp f a b:=by
    have hc:Continuous (fun t:ℝ=>ρ^(n+1)*‖embed (sourceY sharp (literalCoreTime F sharp f t))‖):=
      continuous_const.mul (source_y_time_continuous F sharp f).norm
    have hm:=intervalIntegral.integral_mono_on hab (hI n) (hc.intervalIntegrable a b)
      (fun t _=>h n t)
    simpa only [intervalIntegral.integral_const_mul,dynamicYCost] using hm
  have hl:=((tendsto_pow_const_mul_const_pow_of_lt_one k hρ hρ1).comp
    (tendsto_add_atTop_nat 1)).mul_const (dynamicYCost F sharp f a b)
  have hl':Tendsto (fun n:ℕ=>(((n+1:ℕ):ℝ)^k*ρ^(n+1))*dynamicYCost F sharp f a b) atTop (𝓝 0):=by
    simpa only [Function.comp_def,zero_mul] using hl
  have hn(n:ℕ):0≤((n+1:ℕ):ℝ)^k*(∫t in a..b,dynamicCutoffError F sharp f n t):=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg (n+1)) k)
      (intervalIntegral.integral_nonneg hab (fun t _=>show 0≤dynamicCutoffError F sharp f n t from norm_nonneg _))
  apply squeeze_zero hn (fun n=>?_) hl'
  exact (mul_le_mul_of_nonneg_left (hb n) (pow_nonneg (Nat.cast_nonneg _) _)).trans_eq (mul_assoc _ _ _).symm

end LowEnergy.FullYDynamicSourceNext
