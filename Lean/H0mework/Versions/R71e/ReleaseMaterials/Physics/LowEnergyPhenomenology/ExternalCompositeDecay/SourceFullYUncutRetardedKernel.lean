import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCutoffDynamicReturn
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicSourceNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussNativeForm GaussNativePotential GaussRadialDomain GaussYukawaOperator GaussYukawaCoefficient
open GaussDensityCore GaussFockWeights GaussBoundedMultiplier GaussYukawaGrade
open GaussUnitaryHistory FullYDynamicSource FullYSourceCutoffVolterra FullYSourceCutoffSharp
open SourceScalarPairedTransport MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff Interval
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] sourcePair embed diagonalAction originalAction GaussFullHamiltonian.adjointAction

private def radialCap(R:ℝ)(z:SourceCoordinateSlice):ℝ:=1-Real.smoothTransition (radius z-R)
private theorem cap_smooth(R:ℝ):ContDiff ℝ ∞ (radialCap R):=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (radius_smooth.sub contDiff_const))
private theorem cap_nonneg(R:ℝ)(z:SourceCoordinateSlice):0 ≤ radialCap R z:=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)
private theorem cap_le_one(R:ℝ)(z:SourceCoordinateSlice):radialCap R z ≤ 1:=
  sub_le_self _ (Real.smoothTransition.nonneg _)
private theorem cap_one(R:ℝ)(z:SourceCoordinateSlice)(hz:radius z ≤ R):radialCap R z=1:=by
  rw [radialCap,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hz),sub_zero]
private theorem cap_radius_bound(R:ℝ)(hR:1 ≤ R)(z:SourceCoordinateSlice):
    radialCap R z*radius z ≤ R+1:=by
  by_cases hz:radius z ≤ R+1
  · exact (mul_le_of_le_one_left (radius_pos z).le (cap_le_one R z)).trans hz
  · have hh:1 ≤ radius z-R:=by linarith
    rw [radialCap,Real.smoothTransition.one_of_one_le hh,sub_self,zero_mul]
    linarith
private def localizedFiber(R:ℝ)(z:SourceCoordinateSlice):FockFiber→L[ℂ]FockFiber:=
  (radialCap R z:ℂ) • sourceMap (scalarField z)
private theorem localized_smooth(R:ℝ):ContDiff ℝ ∞ (localizedFiber R):=
  (Complex.ofRealCLM.contDiff.comp (cap_smooth R)).smul (sourceMap.contDiff.comp scalarField_smooth)
private theorem localized_commutes(R:ℝ)(z:SourceCoordinateSlice)(w:ℕ→ℂ):
    Commute (weight w) (localizedFiber R z):=by
  have h:Commute (weight w) (sourceMap (scalarField z)):=by
    rw [source_map_return]
    exact GaussQuantumMultiplier.weight_commute _ _
  exact h.smul_right (radialCap R z:ℂ)
private theorem original_fiber_bound(z:SourceCoordinateSlice)(v:FockFiber):
    ‖sourceMap (scalarField z) v‖ ≤ radius z*GaussYukawaCoefficient.bound*‖v‖:=by
  rw [←radius_return z]
  change ‖radius z • normalized z v‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (radius_pos z)]
  exact (mul_le_mul_of_nonneg_left (normalized_bound z v) (radius_pos z).le).trans_eq (mul_assoc _ _ _).symm
private theorem localized_bound(R:ℝ)(hR:1 ≤ R)(z:SourceCoordinateSlice)(v:FockFiber):
    ‖localizedFiber R z v‖ ≤ ((R+1)*GaussYukawaCoefficient.bound)*‖v‖:=by
  change ‖(radialCap R z:ℂ) • sourceMap (scalarField z) v‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cap_nonneg R z)]
  have h:radialCap R z*‖sourceMap (scalarField z) v‖ ≤
      radialCap R z*(radius z*GaussYukawaCoefficient.bound*‖v‖):=
    mul_le_mul_of_nonneg_left (original_fiber_bound z v) (cap_nonneg R z)
  calc
    _ ≤ radialCap R z*(radius z*GaussYukawaCoefficient.bound*‖v‖):=h
    _=(radialCap R z*radius z)*(GaussYukawaCoefficient.bound*‖v‖):=by ring
    _ ≤ (R+1)*(GaussYukawaCoefficient.bound*‖v‖):=
      mul_le_mul_of_nonneg_right (cap_radius_bound R hR z)
        (mul_nonneg GaussYukawaCoefficient.bound_nonneg (norm_nonneg v))
    _=_:=by ring
private def localizedCore(R:ℝ):End:=localMultiplier (localizedFiber R) (fun _=>(localized_smooth R).contDiffAt)
private def capCore(R:ℝ):End:=multiply (radialCap R) (fun _=>(cap_smooth R).contDiffAt)
private theorem localized_core_factor(R:ℝ)(f:QuantumTest):localizedCore R f=capCore R (originalAction f):=by
  apply DFunLike.ext
  intro z
  unfold localizedCore localizedFiber capCore originalAction
  rfl
private theorem cap_core_return(R:ℝ)(f:QuantumTest)
    (hf:∀z:SourceCoordinateSlice,f z≠0 → radius z ≤ R):capCore R f=f:=by
  apply DFunLike.ext
  intro z
  by_cases hz:f z=0
  · simp only [capCore,multiply_apply,hz,smul_zero]
  · simp only [capCore,multiply_apply,cap_one R z (hf z hz),Complex.ofReal_one,one_smul]
private theorem original_cap_commute(R:ℝ)(f:QuantumTest):
    originalAction (capCore R f)=capCore R (originalAction f):=by
  apply DFunLike.ext
  intro z
  unfold originalAction capCore
  change sourceMap (scalarField z) ((radialCap R z:ℂ) • f z)=_
  exact map_smul _ _ _
private def localizedY(R:ℝ)(hR:1 ≤ R):H→L[ℂ]H:=
  extension (localizedFiber R) (fun _=>(localized_smooth R).contDiffAt)
    (fun z=>localized_commutes R z) ((R+1)*GaussYukawaCoefficient.bound)
    (mul_nonneg (by linarith) GaussYukawaCoefficient.bound_nonneg) (fun z=>localized_bound R hR z)
private theorem localized_y_core(R:ℝ)(hR:1 ≤ R)(f:QuantumTest):
    localizedY R hR (embed f)=embed (localizedCore R f):=extension_core _ _ _ _ _ _ f
private theorem localized_y_norm(R:ℝ)(hR:1 ≤ R):
    ‖localizedY R hR‖ ≤ (R+1)*GaussYukawaCoefficient.bound:=extension_norm _ _ _ _ _ _
private theorem core_inner_ext(x y:H)(h:∀g:QuantumTest,inner ℂ (embed g) x=inner ℂ (embed g) y):x=y:=by
  apply core_dense.eq_of_inner_right ℂ
  intro a
  let g:QuantumTest:=coreEquiv.symm a
  have hg:embed g=(a:H):=congrArg Subtype.val (coreEquiv.apply_symm_apply a)
  exact (congrArg (fun u:H=>inner ℂ u x) hg).symm.trans
    ((h g).trans (congrArg (fun u:H=>inner ℂ u y) hg))
private theorem localized_sharp_core(R:ℝ)(hR:1 ≤ R)(f:QuantumTest):
    (localizedY R hR).adjoint (embed f)=embed (GaussFullHamiltonian.adjointAction (capCore R f)):=by
  apply core_inner_ext
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right,localized_y_core,localized_core_factor]
  have h:sourcePair (capCore R (originalAction g)) f=sourcePair g (GaussFullHamiltonian.adjointAction (capCore R f)):=
    (multiply_pair (radialCap R) (fun _=>(cap_smooth R).contDiffAt) (originalAction g) f).symm.trans
      (GaussFullHamiltonian.yukawa_pair g (capCore R f)).symm
  simpa only [sourcePair] using h
private def localizedBranch(R:ℝ)(hR:1 ≤ R)(sharp:Bool):H→L[ℂ]H:=
  if sharp then (localizedY R hR).adjoint else localizedY R hR
private theorem localized_return(R:ℝ)(hR:1 ≤ R)(sharp:Bool)(f:QuantumTest)
    (hf:∀z:SourceCoordinateSlice,f z≠0 → radius z ≤ R):
    localizedBranch R hR sharp (embed f)=embed (sourceY sharp f):=by
  cases sharp
  · change localizedY R hR (embed f)=embed (originalAction f)
    rw [localized_y_core,localized_core_factor,←original_cap_commute,cap_core_return R f hf]
  · change (localizedY R hR).adjoint (embed f)=embed (GaussFullHamiltonian.adjointAction f)
    rw [localized_sharp_core,cap_core_return R f hf]

attribute [local irreducible] localizedY localizedCore localizedBranch capCore GaussYukawaGrade.grade GaussYukawaGrade.gradeCore
  sourceOrbit sourceSpace

private theorem core_clm_ext(T U:H→L[ℂ]H)(h:∀f:QuantumTest,T (embed f)=U (embed f)):T=U:=by
  have ha:T.adjoint=U.adjoint:=by
    apply ContinuousLinearMap.ext
    intro x
    apply core_inner_ext
    intro f
    exact (ContinuousLinearMap.adjoint_inner_right T (embed f) x).trans
      ((congrArg (fun v:H=>inner ℂ v x) (h f)).trans
        (ContinuousLinearMap.adjoint_inner_right U (embed f) x).symm)
  have hb:=congrArg (fun A:H→L[ℂ]H=>A.adjoint) ha
  exact (ContinuousLinearMap.adjoint_adjoint T).symm.trans
    (hb.trans (ContinuousLinearMap.adjoint_adjoint U))
private theorem localized_core_grade(R:ℝ)(f:QuantumTest):
    gradeCore (localizedCore R f)=localizedCore R (gradeCore f)+localizedCore R f:=by
  apply DFunLike.ext
  intro z
  unfold gradeCore localizedCore localizedFiber
  change fiberGrade ((radialCap R z:ℂ) • sourceMap (scalarField z) (f z))=
    (radialCap R z:ℂ) • sourceMap (scalarField z) (fiberGrade (f z))+
      (radialCap R z:ℂ) • sourceMap (scalarField z) (f z)
  rw [map_smul,fiber_source_grade,smul_add]
private theorem localized_y_grade(R:ℝ)(hR:1 ≤ R):
    GaussYukawaGrade.grade*localizedY R hR=localizedY R hR*GaussYukawaGrade.grade+localizedY R hR:=by
  apply core_clm_ext
  intro f
  change GaussYukawaGrade.grade (localizedY R hR (embed f))=
    localizedY R hR (GaussYukawaGrade.grade (embed f))+localizedY R hR (embed f)
  have h1:GaussYukawaGrade.grade (localizedY R hR (embed f))=embed (gradeCore (localizedCore R f)):=
    (congrArg GaussYukawaGrade.grade (localized_y_core R hR f)).trans (grade_core (localizedCore R f))
  have h2:localizedY R hR (GaussYukawaGrade.grade (embed f))=embed (localizedCore R (gradeCore f)):=
    (congrArg (localizedY R hR) (grade_core f)).trans (localized_y_core R hR (gradeCore f))
  exact h1.trans (((congrArg embed (localized_core_grade R f)).trans (map_add embed _ _)).trans
    (congrArg₂ (·+·) h2.symm (localized_y_core R hR f).symm))
private theorem raising_product {A:Type*}[Ring A][Module ℂ A][IsScalarTower ℂ A A][SMulCommClass ℂ A A]
    (G X Y:A)(k:ℂ)(hX:G*X=X*G+k • X)(hY:G*Y=Y*G+Y):
    G*(X*Y)=(X*Y)*G+(k+1) • (X*Y):=by
  rw [←mul_assoc G X Y,hX,add_mul,smul_mul_assoc,mul_assoc X G Y,hY,mul_add,
    ←mul_assoc X Y G,add_smul,one_smul]
  abel
private theorem localized_time_bound(R:ℝ)(hR:1 ≤ R)(F:Index)(t:ℝ):
    ‖SourceFiniteUnitary.time (GaussGradedCompression.compression F+localizedY R hR) t‖ ≤
      ∑j∈Finset.range 57,(|t| * ((R+1)*GaussYukawaCoefficient.bound))^j:=by
  let C:=GaussGradedCompression.compression F
  let B:=localizedY R hR
  have hterm(s:ℝ):finitePrefix C B 56 s*B=0:=by
    apply source_homogeneous_zero _ 57 _ (by norm_num)
    simpa only [Nat.cast_ofNat,show (56:ℂ)+1=57 by norm_num] using
      raising_product GaussYukawaGrade.grade (finitePrefix C B 56 s) B 56
        (finitePrefix_homogeneous C B GaussYukawaGrade.grade (source_compression_grade F) (localized_y_grade R hR) 56 s)
        (localized_y_grade R hR)
  have he(s:ℝ):partialEvolution C B 56 s=SourceFiniteUnitary.time (C+B) s:=by
    apply autonomous_evolution_unique _ _ _ (partialEvolution_initial C B 56) s
    intro v
    simpa only [mul_smul_comm,hterm,smul_zero,sub_zero] using partialEvolution_derivative C B 56 v
  rw [←he]
  apply (partialEvolution_bound C B (GaussGradedCompression.compression_selfAdjoint F) 56 t).trans
  exact Finset.sum_le_sum (fun j _=>pow_le_pow_left₀ (mul_nonneg (abs_nonneg t) (norm_nonneg B))
    (mul_le_mul_of_nonneg_left (localized_y_norm R hR) (abs_nonneg t)) j)
private theorem localized_branch_time_bound(R:ℝ)(hR:1 ≤ R)(F:Index)(sharp:Bool)(t:ℝ):
    ‖SourceFiniteUnitary.time (GaussGradedCompression.compression F+localizedBranch R hR sharp) t‖ ≤
      ∑j∈Finset.range 57,(|t| * ((R+1)*GaussYukawaCoefficient.bound))^j:=by
  unfold localizedBranch
  cases sharp
  · exact localized_time_bound R hR F t
  · change ‖SourceFiniteUnitary.time (GaussGradedCompression.compression F+(localizedY R hR).adjoint) t‖ ≤ _
    rw [←time_sum_adjoint _ _ (GaussGradedCompression.compression_selfAdjoint F),ContinuousLinearMap.adjoint.norm_map]
    simpa only [abs_neg] using localized_time_bound R hR F (-t)

private theorem intertwined_time {E D:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
    [NormedAddCommGroup D][InnerProductSpace ℂ D][CompleteSpace D]
    (A:E→L[ℂ]E)(B:D→L[ℂ]D)(J:E→L[ℂ]D)(h:∀x:E,J (A x)=B (J x))(x:E)(t:ℝ):
    J (SourceFiniteUnitary.time A t x)=SourceFiniteUnitary.time B t (J x):=by
  have hu(s:ℝ):HasDerivAt (fun v:ℝ=>J (SourceFiniteUnitary.time A v x))
      ((-Complex.I) • (B (J (SourceFiniteUnitary.time A s x))+0)) s:=by
    have hd:=(J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (SourceFiniteUnitary.time_derivative A s x)
    have hc:=congrArg (fun T:E→L[ℂ]E=>T x) (SourceFiniteUnitary.time_commutes A A (Commute.refl A) s).eq
    change A (SourceFiniteUnitary.time A s x)=SourceFiniteUnitary.time A s (A x) at hc
    change HasDerivAt (fun v:ℝ=>J (SourceFiniteUnitary.time A v x))
      (J ((-Complex.I) • SourceFiniteUnitary.time A s (A x))) s at hd
    apply hd.congr_deriv
    rw [map_smul,←hc,h,add_zero]
  have hi:=source_forced_time_integral B (fun v:ℝ=>J (SourceFiniteUnitary.time A v x)) (fun _=>0)
    hu continuous_const t
  simpa only [SourceFiniteUnitary.time_zero,one_apply_eq_self,map_zero,intervalIntegral.integral_zero,
    smul_zero,sub_eq_zero] using hi

private theorem localized_source_intertwining(F:Index)(sharp:Bool)(f:QuantumTest)(R:ℝ)(hR:1 ≤ R)
    (hbound:∀q:sourceOrbit F sharp f,∀z:SourceCoordinateSlice,q.val z≠0 → radius z ≤ R)
    (x:sourceSpace F sharp f):
    (sourceGenerator F sharp f x:H)=
      (GaussGradedCompression.compression F+localizedBranch R hR sharp) (x:H):=by
  let q:sourceOrbit F sharp f:=(sourceEquiv F sharp f).symm x
  have hq:embed q.val=(x:H):=congrArg Subtype.val ((sourceEquiv F sharp f).apply_symm_apply x)
  have hC:embed (compressionCore F q.val)=GaussGradedCompression.compression F (embed q.val):=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hY:=localized_return R hR sharp q.val (hbound q)
  change embed (compressionCore F q.val+sourceY sharp q.val)=_
  exact ((map_add embed _ _).trans (congrArg₂ (·+·) hC hY.symm)).trans
    (congrArg (fun v:H=>GaussGradedCompression.compression F v+localizedBranch R hR sharp v) hq)

/-- Original finite source support and full grade 0..56 generate polynomial propagation at every time. -/
theorem actual_source_time_polynomial_bound(F:Index)(sharp:Bool)(f:QuantumTest):
    ∃C:ℝ,0 ≤ C ∧ ∀t:ℝ,‖SourceFiniteUnitary.time (sourceGenerator F sharp f) t‖ ≤
      ∑j∈Finset.range 57,(|t| * C)^j:=by
  have hrad:∃R:ℝ,1 ≤ R ∧ ∀q:sourceOrbit F sharp f,∀z:SourceCoordinateSlice,q.val z≠0 → radius z ≤ R:=
    @finite_source_radius (sourceOrbit F sharp f) (sourceOrbit_finite F sharp f)
  rcases hrad with ⟨R,hR,hbound⟩
  refine ⟨(R+1)*GaussYukawaCoefficient.bound,mul_nonneg (by linarith) GaussYukawaCoefficient.bound_nonneg,?_⟩
  let A:=sourceGenerator F sharp f
  let B:=GaussGradedCompression.compression F+localizedBranch R hR sharp
  let J:sourceSpace F sharp f→L[ℂ]H:=(sourceSpace F sharp f).subtypeL
  have hj(x:sourceSpace F sharp f):J (A x)=B (J x):=
    localized_source_intertwining F sharp f R hR hbound x
  intro t
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun j _=>
    pow_nonneg (mul_nonneg (abs_nonneg t) (mul_nonneg (by linarith) GaussYukawaCoefficient.bound_nonneg)) j))
  intro x
  change ‖J (SourceFiniteUnitary.time A t x)‖ ≤ _*‖J x‖
  rw [intertwined_time A B J hj x t]
  exact ((SourceFiniteUnitary.time B t).le_opNorm (J x)).trans
    (mul_le_mul_of_nonneg_right (localized_branch_time_bound R hR F sharp t) (norm_nonneg (J x)))

private def retardedPhase(z:ℂ)(t:ℝ):ℂ:=Complex.exp (t • (Complex.I*z))
private theorem phase_derivative(z:ℂ)(t:ℝ):
    HasDerivAt (retardedPhase z) (retardedPhase z t*(Complex.I*z)) t:=by
  change HasDerivAt (fun s:ℝ=>Complex.exp (s • (Complex.I*z)))
    (Complex.exp (t • (Complex.I*z))*(Complex.I*z)) t
  simpa only [Complex.exp_eq_exp_ℂ] using! hasDerivAt_exp_smul_const (Complex.I*z) t
private theorem phase_norm(z:ℂ)(t:ℝ):‖retardedPhase z t‖=Real.exp (-z.im*t):=by
  simp [retardedPhase,Complex.norm_exp,Complex.real_smul,mul_comm]

section Retarded
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
local instance :NormedAlgebra ℝ (E→L[ℂ]E):=NormedAlgebra.restrictScalars ℝ ℂ _
private def dampedTime(A:E→L[ℂ]E)(z:ℂ)(t:ℝ):E→L[ℂ]E:=retardedPhase z t • SourceFiniteUnitary.time A t
private theorem damped_derivative(A:E→L[ℂ]E)(z:ℂ)(t:ℝ):
    HasDerivAt (dampedTime A z) (dampedTime A z t*((-Complex.I) • (A-z • 1))) t:=by
  have ht:=hasDerivAt_exp_smul_const ((-Complex.I) • A) t
  change HasDerivAt (SourceFiniteUnitary.time A) (SourceFiniteUnitary.time A t*((-Complex.I) • A)) t at ht
  have h:=(phase_derivative z t).smul ht
  have he:(retardedPhase z t*(Complex.I*z)) • SourceFiniteUnitary.time A t+
      retardedPhase z t • (SourceFiniteUnitary.time A t*((-Complex.I) • A))=
      dampedTime A z t*((-Complex.I) • (A-z • 1)):=by
    simp only [dampedTime,smul_mul_assoc,mul_smul_comm,mul_sub,mul_one,smul_sub,smul_smul]
    module
  exact h.congr_deriv ((add_comm _ _).trans he)
private theorem damped_continuous(A:E→L[ℂ]E)(z:ℂ):Continuous (dampedTime A z):=
  continuous_iff_continuousAt.mpr (fun t=>(damped_derivative A z t).continuousAt)
def sourceCausal(A:E→L[ℂ]E)(z:ℂ)(T:ℝ):E→L[ℂ]E:=Complex.I • ∫t in (0:ℝ)..T,dampedTime A z t
private theorem causal_identity(A R:E→L[ℂ]E)(z:ℂ)(hR:(A-z • 1)*R=1)(T:ℝ):
    sourceCausal A z T=R-dampedTime A z T*R:=by
  have hd(t:ℝ):HasDerivAt (fun s:ℝ=>Complex.I • (dampedTime A z s*R)) (dampedTime A z t) t:=by
    have h:=((damped_derivative A z t).mul_const R).const_smul Complex.I
    simpa only [mul_smul_comm,smul_mul_assoc,mul_assoc,hR,mul_one,smul_smul,mul_neg,
      Complex.I_mul_I,neg_neg,one_smul,Pi.smul_apply] using! h
  have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hd t)
    ((damped_continuous A z).intervalIntegrable (μ:=volume) 0 T)
  have hzero:dampedTime A z 0=1:=by
    simp only [dampedTime,retardedPhase,zero_smul,Complex.exp_zero,one_smul,SourceFiniteUnitary.time_zero]
  have h:=congrArg (fun X:E→L[ℂ]E=>Complex.I • X) hi
  rw [hzero,one_mul] at h
  calc
    sourceCausal A z T=Complex.I • (Complex.I • (dampedTime A z T*R)-Complex.I • R):=h
    _=R-dampedTime A z T*R:=by
      rw [smul_sub,smul_smul,smul_smul,Complex.I_mul_I,neg_one_smul,neg_one_smul]
      abel
private theorem causal_error(A R:E→L[ℂ]E)(z:ℂ)(hR:(A-z • 1)*R=1)(C:ℝ)
    (hbound:∀t:ℝ,‖SourceFiniteUnitary.time A t‖ ≤ ∑j∈Finset.range 57,(|t| * C)^j)(T:ℝ):
    ‖sourceCausal A z T-R‖ ≤
      (Real.exp (-z.im*T)*(∑j∈Finset.range 57,(|T| * C)^j))*‖R‖:=by
  have he:sourceCausal A z T-R= -(dampedTime A z T*R):=by rw [causal_identity A R z hR];abel
  rw [he,norm_neg]
  apply (norm_mul_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg R)
  rw [dampedTime,norm_smul,phase_norm]
  exact mul_le_mul_of_nonneg_left (hbound T) (Real.exp_pos _).le
private theorem causal_limit(A R:E→L[ℂ]E)(z:ℂ)(hz:0<z.im)(hR:(A-z • 1)*R=1)(C:ℝ)
    (hbound:∀t:ℝ,‖SourceFiniteUnitary.time A t‖ ≤ ∑j∈Finset.range 57,(|t| * C)^j):
    Tendsto (sourceCausal A z) atTop (𝓝 R):=by
  have hterm(j:ℕ):Tendsto (fun T:ℝ=>C^j*(T^j*Real.exp (-z.im*T))) atTop (𝓝 0):=by
    simpa only [Real.rpow_natCast,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j:ℝ) z.im hz).const_mul (C^j)
  have hsum:Tendsto (fun T:ℝ=>(∑j∈Finset.range 57,C^j*(T^j*Real.exp (-z.im*T)))*‖R‖) atTop (𝓝 0):=by
    simpa only [Finset.sum_const_zero,zero_mul] using
      (tendsto_finsetSum (Finset.range 57) (fun j _=>hterm j)).mul_const ‖R‖
  have hl:Tendsto (fun T:ℝ=>(Real.exp (-z.im*T)*(∑j∈Finset.range 57,(|T| * C)^j))*‖R‖) atTop (𝓝 0):=by
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    simp only [abs_of_nonneg hT,Finset.mul_sum,Finset.sum_mul,mul_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _=>norm_nonneg _) (fun T=>causal_error A R z hR C hbound T) hl
end Retarded

/-- Every positive damping is paid by the actual uncut source polynomial; no time-tail premise is supplied. -/
theorem actual_source_uncut_retarded_limit(F:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ)(hz:0<z.im):
    Tendsto (sourceCausal (sourceGenerator F sharp f) z) atTop (𝓝 (sourceResolvent F sharp f z)):=by
  have hpoly:∃C:ℝ,0 ≤ C ∧ ∀t:ℝ,‖SourceFiniteUnitary.time (sourceGenerator F sharp f) t‖ ≤
      ∑j∈Finset.range 57,(|t| * C)^j:=actual_source_time_polynomial_bound F sharp f
  rcases hpoly with ⟨C,_hC,hbound⟩
  exact causal_limit (sourceGenerator F sharp f) (sourceResolvent F sharp f z) z hz
    (source_resolvent_inverse F sharp f z hz.ne').2 C hbound

private theorem time_negative {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
    (A:E→L[ℂ]E)(t:ℝ):SourceFiniteUnitary.time (-A) t=SourceFiniteUnitary.time A (-t):=by
  simp only [SourceFiniteUnitary.time,smul_neg,neg_smul]
private theorem phase_negative(z:ℂ)(t:ℝ):retardedPhase (-z) t=retardedPhase z (-t):=by
  simp only [retardedPhase,mul_neg,smul_neg,neg_smul]
private theorem negative_inverse {A:Type*}[Ring A][Module ℂ A](X R:A)(z:ℂ)
    (h:(X-z • 1)*R=1):(-X-(-z) • 1)*(-R)=1:=by
  have he:-X-(-z) • (1:A)= -(X-z • 1):=by rw [neg_smul,sub_neg_eq_add,neg_sub];abel
  rw [he,neg_mul_neg,h]

def orientedSourceCausal {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
    (A:E→L[ℂ]E)(advanced:Bool)(z:ℂ)(T:ℝ):E→L[ℂ]E:=
  if advanced then -sourceCausal (-A) (-z) T else sourceCausal A z T
private theorem causal_nonreal(advanced:Bool)(z:ℂ)
    (hz:if advanced then z.im<0 else 0<z.im):z.im≠0:=by
  cases advanced
  · exact ne_of_gt hz
  · exact ne_of_lt hz

private theorem oriented_causal_limit {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
    (A R:E→L[ℂ]E)(advanced:Bool)(z:ℂ)(hz:if advanced then z.im<0 else 0<z.im)
    (hR:(A-z • 1)*R=1)(C:ℝ)
    (hbound:∀t:ℝ,‖SourceFiniteUnitary.time A t‖ ≤ ∑j∈Finset.range 57,(|t| * C)^j):
    Tendsto (orientedSourceCausal A advanced z) atTop (𝓝 R):=by
  cases advanced
  · exact causal_limit A R z hz hR C hbound
  · have hneg(t:ℝ):‖SourceFiniteUnitary.time (-A) t‖ ≤ ∑j∈Finset.range 57,(|t| * C)^j:=by
      rw [time_negative]
      simpa only [abs_neg] using hbound (-t)
    have hhz:0<(-z).im:=by simpa only [Complex.neg_im] using neg_pos.mpr hz
    have h:=causal_limit (-A) (-R) (-z) hhz (negative_inverse A R z hR) C hneg
    change Tendsto (fun T:ℝ=> -sourceCausal (-A) (-z) T) atTop (𝓝 R)
    simpa only [neg_neg] using h.neg

/-- Both causal orientations are generated by the same literal full-Y source generator. -/
theorem actual_source_uncut_causal_limit(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(z:ℂ)
    (hz:if advanced then z.im<0 else 0<z.im):
    Tendsto (orientedSourceCausal (sourceGenerator F sharp f) advanced z) atTop
      (𝓝 (sourceResolvent F sharp f z)):=by
  have hpoly:∃C:ℝ,0 ≤ C ∧ ∀t:ℝ,‖SourceFiniteUnitary.time (sourceGenerator F sharp f) t‖ ≤
      ∑j∈Finset.range 57,(|t| * C)^j:=actual_source_time_polynomial_bound F sharp f
  rcases hpoly with ⟨C,_hC,hbound⟩
  exact oriented_causal_limit (sourceGenerator F sharp f) (sourceResolvent F sharp f z)
    advanced z hz (source_resolvent_inverse F sharp f z (causal_nonreal advanced z hz)).2 C hbound

private theorem causal_apply {E D:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
    [NormedAddCommGroup D][InnerProductSpace ℂ D][CompleteSpace D]
    (A:E→L[ℂ]E)(J:E→L[ℂ]D)(x:E)(z:ℂ)(T:ℝ):
    J (sourceCausal A z T x)=Complex.I • ∫s in (0:ℝ)..T,
      retardedPhase z s • J (SourceFiniteUnitary.time A s x):=by
  let L:(E→L[ℂ]E)→L[ℂ]D:=J.comp (ContinuousLinearMap.apply ℂ E x)
  have hi:=L.intervalIntegral_comp_comm ((damped_continuous A z).intervalIntegrable (μ:=volume) 0 T)
  calc
    J (sourceCausal A z T x)=Complex.I • L (∫s in (0:ℝ)..T,dampedTime A z s):=by
      rw [sourceCausal,smul_apply,map_smul]
      rfl
    _=Complex.I • ∫s in (0:ℝ)..T,L (dampedTime A z s):=congrArg (fun y:D=>Complex.I • y) hi.symm
    _=_:=by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      change J (retardedPhase z s • SourceFiniteUnitary.time A s x)=_
      exact map_smul J _ _

private theorem oriented_causal_apply {E D:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
    [NormedAddCommGroup D][InnerProductSpace ℂ D][CompleteSpace D]
    (A:E→L[ℂ]E)(J:E→L[ℂ]D)(x:E)(advanced:Bool)(z:ℂ)(T:ℝ):
    J (orientedSourceCausal A advanced z T x)=
      (if advanced then -Complex.I else Complex.I) • ∫s in (0:ℝ)..T,
        retardedPhase z (if advanced then -s else s) •
          J (SourceFiniteUnitary.time A (if advanced then -s else s) x):=by
  cases advanced
  · exact causal_apply A J x z T
  · change J ((-sourceCausal (-A) (-z) T) x)=
      (-Complex.I) • ∫s in (0:ℝ)..T,retardedPhase z (-s) • J (SourceFiniteUnitary.time A (-s) x)
    rw [neg_apply,map_neg,causal_apply,←neg_smul]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    change retardedPhase (-z) s • J (SourceFiniteUnitary.time (-A) s x)=
      retardedPhase z (-s) • J (SourceFiniteUnitary.time A (-s) x)
    rw [phase_negative,time_negative]

def uncutCausalVector(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(z:ℂ)(T:ℝ):H:=
  (if advanced then -Complex.I else Complex.I) • ∫s in (0:ℝ)..T,
    retardedPhase z (if advanced then -s else s) •
      embed (literalCoreTime F sharp f (if advanced then -s else s))

private def causalEvaluation(F:Index)(sharp:Bool)(f:QuantumTest):
    (sourceSpace F sharp f→L[ℂ]sourceSpace F sharp f)→L[ℂ]H:=
  (sourceSpace F sharp f).subtypeL.comp (ContinuousLinearMap.apply ℂ (sourceSpace F sharp f)
    (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩))
private theorem causal_evaluation(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(z:ℂ)(T:ℝ):
    causalEvaluation F sharp f (orientedSourceCausal (sourceGenerator F sharp f) advanced z T)=
      uncutCausalVector F sharp f advanced z T:=by
  let A:=sourceGenerator F sharp f
  let J:sourceSpace F sharp f→L[ℂ]H:=(sourceSpace F sharp f).subtypeL
  let x:=sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩
  have ht(s:ℝ):embed (literalCoreTime F sharp f s)=J (SourceFiniteUnitary.time A s x):=
    congrArg Subtype.val ((sourceEquiv F sharp f).apply_symm_apply _)
  have hc:=oriented_causal_apply A J x advanced z T
  change J (orientedSourceCausal A advanced z T x)=_
  refine hc.trans ?_
  apply congrArg (fun v:H=>(if advanced then -Complex.I else Complex.I) • v)
  apply intervalIntegral.integral_congr
  intro s _
  exact congrArg (fun v:H=>retardedPhase z (if advanced then -s else s) • v)
    (ht (if advanced then -s else s)).symm
private theorem resolvent_evaluation(F:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ)(hz:z.im≠0):
    causalEvaluation F sharp f (sourceResolvent F sharp f z)=
      embed (if sharp then literalSharpResolvent F z hz f else literalCoreResolvent F z hz f):=by
  let J:sourceSpace F sharp f→L[ℂ]H:=(sourceSpace F sharp f).subtypeL
  let x:=sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩
  let y:=sourceResolvent F sharp f z x
  have hy:embed ((sourceEquiv F sharp f).symm y).val=J y:=
    congrArg Subtype.val ((sourceEquiv F sharp f).apply_symm_apply y)
  exact hy.symm.trans (congrArg embed (source_resolvent_literal_return F sharp f z hz))

private theorem mapped_limit {E D:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
    [NormedAddCommGroup D][NormedSpace ℂ D](L:E→L[ℂ]D)(u:ℝ→E)(v:ℝ→D)(x:E)(y:D)
    (hu:Tendsto u atTop (𝓝 x))(hv:∀t:ℝ,L (u t)=v t)(hy:L x=y):
    Tendsto v atTop (𝓝 y):=by
  have h:=L.continuous.tendsto x |>.comp hu
  rw [hy] at h
  exact h.congr' (Eventually.of_forall hv)

/-- The actual μ₀-valued full-Y propagation generates its original core inverse on each causal half-line. -/
theorem actual_original_uncut_retarded_kernel(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(z:ℂ)
    (hz:if advanced then z.im<0 else 0<z.im):
    Tendsto (uncutCausalVector F sharp f advanced z) atTop
      (𝓝 (embed (if sharp then literalSharpResolvent F z (causal_nonreal advanced z hz) f
        else literalCoreResolvent F z (causal_nonreal advanced z hz) f))):=by
  exact mapped_limit (causalEvaluation F sharp f)
    (orientedSourceCausal (sourceGenerator F sharp f) advanced z) (uncutCausalVector F sharp f advanced z)
    (sourceResolvent F sharp f z)
    (embed (if sharp then literalSharpResolvent F z (causal_nonreal advanced z hz) f
      else literalCoreResolvent F z (causal_nonreal advanced z hz) f))
    (actual_source_uncut_causal_limit F sharp f advanced z hz)
    (causal_evaluation F sharp f advanced z)
    (resolvent_evaluation F sharp f z (causal_nonreal advanced z hz))

end LowEnergy.FullYDynamicSourceNext
