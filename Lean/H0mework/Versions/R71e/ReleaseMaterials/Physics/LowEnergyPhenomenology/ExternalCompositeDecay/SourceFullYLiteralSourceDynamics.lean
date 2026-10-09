import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYLiteralCoreResolvent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussNativeEnergy GaussNativePotential
open GaussYukawaGrade GaussYukawaOperator GaussCoreLabel GaussYukawaInteraction
open SourceScalarPairedTransport GaussUnitaryHistory Filter
open scoped Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
local instance dynamicsLabelFintype:Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourcePair embed diagonalAction originalAction GaussFullHamiltonian.adjointAction

/-- The original source and its independent dual stay separate throughout the generated orbit. -/
def sourceY(sharp:Bool):End:=if sharp then GaussFullHamiltonian.adjointAction else originalAction
private theorem original_raises:gradeCore*originalAction=originalAction*gradeCore+originalAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [Module.End.mul_apply,LinearMap.add_apply,add_apply]
  unfold gradeCore originalAction
  exact fiber_source_grade (scalarField z) (f z)
private theorem resolution:(∑g:NativeHistoryGrade.Label,project g)=(1:End):=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [LinearMap.sum_apply,Module.End.one_apply,map_sum,embed_project]
  rw [←sum_apply,NativeHistoryGrade.projection_resolution]
  rfl
private theorem project_grade_left(g:NativeHistoryGrade.Label):
    project g*gradeCore=(g.2.val:ℂ) • project g:=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [Module.End.mul_apply,LinearMap.smul_apply,map_smul,embed_project,←grade_core]
  exact congrArg (fun A:H→L[ℂ]H=>A (embed f)) (source_grade_left g)
private theorem project_grade_right(g:NativeHistoryGrade.Label):
    gradeCore*project g=(g.2.val:ℂ) • project g:=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [Module.End.mul_apply,LinearMap.smul_apply,map_smul,←grade_core,embed_project]
  exact congrArg (fun A:H→L[ℂ]H=>A (embed f)) (source_grade_right g)
private theorem original_nilpotent:originalAction^57=0:=by
  have h:=FiniteGradeAlgebra.words_zero gradeCore project
    (fun g:NativeHistoryGrade.Label=>(g.2.val:ℤ)) resolution
    (fun g=>by simpa only [Int.cast_natCast] using project_grade_left g)
    (fun g=>by simpa only [Int.cast_natCast] using project_grade_right g)
    0 56 (fun g=>by have hg:=g.2.isLt;constructor <;> omega)
    (List.replicate 57 originalAction)
    (fun T hT=>by obtain ⟨_,rfl⟩:=List.mem_replicate.mp hT;exact original_raises)
    (by simp)
  simpa only [List.prod_replicate] using h
private theorem sharp_power_pair(n:ℕ)(f g:QuantumTest):
    sourcePair f ((GaussFullHamiltonian.adjointAction^n) g)=sourcePair ((originalAction^n) f) g:=by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,pow_succ' originalAction]
    exact (ih f (GaussFullHamiltonian.adjointAction g)).trans
      (GaussFullHamiltonian.yukawa_pair ((originalAction^n) f) g)
theorem source_y_nilpotent(sharp:Bool):(sourceY sharp)^57=0:=by
  cases sharp
  · exact original_nilpotent
  · apply LinearMap.ext
    intro f
    apply pair_separates
    intro g
    simp only [sourceY,ite_true,sharp_power_pair,original_nilpotent,
      LinearMap.zero_apply,sourcePair,map_zero,inner_zero_left,inner_zero_right]

private def compressionSeed(F:Index):Submodule ℂ QuantumTest:=
  (FiniteCoreEvolution.coreSpan diagonal F).comap embed
private instance seed_finite(F:Index):FiniteDimensional ℂ (compressionSeed F):=by
  have :FiniteDimensional ℂ (LinearMap.ker embed):=by
    rw [LinearMap.ker_eq_bot.mpr embed_injective]
    infer_instance
  unfold compressionSeed
  infer_instance
private def gradedSeed(F:Index):Submodule ℂ QuantumTest:=
  ⨆g:NativeHistoryGrade.Label,(compressionSeed F).map (project g)
private instance graded_seed_finite(F:Index):FiniteDimensional ℂ (gradedSeed F):=by
  unfold gradedSeed
  infer_instance
private theorem base_compression_mem(F:Index)(x:H):
    FiniteCoreEvolution.compression diagonal F x∈FiniteCoreEvolution.coreSpan diagonal F:=
  (FiniteCoreEvolution.finiteAction diagonal F
    ((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto x)).property
private theorem compression_seed_mem(F:Index)(f:QuantumTest):compressionCore F f∈gradedSeed F:=by
  let q (g:NativeHistoryGrade.Label):QuantumTest:=coreEquiv.symm
    ⟨FiniteCoreEvolution.compression diagonal F (NativeHistoryGrade.projection g (embed f)),
      FiniteCoreEvolution.coreSpan_le diagonal F (base_compression_mem F _)⟩
  have hq(g:NativeHistoryGrade.Label):embed (q g)=
      FiniteCoreEvolution.compression diagonal F (NativeHistoryGrade.projection g (embed f)):=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hmem(g:NativeHistoryGrade.Label):q g∈compressionSeed F:=by
    change embed (q g)∈FiniteCoreEvolution.coreSpan diagonal F
    rw [hq]
    exact base_compression_mem F _
  have hc:compressionCore F f=∑g:NativeHistoryGrade.Label,project g (q g):=by
    apply embed_injective
    have he:embed (compressionCore F f)=GaussGradedCompression.compression F (embed f):=
      congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    calc
      embed (compressionCore F f)=GaussGradedCompression.compression F (embed f):=he
      _=∑g:NativeHistoryGrade.Label,NativeHistoryGrade.projection g
          (FiniteCoreEvolution.compression diagonal F (NativeHistoryGrade.projection g (embed f))):=
        GaussGradedCompression.compression_apply F (embed f)
      _=embed (∑g:NativeHistoryGrade.Label,project g (q g)):=by
        simp only [map_sum,embed_project,hq]
  rw [hc]
  exact Submodule.sum_mem _ (fun g _=>Submodule.mem_iSup_of_mem g
    (Submodule.mem_map.mpr ⟨q g,hmem g,rfl⟩))

section Orbit
variable {V:Type*}[AddCommGroup V][Module ℂ V]
private def finiteOrbit(T:V→ₗ[ℂ]V)(S:Submodule ℂ V):Submodule ℂ V:=
  ⨆i:Fin 57,S.map (T^i.val)
private instance orbit_finite(T:V→ₗ[ℂ]V)(S:Submodule ℂ V)[FiniteDimensional ℂ S]:
    FiniteDimensional ℂ (finiteOrbit T S):=by
  unfold finiteOrbit
  infer_instance
private theorem seed_le_orbit(T:V→ₗ[ℂ]V)(S:Submodule ℂ V):S≤finiteOrbit T S:=by
  intro x hx
  exact Submodule.mem_iSup_of_mem (⟨0,by omega⟩:Fin 57)
    (Submodule.mem_map.mpr ⟨x,hx,rfl⟩)
private theorem orbit_invariant(T:V→ₗ[ℂ]V)(hT:T^57=0)(S:Submodule ℂ V):
    finiteOrbit T S≤(finiteOrbit T S).comap T:=by
  apply iSup_le
  intro i x hx
  obtain ⟨y,hy,rfl⟩:=Submodule.mem_map.mp hx
  change T ((T^i.val) y)∈finiteOrbit T S
  by_cases hi:i.val+1<57
  · have he:T ((T^i.val) y)=(T^(i.val+1)) y:=by rw [pow_succ'];rfl
    rw [he]
    exact Submodule.mem_iSup_of_mem (⟨i.val+1,hi⟩:Fin 57)
      (Submodule.mem_map.mpr ⟨y,hy,rfl⟩)
  · have hi':i.val+1=57:=by omega
    have he:T ((T^i.val) y)=(T^57) y:=
      (show T ((T^i.val) y)=(T^(i.val+1)) y by rw [pow_succ'];rfl).trans
        (congrArg (fun n:ℕ=>(T^n) y) hi')
    rw [he,hT,LinearMap.zero_apply]
    exact Submodule.zero_mem _
end Orbit

/-- All source columns and the original input generate their own invariant core carrier. -/
def sourceOrbit(F:Index)(sharp:Bool)(f:QuantumTest):Submodule ℂ QuantumTest:=
  finiteOrbit (sourceY sharp) (gradedSeed F⊔Submodule.span ℂ {f})
instance sourceOrbit_finite(F:Index)(sharp:Bool)(f:QuantumTest):
    FiniteDimensional ℂ (sourceOrbit F sharp f):=by
  unfold sourceOrbit
  infer_instance
theorem sourceOrbit_input(F:Index)(sharp:Bool)(f:QuantumTest):f∈sourceOrbit F sharp f:=
  seed_le_orbit _ _ (show f∈gradedSeed F⊔Submodule.span ℂ {f} from
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton f)))
theorem sourceOrbit_invariant(F:Index)(sharp:Bool)(f q:QuantumTest)(hq:q∈sourceOrbit F sharp f):
    (compressionCore F+sourceY sharp) q∈sourceOrbit F sharp f:=by
  apply Submodule.add_mem
  · exact seed_le_orbit _ _ (Submodule.mem_sup_left (compression_seed_mem F q))
  · exact orbit_invariant _ (source_y_nilpotent sharp) _ hq

/-- The norm is inherited from the original μ₀ Hilbert carrier. -/
def sourceSpace(F:Index)(sharp:Bool)(f:QuantumTest):Submodule ℂ H:=
  LinearMap.range (embed.domRestrict (sourceOrbit F sharp f))
instance sourceSpace_finite(F:Index)(sharp:Bool)(f:QuantumTest):
    FiniteDimensional ℂ (sourceSpace F sharp f):=by
  unfold sourceSpace
  infer_instance
def sourceEquiv(F:Index)(sharp:Bool)(f:QuantumTest):
    sourceOrbit F sharp f≃ₗ[ℂ]sourceSpace F sharp f:=
  LinearEquiv.ofInjective (embed.domRestrict (sourceOrbit F sharp f))
    (fun _ _ h=>Subtype.ext (embed_injective h))
private def coreGenerator(F:Index)(sharp:Bool)(f:QuantumTest):
    sourceOrbit F sharp f→ₗ[ℂ]sourceOrbit F sharp f:=
  (compressionCore F+sourceY sharp).restrict (sourceOrbit_invariant F sharp f)
def sourceGenerator(F:Index)(sharp:Bool)(f:QuantumTest):
    sourceSpace F sharp f→L[ℂ]sourceSpace F sharp f:=
  ((sourceEquiv F sharp f).toLinearMap.comp ((coreGenerator F sharp f).comp
    (sourceEquiv F sharp f).symm.toLinearMap)).toContinuousLinearMap

def literalCoreTime(F:Index)(sharp:Bool)(f:QuantumTest)(t:ℝ):QuantumTest:=
  ((sourceEquiv F sharp f).symm
    (SourceFiniteUnitary.time (sourceGenerator F sharp f) t
      (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩))).val

theorem literal_core_time_zero(F:Index)(sharp:Bool)(f:QuantumTest):literalCoreTime F sharp f 0=f:=by
  simp only [literalCoreTime,SourceFiniteUnitary.time_zero,one_apply_eq_self,
    LinearEquiv.symm_apply_apply]

private theorem generator_embed(F:Index)(sharp:Bool)(f:QuantumTest)(x:sourceSpace F sharp f):
    (sourceGenerator F sharp f x:H)=
      embed ((compressionCore F+sourceY sharp) ((sourceEquiv F sharp f).symm x).val):=rfl
private theorem time_embed(F:Index)(sharp:Bool)(f:QuantumTest)(t:ℝ):
    embed (literalCoreTime F sharp f t)=
      (SourceFiniteUnitary.time (sourceGenerator F sharp f) t
        (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩):H):=
  congrArg Subtype.val ((sourceEquiv F sharp f).apply_symm_apply _)

/-- The complete uncut source generates time in its own finite invariant carrier. -/
theorem literal_core_time_derivative(F:Index)(sharp:Bool)(f:QuantumTest)(t:ℝ):
    HasDerivAt (fun s=>embed (literalCoreTime F sharp f s))
      ((-Complex.I) • embed ((compressionCore F+sourceY sharp) (literalCoreTime F sharp f t))) t:=by
  let A:=sourceGenerator F sharp f
  let x:=sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩
  have hd:=((sourceSpace F sharp f).subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (SourceFiniteUnitary.time_derivative A t x)
  change HasDerivAt (fun s=>(SourceFiniteUnitary.time A s x:H))
    ((-Complex.I) • (SourceFiniteUnitary.time A t (A x):H)) t at hd
  have hc:=congrArg (fun B:sourceSpace F sharp f→L[ℂ]sourceSpace F sharp f=>B x)
    (SourceFiniteUnitary.time_commutes A A (Commute.refl A) t).eq
  change A (SourceFiniteUnitary.time A t x)=SourceFiniteUnitary.time A t (A x) at hc
  have hv:(SourceFiniteUnitary.time A t (A x):H)=
      embed ((compressionCore F+sourceY sharp) (literalCoreTime F sharp f t)):=
    (congrArg Subtype.val hc.symm).trans (generator_embed F sharp f (SourceFiniteUnitary.time A t x))
  exact (hd.congr_deriv (congrArg (fun v:H=>(-Complex.I) • v) hv)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (time_embed F sharp f))

/-- Full H0+Y, or independent H0+Y†, keeps the original compression residual in the time equation. -/
theorem literal_full_time_equation(F:Index)(sharp:Bool)(f:QuantumTest)(t:ℝ):
    HasDerivAt (fun s=>embed (literalCoreTime F sharp f s))
      ((-Complex.I) • embed ((diagonalAction+sourceY sharp) (literalCoreTime F sharp f t)-
        defectAction F (literalCoreTime F sharp f t))) t:=by
  have he:(diagonalAction+sourceY sharp)-defectAction F=compressionCore F+sourceY sharp:=by
    unfold defectAction
    abel
  exact (literal_core_time_derivative F sharp f t).congr_deriv
    (congrArg (fun q:QuantumTest=>(-Complex.I) • embed q)
      (LinearMap.congr_fun he (literalCoreTime F sharp f t)).symm)
private theorem source_generator_pair(F:Index)(f g:QuantumTest):
    sourcePair f ((compressionCore F+sourceY true) g)=
      sourcePair ((compressionCore F+sourceY false) f) g:=by
  have he(q:QuantumTest):embed (compressionCore F q)=GaussGradedCompression.compression F (embed q):=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hC:sourcePair f (compressionCore F g)=sourcePair (compressionCore F f) g:=by
    simp only [sourcePair,he]
    exact (GaussGradedCompression.compression_pair F (embed f) (embed g)).symm
  have hY:=GaussFullHamiltonian.yukawa_pair f g
  simpa only [sourceY,ite_true,Bool.false_eq_true,ite_false,LinearMap.add_apply,sourcePair,
    map_add,inner_add_left,inner_add_right] using congrArg₂ (·+·) hC hY

theorem literal_dynamic_two_leg_pair(F:Index)(f g:QuantumTest)(t:ℝ):
    sourcePair (literalCoreTime F false f t) (literalCoreTime F true g t)=sourcePair f g:=by
  let K:=fun s:ℝ=>sourcePair (literalCoreTime F false f s) (literalCoreTime F true g s)
  have hd(s:ℝ):HasDerivAt K 0 s:=by
    have hi:=(literal_core_time_derivative F false f s).inner ℂ
      (literal_core_time_derivative F true g s)
    simp only [K,sourcePair]
    apply hi.congr_deriv
    have hp:=source_generator_pair F (literalCoreTime F false f s) (literalCoreTime F true g s)
    simp only [sourcePair] at hp
    simp only [inner_smul_left,inner_smul_right,map_neg,Complex.conj_I]
    rw [hp]
    ring
  have he:=is_const_of_deriv_eq_zero (fun s=>(hd s).differentiableAt) (fun s=>(hd s).deriv) t 0
  simpa only [K,literal_core_time_zero] using he

private theorem inverse_injective {V:Type*}[AddCommGroup V][Module ℂ V]
    (A B:V→ₗ[ℂ]V)(h:B*A=1):Function.Injective A:=by
  have hi:Function.LeftInverse B A:=by
    intro q
    have hq:=LinearMap.congr_fun h q
    simpa only [Module.End.mul_apply,Module.End.one_apply] using hq
  exact hi.injective
private theorem core_shift_injective(F:Index)(sharp:Bool)(z:ℂ)(hz:z.im≠0):
    Function.Injective ((compressionCore F+sourceY sharp-z • (1:End)):End):=by
  cases sharp
  · exact inverse_injective (literalCoreShift F z) (literalCoreResolvent F z hz)
      (literal_core_left_inverse F z hz)
  · exact inverse_injective (literalSharpShift F z) (literalSharpResolvent F z hz)
      (literal_sharp_left_inverse F z hz)
private theorem shifted_generator_embed(F:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ)
    (x:sourceSpace F sharp f):
    ((sourceGenerator F sharp f-z • 1) x:H)=
      embed ((compressionCore F+sourceY sharp-z • (1:End)) ((sourceEquiv F sharp f).symm x).val):=by
  have hx:embed ((sourceEquiv F sharp f).symm x).val=(x:H):=
    congrArg Subtype.val ((sourceEquiv F sharp f).apply_symm_apply x)
  simp only [sub_apply,smul_apply,one_apply_eq_self,Submodule.coe_sub,Submodule.coe_smul,
    generator_embed,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,map_sub,map_smul,hx]

theorem source_shift_isUnit(F:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ)(hz:z.im≠0):
    IsUnit (sourceGenerator F sharp f-z • 1):=by
  let A:sourceSpace F sharp f→L[ℂ]sourceSpace F sharp f:=sourceGenerator F sharp f-z • 1
  have hi:Function.Injective A:=by
    intro x y hxy
    apply (sourceEquiv F sharp f).symm.injective
    apply Subtype.ext
    apply core_shift_injective F sharp z hz
    apply embed_injective
    exact (shifted_generator_embed F sharp f z x).symm.trans
      ((congrArg Subtype.val hxy).trans (shifted_generator_embed F sharp f z y))
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨hi,LinearMap.injective_iff_surjective (f:=A.toLinearMap) |>.mp hi⟩

/-- The actual bounded inverse of the generated full-Y time generator. -/
def sourceResolvent(F:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ):
    sourceSpace F sharp f→L[ℂ]sourceSpace F sharp f:=
  Ring.inverse (sourceGenerator F sharp f-z • 1)
theorem source_resolvent_inverse(F:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ)(hz:z.im≠0):
    sourceResolvent F sharp f z*(sourceGenerator F sharp f-z • 1)=1 ∧
      (sourceGenerator F sharp f-z • 1)*sourceResolvent F sharp f z=1:=
  ⟨Ring.inverse_mul_cancel _ (source_shift_isUnit F sharp f z hz),
    Ring.mul_inverse_cancel _ (source_shift_isUnit F sharp f z hz)⟩

/-- The time-generated finite carrier consumes exactly the original two core inverses. -/
theorem source_resolvent_literal_return(F:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ)(hz:z.im≠0):
    ((sourceEquiv F sharp f).symm
      (sourceResolvent F sharp f z (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩))).val=
      if sharp then literalSharpResolvent F z hz f else literalCoreResolvent F z hz f:=by
  apply core_shift_injective F sharp z hz
  have hs:=congrArg (fun A:sourceSpace F sharp f→L[ℂ]sourceSpace F sharp f=>
      (A (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩):H))
    (source_resolvent_inverse F sharp f z hz).2
  have he:embed ((compressionCore F+sourceY sharp-z • (1:End))
      ((sourceEquiv F sharp f).symm
        (sourceResolvent F sharp f z (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩))).val)=embed f:=
    (shifted_generator_embed F sharp f z _).symm.trans hs
  have he':(compressionCore F+sourceY sharp-z • (1:End))
      (if sharp then literalSharpResolvent F z hz f else literalCoreResolvent F z hz f)=f:=by
    cases sharp
    · exact LinearMap.congr_fun (literal_core_right_inverse F z hz) f
    · exact LinearMap.congr_fun (literal_sharp_right_inverse F z hz) f
  exact (embed_injective he).trans he'.symm

end LowEnergy.FullYDynamicSource
