import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYLiteralSourceDynamics
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceScalarPairedTransport GaussUnitaryHistory Filter MeasureTheory
open scoped Topology InnerProductSpace Interval
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
local instance defectLabelFintype:Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourcePair embed diagonalAction GaussYukawaOperator.originalAction
  GaussFullHamiltonian.adjointAction
private theorem compression_embed(F:Index)(f:QuantumTest):
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f):=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_pair(F:Index)(f g:QuantumTest):
    sourcePair (compressionCore F f) g=sourcePair f (compressionCore F g):=by
  simp only [sourcePair,compression_embed]
  exact GaussGradedCompression.compression_pair F (embed f) (embed g)
private theorem defect_difference(F G:Index):
    defectAction G-defectAction F=compressionCore F-compressionCore G:=by
  unfold defectAction
  abel
private theorem mixed_generator_pair(F G:Index)(f g:QuantumTest):
    sourcePair ((compressionCore F+sourceY false) f) g-
      sourcePair f ((compressionCore G+sourceY true) g)=
      sourcePair f ((defectAction G-defectAction F) g):=by
  have hC:=compression_pair F f g
  have hY:=GaussFullHamiltonian.yukawa_pair f g
  rw [defect_difference]
  simp only [sourceY,Bool.false_eq_true,ite_false,ite_true,LinearMap.add_apply,LinearMap.sub_apply,
    sourcePair,map_add,map_sub,inner_add_left,inner_add_right,inner_sub_right] at hC hY ⊢
  exact sub_eq_sub_iff_add_eq_add.mpr (by rw [hC,hY];ring)
private theorem imaginary_difference(a b c:ℂ)(h:a-b=c):
    (-Complex.I)*b+Complex.I*a=Complex.I*c:=by rw [←h];ring

def dynamicDefectCurrent(F G:Index)(f g:QuantumTest)(t:ℝ):ℂ:=
  sourcePair (literalCoreTime F false f t)
    ((defectAction G-defectAction F) (literalCoreTime G true g t))

/-- Across actual finite sources, the literal Yukawa and independent dual cancel before estimating. -/
theorem literal_dynamic_defect_derivative(F G:Index)(f g:QuantumTest)(t:ℝ):
    HasDerivAt (fun s=>sourcePair (literalCoreTime F false f s) (literalCoreTime G true g s))
      (Complex.I*dynamicDefectCurrent F G f g t) t:=by
  have h:=(literal_core_time_derivative F false f t).inner ℂ
    (literal_core_time_derivative G true g t)
  simp only [dynamicDefectCurrent,sourcePair]
  apply h.congr_deriv
  have hp:=mixed_generator_pair F G (literalCoreTime F false f t) (literalCoreTime G true g t)
  simp only [sourcePair] at hp
  simp only [inner_smul_left,inner_smul_right,map_neg,Complex.conj_I,neg_neg]
  exact imaginary_difference _ _ _ hp
private theorem dynamic_defect_embed(F G:Index)(f g:QuantumTest)(t:ℝ):
    dynamicDefectCurrent F G f g t=
      inner ℂ (embed (literalCoreTime F false f t))
        ((GaussGradedCompression.compression F-GaussGradedCompression.compression G)
          (embed (literalCoreTime G true g t))):=by
  simp only [dynamicDefectCurrent,defect_difference,sourcePair,LinearMap.sub_apply,map_sub,
    compression_embed,sub_apply]

theorem dynamic_defect_continuous(F G:Index)(f g:QuantumTest):
    Continuous (dynamicDefectCurrent F G f g):=by
  have hf:Continuous (fun t=>embed (literalCoreTime F false f t)):=
    continuous_iff_continuousAt.mpr (fun t=>(literal_core_time_derivative F false f t).continuousAt)
  have hg:Continuous (fun t=>embed (literalCoreTime G true g t)):=
    continuous_iff_continuousAt.mpr (fun t=>(literal_core_time_derivative G true g t).continuousAt)
  have h:=hf.inner (𝕜:=ℂ) ((GaussGradedCompression.compression F-GaussGradedCompression.compression G).continuous.comp hg)
  exact h.congr (fun t=>(dynamic_defect_embed F G f g t).symm)

/-- The original dynamic current generates its own finite-time integrability. -/
theorem dynamic_defect_integrable(F G:Index)(f g:QuantumTest)(T:ℝ):
    IntervalIntegrable (dynamicDefectCurrent F G f g) volume 0 T:=
  (dynamic_defect_continuous F G f g).intervalIntegrable 0 T

/-- The exact signed cofinal price retains both actual full-Y propagated legs. -/
theorem literal_dynamic_defect_integral(F G:Index)(f g:QuantumTest)(T:ℝ):
    sourcePair (literalCoreTime F false f T) (literalCoreTime G true g T)=
      sourcePair f g+Complex.I*∫ t in (0:ℝ)..T,dynamicDefectCurrent F G f g t:=by
  have hc:Continuous (fun t=>Complex.I*dynamicDefectCurrent F G f g t):=
    continuous_const.mul (dynamic_defect_continuous F G f g)
  have h:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>literal_dynamic_defect_derivative F G f g t) (hc.intervalIntegrable 0 T)
  rw [literal_core_time_zero,literal_core_time_zero,intervalIntegral.integral_const_mul] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

private theorem core_atTop_exact(q:QuantumTest):
    ∀ᶠ G in (atTop:Filter Index),compressionCore G q=diagonalAction q:=by
  classical
  let x:diagonal.domain:=coreEquiv q
  let y:diagonal.domain:=⟨diagonal x,diagonal_invariant x⟩
  refine Filter.eventually_atTop.mpr
    ⟨GaussGradedCompression.support x∪GaussGradedCompression.support y,fun G hG=>?_⟩
  apply embed_injective
  rw [compression_embed]
  have hx:∀g:NativeHistoryGrade.Label,GaussGradedCompression.piece g x∈G:=by
    intro g
    apply hG
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨g,Finset.mem_univ g,rfl⟩
  have hy:∀g:NativeHistoryGrade.Label,GaussGradedCompression.piece g y∈G:=by
    intro g
    apply hG
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨g,Finset.mem_univ g,rfl⟩
  have he:=GaussGradedCompression.compression_core_exact G x hx hy
  have hd:diagonal x=embed (diagonalAction q):=by
    change embed (diagonalAction (coreEquiv.symm (coreEquiv q)))=_
    rw [coreEquiv.symm_apply_apply]
  exact he.trans hd
private theorem finite_core_atTop_exact(S:Submodule ℂ QuantumTest)[FiniteDimensional ℂ S]:
    ∀ᶠ G in (atTop:Filter Index),∀q:S,compressionCore G q.val=diagonalAction q.val:=by
  let b:=Module.finBasis ℂ S
  have hh:∀i,∀ᶠ G in (atTop:Filter Index),compressionCore G (b i).val=diagonalAction (b i).val:=
    fun i=>core_atTop_exact (b i).val
  filter_upwards [Filter.eventually_all.mpr hh] with G hG
  have he:(compressionCore G).comp S.subtype=diagonalAction.comp S.subtype:=by
    apply b.ext
    intro i
    exact hG i
  intro q
  exact LinearMap.congr_fun he q
private theorem dynamic_orbit_atTop_exact(F:Index)(sharp:Bool)(f:QuantumTest):
    ∀ᶠ G in (atTop:Filter Index),∀t:ℝ,defectAction G (literalCoreTime F sharp f t)=0:=by
  filter_upwards [finite_core_atTop_exact (sourceOrbit F sharp f)] with G hG
  intro t
  let q:sourceOrbit F sharp f:=(sourceEquiv F sharp f).symm
    (SourceFiniteUnitary.time (sourceGenerator F sharp f) t
      (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩))
  have he:compressionCore G (literalCoreTime F sharp f t)=diagonalAction (literalCoreTime F sharp f t):=hG q
  simp only [defectAction,LinearMap.sub_apply,he,sub_self]

/-- Both actual dynamic carriers generate one ordinary cofinal upper source, uniformly over all times. -/
theorem literal_dynamic_common_upper(F G:Index)(f g:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ G⊆K₀ ∧ ∀K:Index,K₀⊆K →
      (∀t:ℝ,defectAction K (literalCoreTime F false f t)=0) ∧
      (∀t:ℝ,defectAction K (literalCoreTime G true g t)=0):=by
  classical
  have h:=((dynamic_orbit_atTop_exact F false f).and (dynamic_orbit_atTop_exact G true g)).and
    (eventually_ge_atTop (F∪G))
  obtain ⟨K₀,hK₀⟩:=Filter.eventually_atTop.mp h
  have hu:= (hK₀ K₀ le_rfl).2
  refine ⟨K₀,Finset.union_subset_iff.mp hu |>.1,Finset.union_subset_iff.mp hu |>.2,?_⟩
  intro K hK
  exact (hK₀ K hK).1

end LowEnergy.FullYDynamicSource
