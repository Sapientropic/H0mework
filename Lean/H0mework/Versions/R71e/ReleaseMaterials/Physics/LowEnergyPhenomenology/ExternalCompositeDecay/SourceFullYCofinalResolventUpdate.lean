import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYLiteralDynamicDefect
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicSourceRefinement
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceScalarPairedTransport GaussUnitaryHistory FullYDynamicSource Filter
open scoped Topology InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
local instance refinementLabelFintype : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _
attribute [local irreducible] sourcePair embed diagonalAction GaussYukawaOperator.originalAction
  GaussFullHamiltonian.adjointAction literalCoreResolvent literalSharpResolvent sourceOrbit sourceSpace

private theorem core_atTop_exact(q:QuantumTest):
    ∀ᶠ K in (atTop:Filter Index),compressionCore K q=diagonalAction q:=by
  classical
  let x:diagonal.domain:=coreEquiv q
  let y:diagonal.domain:=⟨diagonal x,diagonal_invariant x⟩
  refine Filter.eventually_atTop.mpr
    ⟨GaussGradedCompression.support x∪GaussGradedCompression.support y,fun K hK=>?_⟩
  apply embed_injective
  have hx:∀g:NativeHistoryGrade.Label,GaussGradedCompression.piece g x∈K:=by
    intro g
    exact hK (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g,Finset.mem_univ g,rfl⟩))
  have hy:∀g:NativeHistoryGrade.Label,GaussGradedCompression.piece g y∈K:=by
    intro g
    exact hK (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,Finset.mem_univ g,rfl⟩))
  have hc:embed (compressionCore K q)=GaussGradedCompression.compression K (embed q):=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hd:diagonal x=embed (diagonalAction q):=by
    change embed (diagonalAction (coreEquiv.symm (coreEquiv q)))=_
    rw [coreEquiv.symm_apply_apply]
  exact hc.trans ((GaussGradedCompression.compression_core_exact K x hx hy).trans hd)

private theorem finite_orbit_atTop_exact(S:Submodule ℂ QuantumTest)[FiniteDimensional ℂ S]:
    ∀ᶠ K in (atTop:Filter Index),∀q:S,defectAction K q.val=0:=by
  let b:=Module.finBasis ℂ S
  have hh:∀i,∀ᶠ K in (atTop:Filter Index),compressionCore K (b i).val=diagonalAction (b i).val:=
    fun i=>core_atTop_exact (b i).val
  filter_upwards [Filter.eventually_all.mpr hh] with K hK
  have he:(compressionCore K).comp S.subtype=diagonalAction.comp S.subtype:=by
    apply b.ext
    intro i
    exact hK i
  intro q
  have hq:=LinearMap.congr_fun he q
  change compressionCore K q.val=diagonalAction q.val at hq
  simp only [defectAction,LinearMap.sub_apply,hq,sub_self]

/-- A single upper source covers each independently generated whole orbit, before frequency is chosen. -/
theorem literal_orbit_common_upper(F G:Index)(f g:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ G⊆K₀ ∧ ∀K:Index,K₀⊆K →
      (∀q:sourceOrbit F false f,defectAction K q.val=0) ∧
      (∀q:sourceOrbit G true g,defectAction K q.val=0):=by
  classical
  have h:=((finite_orbit_atTop_exact (sourceOrbit F false f)).and
    (finite_orbit_atTop_exact (sourceOrbit G true g))).and (eventually_ge_atTop (F∪G))
  obtain ⟨K₀,hK₀⟩:=Filter.eventually_atTop.mp h
  have hu:=(hK₀ K₀ le_rfl).2
  exact ⟨K₀,(Finset.union_subset_iff.mp hu).1,(Finset.union_subset_iff.mp hu).2,
    fun K hK=>(hK₀ K hK).1⟩

private def branchResolvent(F:Index)(sharp:Bool)(z:ℂ)(hz:z.im≠0):End:=
  if sharp then literalSharpResolvent F z hz else literalCoreResolvent F z hz
private def branchShift(F:Index)(sharp:Bool)(z:ℂ):End:=
  compressionCore F+sourceY sharp-z • (1:End)
private theorem branch_left(F:Index)(sharp:Bool)(z:ℂ)(hz:z.im≠0):
    branchResolvent F sharp z hz*branchShift F sharp z=1:=by
  cases sharp
  · exact literal_core_left_inverse F z hz
  · exact literal_sharp_left_inverse F z hz
private theorem branch_right(F:Index)(sharp:Bool)(z:ℂ)(hz:z.im≠0):
    branchShift F sharp z*branchResolvent F sharp z hz=1:=by
  cases sharp
  · exact literal_core_right_inverse F z hz
  · exact literal_sharp_right_inverse F z hz
private theorem branch_mem(F:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ)(hz:z.im≠0):
    branchResolvent F sharp z hz f∈sourceOrbit F sharp f:=by
  let q:sourceOrbit F sharp f:=(sourceEquiv F sharp f).symm
    (sourceResolvent F sharp f z (sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩))
  have he:q.val=branchResolvent F sharp z hz f:=by
    cases sharp <;> exact source_resolvent_literal_return F _ f z hz
  exact he ▸ q.property

section Algebra
variable {V:Type*}[AddCommGroup V][Module ℂ V]
private theorem inverse_defect_update(A R:V→ₗ[ℂ]V)(hR:R*A=1)(f x d:V)(h:A x=f+d):
    R f-x= -R d:=by
  have hi: R (A x)=x:=LinearMap.congr_fun hR x
  have he:R f+R d=x:=(map_add R f d).symm.trans ((congrArg R h).symm.trans hi)
  rw [←he]
  abel
end Algebra

private theorem branch_update(F K:Index)(sharp:Bool)(f:QuantumTest)(z:ℂ)(hz:z.im≠0)
    (hK:defectAction K (branchResolvent F sharp z hz f)=0):
    branchResolvent K sharp z hz f-branchResolvent F sharp z hz f=
      -branchResolvent K sharp z hz (defectAction F (branchResolvent F sharp z hz f)):=by
  have he:branchShift K sharp z=branchShift F sharp z+defectAction F-defectAction K:=by
    unfold branchShift defectAction
    abel
  have hr:branchShift F sharp z (branchResolvent F sharp z hz f)=f:=
    LinearMap.congr_fun (branch_right F sharp z hz) f
  have hs:branchShift K sharp z (branchResolvent F sharp z hz f)=
      f+defectAction F (branchResolvent F sharp z hz f):=by
    rw [he,LinearMap.sub_apply,LinearMap.add_apply,hr,hK,sub_zero]
  exact inverse_defect_update (branchShift K sharp z) (branchResolvent K sharp z hz)
    (branch_left K sharp z hz) f _ _ hs

/-- The original full-Y response changes by its own frozen full-H0 residual; the comparison cutoff is eliminated. -/
theorem literal_cofinal_resolvent_update(F G:Index)(f g:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ G⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀z:ℂ,∀hz:z.im≠0,
      defectAction K (literalCoreResolvent F z hz f)=0 ∧
      defectAction K (literalSharpResolvent G z hz g)=0 ∧
      literalCoreResolvent K z hz f-literalCoreResolvent F z hz f=
        -literalCoreResolvent K z hz (defectAction F (literalCoreResolvent F z hz f)) ∧
      literalSharpResolvent K z hz g-literalSharpResolvent G z hz g=
        -literalSharpResolvent K z hz (defectAction G (literalSharpResolvent G z hz g)):=by
  obtain ⟨K₀,hF,hG,hK₀⟩:=literal_orbit_common_upper F G f g
  refine ⟨K₀,hF,hG,?_⟩
  intro K hK z hz
  have hleft:= (hK₀ K hK).1 ⟨_,branch_mem F false f z hz⟩
  have hright:= (hK₀ K hK).2 ⟨_,branch_mem G true g z hz⟩
  exact ⟨hleft,hright,branch_update F K false f z hz hleft,
    branch_update G K true g z hz hright⟩

private theorem conjugate_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0:=by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
private theorem primal_two_leg(F:Index)(z:ℂ)(hz:z.im≠0)(f g:QuantumTest):
    sourcePair f (literalCoreResolvent F z hz g)=
      sourcePair (literalSharpResolvent F (star z) (conjugate_nonreal z hz) f) g:=by
  have h:=congrArg (starRingEnd ℂ)
    (literal_two_leg_pair F (star z) (conjugate_nonreal z hz) g f)
  simpa only [sourcePair,inner_conj_symm,star_star] using h.symm
private theorem pair_neg(f g:QuantumTest):sourcePair f (-g)= -sourcePair f g:=by
  simp only [sourcePair,map_neg,inner_neg_right]

/-- The comparison response is priced by the original independent leg and the fixed source's own defect. -/
theorem literal_cofinal_signed_price(F G:Index)(f g:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ G⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀z:ℂ,∀hz:z.im≠0,∀a b:QuantumTest,
      sourcePair a (literalCoreResolvent K z hz f-literalCoreResolvent F z hz f)=
        -sourcePair (literalSharpResolvent K (star z) (conjugate_nonreal z hz) a)
          (defectAction F (literalCoreResolvent F z hz f)) ∧
      sourcePair b (literalSharpResolvent K z hz g-literalSharpResolvent G z hz g)=
        -sourcePair (literalCoreResolvent K (star z) (conjugate_nonreal z hz) b)
          (defectAction G (literalSharpResolvent G z hz g)):=by
  obtain ⟨K₀,hF,hG,hK₀⟩:=literal_cofinal_resolvent_update F G f g
  refine ⟨K₀,hF,hG,?_⟩
  intro K hK z hz a b
  have h:=hK₀ K hK z hz
  constructor
  · rw [h.2.2.1,pair_neg]
    exact congrArg Neg.neg (primal_two_leg K z hz a _)
  · rw [h.2.2.2,pair_neg]
    exact congrArg Neg.neg (literal_two_leg_pair K z hz b _)

end LowEnergy.FullYDynamicSourceRefinement
