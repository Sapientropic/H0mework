import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCofinalResolventUpdate
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYUncutRetardedKernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicSourceRefinement
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceScalarPairedTransport GaussUnitaryHistory FullYDynamicSource FullYDynamicSourceNext Filter
open scoped Topology InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair embed diagonalAction GaussYukawaOperator.originalAction
  GaussFullHamiltonian.adjointAction literalCoreResolvent literalSharpResolvent sourceOrbit sourceSpace

private theorem full_forcing_return(K:Index)(q:QuantumTest)(z:ℂ)(hz:z.im≠0)
    (hq:defectAction K q=0):
    literalCoreResolvent K z hz ((GaussFullHamiltonian.fullAction-z • (1:End)) q)=q:=by
  have he:GaussFullHamiltonian.fullAction-z • (1:End)=literalCoreShift K z+defectAction K:=by
    unfold GaussFullHamiltonian.fullAction literalCoreShift defectAction
    abel
  rw [he,LinearMap.add_apply,hq,add_zero]
  exact LinearMap.congr_fun (literal_core_left_inverse K z hz) q
private theorem sharp_forcing_return(K:Index)(q:QuantumTest)(z:ℂ)(hz:z.im≠0)
    (hq:defectAction K q=0):
    literalSharpResolvent K z hz ((GaussFullHamiltonian.sharpAction-z • (1:End)) q)=q:=by
  have he:GaussFullHamiltonian.sharpAction-z • (1:End)=literalSharpShift K z+defectAction K:=by
    unfold GaussFullHamiltonian.sharpAction literalSharpShift defectAction
    abel
  rw [he,LinearMap.add_apply,hq,add_zero]
  exact LinearMap.congr_fun (literal_sharp_left_inverse K z hz) q

/-- Original full-H0 forcing is solved exactly on one ordinary cofinal event, before any frequency is selected. -/
theorem actual_full_source_forcing_return(F:Index)(q r:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀z:ℂ,∀hz:z.im≠0,
      literalCoreResolvent K z hz ((GaussFullHamiltonian.fullAction-z • (1:End)) q)=q ∧
      literalSharpResolvent K z hz ((GaussFullHamiltonian.sharpAction-z • (1:End)) r)=r:=by
  obtain ⟨K₀,hF,_hG,hK₀⟩:=literal_orbit_common_upper F F q r
  refine ⟨K₀,hF,?_⟩
  intro K hK z hz
  have hq:defectAction K q=0:=(hK₀ K hK).1 ⟨q,sourceOrbit_input F false q⟩
  have hr:defectAction K r=0:=(hK₀ K hK).2 ⟨r,sourceOrbit_input F true r⟩
  exact ⟨full_forcing_return K q z hz hq,sharp_forcing_return K r z hz hr⟩

private theorem causal_nonreal(advanced:Bool)(z:ℂ)
    (hz:if advanced then z.im<0 else 0<z.im):z.im≠0:=by
  cases advanced
  · exact ne_of_gt hz
  · exact ne_of_lt hz
private theorem full_kernel_return(K:Index)(q:QuantumTest)(advanced:Bool)(z:ℂ)
    (hz:if advanced then z.im<0 else 0<z.im)
    (hq:literalCoreResolvent K z (causal_nonreal advanced z hz)
      ((GaussFullHamiltonian.fullAction-z • (1:End)) q)=q):
    Tendsto (uncutCausalVector K false ((GaussFullHamiltonian.fullAction-z • (1:End)) q) advanced z)
      atTop (𝓝 (embed q)):=by
  have h:=actual_original_uncut_retarded_kernel K false
    ((GaussFullHamiltonian.fullAction-z • (1:End)) q) advanced z hz
  simpa only [Bool.false_eq_true,ite_false,hq] using h
private theorem sharp_kernel_return(K:Index)(q:QuantumTest)(advanced:Bool)(z:ℂ)
    (hz:if advanced then z.im<0 else 0<z.im)
    (hq:literalSharpResolvent K z (causal_nonreal advanced z hz)
      ((GaussFullHamiltonian.sharpAction-z • (1:End)) q)=q):
    Tendsto (uncutCausalVector K true ((GaussFullHamiltonian.sharpAction-z • (1:End)) q) advanced z)
      atTop (𝓝 (embed q)):=by
  have h:=actual_original_uncut_retarded_kernel K true
    ((GaussFullHamiltonian.sharpAction-z • (1:End)) q) advanced z hz
  simpa only [ite_true,hq] using h

/-- Both actual causal half-lines consume the original full-Y forcing and return the original μ₀ source exactly. -/
theorem actual_full_source_causal_return(F:Index)(q r:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀advanced:Bool,∀z:ℂ,
      (if advanced then z.im<0 else 0<z.im) →
      Tendsto (uncutCausalVector K false ((GaussFullHamiltonian.fullAction-z • (1:End)) q) advanced z)
        atTop (𝓝 (embed q)) ∧
      Tendsto (uncutCausalVector K true ((GaussFullHamiltonian.sharpAction-z • (1:End)) r) advanced z)
        atTop (𝓝 (embed r)):=by
  obtain ⟨K₀,hF,hK₀⟩:=actual_full_source_forcing_return F q r
  refine ⟨K₀,hF,?_⟩
  intro K hK advanced z hz
  have h:=hK₀ K hK z (causal_nonreal advanced z hz)
  exact ⟨full_kernel_return K q advanced z hz h.1,sharp_kernel_return K r advanced z hz h.2⟩

private theorem conjugate_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0:=by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
private theorem primal_pair(K:Index)(z:ℂ)(hz:z.im≠0)(a f:QuantumTest):
    sourcePair a (literalCoreResolvent K z hz f)=
      sourcePair (literalSharpResolvent K (star z) (conjugate_nonreal z hz) a) f:=by
  have h:=congrArg (starRingEnd ℂ)
    (literal_two_leg_pair K (star z) (conjugate_nonreal z hz) f a)
  simpa only [sourcePair,inner_conj_symm,star_star] using h.symm

/-- The full original weak equation holds for every forcing on one common test-generated cofinal event. -/
theorem actual_full_source_weak_equation(F:Index)(q r:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀z:ℂ,∀hz:z.im≠0,∀f g:QuantumTest,
      sourcePair ((GaussFullHamiltonian.sharpAction-(star z) • (1:End)) q)
        (literalCoreResolvent K z hz f)=sourcePair q f ∧
      sourcePair ((GaussFullHamiltonian.fullAction-(star z) • (1:End)) r)
        (literalSharpResolvent K z hz g)=sourcePair r g:=by
  obtain ⟨K₀,hF,hK₀⟩:=actual_full_source_forcing_return F r q
  refine ⟨K₀,hF,?_⟩
  intro K hK z hz f g
  have h:=hK₀ K hK (star z) (conjugate_nonreal z hz)
  exact ⟨(primal_pair K z hz _ f).trans (congrArg (fun a:QuantumTest=>sourcePair a f) h.2),
    (literal_two_leg_pair K z hz _ g).trans (congrArg (fun a:QuantumTest=>sourcePair a g) h.1)⟩

private theorem inner_limit {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E]
    (a:E)(u:ℝ→E)(x:E)(hu:Tendsto u atTop (𝓝 x)):
    Tendsto (fun t:ℝ=>inner ℂ a (u t)) atTop (𝓝 (inner ℂ a x)):=
  (continuous_const.inner continuous_id).tendsto x |>.comp hu
private theorem causal_pair_limit(K:Index)(sharp:Bool)(f a:QuantumTest)(advanced:Bool)(z:ℂ)
    (hz:if advanced then z.im<0 else 0<z.im):
    Tendsto (fun T:ℝ=>inner ℂ (embed a) (uncutCausalVector K sharp f advanced z T)) atTop
      (𝓝 (sourcePair a (if sharp then literalSharpResolvent K z (causal_nonreal advanced z hz) f
        else literalCoreResolvent K z (causal_nonreal advanced z hz) f))):=by
  simpa only [sourcePair] using inner_limit (embed a) _ _
    (actual_original_uncut_retarded_kernel K sharp f advanced z hz)

/-- Actual full-Y propagation solves both independent full-source weak equations on both causal half-lines. -/
theorem actual_full_source_causal_weak_equation(F:Index)(q r:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀advanced:Bool,∀z:ℂ,
      (if advanced then z.im<0 else 0<z.im) → ∀f g:QuantumTest,
      Tendsto (fun T:ℝ=>inner ℂ
        (embed ((GaussFullHamiltonian.sharpAction-(star z) • (1:End)) q))
        (uncutCausalVector K false f advanced z T)) atTop (𝓝 (sourcePair q f)) ∧
      Tendsto (fun T:ℝ=>inner ℂ
        (embed ((GaussFullHamiltonian.fullAction-(star z) • (1:End)) r))
        (uncutCausalVector K true g advanced z T)) atTop (𝓝 (sourcePair r g)):=by
  obtain ⟨K₀,hF,hK₀⟩:=actual_full_source_weak_equation F q r
  refine ⟨K₀,hF,?_⟩
  intro K hK advanced z hz f g
  have h:=hK₀ K hK z (causal_nonreal advanced z hz) f g
  constructor
  · simpa only [Bool.false_eq_true,ite_false,h.1] using causal_pair_limit K false f
      ((GaussFullHamiltonian.sharpAction-(star z) • (1:End)) q) advanced z hz
  · simpa only [ite_true,h.2] using causal_pair_limit K true g
      ((GaussFullHamiltonian.fullAction-(star z) • (1:End)) r) advanced z hz

end LowEnergy.FullYDynamicSourceRefinement
