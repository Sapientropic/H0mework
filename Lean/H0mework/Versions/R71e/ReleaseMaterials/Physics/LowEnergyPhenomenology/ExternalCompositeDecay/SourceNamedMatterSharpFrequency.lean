import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSharpResolvent
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceActualResolventEnergy
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYBornFrequency
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceHamiltonianSpectralFrequency
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open MeasureTheory GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open GaussFockPair FullYDynamicSource FullYSourceResolventGraphSplice SourceClockYukawaCubicCurrent
open FullYDynamicResponse SourceResolventBandLimit GaussDensityCore
open scoped BigOperators InnerProductSpace
attribute [local irreducible] embed sourcePair literalSharpResolvent literalCoreResolvent

private theorem conj_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0:=by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

section ResolventAlgebra
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
private theorem resolvent_pair(C:E→L[ℂ]E)(hC:IsSelfAdjoint C)(z:ℂ)(hz:z.im≠0)(x y:E):
    inner ℂ x (FullYSourceResolventGraphSplice.resolvent C (star z) y)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C z x) y:=by
  let R:=FullYSourceResolventGraphSplice.resolvent C
  have hx:=congrArg (fun T:E→L[ℂ]E=>T x) (resolvent_right C hC z hz)
  have hy:=congrArg (fun T:E→L[ℂ]E=>T y) (resolvent_right C hC (star z) (conj_nonreal z hz))
  change C (R z x)-z • R z x=x at hx
  change C (R (star z) y)-star z • R (star z) y=y at hy
  change inner ℂ x (R (star z) y)=inner ℂ (R z x) y
  calc
    _=inner ℂ (C (R z x)-z • R z x) (R (star z) y):=by rw [hx]
    _=inner ℂ (R z x) (C (R (star z) y)-star z • R (star z) y):=by
      rw [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right]
      have hc:inner ℂ (C (R z x)) (R (star z) y)=inner ℂ (R z x) (C (R (star z) y)):=
        hC.isSymmetric (R z x) (R (star z) y)
      rw [hc]
      rfl
    _=_:=by rw [hy]

private theorem resolvent_commute(C:E→L[ℂ]E)(hC:IsSelfAdjoint C)(z w:ℂ)(hz:z.im≠0)(hw:w.im≠0):
    Commute (FullYSourceResolventGraphSplice.resolvent C z) (FullYSourceResolventGraphSplice.resolvent C w):=by
  have hc:Commute (C-z • 1) (C-w • 1):=
    ((Commute.refl C).sub_right ((Commute.one_right C).smul_right w)).sub_left
      ((Commute.one_left _).smul_left z)
  obtain ⟨u,hu⟩:=resolvent_isUnit C hC z hz
  obtain ⟨v,hv⟩:=resolvent_isUnit C hC w hw
  unfold FullYSourceResolventGraphSplice.resolvent
  rw [←hu,←hv] at hc ⊢
  rw [Ring.inverse_unit,Ring.inverse_unit]
  exact hc.units_inv_left.units_inv_right
end ResolventAlgebra

private theorem finite_pair(F:Index)(z:ℂ)(hz:z.im≠0)(x y:H):
    inner ℂ x (finiteResolvent F (star z) y)=inner ℂ (finiteResolvent F z x) y:=
  resolvent_pair (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz x y
private theorem finite_commute(F:Index)(z w:ℂ)(hz:z.im≠0)(hw:w.im≠0):
    Commute (finiteResolvent F z) (finiteResolvent F w):=
  resolvent_commute (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z w hz hw

private theorem finite_conjugate_norm(F:Index)(z:ℂ)(hz:z.im≠0)(x:H):
    ‖finiteResolvent F (star z) x‖^2=‖finiteResolvent F z x‖^2:=by
  have hc:=congrArg (fun T:H→L[ℂ]H=>T x) (finite_commute F z (star z) hz (conj_nonreal z hz)).eq
  simp only [mul_apply_eq_comp] at hc
  have h:inner ℂ (finiteResolvent F (star z) x) (finiteResolvent F (star z) x)=
      inner ℂ (finiteResolvent F z x) (finiteResolvent F z x):=by
    calc
      _=inner ℂ x (finiteResolvent F z (finiteResolvent F (star z) x)):=by
        simpa only [star_star] using (finite_pair F (star z) (conj_nonreal z hz) x (finiteResolvent F (star z) x)).symm
      _=inner ℂ x (finiteResolvent F (star z) (finiteResolvent F z x)):=congrArg (fun u:H=>inner ℂ x u) hc
      _=_:=finite_pair F z hz x (finiteResolvent F z x)
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

private theorem core_embed(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f):=by
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The actual primal response retains all its output, while every generated external epsilon test reads exactly its bottom-grade response. -/
theorem actual_epsilon_primal_pair(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(e:Epsilon20)(f:ScalarTest)(g:QuantumTest):
    sourcePair (epsilonSection dual e f) (literalCoreResolvent F z hz g)=
      sourcePair (epsilonSection dual e f) (resolventCore F z hz g):=by
  have h:=congrArg (starRingEnd ℂ)
    (literal_two_leg_pair F (star z) (conj_nonreal z hz) g (epsilonSection dual e f))
  simp only [sourcePair,inner_conj_symm,star_star] at h
  rw [actual_epsilon_sharp_resolvent] at h
  simp only [sourcePair]
  change inner ℂ (embed (epsilonSection dual e f)) (embed (literalCoreResolvent F z hz g))=_
  rw [←h]
  simp only [core_embed]
  simpa only [star_star] using (finite_pair F (star z) (conj_nonreal z hz) (embed (epsilonSection dual e f)) (embed g)).symm

private theorem causal_sharp_norm(F:Index)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ)
    (dual:Bool)(e:Epsilon20)(f:ScalarTest):
    ‖embed (literalResponse F true (epsilonSection dual e f) advanced μ hμ w)‖^2=
      ‖finiteResolvent F (line μ w) (embed (epsilonSection dual e f))‖^2:=by
  change ‖embed (literalSharpResolvent F (line (FullYPairedParseval.direction advanced*μ) w)
    (causal_line_nonreal advanced μ w hμ) (epsilonSection dual e f))‖^2=_
  rw [actual_epsilon_sharp_resolvent]
  cases advanced with
  | false=>simp only [FullYPairedParseval.direction,Bool.false_eq_true,ite_false,one_mul]
  | true=>
    simp only [FullYPairedParseval.direction,ite_true,neg_one_mul]
    have he:line (-μ) w=star (line μ w):=by
      apply Complex.ext <;> simp [line,Complex.mul_re,Complex.mul_im]
    rw [he]
    exact finite_conjugate_norm F (line μ w) (by simpa only [line_im] using hμ.ne') _

/-- Both causal sharp responses pay a positive full-frequency L1 price independent of F. -/
theorem actual_epsilon_sharp_frequency_integrable(F:Index)(advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (dual:Bool)(e:Epsilon20)(f:ScalarTest):
    Integrable (fun w:ℝ=>‖embed (literalResponse F true (epsilonSection dual e f) advanced μ hμ w)‖^2):=by
  simp_rw [causal_sharp_norm]
  simpa only [line,mul_comm (μ:ℂ) Complex.I] using
    SourceActualResolventEnergy.actual_square_integrable F μ hμ (embed (epsilonSection dual e f))

/-- The exact same-source positive mass has no cutoff-dependent constant or supplied domination. -/
theorem actual_epsilon_sharp_common_frequency_price(F:Index)(advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (dual:Bool)(e:Epsilon20)(f:ScalarTest):
    (∫w:ℝ,‖embed (literalResponse F true (epsilonSection dual e f) advanced μ hμ w)‖^2)=
      Real.pi/μ*(‖e‖^2*‖scalarLp 3 f‖^2):=by
  simp_rw [causal_sharp_norm]
  have h:=SourceActualResolventEnergy.actual_square_integral F μ hμ (embed (epsilonSection dual e f))
  simp only [line,mul_comm (μ:ℂ) Complex.I]
  rw [h]
  change Real.pi/μ*‖embed (epsilon20Test dual e f)‖^2=_
  rw [actual_epsilon20_source_norm,mul_pow]

/-- One generated finite positive measure reads the actual full sharp-Y epsilon response on both causal lines, with full-frequency L1 convergence along the original source filter. -/
theorem actual_epsilon_sharp_source_frequency_measure(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    ∃ν:Measure ℝ,IsFiniteMeasure ν ∧
      ν Set.univ=ENNReal.ofReal (‖e‖^2*‖scalarLp 3 f‖^2) ∧
      ∀(μ:ℝ)(hμ:0<μ),
        Integrable (SourceHamiltonianSpectralFrequency.profile ν μ) ∧
        (∫w:ℝ,SourceHamiltonianSpectralFrequency.profile ν μ w)=
          Real.pi/μ*(‖e‖^2*‖scalarLp 3 f‖^2) ∧
        ∀advanced:Bool,Filter.Tendsto
          (fun F:Index=>∫w:ℝ,|‖embed (literalResponse F true (epsilonSection dual e f)
            advanced μ hμ w)‖^2-SourceHamiltonianSpectralFrequency.profile ν μ w|)
          (sourceFilter:Filter Index) (nhds 0):=by
  let g:GaussDiagonalHistory.diagonal.domain:=coreEquiv (epsilonSection dual e f)
  obtain ⟨ν,hfinite,hm,hν⟩:=SourceHamiltonianSpectralFrequency.actual_source_frequency_measure g
  have hn:‖(g:H)‖^2=‖e‖^2*‖scalarLp 3 f‖^2:=by
    change ‖embed (epsilon20Test dual e f)‖^2=_
    rw [actual_epsilon20_source_norm,mul_pow]
  refine ⟨ν,hfinite,hm.trans (congrArg ENNReal.ofReal hn),fun μ hμ=>?_⟩
  obtain ⟨hi,hprice,hlimit⟩:=hν μ hμ
  refine ⟨hi,hprice.trans (congrArg (fun r:ℝ=>Real.pi/μ*r) hn),fun advanced=>?_⟩
  have hg:(g:H)=embed (epsilonSection dual e f):=rfl
  rw [hg] at hlimit
  simpa only [causal_sharp_norm] using hlimit

end LowEnergy.NamedColorQtNext
