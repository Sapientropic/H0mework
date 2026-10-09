import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYSourceJetReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicCofinalJets
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussUnitaryHistory FullYDynamicSource FullYDynamicResponse CompositeFullYBorn SourceResolventBandLimit MeasureTheory
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev Z(advanced:Bool)(μ w:ℝ):ℂ:=line (FullYPairedParseval.direction advanced*μ) w
private abbrev J(sharp:Bool)(n:ℕ)(q:QuantumTest):QuantumTest:=
  if sharp then (GaussFullHamiltonian.sharpAction^n) q else (GaussFullHamiltonian.fullAction^n) q
attribute [local irreducible] embed sourcePair literalResponse sourceReader literalCoreResolvent literalSharpResolvent
  GaussFullHamiltonian.fullAction GaussFullHamiltonian.sharpAction
local instance : SecondCountableTopologyEither ℝ H := ⟨Or.inl inferInstance⟩

theorem actual_core_response_word_L2(F:Index)(sharp:Bool)(q:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(A:End):
    MemLp (fun w:ℝ=>embed (A (literalResponse F sharp q advanced μ hμ w))) 2 volume:=by
  have hc:Continuous (fun w:ℝ=>sourceReader F sharp q A (embed (literalResponse F sharp q advanced μ hμ w))):=
    (sourceReader F sharp q A).continuous.comp (actual_response_continuous F sharp q advanced μ hμ)
  have he(w:ℝ):sourceReader F sharp q A (embed (literalResponse F sharp q advanced μ hμ w))=
      embed (A (literalResponse F sharp q advanced μ hμ w)):=
    source_reader_return F sharp q _ A (actual_response_orbit F sharp q advanced μ hμ w)
  have hc' : Continuous (fun w:ℝ=>embed (A (literalResponse F sharp q advanced μ hμ w))) := hc.congr he
  have hm : AEStronglyMeasurable (fun w:ℝ=>embed (A (literalResponse F sharp q advanced μ hμ w))) volume := hc'.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hm).mpr
    (actual_core_word_square_integrable F sharp q advanced μ hμ A)

private theorem power_L2(F G:Index)(q:QuantumTest)(n:ℕ)(sharp advanced:Bool)(μ:ℝ)(hμ:0<μ)(A:End)
    (he:∀w:ℝ,Z advanced μ w^n • (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)=
      literalResponse F sharp (J sharp n q) advanced μ hμ w-literalResponse G sharp (J sharp n q) advanced μ hμ w):
    MemLp (fun w:ℝ=>embed (A (Z advanced μ w^n •
      (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)))) 2 volume:=by
  have h:=(actual_core_response_word_L2 F sharp (J sharp n q) advanced μ hμ A).sub
    (actual_core_response_word_L2 G sharp (J sharp n q) advanced μ hμ A)
  apply h.ae_eq
  exact Filter.Eventually.of_forall (fun w=>by simp only [he,map_sub,Pi.sub_apply])

private theorem line_one_nonzero(w:ℝ):line 1 w≠0:=by
  intro h
  have hi:=congrArg Complex.im h
  simp only [line_im,Complex.zero_im] at hi
  norm_num at hi
private theorem inverse_line_L2:MemLp (fun w:ℝ=>(line 1 w)⁻¹) 2 volume:=by
  have hc:Continuous (fun w:ℝ=>(line 1 w)⁻¹):=by
    apply Continuous.inv₀
    · exact Complex.continuous_ofReal.add continuous_const
    · exact line_one_nonzero
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply (SourceResolventLorentzian.kernel_integrable 1 0 (by norm_num)).congr
  exact Filter.Eventually.of_forall (fun w=>by
    have h:=SourceResolventLorentzian.inverse_norm_square 1 0 w
    simpa only [Complex.ofReal_zero,zero_sub,inv_neg,norm_neg,line,Complex.ofReal_one,one_mul,mul_one] using h.symm)

private theorem weighted_L1(F G:Index)(q:QuantumTest)(n:ℕ)(sharp advanced:Bool)(μ:ℝ)(hμ:0<μ)(A:End)
    (h0:MemLp (fun w:ℝ=>embed (A (Z advanced μ w^n •
      (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)))) 2 volume)
    (h1:MemLp (fun w:ℝ=>embed (A (Z advanced μ w^(n+1) •
      (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)))) 2 volume):
    Integrable (fun w:ℝ=>embed (A (Z advanced μ w^n •
      (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)))):=by
  let c:ℂ:=((FullYPairedParseval.direction advanced*μ:ℝ):ℂ)*Complex.I
  have h:=(h1.add (h0.const_smul (Complex.I-c))).smul inverse_line_L2 (r:=1)
  apply (memLp_one_iff_integrable.mp h).congr
  apply Filter.Eventually.of_forall
  intro w
  change (line 1 w)⁻¹ • (embed (A (Z advanced μ w^(n+1) •
    (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)))+
    (Complex.I-c) • embed (A (Z advanced μ w^n •
      (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w))))=
    embed (A (Z advanced μ w^n •
      (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)))
  simp only [map_smul,smul_smul,←add_smul]
  congr 1
  have hz:Z advanced μ w=(w:ℂ)+c:=rfl
  have hline:line 1 w=(w:ℂ)+Complex.I:=by simp only [line,Complex.ofReal_one,one_mul]
  rw [pow_succ,hz]
  field_simp [line_one_nonzero w]
  rw [hline]
  ring

/-- Actual full-source jets pay every prescribed polynomial frequency weight of the two-cutoff response difference in both L2 and absolute L1, before cause, damping or core word is selected. -/
theorem actual_cofinal_fullsource_weighted_difference(B:Index)(q:QuantumTest)(n:ℕ):
    ∃K₀:Index,B⊆K₀ ∧ ∀F:Index,K₀⊆F → ∀G:Index,K₀⊆G →
      ∀sharp advanced:Bool,∀μ:ℝ,∀hμ:0<μ,∀A:End,
      MemLp (fun w:ℝ=>embed (A (Z advanced μ w^n •
        (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)))) 2 volume ∧
      Integrable (fun w:ℝ=>embed (A (Z advanced μ w^n •
        (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)))):=by
  obtain ⟨K₁,hB,hK₁⟩:=actual_cofinal_fullsource_power_return B q q n
  obtain ⟨K₂,h₁₂,hK₂⟩:=actual_cofinal_fullsource_power_return K₁ q q (n+1)
  refine ⟨K₂,Finset.Subset.trans hB h₁₂,fun F hF G hG sharp advanced μ hμ A=>?_⟩
  have hp(w:ℝ):=hK₁ F (Finset.Subset.trans h₁₂ hF) G (Finset.Subset.trans h₁₂ hG)
    (Z advanced μ w) (causal_line_nonreal advanced μ w hμ)
  have hq(w:ℝ):=hK₂ F hF G hG (Z advanced μ w) (causal_line_nonreal advanced μ w hμ)
  have he(k:ℕ)(h:∀w:ℝ,
      Z advanced μ w^k • (literalCoreResolvent F (Z advanced μ w) (causal_line_nonreal advanced μ w hμ) q-
        literalCoreResolvent G (Z advanced μ w) (causal_line_nonreal advanced μ w hμ) q)=
        literalCoreResolvent F (Z advanced μ w) (causal_line_nonreal advanced μ w hμ) ((GaussFullHamiltonian.fullAction^k) q)-
        literalCoreResolvent G (Z advanced μ w) (causal_line_nonreal advanced μ w hμ) ((GaussFullHamiltonian.fullAction^k) q) ∧
      Z advanced μ w^k • (literalSharpResolvent F (Z advanced μ w) (causal_line_nonreal advanced μ w hμ) q-
        literalSharpResolvent G (Z advanced μ w) (causal_line_nonreal advanced μ w hμ) q)=
        literalSharpResolvent F (Z advanced μ w) (causal_line_nonreal advanced μ w hμ) ((GaussFullHamiltonian.sharpAction^k) q)-
        literalSharpResolvent G (Z advanced μ w) (causal_line_nonreal advanced μ w hμ) ((GaussFullHamiltonian.sharpAction^k) q)):
      ∀w:ℝ,Z advanced μ w^k • (literalResponse F sharp q advanced μ hμ w-literalResponse G sharp q advanced μ hμ w)=
        literalResponse F sharp (J sharp k q) advanced μ hμ w-literalResponse G sharp (J sharp k q) advanced μ hμ w:=by
    intro w
    cases sharp
    · simpa only [literalResponse,J,Bool.false_eq_true,ite_false] using (h w).1
    · simpa only [literalResponse,J,ite_true] using (h w).2
  have h0:=power_L2 F G q n sharp advanced μ hμ A (he n hp)
  have h1:=power_L2 F G q (n+1) sharp advanced μ hμ A (he (n+1) hq)
  exact ⟨h0,weighted_L1 F G q n sharp advanced μ hμ A h0 h1⟩

end LowEnergy.FullYDynamicCofinalJets
