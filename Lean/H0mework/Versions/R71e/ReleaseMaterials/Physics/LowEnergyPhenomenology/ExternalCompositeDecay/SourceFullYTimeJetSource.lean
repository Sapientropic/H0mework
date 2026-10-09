import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYWeightedDifference
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicTimeJets
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussUnitaryHistory FullYDynamicSource FullYDynamicSourceRefinement CompositeFullYBorn
open SourceScalarPairedTransport Filter
open scoped Topology
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev HF(F:Index)(sharp:Bool):End := compressionCore F+sourceY sharp
private abbrev HS(sharp:Bool):End := diagonalAction+sourceY sharp
attribute [local irreducible] embed literalCoreTime sourceReader sourceOrbit sourceSpace
  sourceY diagonalAction compressionCore

private theorem time_orbit(F:Index)(sharp:Bool)(q:QuantumTest)(t:ℝ):
    literalCoreTime F sharp q t∈sourceOrbit F sharp q := by
  unfold literalCoreTime
  exact ((sourceEquiv F sharp q).symm
    (SourceFiniteUnitary.time (sourceGenerator F sharp q) t
      (sourceEquiv F sharp q ⟨q,sourceOrbit_input F sharp q⟩))).property

/-- The original finite source orbit pays differentiation of any core word;
the word is never extended as an unbounded operator on the whole Hilbert space. -/
theorem actual_time_word_derivative(F:Index)(sharp:Bool)(q:QuantumTest)(A:End)(t:ℝ):
    HasDerivAt (fun s:ℝ=>embed (A (literalCoreTime F sharp q s)))
      ((-Complex.I) • embed (A (HF F sharp (literalCoreTime F sharp q t)))) t := by
  let L := sourceReader F sharp q A
  have hd := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (literal_core_time_derivative F sharp q t)
  have he(s:ℝ):L (embed (literalCoreTime F sharp q s))=
      embed (A (literalCoreTime F sharp q s)) :=
    source_reader_return F sharp q _ A (time_orbit F sharp q s)
  have hv:L ((-Complex.I) • embed (HF F sharp (literalCoreTime F sharp q t)))=
      (-Complex.I) • embed (A (HF F sharp (literalCoreTime F sharp q t))) := by
    rw [map_smul]
    congr 1
    exact source_reader_return F sharp q _ A
      (sourceOrbit_invariant F sharp q _ (time_orbit F sharp q t))
  exact (hd.congr_deriv hv).congr_of_eventuallyEq (Eventually.of_forall (fun s=>(he s).symm))

def actualTimeJet(F:Index)(sharp:Bool)(q:QuantumTest)(A:End)(n:ℕ)(t:ℝ):H :=
  (-Complex.I)^n • embed (A ((HF F sharp^n) (literalCoreTime F sharp q t)))

/-- Every time jet is generated from the same actual source orbit and full
compressed H0+Y, or its independent sharp generator. -/
theorem actual_time_jet_derivative(F:Index)(sharp:Bool)(q:QuantumTest)(A:End)(n:ℕ)(t:ℝ):
    HasDerivAt (actualTimeJet F sharp q A n) (actualTimeJet F sharp q A (n+1) t) t := by
  have h := (actual_time_word_derivative F sharp q (A*(HF F sharp)^n) t).const_smul ((-Complex.I)^n)
  simpa only [actualTimeJet,Pi.smul_apply,Module.End.mul_apply,pow_succ,smul_smul] using! h

private theorem source_power_event(B:Index)(q r:QuantumTest)(n:ℕ):
    ∃K₀:Index,B⊆K₀ ∧ ∀F:Index,K₀⊆F → ∀m:ℕ,m≤n →
      (HF F false^m) q=(HS false^m) q ∧ (HF F true^m) r=(HS true^m) r := by
  induction n generalizing B q r with
  | zero =>
    refine ⟨B,Finset.Subset.refl _,fun F _ m hm=>?_⟩
    have h:m=0 := Nat.eq_zero_of_le_zero hm
    simp only [h,pow_zero,Module.End.one_apply,and_self]
  | succ n ih =>
    obtain ⟨K₁,hB,hK₁⟩ := ih B (HS false q) (HS true r)
    obtain ⟨K₂,h₁₂,_h₂,hK₂⟩ := literal_orbit_common_upper K₁ K₁ q r
    refine ⟨K₂,Finset.Subset.trans hB h₁₂,fun F hF m hm=>?_⟩
    have hq := (hK₂ F hF).1 ⟨q,sourceOrbit_input K₁ false q⟩
    have hr := (hK₂ F hF).2 ⟨r,sourceOrbit_input K₁ true r⟩
    have hP:HF F false q=HS false q := by
      change diagonalAction q-compressionCore F q=0 at hq
      have he:compressionCore F q=diagonalAction q := (sub_eq_zero.mp hq).symm
      simp only [HF,HS,LinearMap.add_apply,he]
    have hS:HF F true r=HS true r := by
      change diagonalAction r-compressionCore F r=0 at hr
      have he:compressionCore F r=diagonalAction r := (sub_eq_zero.mp hr).symm
      simp only [HF,HS,LinearMap.add_apply,he]
    cases m with
    | zero => simp only [pow_zero,Module.End.one_apply,and_self]
    | succ m =>
      have hi := hK₁ F (Finset.Subset.trans h₁₂ hF) m (Nat.le_of_succ_le_succ hm)
      simpa only [pow_succ,Module.End.mul_apply,hP,hS] using hi

/-- Prescribed full-source time jets have one ordinary cofinal event, before
both later cutoffs, any core word or time is selected. -/
theorem actual_cofinal_initial_time_jets(B:Index)(q r:QuantumTest)(N:ℕ):
    ∃K₀:Index,B⊆K₀ ∧ ∀F:Index,K₀⊆F → ∀G:Index,K₀⊆G →
      ∀m:ℕ,m≤N → ∀A:End,
      actualTimeJet F false q A m 0=(-Complex.I)^m • embed (A ((HS false^m) q)) ∧
      actualTimeJet G true r A m 0=(-Complex.I)^m • embed (A ((HS true^m) r)) := by
  obtain ⟨K₀,hB,hK₀⟩ := source_power_event B q r N
  refine ⟨K₀,hB,fun F hF G hG m hm A=>?_⟩
  have hFjet := (hK₀ F hF m hm).1
  have hGjet := (hK₀ G hG m hm).2
  simp only [actualTimeJet,literal_core_time_zero,hFjet,hGjet,and_self]

end LowEnergy.FullYDynamicTimeJets
