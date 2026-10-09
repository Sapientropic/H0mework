import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Sum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Combine
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Reindex
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Coefficient
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.UpperSum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Symmetry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OneBody.Kinetic

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Kinetic
open BasinRefinement SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.OriginalMetric
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy
open scoped BigOperators
noncomputable section

/-- The ordered double contraction splits into the diagonal and the strict
    upper triangle of a symmetric kernel. -/
private theorem double_sum_eq_diag_upper (g : Basis → Basis → ℝ)
    (hsym : ∀ i j : Basis, g i j = g j i) :
    (∑ i : Basis, ∑ j : Basis, g i j) =
      (∑ i : Basis, g i i) +
        (∑ i : Basis, ∑ j : Basis, if i < j then g i j + g j i else 0) := by
  have pieces (i j : Basis) : g i j =
      (if i = j then g i j else 0) + (if i < j then g i j else 0) +
        (if j < i then g i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, lt_asymm h]
    · simp [h]
    · simp [h, ne_of_gt h, lt_asymm h]
  have transpose :
      (∑ i : Basis, ∑ j : Basis, if j < i then g i j else 0) =
        ∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : j < i
    · simp [h, hsym i j]
    · simp [h]
  calc
    (∑ i : Basis, ∑ j : Basis, g i j) =
        ∑ i : Basis, ∑ j : Basis,
          ((if i = j then g i j else 0) + (if i < j then g i j else 0) +
            (if j < i then g i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact pieces i j
    _ = ((∑ i : Basis, ∑ j : Basis, if i = j then g i j else 0) +
          (∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0)) +
            (∑ i : Basis, ∑ j : Basis, if j < i then g i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i : Basis, ∑ j : Basis, if i = j then g i j else 0) +
          ((∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0) +
            (∑ i : Basis, ∑ j : Basis, if j < i then g i j else 0)) :=
        add_assoc _ _ _
    _ = (∑ i : Basis, g i i) +
          ((∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0) +
            (∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0)) := by
      rw [transpose]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = (∑ i : Basis, g i i) +
          ∑ i : Basis, ∑ j : Basis, if i < j then g i j + g j i else 0 := by
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i < j
      · simp [h, hsym i j]
      · simp [h]

/-- The density-matrix contraction over all AO pairs equals the canonical
    upper-triangle pair sum with the symmetric weights. -/
theorem kinetic_pair_expansion :
    (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j) =
      ∑ pair ∈ sourceUpperPairs,
        pairWeight pair * UnifiedOrbitals.kinetic pair.1 pair.2 := by
  have sym : ∀ i j : Basis,
      (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j =
        (densityMatrix j i : ℝ) * UnifiedOrbitals.kinetic j i := by
    intro i j
    rw [kinetic_symmetric]
    rw [show (densityMatrix i j : ℝ) = (densityMatrix j i : ℝ)
      from congrArg _ (original_D3_AO_symmetric i j)]
  have expand := double_sum_eq_diag_upper
    (fun i j => (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j) sym
  rw [expand]
  rw [← diagonal_upper_eq_source_pairs
    (fun k l => pairWeight (k,l) * UnifiedOrbitals.kinetic k l)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j
  · have pw : pairWeight (i,j) =
        (densityMatrix i j : ℝ) + (densityMatrix j i : ℝ) := by
      unfold pairWeight
      rw [if_neg (ne_of_lt h)]
      rfl
    rw [if_pos h, if_pos h, pw, kinetic_symmetric j i]
    ring
  · rw [if_neg h, if_neg h]

/-- The upper-triangle pair sum reindexes to the target ledger addresses. -/
theorem kinetic_target_row_sum :
    (∑ pair ∈ sourceUpperPairs,
        pairWeight pair * UnifiedOrbitals.kinetic pair.1 pair.2) =
      ∑ address : Fin 4851, (sourceCoefficientAt address : ℝ) *
        UnifiedOrbitals.kinetic (targetLeft address.val) (targetRight address.val) := by
  rw [← Finset.sum_coe_sort]
  rw [← (targetUpperEquiv.sum_comp
    (fun pair : sourceUpperPairs =>
      pairWeight pair.1 * UnifiedOrbitals.kinetic pair.1.1 pair.1.2))]
  apply Finset.sum_congr rfl
  intro address _
  have eval : (targetUpperEquiv address).1 = targetPair address := rfl
  rw [eval]
  change pairWeight (targetPair address) *
      UnifiedOrbitals.kinetic (targetLeft address.val) (targetRight address.val) = _
  rw [pair_weight_target]

/-- The recorded cell equals the ledger's kinetic column entry. -/
theorem recorded_kinetic_at_target (address : Fin 4851) :
    recordedKinetic (targetLeft address.val) (targetRight address.val) =
      (((targetAORow address.val)[5]! : ℤ) : ℚ) / 10^12 := by
  rcases all_target_rows_certified address with ⟨_,_,_,_,ordered,indexed,_,_⟩
  have idx : kineticPairIndex (targetLeft address.val) (targetRight address.val) =
      address.val := indexed
  unfold recordedKinetic
  rw [if_pos ordered, idx]

/-- The chunked term agrees with the row certificate's recorded cell. -/
private theorem recordedTermFin_eq (a : Fin 4851) :
    recordedTermFin a = sourceCoefficientAt a *
      recordedKinetic (targetLeft a.val) (targetRight a.val) := by
  unfold recordedTermFin
  rw [recorded_kinetic_at_target, mul_div_assoc]

/-- The contracted kinetic matrix differs from the recorded sum by at most
    the certified row error times the total density weight. -/
theorem kinetic_contract_within_recorded :
    |∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j -
      (recordedKineticSum : ℝ)| ≤ (kineticRowWeight : ℝ) / 10^12 := by
  rw [kinetic_pair_expansion, kinetic_target_row_sum]
  have castSum : (recordedKineticSum : ℝ) =
      ∑ a : Fin 4851, (sourceCoefficientAt a : ℝ) *
        ((recordedKinetic (targetLeft a.val) (targetRight a.val)) : ℝ) := by
    rw [recordedKineticSum_eq, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [recordedTermFin_eq a]
    norm_cast
  rw [castSum, ← Finset.sum_sub_distrib]
  calc |∑ a : Fin 4851,
          ((sourceCoefficientAt a : ℝ) *
              UnifiedOrbitals.kinetic (targetLeft a.val) (targetRight a.val) -
            (sourceCoefficientAt a : ℝ) *
              (recordedKinetic (targetLeft a.val) (targetRight a.val) : ℝ))|
      = |∑ a : Fin 4851, (sourceCoefficientAt a : ℝ) *
          (UnifiedOrbitals.kinetic (targetLeft a.val) (targetRight a.val) -
            (recordedKinetic (targetLeft a.val) (targetRight a.val) : ℝ))| := by
        apply congrArg abs
        apply Finset.sum_congr rfl
        intro a _
        rw [← mul_sub]
    _ ≤ ∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ) *
          (UnifiedOrbitals.kinetic (targetLeft a.val) (targetRight a.val) -
            (recordedKinetic (targetLeft a.val) (targetRight a.val) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)| *
          |UnifiedOrbitals.kinetic (targetLeft a.val) (targetRight a.val) -
            (recordedKinetic (targetLeft a.val) (targetRight a.val) : ℝ)| := by
        apply Finset.sum_congr rfl
        intro a _
        rw [abs_mul]
    _ ≤ ∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)| * ((1/10^12 : ℚ) : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact kinetic_error (targetLeft a.val) (targetRight a.val)
    _ = (∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)|) * ((1/10^12 : ℚ) : ℝ) :=
        (Finset.sum_mul _ _ _).symm
    _ = (kineticRowWeight : ℝ) * ((1/10^12 : ℚ) : ℝ) := by
        congr 1
        unfold kineticRowWeight
        rw [Rat.cast_sum]
        apply Finset.sum_congr rfl
        intro a _
        simp only [weightTermFin, Rat.cast_abs]
    _ = (kineticRowWeight : ℝ) / 10^12 := by ring

/-- The fourteen-zone kinetic sum reproduces the original Reentry target
    ledger's certified kinetic integral within one nanohartree. -/
theorem zone_kinetic_ledger :
    |∑ z : Option (Fin 13), OneBody.zoneKinetic z -
      (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℝ) /
        10^9| ≤ (1/10^9 : ℝ) := by
  rw [OneBody.zone_kinetic_sum, OneBody.total_kinetic_original_ao]
  have rows := kinetic_contract_within_recorded
  have ledger : |(recordedKineticSum : ℝ) -
      (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℝ) /
        10^9| ≤ (4/10^10 : ℝ) := by
    calc |(recordedKineticSum : ℝ) -
            (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℝ) /
              10^9|
        = |((recordedKineticSum -
            (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℚ) /
              10^9 : ℚ) : ℝ)| := by
          congr 1
          norm_cast
      _ ≤ (4/10^10 : ℝ) := by
          rw [← Rat.cast_abs]
          calc ((|recordedKineticSum -
                (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℚ) /
                  10^9| : ℚ) : ℝ)
              ≤ ((4/10^10 : ℚ) : ℝ) := Rat.cast_le.mpr recorded_kinetic_sum_within
            _ = (4/10^10 : ℝ) := by norm_num
  have weight : (kineticRowWeight : ℝ) ≤ 200 := by
    exact_mod_cast kinetic_row_weight_bound
  have triangle :
      |∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j -
          (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℝ) /
            10^9| ≤
        |∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j -
            (recordedKineticSum : ℝ)| +
          |(recordedKineticSum : ℝ) -
            (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℝ) /
              10^9| := by
    have e : ∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j -
          (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℝ) /
            10^9 =
        (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j -
            (recordedKineticSum : ℝ)) +
          ((recordedKineticSum : ℝ) -
            (((Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral : ℤ) : ℝ) /
              10^9) := by ring
    rw [e]
    exact abs_add_le _ _
  refine triangle.trans ?_
  refine (add_le_add rows ledger).trans ?_
  have half : (kineticRowWeight : ℝ) / 10^12 ≤ 200 / 10^12 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^12)]
    calc (kineticRowWeight : ℝ) ≤ 200 := weight
      _ = 200 / 10^12 * 10^12 := by ring
  nlinarith

/-- Countercontrol: shifting the recorded kinetic cell for the diagonal AO
    pair (0,0) by 10⁻⁹ hartree destroys the certified residual enclosure. -/
theorem kinetic_counterfactual_row :
    ¬ RecordedResidual (rowInterval radialMaterial kentry0_0_summands)
      (recordedKinetic (⟨0,by decide⟩ : Basis) (⟨0,by decide⟩ : Basis) + 1/10^9)
      (1/10^12) := by
  unfold RecordedResidual
  decide +kernel

end
end LAlanine40K2025.UnifiedOrbitals.Kinetic
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
