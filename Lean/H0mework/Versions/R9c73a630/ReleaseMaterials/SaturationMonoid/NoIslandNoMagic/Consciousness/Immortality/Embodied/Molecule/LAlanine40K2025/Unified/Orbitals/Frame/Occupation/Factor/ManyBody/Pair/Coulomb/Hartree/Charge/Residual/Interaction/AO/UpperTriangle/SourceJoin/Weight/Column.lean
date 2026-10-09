import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Energy

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceFiniteData
open scoped BigOperators
noncomputable section

def reportPotentialAt (a : Fin 4851) : ℚ :=
  ((targetAORow a.val)[7]! : ℚ) / 10^12

def reportPotentialResidual : ℝ :=
  (1/2 : ℝ) * 10^9 * ∑ a : Fin 4851, (reportCoefficientAt a : ℝ) *
    (reportWeightedJ (targetLeft a.val) (targetRight a.val) - (reportPotentialAt a : ℝ))

def coulombColumnQuantization : ℚ :=
  (Reentry.Source.stepReadout.nuclear.targetLedger.rowSum .coulomb : ℚ) -
    (1/2) * 10^9 * ∑ a : Fin 4851, reportCoefficientAt a * reportPotentialAt a

private theorem finOfNat4851 (a : Fin 4851) : Fin.ofNat 4851 a.val = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

private theorem finset_range_sum_eq_list {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  show Multiset.sum (Multiset.map f (Finset.range n).val) = _
  rw [Finset.range_val]
  show Multiset.sum ((Multiset.range n).map f) = _
  rw [show Multiset.range n = (List.range n : Multiset ℕ) from rfl]
  rw [Multiset.map_coe, Multiset.sum_coe]

private theorem list_cast_sum (l : List ℚ) :
    ((l.map (Rat.cast : ℚ → ℝ)).sum) = (l.sum : ℝ) := by
  have h := (map_list_sum (Rat.castHom ℝ) l).symm
  simpa only [Rat.coe_castHom] using h

private theorem targetLedger_coulomb_rowSum :
    Reentry.Source.stepReadout.nuclear.targetLedger.rowSum .coulomb =
      409702304473 := by
  decide +kernel

private theorem targetLedger_coulomb_independentIntegral :
    (Reentry.Source.stepReadout.nuclear.targetLedger.integral .coulomb).independentIntegral =
      409702304476 := by
  decide +kernel

private theorem reportProd_range_split (start n m : Nat) :
    ((List.range' start (n + m)).map fun i : ℕ =>
      reportCoefficientAt (Fin.ofNat 4851 i) *
        reportPotentialAt (Fin.ofNat 4851 i)).sum =
      ((List.range' start n).map fun i : ℕ =>
        reportCoefficientAt (Fin.ofNat 4851 i) *
          reportPotentialAt (Fin.ofNat 4851 i)).sum +
        ((List.range' (start + n) m).map fun i : ℕ =>
          reportCoefficientAt (Fin.ofNat 4851 i) *
            reportPotentialAt (Fin.ofNat 4851 i)).sum := by
  rw [← List.range'_append]
  simp only [Nat.one_mul, List.map_append, List.sum_append]

private theorem reportProd_0 : ((List.range' 0 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    137937411002170318818306901 / 10^24 := by decide +kernel
private theorem reportProd_1 : ((List.range' (0+486) 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    2515768752359896663884857 / 125000000000000000000000 := by decide +kernel
private theorem reportProd_2 : ((List.range' (0+486+486) 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    82452226237093796903711173 / 10^24 := by decide +kernel
private theorem reportProd_3 : ((List.range' (0+486+486+486) 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    78708654104456873656899953 / 10^24 := by decide +kernel
private theorem reportProd_4 : ((List.range' (0+486+486+486+486) 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    3026335287885792622634437 / 62500000000000000000000 := by decide +kernel
private theorem reportProd_5 : ((List.range' (0+486+486+486+486+486) 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    93694659994100814879218891 / 10^24 := by decide +kernel
private theorem reportProd_6 : ((List.range' (0+486+486+486+486+486+486) 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    4122026508797949726284729 / 500000000000000000000000 := by decide +kernel
private theorem reportProd_7 : ((List.range' (0+486+486+486+486+486+486+486) 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    90841689874590944511206633 / 10^24 := by decide +kernel
private theorem reportProd_8 : ((List.range' (0+486+486+486+486+486+486+486+486) 486).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    58285858095470242514526067 / 500000000000000000000000 := by decide +kernel
private theorem reportProd_9 : ((List.range' (0+486+486+486+486+486+486+486+486+486) 477).map fun i : ℕ =>
    reportCoefficientAt (Fin.ofNat 4851 i) * reportPotentialAt (Fin.ofNat 4851 i)).sum =
    142406683906240792668497123 / 10^24 := by decide +kernel

private theorem reportCoeffTimesPotential_list_sum :
    ((List.range' 0 4851).map fun i : ℕ =>
      reportCoefficientAt (Fin.ofNat 4851 i) *
        reportPotentialAt (Fin.ofNat 4851 i)).sum =
      819404608952241781192692114 / 10^24 := by
  show ((List.range' 0 (486 + (486 + (486 + (486 + (486 +
        (486 + (486 + (486 + (486 + (477))))))))))).map fun i : ℕ =>
      reportCoefficientAt (Fin.ofNat 4851 i) *
        reportPotentialAt (Fin.ofNat 4851 i)).sum =
      819404608952241781192692114 / 10^24
  rw [reportProd_range_split, reportProd_range_split, reportProd_range_split,
      reportProd_range_split, reportProd_range_split, reportProd_range_split,
      reportProd_range_split, reportProd_range_split, reportProd_range_split]
  rw [reportProd_0, reportProd_1, reportProd_2, reportProd_3, reportProd_4,
    reportProd_5, reportProd_6, reportProd_7, reportProd_8, reportProd_9]
  decide +kernel

private theorem reportCoeffTimesPotential_sum :
    ∑ a : Fin 4851, reportCoefficientAt a * reportPotentialAt a =
      819404608952241781192692114 / 10^24 := by
  have key : (∑ a : Fin 4851, reportCoefficientAt a * reportPotentialAt a) =
      ∑ i ∈ Finset.range 4851, reportCoefficientAt (Fin.ofNat 4851 i) *
        reportPotentialAt (Fin.ofNat 4851 i) := by
    rw [Finset.sum_range (fun i : ℕ => reportCoefficientAt (Fin.ofNat 4851 i) *
      reportPotentialAt (Fin.ofNat 4851 i))]
    apply Finset.sum_congr rfl
    intro a _
    show reportCoefficientAt a * reportPotentialAt a =
      reportCoefficientAt (Fin.ofNat 4851 a.val) *
        reportPotentialAt (Fin.ofNat 4851 a.val)
    rw [finOfNat4851 a]
  rw [key, finset_range_sum_eq_list, List.range_eq_range',
    reportCoeffTimesPotential_list_sum]

theorem coulombColumnQuantization_value :
    coulombColumnQuantization = -6241781192692114 / 2000000000000000 := by
  unfold coulombColumnQuantization
  rw [targetLedger_coulomb_rowSum, reportCoeffTimesPotential_sum]
  decide +kernel

theorem coulomb_column_readout :
    (Reentry.Source.stepReadout.nuclear.targetLedger.rowSum .coulomb : ℝ) =
      (1/2 : ℝ) * 10^9 * ∑ a : Fin 4851,
        (reportCoefficientAt a : ℝ) * (reportPotentialAt a : ℝ) +
          (coulombColumnQuantization : ℝ) := by
  have hrow : (Reentry.Source.stepReadout.nuclear.targetLedger.rowSum .coulomb : ℝ) =
      (409702304473 : ℝ) := by
    rw [targetLedger_coulomb_rowSum]
    norm_num
  have hsum : (∑ a : Fin 4851,
      (reportCoefficientAt a : ℝ) * (reportPotentialAt a : ℝ)) =
      ((819404608952241781192692114 / 10^24 : ℚ) : ℝ) := by
    have key : (∑ a : Fin 4851,
        (reportCoefficientAt a : ℝ) * (reportPotentialAt a : ℝ)) =
        ∑ i ∈ Finset.range 4851, (reportCoefficientAt (Fin.ofNat 4851 i) : ℝ) *
          (reportPotentialAt (Fin.ofNat 4851 i) : ℝ) := by
      rw [Finset.sum_range (fun i : ℕ => (reportCoefficientAt (Fin.ofNat 4851 i) : ℝ) *
        (reportPotentialAt (Fin.ofNat 4851 i) : ℝ))]
      apply Finset.sum_congr rfl
      intro a _
      show (reportCoefficientAt a : ℝ) * (reportPotentialAt a : ℝ) =
        (reportCoefficientAt (Fin.ofNat 4851 a.val) : ℝ) *
          (reportPotentialAt (Fin.ofNat 4851 a.val) : ℝ)
      rw [finOfNat4851 a]
    rw [key, finset_range_sum_eq_list, List.range_eq_range']
    rw [show ((List.range' 0 4851).map fun i =>
          (reportCoefficientAt (Fin.ofNat 4851 i) : ℝ) *
            (reportPotentialAt (Fin.ofNat 4851 i) : ℝ)) =
        (List.map (Rat.cast : ℚ → ℝ))
          ((List.range' 0 4851).map fun i =>
            reportCoefficientAt (Fin.ofNat 4851 i) *
              reportPotentialAt (Fin.ofNat 4851 i)) from by
      rw [List.map_map]
      apply List.map_congr_left
      intro a _
      simp only [Function.comp_apply]
      exact (Rat.cast_mul _ _).symm]
    rw [list_cast_sum, reportCoeffTimesPotential_list_sum]
  rw [hrow, hsum]
  have qv : (coulombColumnQuantization : ℝ) =
      ((-6241781192692114 / 2000000000000000 : ℚ) : ℝ) := by
    rw [coulombColumnQuantization_value]
  rw [qv]
  norm_num

private theorem reportHartreeEnergy_split :
    10^9 * reportHartreeEnergy - reportPotentialResidual =
      (1/2 : ℝ) * 10^9 * ∑ a : Fin 4851,
        (reportCoefficientAt a : ℝ) * (reportPotentialAt a : ℝ) := by
  unfold reportHartreeEnergy reportPotentialResidual
  have expand : (∑ a : Fin 4851, (reportCoefficientAt a : ℝ) *
      (reportWeightedJ (targetLeft a.val) (targetRight a.val) -
        (reportPotentialAt a : ℝ))) =
    ∑ a : Fin 4851, ((reportCoefficientAt a : ℝ) *
        reportWeightedJ (targetLeft a.val) (targetRight a.val) -
      (reportCoefficientAt a : ℝ) * (reportPotentialAt a : ℝ)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_sub]
  rw [expand, Finset.sum_sub_distrib]
  ring

theorem blyp_coulomb_column :
    |10^9 * Interaction.d3HartreeEnergy -
        (Reentry.Source.stepReadout.nuclear.targetLedger.rowSum .coulomb : ℝ) -
        reportPotentialResidual| ≤ 863 := by
  have shape : 10^9 * Interaction.d3HartreeEnergy -
        (Reentry.Source.stepReadout.nuclear.targetLedger.rowSum .coulomb : ℝ) -
        reportPotentialResidual =
      10^9 * (Interaction.d3HartreeEnergy - reportHartreeEnergy) -
        (coulombColumnQuantization : ℝ) := by
    rw [coulomb_column_readout, ← reportHartreeEnergy_split]
    ring
  rw [shape]
  have hQ : |(coulombColumnQuantization : ℝ)| ≤ 4 := by
    rw [coulombColumnQuantization_value]
    have h : |(-6241781192692114 / 2000000000000000 : ℚ)| ≤ (4 : ℚ) := by
      decide +kernel
    rw [← Rat.cast_abs]
    exact_mod_cast h
  calc |10^9 * (Interaction.d3HartreeEnergy - reportHartreeEnergy) -
        (coulombColumnQuantization : ℝ)|
      ≤ |10^9 * (Interaction.d3HartreeEnergy - reportHartreeEnergy)| +
          |(coulombColumnQuantization : ℝ)| := abs_sub _ _
    _ = 10^9 * |Interaction.d3HartreeEnergy - reportHartreeEnergy| +
          |(coulombColumnQuantization : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10^9)]
    _ ≤ (hartreeNanoBound : ℝ) + 4 :=
        add_le_add blyp_coulomb_nanohartree hQ
    _ = 863 := by unfold hartreeNanoBound; norm_num

theorem blyp_coulomb_integral :
    |10^9 * Interaction.d3HartreeEnergy -
        ((Reentry.Source.stepReadout.nuclear.targetLedger.integral .coulomb).independentIntegral : ℝ) -
        reportPotentialResidual| ≤ 860 := by
  have hint : ((Reentry.Source.stepReadout.nuclear.targetLedger.integral .coulomb).independentIntegral : ℝ) =
      (Reentry.Source.stepReadout.nuclear.targetLedger.rowSum .coulomb : ℝ) + 3 := by
    rw [targetLedger_coulomb_independentIntegral, targetLedger_coulomb_rowSum]
    norm_num
  rw [hint]
  have shape : 10^9 * Interaction.d3HartreeEnergy -
        ((Reentry.Source.stepReadout.nuclear.targetLedger.rowSum .coulomb : ℝ) + 3) -
        reportPotentialResidual =
      10^9 * (Interaction.d3HartreeEnergy - reportHartreeEnergy) -
        ((coulombColumnQuantization : ℝ) + 3) := by
    rw [coulomb_column_readout, ← reportHartreeEnergy_split]
    ring
  rw [shape]
  have hQ : |((coulombColumnQuantization : ℝ) + 3)| ≤ 1 := by
    rw [coulombColumnQuantization_value]
    rw [show ((-6241781192692114 / 2000000000000000 : ℚ) : ℝ) + (3 : ℝ) =
        ((-6241781192692114 / 2000000000000000 + (3 : ℚ)) : ℚ) from by
      rw [Rat.cast_add, Rat.cast_ofNat]]
    have h : |(-6241781192692114 / 2000000000000000 + (3 : ℚ))| ≤ (1 : ℚ) := by
      decide +kernel
    rw [← Rat.cast_abs]
    exact_mod_cast h
  calc |10^9 * (Interaction.d3HartreeEnergy - reportHartreeEnergy) -
        ((coulombColumnQuantization : ℝ) + 3)|
      ≤ |10^9 * (Interaction.d3HartreeEnergy - reportHartreeEnergy)| +
          |((coulombColumnQuantization : ℝ) + 3)| := abs_sub _ _
    _ = 10^9 * |Interaction.d3HartreeEnergy - reportHartreeEnergy| +
          |((coulombColumnQuantization : ℝ) + 3)| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10^9)]
    _ ≤ (hartreeNanoBound : ℝ) + 1 :=
        add_le_add blyp_coulomb_nanohartree hQ
    _ = 860 := by unfold hartreeNanoBound; norm_num

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
