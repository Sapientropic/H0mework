import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OneBody.KineticDensity
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OneBody.ZeroFlux
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Integrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory Function
open WholeBandAttractor Metric
open LAlanine40K2025.UnifiedOrbitals
open scoped BigOperators NNReal
noncomputable section

theorem kinetic_density_difference (x : Point) :
    laplacianKinetic x - gradientKinetic x = -(1/4 : ℝ) * laplacian sourceTerms densityMatrix x := by
  simp only [laplacianKinetic,gradientKinetic,laplacian,secondBilinear,
    show (fun _ : Fin 3 => (0 : ℕ)) = zeroJet from rfl]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem gradientKinetic_integrable : Integrable gradientKinetic :=
  (integrable_finsetSum Finset.univ (fun a _ =>
    source_bilinear_integrable (raise zeroJet a) (raise zeroJet a))).const_mul (1/2 : ℝ)

theorem laplacianKinetic_integrable : Integrable laplacianKinetic :=
  (integrable_finsetSum Finset.univ (fun a _ =>
    (source_bilinear_integrable (raise (raise zeroJet a) a) zeroJet).add
      (source_bilinear_integrable zeroJet (raise (raise zeroJet a) a)))).const_mul (-(1/4 : ℝ))

def zoneKinetic (z : Option (Fin 13)) : ℝ := ∫ x in region z, gradientKinetic x

theorem every_zone_kinetic_unique (z : Option (Fin 13)) :
    (∫ x in region z, laplacianKinetic x) = zoneKinetic z := by
  have hzero : (∫ x in region z, laplacianKinetic x - gradientKinetic x) = 0 := by
    simp_rw [kinetic_density_difference]
    rw [integral_const_mul,every_zone_zero_flux z,mul_zero]
  rw [integral_sub laplacianKinetic_integrable.integrableOn gradientKinetic_integrable.integrableOn] at hzero
  unfold zoneKinetic
  linarith

theorem regions_disjoint : Pairwise (Disjoint on region) :=
  pairwise_disjoint_fiber label

theorem regions_cover : (⋃ z : Option (Fin 13), region z) = Set.univ := by
  ext x
  simp only [region,Partition.Finite.region,Set.mem_iUnion,Set.mem_univ,iff_true,
    Set.mem_preimage,Set.mem_singleton_iff]
  exact ⟨label x,rfl⟩

theorem zone_kinetic_sum :
    ∑ z : Option (Fin 13), zoneKinetic z = ∫ x, gradientKinetic x := by
  have h := integral_iUnion_fintype (s := region) all_regions_measurable regions_disjoint
    (fun _ => gradientKinetic_integrable.integrableOn)
  rw [regions_cover] at h
  simpa only [setIntegral_univ,zoneKinetic] using h.symm

theorem total_kinetic_original_ao :
    (∫ x, gradientKinetic x) =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j := by
  have each (a : Fin 3) (i j : Basis) : Integrable (fun x : Point =>
      (densityMatrix i j : ℝ) * orbital (sourceTerms i) (raise zeroJet a) x *
        orbital (sourceTerms j) (raise zeroJet a) x) := by
    have h := (UnifiedOrbitals.source_product_integrable i j (raise zeroJet a)
      (raise zeroJet a)).const_mul (densityMatrix i j : ℝ)
    simpa only [← mul_assoc] using h
  have lhs : (∫ x : Point, gradientKinetic x) = (1/2 : ℝ) * ∑ a : Fin 3,
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        ∫ x : Point, orbital (sourceTerms i) (raise zeroJet a) x *
          orbital (sourceTerms j) (raise zeroJet a) x := by
    simp only [gradientKinetic,bilinear]
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun j _ => each a i j)))]
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => each a i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => each a i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have reorder : (∑ i : Basis, ∑ j : Basis, ∑ a : Fin 3,
      (densityMatrix i j : ℝ) * ∫ x : Point,
        orbital (sourceTerms i) (raise zeroJet a) x * orbital (sourceTerms j) (raise zeroJet a) x) =
      ∑ a : Fin 3, ∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℝ) * ∫ x : Point,
          orbital (sourceTerms i) (raise zeroJet a) x * orbital (sourceTerms j) (raise zeroJet a) x :=
    calc (∑ i : Basis, ∑ j : Basis, ∑ a : Fin 3, _) =
        ∑ i : Basis, ∑ a : Fin 3, ∑ j : Basis, _ :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ a : Fin 3, ∑ i : Basis, ∑ j : Basis, _ := Finset.sum_comm
  have rhs : (∑ i : Basis, ∑ j : Basis,
      (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j) =
      (1/2 : ℝ) * ∑ a : Fin 3, ∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℝ) * ∫ x : Point,
          orbital (sourceTerms i) (raise zeroJet a) x *
            orbital (sourceTerms j) (raise zeroJet a) x := by
    have term (i j : Basis) : (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j =
        (1/2 : ℝ) * ∑ a : Fin 3, (densityMatrix i j : ℝ) *
          ∫ x : Point, orbital (sourceTerms i) (raise zeroJet a) x *
            orbital (sourceTerms j) (raise zeroJet a) x := by
      simp only [UnifiedOrbitals.kinetic,UnifiedOrbitals.derivative,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    calc ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * UnifiedOrbitals.kinetic i j
        = ∑ i : Basis, ∑ j : Basis, (1/2 : ℝ) * ∑ a : Fin 3,
            (densityMatrix i j : ℝ) * ∫ x : Point,
              orbital (sourceTerms i) (raise zeroJet a) x *
                orbital (sourceTerms j) (raise zeroJet a) x :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => term i j))
      _ = ∑ i : Basis, (1/2 : ℝ) * ∑ j : Basis, ∑ a : Fin 3,
            (densityMatrix i j : ℝ) * ∫ x : Point,
              orbital (sourceTerms i) (raise zeroJet a) x *
                orbital (sourceTerms j) (raise zeroJet a) x := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.mul_sum]
      _ = (1/2 : ℝ) * ∑ i : Basis, ∑ j : Basis, ∑ a : Fin 3,
            (densityMatrix i j : ℝ) * ∫ x : Point,
              orbital (sourceTerms i) (raise zeroJet a) x *
                orbital (sourceTerms j) (raise zeroJet a) x := by
          rw [← Finset.mul_sum]
      _ = (1/2 : ℝ) * ∑ a : Fin 3, ∑ i : Basis, ∑ j : Basis,
            (densityMatrix i j : ℝ) * ∫ x : Point,
              orbital (sourceTerms i) (raise zeroJet a) x *
                orbital (sourceTerms j) (raise zeroJet a) x := by
          rw [reorder]
  rw [lhs,rhs]

/-- A contracted shifted Hessian forces every diagonal entry negative: evaluating
    `id + α·H` on the unit basis vector `a` gives `1 + α·H_{aa}` bounded by `k < 1`. -/
theorem sourceHessian_diagonal_negative {α : ℝ} (apos : 0 < α) {k : ℝ≥0} (klt : k < 1)
    (x : Point)
    (bound : ‖ContinuousLinearMap.id ℝ Point + α • sourceHessianLinear x‖ ≤ (k : ℝ))
    (a : Fin 3) : sourceHessian x a a < 0 := by
  have eval : ((ContinuousLinearMap.id ℝ Point + α • sourceHessianLinear x)
        (Pi.single a (1 : ℝ) : Point)) a =
      1 + α * sourceHessian x a a := by
    simp only [add_apply,ContinuousLinearMap.id_apply,Pi.add_apply,
      smul_apply,Pi.smul_apply,smul_eq_mul,sourceHessianLinear_apply]
    rw [Pi.single_eq_same,Finset.sum_eq_single a]
    · rw [Pi.single_eq_same]
      ring
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      ring
    · intro h
      exact absurd (Finset.mem_univ a) h
  have vnorm : ‖(Pi.single a (1 : ℝ) : Point)‖ = 1 := by
    rw [Pi.norm_single,norm_one]
  have boundv : ‖(ContinuousLinearMap.id ℝ Point + α • sourceHessianLinear x)
        (Pi.single a (1 : ℝ) : Point)‖ ≤ (k : ℝ) := by
    calc ‖(ContinuousLinearMap.id ℝ Point + α • sourceHessianLinear x)
          (Pi.single a (1 : ℝ) : Point)‖
        ≤ ‖ContinuousLinearMap.id ℝ Point + α • sourceHessianLinear x‖ *
            ‖(Pi.single a (1 : ℝ) : Point)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (k : ℝ) * ‖(Pi.single a (1 : ℝ) : Point)‖ :=
          mul_le_mul_of_nonneg_right bound (norm_nonneg _)
      _ = (k : ℝ) := by rw [vnorm,mul_one]
  have component : ‖((ContinuousLinearMap.id ℝ Point + α • sourceHessianLinear x)
        (Pi.single a (1 : ℝ) : Point)) a‖ ≤ (k : ℝ) :=
    (norm_le_pi_norm _ a).trans boundv
  rw [eval,Real.norm_eq_abs] at component
  have upper : 1 + α * sourceHessian x a a ≤ (k : ℝ) := (abs_le.mp component).2
  have klt1 : (k : ℝ) < 1 := by exact_mod_cast klt
  have hmul : α * sourceHessian x a a < 0 := by nlinarith
  rcases mul_neg_iff.mp hmul with ⟨_,h⟩ | ⟨h,_⟩
  · exact h
  · linarith

theorem laplacian_eq_hessian_trace (x : Point) :
    laplacian sourceTerms densityMatrix x = ∑ a : Fin 3, sourceHessian x a a := by
  simp only [laplacian,secondBilinear,sourceHessian,firstBilinear,
    show (fun _ : Fin 3 => (0 : ℕ)) = zeroJet from rfl]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem laplacian_negative_of_contracted {α : ℝ} (apos : 0 < α) {k : ℝ≥0} (klt : k < 1)
    (x : Point)
    (bound : ‖ContinuousLinearMap.id ℝ Point + α • sourceHessianLinear x‖ ≤ (k : ℝ)) :
    laplacian sourceTerms densityMatrix x < 0 := by
  rw [laplacian_eq_hessian_trace]
  have diag : ∀ a : Fin 3, sourceHessian x a a < 0 :=
    fun a => sourceHessian_diagonal_negative apos klt x bound a
  have positive : 0 < ∑ a : Fin 3, -sourceHessian x a a :=
    Finset.sum_pos (fun a _ => neg_pos.mpr (diag a)) Finset.univ_nonempty
  rwa [Finset.sum_neg_distrib,neg_pos] at positive

theorem attractor_laplacian_negative (i : Fin 13) :
    laplacian sourceTerms densityMatrix (sourceSeed i).criticalPoint < 0 := by
  fin_cases i
  · exact laplacian_negative_of_contracted Atom000.alpha_positive Atom000.contraction_lt_one _
      (Atom000.actual_shifted_hessian _ Atom000.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom001.alpha_positive Atom001.contraction_lt_one _
      (Atom001.actual_shifted_hessian _ Atom001.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom002.alpha_positive Atom002.contraction_lt_one _
      (Atom002.actual_shifted_hessian _ Atom002.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom003.alpha_positive Atom003.contraction_lt_one _
      (Atom003.actual_shifted_hessian _ Atom003.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom004.alpha_positive Atom004.contraction_lt_one _
      (Atom004.actual_shifted_hessian _ Atom004.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom005.alpha_positive Atom005.contraction_lt_one _
      (Atom005.actual_shifted_hessian _ Atom005.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom006.alpha_positive Atom006.contraction_lt_one _
      (Atom006.actual_shifted_hessian _ Atom006.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom007.alpha_positive Atom007.contraction_lt_one _
      (Atom007.actual_shifted_hessian _ Atom007.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom008.alpha_positive Atom008.contraction_lt_one _
      (Atom008.actual_shifted_hessian _ Atom008.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom009.alpha_positive Atom009.contraction_lt_one _
      (Atom009.actual_shifted_hessian _ Atom009.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom010.alpha_positive Atom010.contraction_lt_one _
      (Atom010.actual_shifted_hessian _ Atom010.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom011.alpha_positive Atom011.contraction_lt_one _
      (Atom011.actual_shifted_hessian _ Atom011.actualZero.inside)
  · exact laplacian_negative_of_contracted Atom012.alpha_positive Atom012.contraction_lt_one _
      (Atom012.actual_shifted_hessian _ Atom012.actualZero.inside)

theorem attractor_kinetic_densities_differ (i : Fin 13) :
    gradientKinetic (sourceSeed i).criticalPoint < laplacianKinetic (sourceSeed i).criticalPoint := by
  have diff := kinetic_density_difference (sourceSeed i).criticalPoint
  have neg := attractor_laplacian_negative i
  have positive : (0 : ℝ) < -(1/4 : ℝ) * laplacian sourceTerms densityMatrix (sourceSeed i).criticalPoint := by
    nlinarith
  linarith

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
