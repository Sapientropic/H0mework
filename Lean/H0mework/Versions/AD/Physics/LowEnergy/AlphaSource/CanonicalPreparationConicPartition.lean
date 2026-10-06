import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationConicBell

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumConicComposition
open PreparationVacuumCanonicalMoyal PreparationVacuumCutoffBudget PreparationVacuumConicBudget
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

private theorem finite_order (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (ENat.natCast_lt_top n).le

def coordinateL1 (x : Phase) : ℝ := ∑ s : Slot, |phaseCoordinate s x|

theorem original_basis_expansion (x : Phase) :
    x=∑ s : Slot,phaseCoordinate s x • slotDirection s := by
  classical
  apply Prod.ext
  · change (ContinuousLinearMap.fst ℝ _ _) x=(ContinuousLinearMap.fst ℝ _ _) (∑ s : Slot,phaseCoordinate s x • slotDirection s)
    rw [map_sum]
    ext i
    simp [Slot,phaseCoordinate,slotDirection,qDirection,pDirection,Fintype.sum_prod_type,Pi.single_apply]
  · change (ContinuousLinearMap.snd ℝ _ _) x=(ContinuousLinearMap.snd ℝ _ _) (∑ s : Slot,phaseCoordinate s x • slotDirection s)
    rw [map_sum]
    apply WithLp.ofLp_injective 2
    rw [WithLp.ofLp_sum]
    ext i
    simp [Slot,phaseCoordinate,slotDirection,qDirection,pDirection,Fintype.sum_prod_type]

/-- Coordinate estimates expand against the original basis once, with no dimension factor. -/
theorem original_multilinear_budget (k : ℕ) (L : Phase [×k]→L[ℝ] ℝ)
    (B : ℝ) (axes : ∀ w : Word k,|L (slotDirection ∘ w)|≤B)
    (v : Fin k → Phase) : |L v|≤B*∏ i,coordinateL1 (v i) := by
  classical
  have expansion : L v=∑ w : Word k,(∏ i,phaseCoordinate (w i) (v i))*L (slotDirection ∘ w) := by
    have vectors : v=(fun i => ∑ s : Slot,phaseCoordinate s (v i) • slotDirection s) :=
      funext (fun i => original_basis_expansion (v i))
    calc
      _=L.toMultilinearMap (fun i => ∑ s : Slot,phaseCoordinate s (v i) • slotDirection s) := congrArg L vectors
      _=_ := by
        rw [L.toMultilinearMap.map_sum]
        apply Finset.sum_congr rfl
        intro w _
        exact L.toMultilinearMap.map_smul_univ _ _
  rw [expansion]
  calc
    _≤∑ w : Word k,|(∏ i,phaseCoordinate (w i) (v i))*L (slotDirection ∘ w)| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ w : Word k,B*∏ i,|phaseCoordinate (w i) (v i)| := by
      apply Finset.sum_le_sum
      intro w _
      rw [abs_mul,Finset.abs_prod]
      exact (mul_le_mul_of_nonneg_left (axes w) (Finset.prod_nonneg (fun i _ => abs_nonneg _))).trans_eq (mul_comm _ _)
    _=B*∏ i,coordinateL1 (v i) := by
      rw [←Finset.mul_sum]
      congr 1
      exact (Fintype.prod_sum (fun (i : Fin k) (s : Slot) => |phaseCoordinate s (v i)|)).symm

theorem composeBound_partition (O G : ℕ → ℝ) (m : ℕ) :
    composeBound O G m=∑ c : OrderedFinpartition m,O c.length*∏ i,G (c.partSize i) := by
  classical
  unfold composeBound partialBell
  simp_rw [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp [Finset.mem_range,c.length_le]

theorem partialBell_empty (G : ℕ → ℝ) (m : ℕ) : partialBell G (m+1) 0=0 := by
  classical
  apply Finset.sum_eq_zero
  intro c _
  rw [if_neg (by have h := c.length_pos (Nat.succ_pos m); omega)]

theorem composeBound_positive (O G : ℕ → ℝ) (m : ℕ) :
    composeBound O G (m+1)=∑ k ∈ Finset.range (m+1),O (k+1)*partialBell G (m+1) (k+1) := by
  unfold composeBound
  rw [Finset.sum_range_succ',partialBell_empty]
  simp

/-- Full ordered canonical composition through the same Faà di Bruno occurrence. -/
theorem canonical_composition_budget (g : Symbol) (f : Phase → Phase) (x : Phase)
    (outerSmooth : ContDiffAt ℝ ∞ g (f x)) (innerSmooth : ContDiffAt ℝ ∞ f x)
    (O G : ℕ → ℝ) (outerPositive : ∀ k,0 ≤ O k)
    (m : ℕ) (outerBound : ∀ k, k ≤ m → ∀ w : Word k,|jet k g w (f x)|≤O k)
    (innerBound : ∀ k,0 < k → k ≤ m → ∀ w : Word k,
      ∑ s : Slot,|jet k (phaseCoordinate s ∘ f) w x|≤G k)
    (w : Word m) : |jet m (g ∘ f) w x|≤composeBound O G m := by
  classical
  unfold jet
  rw [iteratedFDeriv_comp outerSmooth innerSmooth (finite_order m)]
  simp only [FormalMultilinearSeries.taylorComp,sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries]
  rw [composeBound_partition]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro c _
  let v : Fin c.length → Phase := fun i => iteratedFDeriv ℝ (c.partSize i) f x ((slotDirection ∘ w) ∘ c.emb i)
  have estimate := original_multilinear_budget c.length (iteratedFDeriv ℝ c.length g (f x))
    (O c.length) (outerBound _ c.length_le) v
  refine estimate.trans (mul_le_mul_of_nonneg_left ?_ (outerPositive _))
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.sum_nonneg (fun s _ => abs_nonneg _)
  · intro i _
    have bound := innerBound (c.partSize i) (c.partSize_pos i) (c.partSize_le i) (w ∘ c.emb i)
    have identity : coordinateL1 (v i)=∑ s : Slot,|jet (c.partSize i) (phaseCoordinate s ∘ f) (w ∘ c.emb i) x| := by
      unfold coordinateL1
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      unfold jet
      rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ innerSmooth (finite_order (c.partSize i))]
      rfl
    rw [identity]
    exact bound

/-- Scalar inner jets retain their exact radial power through every partition. -/
theorem scalar_composition_budget (g : ℝ → ℝ) (f : Phase → ℝ) (x : Phase)
    (outerSmooth : ContDiffAt ℝ ∞ g (f x)) (innerSmooth : ContDiffAt ℝ ∞ f x)
    (O G : ℕ → ℝ) (outerPositive : ∀ k,0 ≤ O k)
    (a : ℝ) (m : ℕ)
    (outerBound : ∀ k,k ≤ m → |iteratedDeriv k g (f x)|≤O k)
    (innerBound : ∀ k,0 < k → k ≤ m → ∀ w : Word k,|jet k f w x|≤G k*a^k)
    (w : Word m) : |jet m (g ∘ f) w x|≤composeBound O G m*a^m := by
  classical
  unfold jet
  rw [iteratedFDeriv_comp outerSmooth innerSmooth (finite_order m)]
  simp only [FormalMultilinearSeries.taylorComp,sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,smul_eq_mul]
  rw [composeBound_partition,Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro c _
  rw [mul_comm,abs_mul,Finset.abs_prod]
  have factors : (∏ i,|iteratedFDeriv ℝ (c.partSize i) f x ((slotDirection ∘ w) ∘ c.emb i)|)≤
      ∏ i,G (c.partSize i)*a^(c.partSize i) := by
    apply Finset.prod_le_prod
    · intro i _; exact abs_nonneg _
    · intro i _; exact innerBound _ (c.partSize_pos i) (c.partSize_le i) (w ∘ c.emb i)
  have power : (∏ i : Fin c.length,a^(c.partSize i))=a^m := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      c.prod_sigma_eq_prod (fun _ => a)
  calc
    _≤O c.length*(∏ i,G (c.partSize i)*a^(c.partSize i)) :=
      mul_le_mul (outerBound _ c.length_le) factors
        (Finset.prod_nonneg (fun i _ => abs_nonneg _)) (outerPositive _)
    _=O c.length*(∏ i,G (c.partSize i))*a^m := by rw [Finset.prod_mul_distrib,power]; ring

end LowEnergy.PreparationVacuumConicComposition
