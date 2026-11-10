import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97JointCone

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97WardRow
open Polynomial CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualSourcePreparedClockReducedPencil
open ActualSourcePreparedEMClockEquation ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedAuxiliaryClockReduction ActualPreparedMatterSupport ActualPreparedMatterClock
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedSchur97RatioTail
open ActualDressedNoetherCoulombUnit ActualSourcePreparedFourClockCarrier
open scoped Matrix BigOperators

attribute [local irreducible] sourceClockReducedPencil sourceEMClockReducedRow sourceEMClockForce
  sourceSchur97Polynomial nativeClockInverseNumerator Matrix.det Matrix.adjugate
  sourceSchur97Force sourceFourClockDenominator sourceMatterClockPencil

private theorem inactive_force (i : NativeInactive) : sourceEMClockForce i.val = 0 := by
  unfold sourceEMClockForce
  rw [actual_em_force_inactive_zero i.val i.property,map_zero,map_zero]

private theorem matter_em_row (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) :
    ∑ i : Fin 289, sourceEMClockForce i*sourceMatterClockPencil event n i j =
      X^2*sourceEMClockReducedRow event n j := by
  calc
    _ = ∑ i : Fin 289, sourceEMClockForce i*sourceClockReducedPencil event n i j := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val
      · have zero : sourceEMClockForce i = 0 := by
          unfold sourceEMClockForce
          rw [actual_em_force_inactive_zero i outside,map_zero,map_zero]
        rw [zero,zero_mul,zero_mul]
      · simp only [sourceMatterClockPencil,if_neg outside]
    _ = _ := source_em_clock_reduced_pencil_row event n j


private theorem dot_restrict {M A I : Type*}
    [Fintype M] [Fintype A] [Fintype I]
    (e : M ⊕ A ≃ I) (E v : I → (ℂ[X])[X]) (zero : ∀ i : A,E (e (Sum.inr i)) = 0) :
    dotProduct E v = dotProduct (E ∘ e ∘ Sum.inl) (v ∘ e ∘ Sum.inl) := by
  unfold dotProduct
  rw [←e.sum_comp,Fintype.sum_sum_type]
  have vanished : (∑ i : A,E (e (Sum.inr i))*v (e (Sum.inr i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [zero i,zero_mul]
  change (∑ i : M,E (e (Sum.inl i))*v (e (Sum.inl i))) +
    (∑ i : A,E (e (Sum.inr i))*v (e (Sum.inr i))) = _
  rw [vanished,add_zero]
  rfl

private theorem active_em_column (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) :
    ∑ i : NativeActive,sourceEMClockForce i.val*sourceMatterClockPencil event n i.val j =
      X^2*sourceEMClockReducedRow event n j := by
  have restricted := dot_restrict nativeWholeIndex sourceEMClockForce
    (fun i => sourceMatterClockPencil event n i j) inactive_force
  simpa only [dotProduct,Function.comp_apply,nativeWholeIndex,Equiv.coe_fn_mk,Sum.elim_inl] using
    restricted.symm.trans (matter_em_row event n j)

private theorem columns_to_vector {A I M : Type*} [Fintype A]
    (E : M → (ℂ[X])[X]) (P : Matrix M M ((ℂ[X])[X]))
    (rows : A → M) (columns : I → M) (R : M → (ℂ[X])[X]) (x : (ℂ[X])[X])
    (column : ∀ j, (∑ i : A,E (rows i)*P (rows i) j) = x*R j) :
    (E ∘ rows) ᵥ* P.submatrix rows columns = x • (R ∘ columns) := by
  funext j
  change (∑ i : A,E (rows i)*P (rows i) (columns j)) = x*R (columns j)
  exact column (columns j)

/-- The same original EM row restricts to every source column. Inactive
forcing vanishes, while the complete right columns are retained. -/
theorem source_schur97_active_em_row {I : Type*} (event : DressedEvent)
    (n : PhysicalMomentum) (columns : I → Fin 289) :
    sourceSchur97Force ᵥ* (sourceMatterClockPencil event n).submatrix
      (Subtype.val : NativeActive → Fin 289) columns =
      (X : (ℂ[X])[X])^2 • (sourceEMClockReducedRow event n ∘ columns) := by
  unfold sourceSchur97Force
  exact columns_to_vector sourceEMClockForce (sourceMatterClockPencil event n)
    (Subtype.val : NativeActive → Fin 289) columns (sourceEMClockReducedRow event n)
    (X^2) (active_em_column event n)

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97WardRow
