import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedInactiveNativeCertificate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedInactiveNativeWeights

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedInactiveNativeInverse
open PreparationVacuumOriginalGreenFeedback ActualSourcePreparedInactiveNativeData
open ActualSourcePreparedInactiveNativeCertificate ActualSourcePreparedInactiveNativeWeights
open ActualEMAction PreparationVacuumPhysicalCharacteristic CanonicalGradedSpatialSource
open scoped Matrix BigOperators

abbrev NativeInactive := {i : Fin 289 // sourceInactive i}
abbrev NativeActive := {i : Fin 289 // ¬sourceInactive i}

def nativeWholeIndex : NativeActive ⊕ NativeInactive ≃ Fin 289 where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun i := if h : sourceInactive i then Sum.inr ⟨i,h⟩ else Sum.inl ⟨i,h⟩
  left_inv r := by
    cases r with
    | inl r =>
        change (if h : sourceInactive r.val then Sum.inr (⟨r.val,h⟩ : NativeInactive) else Sum.inl (⟨r.val,h⟩ : NativeActive) : NativeActive ⊕ NativeInactive)=Sum.inl r
        rw [dif_neg r.property]
    | inr r =>
        change (if h : sourceInactive r.val then Sum.inr (⟨r.val,h⟩ : NativeInactive) else Sum.inl (⟨r.val,h⟩ : NativeActive) : NativeActive ⊕ NativeInactive)=Sum.inr r
        rw [dif_pos r.property]
  right_inv i := by
    change Sum.elim Subtype.val Subtype.val (if h : sourceInactive i then Sum.inr ⟨i,h⟩ else Sum.inl ⟨i,h⟩)=i
    split_ifs <;> rfl

theorem source_inactive_native_dimensions : Fintype.card NativeInactive=192 ∧ Fintype.card NativeActive=97 := by
  decide +kernel

def nativeInactiveBlock (p : Fin 4 → ℂ) : Matrix NativeInactive NativeInactive ℂ :=
  (emOriginalJacobi p).submatrix Subtype.val Subtype.val

def nativeInactiveNumerator (p : Fin 4 → ℂ) : Matrix NativeInactive NativeInactive ℂ :=
  (sourceMatrix sourceInactiveInverseNumeratorTerms p).submatrix Subtype.val Subtype.val

def nativeInactiveInverse (p : Fin 4 → ℂ) : Matrix NativeInactive NativeInactive ℂ :=
  Matrix.diagonal (fun i : NativeInactive => (nativeInactiveWeight p i.val)⁻¹)*nativeInactiveNumerator p

attribute [local irreducible] emOriginalJacobi sourceMatrix Matrix.mulVec

private theorem static_entry (ts : List SourceTerm) (p : Fin 4 → ℂ) (static : p 0=0)
    (i j : Fin 289) (hi : sourceInactive i) (hj : sourceInactive j) :
    sourceMatrix (ts.filter (fun a => decide (a.powers.temporal=0 ∧ sourceInactive a.row ∧ sourceInactive a.column))) p i j=
      sourceMatrix ts p i j := by
  induction ts with
  | nil => rfl
  | cons a rest ih =>
      by_cases keep : a.powers.temporal=0 ∧ sourceInactive a.row ∧ sourceInactive a.column
      · simp only [List.filter_cons,decide_eq_true keep,if_true,sourceMatrix_cons,Matrix.add_apply,ih]
      · have zero : a.matrix p i j=0 := by
          by_cases row : a.row=i
          · by_cases col : a.column=j
            · have temporal : a.powers.temporal≠0 := by intro h; exact keep ⟨h,row.symm ▸ hi,col.symm ▸ hj⟩
              simp only [SourceTerm.matrix,Powers.value,static,zero_pow temporal,zero_mul,mul_zero]
              simp
            · simp [SourceTerm.matrix,Matrix.single,col]
          · simp [SourceTerm.matrix,Matrix.single,row]
        simp only [List.filter_cons,decide_eq_false keep,Bool.false_eq_true,if_false,sourceMatrix_cons,Matrix.add_apply,ih,zero,zero_add]

private theorem static_block_actual (p : Fin 4 → ℂ) (static : p 0=0) :
    (sourceMatrix sourceStaticInactiveTerms p).submatrix Subtype.val Subtype.val=nativeInactiveBlock p := by
  ext i j
  unfold sourceStaticInactiveTerms nativeInactiveBlock
  rw [Matrix.submatrix_apply,Matrix.submatrix_apply,static_entry _ p static i.val j.val i.property j.property]
  exact congrFun (congrFun (em_jacobi_source p).symm i.val) j.val

private theorem numerator_column_support :
    sourceInactiveInverseNumeratorTerms.filter (fun a => decide (sourceInactive a.column))=
      sourceInactiveInverseNumeratorTerms := by decide +kernel

private theorem column_filter (ts : List SourceTerm) (f : Fin 289 → Bool)
    (p : Fin 4 → ℂ) (i j : Fin 289) :
    sourceMatrix (ts.filter (fun a => f a.column)) p i j=if f j then sourceMatrix ts p i j else 0 := by
  induction ts with
  | nil => simp [sourceMatrix]
  | cons a rest ih =>
      by_cases same : a.column=j
      · by_cases keep : f j=true <;> simp [same,keep,sourceMatrix_cons,ih]
      · have zero : a.matrix p i j=0 := by simp [SourceTerm.matrix,Matrix.single,same]
        cases keep : f a.column <;> simp [keep,sourceMatrix_cons,ih,zero]

private theorem numerator_active_column_zero (p : Fin 4 → ℂ) (i : NativeInactive) (j : NativeActive) :
    sourceMatrix sourceInactiveInverseNumeratorTerms p i.val j.val=0 := by
  have filtered := column_filter sourceInactiveInverseNumeratorTerms
    (fun k => decide (sourceInactive k)) p i.val j.val
  rw [numerator_column_support] at filtered
  simpa only [decide_eq_false j.property,Bool.false_eq_true,if_false] using filtered

private theorem restricted_product {M A I : Type*} [Fintype M] [Fintype A] [Fintype I]
    (e : M ⊕ A ≃ I) (N D : Matrix I I ℂ)
    (zero : ∀i : A,∀j : M,N (e (Sum.inr i)) (e (Sum.inl j))=0) :
    (N*D).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)=
      N.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)*D.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr) := by
  ext i j
  change (∑k,N (e (Sum.inr i)) k*D k (e (Sum.inr j)))=_
  rw [←e.sum_comp,Fintype.sum_sum_type]
  simp only [zero,zero_mul,Finset.sum_const_zero,zero_add]
  rfl

/-- The actual original192 block consumes the cleared source numerator;
its nontrivial row weights are generated from the same source dictionary. -/
theorem source_inactive_native_numerator_product (p : Fin 4 → ℂ) (static : p 0=0) :
    nativeInactiveNumerator p*nativeInactiveBlock p=
      Matrix.diagonal (fun i : NativeInactive => nativeInactiveWeight p i.val) := by
  have full := (source_inactive_native_cleared_products p).1
  have restricted := congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ =>
    A.submatrix (nativeWholeIndex ∘ Sum.inr) (nativeWholeIndex ∘ Sum.inr)) full
  rw [restricted_product nativeWholeIndex _ _ (numerator_active_column_zero p),
    source_inactive_native_weight_matrix] at restricted
  have value : (nativeWholeIndex ∘ Sum.inr : NativeInactive → Fin 289)=Subtype.val := rfl
  rw [value,static_block_actual p static] at restricted
  unfold nativeInactiveNumerator
  have diagonal : (Matrix.diagonal (nativeInactiveWeight p)).submatrix Subtype.val Subtype.val=
      Matrix.diagonal (fun i : NativeInactive => nativeInactiveWeight p i.val) := by
    ext i j
    simp only [Matrix.submatrix_apply,Matrix.diagonal_apply,Subtype.val_inj]
  exact restricted.trans diagonal

private theorem diagonal_inverse {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℂ) (nonzero : ∀i,w i≠0) :
    Matrix.diagonal (fun i => (w i)⁻¹)*Matrix.diagonal w=1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have point : (fun i => (w i)⁻¹*w i)=fun _ => (1:ℂ) := by funext i; exact inv_mul_cancel₀ (nonzero i)
  rw [point,Matrix.diagonal_one]

/-- The source small spatial ball produces the inverse on both sides,
without a full Green regularity or quantum-response witness. -/
theorem source_inactive_native_physical_inverse (eps : ℝ) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2) :
    nativeInactiveInverse (frequencyRay eps 0 n)*nativeInactiveBlock (frequencyRay eps 0 n)=1 ∧
      nativeInactiveBlock (frequencyRay eps 0 n)*nativeInactiveInverse (frequencyRay eps 0 n)=1 := by
  have static : frequencyRay eps 0 n 0=0 := by
    change -Complex.I*((0*eps^2:ℝ):ℂ)=0
    simp
  have nonzero (i : NativeInactive) : nativeInactiveWeight (frequencyRay eps 0 n) i.val≠0 :=
    source_inactive_native_weight_nonzero eps n unit positive small i.val i.property
  have left : nativeInactiveInverse (frequencyRay eps 0 n)*nativeInactiveBlock (frequencyRay eps 0 n)=1 := by
    unfold nativeInactiveInverse
    rw [Matrix.mul_assoc,source_inactive_native_numerator_product _ static]
    exact diagonal_inverse _ nonzero
  exact ⟨left,mul_eq_one_comm.mp left⟩

end LowEnergy.GaussComposite.ActualSourcePreparedInactiveNativeInverse
