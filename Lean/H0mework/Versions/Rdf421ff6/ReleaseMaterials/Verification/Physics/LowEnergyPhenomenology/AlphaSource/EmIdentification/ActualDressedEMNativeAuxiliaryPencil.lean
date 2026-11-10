import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeAuxiliaryUnit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
open SaturationMonoid.PhysicsCore
open SourcePropagationNativeActionHessian ActualEMAction PreparationVacuumMixedFieldReturn
open scoped Matrix BigOperators

def gaugeAuxiliaryIndex (i : Fin 6 × Fin 12) : Fin 289 := gaugeBSlot i.1 i.2

def originalGaugeAuxiliaryPencil (p : Fin 4 → ℂ) : Matrix (Fin 6 × Fin 12) (Fin 6 × Fin 12) ℂ :=
  (emOriginalJacobi p).submatrix gaugeAuxiliaryIndex gaugeAuxiliaryIndex

def originalGaugeAuxiliaryUnit : Matrix (Fin 6 × Fin 12) (Fin 6 × Fin 12) ℂ :=
  (nativeLiteralFourier literalGaugeBBTerms 0).submatrix gaugeAuxiliaryIndex gaugeAuxiliaryIndex

private def auxiliaryPredicate (t : NativeJetIndex × NativeJetIndex × ℝ) : Bool :=
  decide (217≤t.1.2.val ∧ 217≤t.2.1.2.val)

private theorem literal_cons (t : NativeJetIndex × NativeJetIndex × ℝ)
    (terms : List (NativeJetIndex × NativeJetIndex × ℝ)) (p : Fin 4 → ℂ) :
    nativeLiteralFourier (t::terms) p=
      (Matrix.single t.1.2 t.2.1.2 ((t.2.2:ℂ)*jetSymbol t.1.1 (-p)*jetSymbol t.2.1.1 p)+
        Matrix.single t.2.1.2 t.1.2 ((t.2.2:ℂ)*jetSymbol t.2.1.1 (-p)*jetSymbol t.1.1 p))+
      nativeLiteralFourier terms p := rfl

private theorem literal_auxiliary_filter (terms : List (NativeJetIndex × NativeJetIndex × ℝ))
    (p : Fin 4 → ℂ) (i j : Fin 289) (iHigh : 217 ≤ i.val) (jHigh : 217 ≤ j.val) :
    nativeLiteralFourier terms p i j=nativeLiteralFourier (terms.filter auxiliaryPredicate) p i j := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    by_cases keep : auxiliaryPredicate t=true
    · rw [List.filter_cons_of_pos keep,literal_cons,literal_cons,Matrix.add_apply,ih]
      rfl
    · rw [List.filter_cons_of_neg keep,literal_cons,Matrix.add_apply,ih]
      have outside : ¬(217≤t.1.2.val ∧ 217≤t.2.1.2.val) := by
        simpa only [auxiliaryPredicate,decide_eq_true_eq] using keep
      have termZero : (Matrix.single t.1.2 t.2.1.2
          ((t.2.2:ℂ)*jetSymbol t.1.1 (-p)*jetSymbol t.2.1.1 p)+
          Matrix.single t.2.1.2 t.1.2
          ((t.2.2:ℂ)*jetSymbol t.2.1.1 (-p)*jetSymbol t.1.1 p)) i j=0 := by
        rcases not_and_or.mp outside with left | right
        · have leftI : t.1.2≠i := by intro h;have same:=congrArg Fin.val h;omega
          have leftJ : t.1.2≠j := by intro h;have same:=congrArg Fin.val h;omega
          rw [Matrix.add_apply,Matrix.single_apply_of_row_ne leftI,
            Matrix.single_apply_of_col_ne _ _ leftJ,zero_add]
        · have rightI : t.2.1.2≠i := by intro h;have same:=congrArg Fin.val h;omega
          have rightJ : t.2.1.2≠j := by intro h;have same:=congrArg Fin.val h;omega
          rw [Matrix.add_apply,Matrix.single_apply_of_col_ne _ _ rightJ,
            Matrix.single_apply_of_row_ne rightI,zero_add]
      rw [termZero,zero_add]

private theorem algebraic_literal_fourier (terms : List (NativeJetIndex × NativeJetIndex × ℝ))
    (p : Fin 4 → ℂ) (algebraic : terms.all (fun t => decide (t.1.1=none ∧ t.2.1.1=none))=true) :
    nativeLiteralFourier terms p=nativeLiteralFourier terms 0 := by
  unfold nativeLiteralFourier
  congr 1
  apply List.map_congr_left
  intro t member
  have value := List.all_eq_true.mp algebraic t member
  have slots : t.1.1=none ∧ t.2.1.1=none := by simpa only [decide_eq_true_eq] using value
  simp only [slots.1,slots.2,jetSymbol,mul_one]

/-- The original full-action auxiliary block is algebraic at every physical or complex momentum. -/
theorem actual_native_gauge_auxiliary_unit (p : Fin 4 → ℂ) :
    originalGaugeAuxiliaryPencil p=originalGaugeAuxiliaryUnit := by
  unfold originalGaugeAuxiliaryPencil emOriginalJacobi
  rw [em_hessian_source,nativeHessian_complete_literal,nativeLiteralFourier_sound]
  have algebraic : literalGaugeBBTerms.all (fun t => decide (t.1.1=none ∧ t.2.1.1=none))=true := by decide +kernel
  ext i j
  have iHigh : 217 ≤ (gaugeAuxiliaryIndex i).val := by dsimp only [gaugeAuxiliaryIndex,gaugeBSlot];omega
  have jHigh : 217 ≤ (gaugeAuxiliaryIndex j).val := by dsimp only [gaugeAuxiliaryIndex,gaugeBSlot];omega
  have filtered := literal_auxiliary_filter nativeCompleteLiteralTerms p
    (gaugeAuxiliaryIndex i) (gaugeAuxiliaryIndex j) iHigh jHigh
  rw [show nativeCompleteLiteralTerms.filter auxiliaryPredicate=literalGaugeBBTerms from actual_native_auxiliary_terms,
    algebraic_literal_fourier literalGaugeBBTerms p algebraic] at filtered
  exact filtered

end LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
