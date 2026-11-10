import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeLieUnit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
open SaturationMonoid.PhysicsCore
open Stage9C.Material.SpinPair
open SourcePropagationNativeActionHessian PreparationVacuumMixedFieldReturn
open scoped Matrix BigOperators

private def rawBlockCoefficient (p : Fin 6) : ℝ :=
  if p.val < 3 then 3*(25*lapse/3)/50 else -5*(25*lapse/3)/36

private def rawLastCoefficient (p : Fin 6) : ℝ :=
  if p.val < 3 then 3*(25*lapse/3)/100 else -5*(25*lapse/3)/72

private def auxiliaryColourTerms (p : Fin 6) : List ((Fin 6 × Fin 12) × (Fin 6 × Fin 12) × ℝ) :=
  let t := fun a b : Fin 12 => ((p,a),(p,b),rawBlockCoefficient p)
  [t 0 0,t 1 1,t 2 2,t 3 3,t 4 4,t 5 5,t 6 6,t 6 7,t 7 7,t 8 8,t 9 9,t 10 10,
    ((p,11),(p,11),rawLastCoefficient p)]

private def embedAuxiliaryTerms (ts : List ((Fin 6 × Fin 12) × (Fin 6 × Fin 12) × ℝ)) :
    List (NativeJetIndex × NativeJetIndex × ℝ) :=
  ts.map fun t => ((none,gaugeAuxiliaryIndex t.1),(none,gaugeAuxiliaryIndex t.2.1),t.2.2)

private theorem auxiliary_index_injective : Function.Injective gaugeAuxiliaryIndex := by
  intro i j h
  have same := congrArg Fin.val h
  dsimp only [gaugeAuxiliaryIndex,gaugeBSlot] at same
  have ia := i.2.isLt
  have ja := j.2.isLt
  apply Prod.ext <;> apply Fin.ext <;> omega

private theorem auxiliary_single (i j : Fin 6 × Fin 12) (z : ℂ) :
    (Matrix.single (gaugeAuxiliaryIndex i) (gaugeAuxiliaryIndex j) z).submatrix
      gaugeAuxiliaryIndex gaugeAuxiliaryIndex=Matrix.single i j z := by
  ext a b
  simp only [Matrix.submatrix_apply,Matrix.single_apply,auxiliary_index_injective.eq_iff]

private theorem embedded_literal_fourier (ts : List ((Fin 6 × Fin 12) × (Fin 6 × Fin 12) × ℝ)) :
    (nativeLiteralFourier (embedAuxiliaryTerms ts) 0).submatrix gaugeAuxiliaryIndex gaugeAuxiliaryIndex=
      (ts.map fun t => Matrix.single t.1 t.2.1 (t.2.2 : ℂ)+Matrix.single t.2.1 t.1 (t.2.2 : ℂ)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change (_+nativeLiteralFourier (embedAuxiliaryTerms ts) 0).submatrix _ _=_+_
    simp only [Matrix.submatrix_add,Pi.add_apply]
    rw [ih]
    congr 1
    simp only [jetSymbol,mul_one,auxiliary_single]

private theorem literal_append (a b : List (NativeJetIndex × NativeJetIndex × ℝ)) :
    nativeLiteralFourier (a++b) 0=nativeLiteralFourier a 0+nativeLiteralFourier b 0 := by
  simp only [nativeLiteralFourier,List.map_append,List.sum_append]

private theorem actual_six_auxiliary_terms : literalGaugeBBTerms=
    embedAuxiliaryTerms (auxiliaryColourTerms 0)++embedAuxiliaryTerms (auxiliaryColourTerms 1)++
      embedAuxiliaryTerms (auxiliaryColourTerms 2)++embedAuxiliaryTerms (auxiliaryColourTerms 3)++
      embedAuxiliaryTerms (auxiliaryColourTerms 4)++embedAuxiliaryTerms (auxiliaryColourTerms 5) := by
  run_tac
    let proof ← Lean.Meta.mkEqRefl (Lean.mkConst ``literalGaugeBBTerms)
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

private def colourBlockMatrix (p : Fin 6) : Matrix (Fin 6 × Fin 12) (Fin 6 × Fin 12) ℂ :=
  ((auxiliaryColourTerms p).map fun t =>
    Matrix.single t.1 t.2.1 (t.2.2 : ℂ)+Matrix.single t.2.1 t.1 (t.2.2 : ℂ)).sum

private theorem actual_six_auxiliary_matrices : originalGaugeAuxiliaryUnit=
    colourBlockMatrix 0+colourBlockMatrix 1+colourBlockMatrix 2+
      colourBlockMatrix 3+colourBlockMatrix 4+colourBlockMatrix 5 := by
  unfold originalGaugeAuxiliaryUnit
  rw [actual_six_auxiliary_terms]
  simp only [literal_append,Matrix.submatrix_add,Pi.add_apply,embedded_literal_fourier,colourBlockMatrix]

private theorem colour_block_read (p a : Fin 6) (i : Fin 12) (v : (Fin 6 × Fin 12) → ℂ) :
    (colourBlockMatrix p*ᵥv) (a,i)=
      if p=a then (rawBlockCoefficient p : ℂ)*auxiliaryLieReader (fun j => v (p,j)) i else 0 := by
  have last : 2*(rawLastCoefficient p : ℂ)=(rawBlockCoefficient p : ℂ) := by
    by_cases electric : p.val < 3 <;>
      simp only [rawLastCoefficient,rawBlockCoefficient,electric,if_true,if_false,
        Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat] <;> ring
  by_cases same : p=a
  · subst a
    fin_cases i <;>
      simp [colourBlockMatrix,auxiliaryColourTerms,Matrix.add_mulVec,Matrix.single_mulVec,
        auxiliaryLieReader]
    all_goals try ring1
    linear_combination (v (p,11))*last
  · simp [colourBlockMatrix,auxiliaryColourTerms,Matrix.add_mulVec,Matrix.single_mulVec,
      Prod.mk.injEq,same,Ne.symm same]

def nativeAuxiliaryWeight (p : Fin 6) : ℂ :=
  if p.val < 3 then (lapse : ℂ)/2 else -(lapse : ℂ)⁻¹/2

private theorem raw_coefficient_weight (p : Fin 6) :
    (rawBlockCoefficient p : ℂ)=nativeAuxiliaryWeight p := by
  have original : (lapse : ℂ)⁻¹=(125/54 : ℂ)*(lapse : ℂ) := by
    simpa only [Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
      using congrArg Complex.ofReal lapseInv_source
  by_cases electric : p.val < 3 <;>
    simp only [rawBlockCoefficient,nativeAuxiliaryWeight,electric,if_true,if_false,
      Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  · ring
  · rw [original];ring

/-- All six original lapse blocks act on the complete 72 auxiliary coordinates. -/
theorem actual_native_auxiliary_reader (p : Fin 4 → ℂ) (v : (Fin 6 × Fin 12) → ℂ) :
    originalGaugeAuxiliaryPencil p*ᵥv=fun i =>
      nativeAuxiliaryWeight i.1*auxiliaryLieReader (fun a => v (i.1,a)) i.2 := by
  rw [actual_native_gauge_auxiliary_unit,actual_six_auxiliary_matrices]
  funext i
  rcases i with ⟨a,i⟩
  simp only [Matrix.add_mulVec,Pi.add_apply,colour_block_read,raw_coefficient_weight]
  fin_cases a <;> simp

end LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
