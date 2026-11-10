import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeTimeFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativePrincipal
open SourcePropagationNativeActionHessian ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open ActualDressedEMClockDispersion
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

private def clockPair (a b : Option (Fin 4)) : Bool := decide (a=some 0 ∧ b=some 0)

private theorem jet_second_coefficient (a b : Option (Fin 4)) (h : ℂ) (k : PhysicalMomentum) :
    (1/2 : ℂ)*(h*jetSymbol a (-physicalFrequencyMomentum 1 k)*jetSymbol b (physicalFrequencyMomentum 1 k)+
      h*jetSymbol a (-physicalFrequencyMomentum (-1) k)*jetSymbol b (physicalFrequencyMomentum (-1) k))-
      h*jetSymbol a (-physicalFrequencyMomentum 0 k)*jetSymbol b (physicalFrequencyMomentum 0 k)=
      if clockPair a b then h else 0 := by
  cases a with
  | none =>
    cases b with
    | none => simp [clockPair,jetSymbol];ring1
    | some mu => fin_cases mu <;> simp [clockPair,jetSymbol,physicalFrequencyMomentum,Fin.cases,Fin.induction,Fin.induction.go] <;> ring1
  | some mu =>
    cases b with
    | none => fin_cases mu <;> simp [clockPair,jetSymbol,physicalFrequencyMomentum,Fin.cases,Fin.induction,Fin.induction.go] <;> ring1
    | some nu =>
      fin_cases mu <;> fin_cases nu <;> simp [clockPair,jetSymbol,physicalFrequencyMomentum,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring1

private def secondTermMatrix (t : NativeJetIndex × NativeJetIndex × ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  if clockPair t.1.1 t.2.1.1 then
    Matrix.single t.1.2 t.2.1.2 (t.2.2 : ℂ)+Matrix.single t.2.1.2 t.1.2 (t.2.2 : ℂ) else 0

private theorem second_single_coefficient (a b : NativeJetIndex) (h : ℂ) (k : PhysicalMomentum) (i j : Fin 289) :
    (1/2 : ℂ)*((Matrix.single a.2 b.2
      (h*jetSymbol a.1 (-physicalFrequencyMomentum 1 k)*jetSymbol b.1 (physicalFrequencyMomentum 1 k))) i j+
      (Matrix.single a.2 b.2
        (h*jetSymbol a.1 (-physicalFrequencyMomentum (-1) k)*jetSymbol b.1 (physicalFrequencyMomentum (-1) k))) i j)-
      (Matrix.single a.2 b.2
        (h*jetSymbol a.1 (-physicalFrequencyMomentum 0 k)*jetSymbol b.1 (physicalFrequencyMomentum 0 k))) i j=
    if clockPair a.1 b.1 then Matrix.single a.2 b.2 h i j else 0 := by
  by_cases cell : a.2=i ∧ b.2=j
  · simp only [Matrix.single_apply,cell]
    exact jet_second_coefficient _ _ _ _
  · simp only [Matrix.single_apply,cell,if_false,add_zero,mul_zero,sub_self,ite_self]

private theorem second_literal_single (t : NativeJetIndex × NativeJetIndex × ℝ) (k : PhysicalMomentum) (i j : Fin 289) :
    (1/2 : ℂ)*(nativeLiteralFourier [t] (physicalFrequencyMomentum 1 k) i j+
      nativeLiteralFourier [t] (physicalFrequencyMomentum (-1) k) i j)-
      nativeLiteralFourier [t] (physicalFrequencyMomentum 0 k) i j=secondTermMatrix t i j := by
  have left := second_single_coefficient t.1 t.2.1 (t.2.2 : ℂ) k i j
  have right := second_single_coefficient t.2.1 t.1 (t.2.2 : ℂ) k i j
  have flip : clockPair t.2.1.1 t.1.1=clockPair t.1.1 t.2.1.1 := by simp only [clockPair,and_comm]
  rw [flip] at right
  simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Matrix.add_apply,Matrix.zero_apply,add_zero,secondTermMatrix,Matrix.ite_apply]
  by_cases pair : clockPair t.1.1 t.2.1.1=true
  · simp only [pair,if_true] at left right ⊢
    linear_combination left+right
  · have zero : clockPair t.1.1 t.2.1.1=false := Bool.eq_false_iff.mpr pair
    simp only [zero,Bool.false_eq_true,if_false] at left right ⊢
    linear_combination left+right

private theorem literal_cons (t : NativeJetIndex × NativeJetIndex × ℝ)
    (ts : List (NativeJetIndex × NativeJetIndex × ℝ)) (p : Fin 4 → ℂ) :
    nativeLiteralFourier (t::ts) p=
      nativeLiteralFourier [t] p+nativeLiteralFourier ts p := by
  simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

private theorem literal_clock_second (ts : List (NativeJetIndex × NativeJetIndex × ℝ))
    (k : PhysicalMomentum) (i j : Fin 289) :
    (1/2 : ℂ)*(nativeLiteralFourier ts (physicalFrequencyMomentum 1 k) i j+
      nativeLiteralFourier ts (physicalFrequencyMomentum (-1) k) i j)-
      nativeLiteralFourier ts (physicalFrequencyMomentum 0 k) i j=
      (ts.map fun t => secondTermMatrix t i j).sum := by
  induction ts with
  | nil => simp [nativeLiteralFourier]
  | cons t ts ih =>
    rw [literal_cons t ts (physicalFrequencyMomentum 1 k),
      literal_cons t ts (physicalFrequencyMomentum (-1) k),literal_cons t ts (physicalFrequencyMomentum 0 k)]
    simp only [Matrix.add_apply,List.map_cons,List.sum_cons]
    linear_combination (second_literal_single t k i j)+ih

private theorem original_gauge_clock_support : nativeCompleteLiteralTerms.all (fun t =>
    !clockPair t.1.1 t.2.1.1 || decide
      ((t.1.2.val<9 ∨ 57 ≤ t.1.2.val) ∧ (t.2.1.2.val<9 ∨ 57 ≤ t.2.1.2.val)))=true := by decide +kernel

/-- The complete original action has no second time derivative incident to any gauge-potential row. -/
theorem actual_native_gauge_clock_second_zero (k : PhysicalMomentum) (mu : Fin 4) (a : Fin 12) (j : Fin 289) :
    nativePhysicalClockSecond k (gaugeSlot mu a) j=0 := by
  have source (w : ℝ) : emOriginalJacobi (physicalFrequencyMomentum w k)=
      nativeLiteralFourier nativeCompleteLiteralTerms (physicalFrequencyMomentum w k) := by
    unfold emOriginalJacobi
    rw [em_hessian_source,nativeHessian_complete_literal,nativeLiteralFourier_sound]
  have rowLow : 9 ≤ (gaugeSlot mu a).val := by dsimp only [gaugeSlot];omega
  have rowHigh : (gaugeSlot mu a).val<57 := by have M:=mu.isLt;have A:=a.isLt;dsimp only [gaugeSlot];omega
  change (1/2 : ℂ)*(emOriginalJacobi (physicalFrequencyMomentum 1 k) (gaugeSlot mu a) j+
    emOriginalJacobi (physicalFrequencyMomentum (-1) k) (gaugeSlot mu a) j)-
      emOriginalJacobi (physicalFrequencyMomentum 0 k) (gaugeSlot mu a) j=0
  rw [source 1,source (-1),source 0,literal_clock_second]
  apply List.sum_eq_zero
  intro z member
  obtain ⟨t,term,same⟩ := List.mem_map.mp member
  subst z
  have support := List.all_eq_true.mp original_gauge_clock_support t term
  by_cases pair : clockPair t.1.1 t.2.1.1=true
  · have outside : (t.1.2.val<9 ∨ 57 ≤ t.1.2.val) ∧ (t.2.1.2.val<9 ∨ 57 ≤ t.2.1.2.val) := by
      simpa only [pair,Bool.not_true,Bool.false_or,decide_eq_true_eq] using support
    have L : t.1.2≠gaugeSlot mu a := by intro h;have e:=congrArg Fin.val h;rcases outside.1 with h|h <;> omega
    have R : t.2.1.2≠gaugeSlot mu a := by intro h;have e:=congrArg Fin.val h;rcases outside.2 with h|h <;> omega
    simp [secondTermMatrix,pair,L,R]
  · have zero : clockPair t.1.1 t.2.1.1=false := Bool.eq_false_iff.mpr pair
    simp only [secondTermMatrix,zero,Bool.false_eq_true,if_false,Matrix.zero_apply]

end LowEnergy.GaussComposite.ActualDressedEMNativePrincipal
