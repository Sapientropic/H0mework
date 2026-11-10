import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeSchurPhysicalClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativePrincipal
open SourcePropagationNativeActionHessian ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMClockDispersion
open ActualDressedEMNativeSchurClock
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

private def clockAuxiliaryTerm (t : NativeJetIndex × NativeJetIndex × ℝ) : Bool :=
  decide ((t.1.1=some 0 ∧ t.2.1.1=none ∧ 217 ≤ t.2.1.2.val) ∨
    (t.2.1.1=some 0 ∧ t.1.1=none ∧ 217 ≤ t.1.2.val))

private def timeColourTerms (mu : Fin 4) (pair : Fin 6) : List (NativeJetIndex × NativeJetIndex × ℝ) :=
  let t := fun a b : Fin 12 => ((some 0,gaugeSlot mu a),(none,gaugeBSlot pair b),(2 : ℝ))
  let c := fun a b : Fin 12 => ((some 0,gaugeSlot mu a),(none,gaugeBSlot pair b),(1 : ℝ))
  [t 0 0,t 1 1,t 2 2,t 3 3,t 4 4,t 5 5,t 6 6,c 6 7,c 7 6,t 7 7,t 8 8,t 9 9,t 10 10,c 11 11]

private def sourceTimeTerms : List (NativeJetIndex × NativeJetIndex × ℝ) :=
  timeColourTerms 1 3++timeColourTerms 2 4++timeColourTerms 3 5

private theorem actual_clock_auxiliary_terms :
    nativeCompleteLiteralTerms.filter clockAuxiliaryTerm=sourceTimeTerms := by
  run_tac
    let proof ← Lean.Meta.mkEqRefl (Lean.mkConst ``sourceTimeTerms)
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

private theorem excluded_clock_support : nativeCompleteLiteralTerms.all (fun t =>
    clockAuxiliaryTerm t || decide ((t.1.2.val<217 ∧ t.2.1.2.val<217) ∨
      (t.1.1≠some 0 ∧ t.2.1.1≠some 0)))=true := by decide +kernel

private theorem jet_clock_constant (sign : ℂ) (slot : Option (Fin 4)) (omega : ℝ)
    (k : PhysicalMomentum) (notTime : slot≠some 0) :
    jetSymbol slot (fun mu => sign*physicalFrequencyMomentum omega k mu)=
      jetSymbol slot (fun mu => sign*physicalFrequencyMomentum 0 k mu) := by
  cases slot with
  | none => rfl
  | some mu =>
    revert notTime
    refine Fin.cases ?_ (fun _ _ => rfl) mu
    intro impossible
    exact False.elim (impossible rfl)

private theorem literal_cons (t : NativeJetIndex × NativeJetIndex × ℝ)
    (terms : List (NativeJetIndex × NativeJetIndex × ℝ)) (p : Fin 4 → ℂ) :
    nativeLiteralFourier (t::terms) p=
      (Matrix.single t.1.2 t.2.1.2 ((t.2.2 : ℂ)*jetSymbol t.1.1 (-p)*jetSymbol t.2.1.1 p)+
        Matrix.single t.2.1.2 t.1.2 ((t.2.2 : ℂ)*jetSymbol t.2.1.1 (-p)*jetSymbol t.1.1 p))+
      nativeLiteralFourier terms p := rfl

private theorem excluded_term_constant (t : NativeJetIndex × NativeJetIndex × ℝ)
    (omega : ℝ) (k : PhysicalMomentum) (i j : Fin 289) (high : 217 ≤ i.val ∨ 217 ≤ j.val)
    (support : (t.1.2.val<217 ∧ t.2.1.2.val<217) ∨ (t.1.1≠some 0 ∧ t.2.1.1≠some 0)) :
    (nativeLiteralFourier [t] (physicalFrequencyMomentum omega k)) i j=
      (nativeLiteralFourier [t] (physicalFrequencyMomentum 0 k)) i j := by
  rcases support with outside | noTime
  · rcases high with row | col
    · have L : t.1.2≠i := by intro h;have e:=congrArg Fin.val h;omega
      have R : t.2.1.2≠i := by intro h;have e:=congrArg Fin.val h;omega
      simp [nativeLiteralFourier,L,R]
    · have L : t.1.2≠j := by intro h;have e:=congrArg Fin.val h;omega
      have R : t.2.1.2≠j := by intro h;have e:=congrArg Fin.val h;omega
      simp [nativeLiteralFourier,L,R]
  · have positive (slot : Option (Fin 4)) (h : slot≠some 0) :
        jetSymbol slot (physicalFrequencyMomentum omega k)=jetSymbol slot (physicalFrequencyMomentum 0 k) := by
      simpa only [one_mul] using jet_clock_constant 1 slot omega k h
    have negative (slot : Option (Fin 4)) (h : slot≠some 0) :
        jetSymbol slot (-physicalFrequencyMomentum omega k)=jetSymbol slot (-physicalFrequencyMomentum 0 k) := by
      have neg (w : ℝ) : (fun mu => -physicalFrequencyMomentum w k mu)=-physicalFrequencyMomentum w k := rfl
      simpa only [neg_one_mul,neg] using jet_clock_constant (-1) slot omega k h
    simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      positive t.1.1 noTime.1,positive t.2.1.1 noTime.2,
      negative t.1.1 noTime.1,negative t.2.1.1 noTime.2]

private theorem clock_auxiliary_filter (terms : List (NativeJetIndex × NativeJetIndex × ℝ))
    (support : terms.all (fun t => clockAuxiliaryTerm t || decide
      ((t.1.2.val<217 ∧ t.2.1.2.val<217) ∨ (t.1.1≠some 0 ∧ t.2.1.1≠some 0)))=true)
    (k : PhysicalMomentum) (i j : Fin 289) (high : 217 ≤ i.val ∨ 217 ≤ j.val) :
    nativeLiteralFourier terms (physicalFrequencyMomentum 1 k) i j-
      nativeLiteralFourier terms (physicalFrequencyMomentum 0 k) i j=
    nativeLiteralFourier (terms.filter clockAuxiliaryTerm) (physicalFrequencyMomentum 1 k) i j-
      nativeLiteralFourier (terms.filter clockAuxiliaryTerm) (physicalFrequencyMomentum 0 k) i j := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    simp only [List.all_cons,Bool.and_eq_true] at support
    have tail := ih support.2
    by_cases keep : clockAuxiliaryTerm t=true
    · rw [List.filter_cons_of_pos keep,literal_cons,literal_cons,literal_cons,literal_cons]
      simp only [Matrix.add_apply]
      linear_combination tail
    · rw [List.filter_cons_of_neg keep,literal_cons,literal_cons]
      simp only [Matrix.add_apply]
      have noClock : (t.1.2.val<217 ∧ t.2.1.2.val<217) ∨ (t.1.1≠some 0 ∧ t.2.1.1≠some 0) := by
        simpa only [keep,Bool.false_or,decide_eq_true_eq] using support.1
      have equal := excluded_term_constant t 1 k i j high noClock
      simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Matrix.add_apply,Matrix.zero_apply,add_zero] at equal
      linear_combination tail+equal

/-- The original time flux comes from the complete native action before any electromagnetic read. -/
theorem actual_native_clock_auxiliary_flux (k : PhysicalMomentum) (i j : Fin 289)
    (high : 217 ≤ i.val ∨ 217 ≤ j.val) :
    emOriginalJacobi (physicalFrequencyMomentum 1 k) i j-emOriginalJacobi (physicalFrequencyMomentum 0 k) i j=
      nativeLiteralFourier sourceTimeTerms (physicalFrequencyMomentum 1 k) i j-
        nativeLiteralFourier sourceTimeTerms (physicalFrequencyMomentum 0 k) i j := by
  have source (w : ℝ) : emOriginalJacobi (physicalFrequencyMomentum w k)=
      nativeLiteralFourier nativeCompleteLiteralTerms (physicalFrequencyMomentum w k) := by
    unfold emOriginalJacobi
    rw [em_hessian_source,nativeHessian_complete_literal,nativeLiteralFourier_sound]
  rw [source 1,source 0,← actual_clock_auxiliary_terms]
  exact clock_auxiliary_filter _ excluded_clock_support k i j high

def gaugeRestIndex (mu : Fin 4) (a : Fin 12) : Fin 217 :=
  ⟨9+12*mu.val+a.val,by have M:=mu.isLt;have A:=a.isLt;omega⟩

private theorem gauge_rest_embed (mu : Fin 4) (a : Fin 12) :
    nativeRestIndex (gaugeRestIndex mu a)=gaugeSlot mu a := by apply Fin.ext;rfl

private theorem auxiliary_index_injective : Function.Injective gaugeAuxiliaryIndex := by
  intro i j h
  have same := congrArg Fin.val h
  dsimp only [gaugeAuxiliaryIndex,gaugeBSlot] at same
  have ia := i.2.isLt
  have ja := j.2.isLt
  apply Prod.ext <;> apply Fin.ext <;> omega

private theorem rest_index_injective : Function.Injective nativeRestIndex := by
  intro i j h
  have same := congrArg (fun x : Fin 289 => x.val) h
  exact Fin.ext same

private theorem auxiliary_gauge_single (i : Fin 6 × Fin 12) (mu : Fin 4) (a : Fin 12) (z : ℂ) :
    (Matrix.single (gaugeAuxiliaryIndex i) (gaugeSlot mu a) z).submatrix gaugeAuxiliaryIndex nativeRestIndex=
      Matrix.single i (gaugeRestIndex mu a) z := by
  ext b r
  rw [← gauge_rest_embed]
  simp only [Matrix.submatrix_apply,Matrix.single_apply,auxiliary_index_injective.eq_iff,rest_index_injective.eq_iff]

private theorem gauge_auxiliary_single_zero (mu : Fin 4) (a : Fin 12) (i : Fin 6 × Fin 12) (z : ℂ) :
    (Matrix.single (gaugeSlot mu a) (gaugeAuxiliaryIndex i) z).submatrix gaugeAuxiliaryIndex nativeRestIndex=0 := by
  ext b r
  have outside : gaugeSlot mu a≠gaugeAuxiliaryIndex b := by
    intro h
    have same:=congrArg Fin.val h
    have M:=mu.isLt
    have A:=a.isLt
    dsimp only [gaugeSlot,gaugeAuxiliaryIndex,gaugeBSlot] at same
    omega
  exact Matrix.single_apply_of_row_ne outside _ _ _

private theorem time_term_auxiliary_matrix (mu : Fin 4) (pair : Fin 6) (a b : Fin 12) (h : ℝ)
    (k : PhysicalMomentum) :
    (nativeLiteralFourier [((some 0,gaugeSlot mu a),(none,gaugeBSlot pair b),h)] (physicalFrequencyMomentum 1 k)-
      nativeLiteralFourier [((some 0,gaugeSlot mu a),(none,gaugeBSlot pair b),h)] (physicalFrequencyMomentum 0 k)).submatrix
        gaugeAuxiliaryIndex nativeRestIndex=Matrix.single (pair,b) (gaugeRestIndex mu a) (-Complex.I*(h : ℂ)) := by
  have positive : nativeLiteralFourier [((some 0,gaugeSlot mu a),(none,gaugeBSlot pair b),h)]
      (physicalFrequencyMomentum 1 k)=
      Matrix.single (gaugeSlot mu a) (gaugeAuxiliaryIndex (pair,b)) (Complex.I*(h : ℂ))+
        Matrix.single (gaugeAuxiliaryIndex (pair,b)) (gaugeSlot mu a) (-Complex.I*(h : ℂ)) := by
    simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      jetSymbol,physicalFrequencyMomentum,Fin.cases_zero,Pi.neg_apply,Complex.ofReal_one,mul_one,add_zero]
    congr 2 <;> ring1
  have zero : nativeLiteralFourier [((some 0,gaugeSlot mu a),(none,gaugeBSlot pair b),h)]
      (physicalFrequencyMomentum 0 k)=0 := by
    simp [nativeLiteralFourier,jetSymbol,physicalFrequencyMomentum]
  rw [positive,zero,sub_zero,Matrix.submatrix_add]
  simp only [Pi.add_apply,gauge_auxiliary_single_zero,auxiliary_gauge_single,zero_add]

private def temporalColourMatrix (mu : Fin 4) (pair : Fin 6) : Matrix (Fin 6 × Fin 12) (Fin 217) ℂ :=
  let t := fun a b : Fin 12 => Matrix.single (pair,b) (gaugeRestIndex mu a) (-Complex.I*2)
  let c := fun a b : Fin 12 => Matrix.single (pair,b) (gaugeRestIndex mu a) (-Complex.I)
  t 0 0+t 1 1+t 2 2+t 3 3+t 4 4+t 5 5+t 6 6+c 6 7+c 7 6+t 7 7+t 8 8+t 9 9+t 10 10+c 11 11

private theorem literal_clock_diff_cons (t : NativeJetIndex × NativeJetIndex × ℝ)
    (ts : List (NativeJetIndex × NativeJetIndex × ℝ)) (p q : Fin 4 → ℂ) :
    nativeLiteralFourier (t::ts) p-nativeLiteralFourier (t::ts) q=
      (nativeLiteralFourier [t] p-nativeLiteralFourier [t] q)+
        (nativeLiteralFourier ts p-nativeLiteralFourier ts q) := by
  simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  abel

private theorem literal_clock_diff_cons_two (t u : NativeJetIndex × NativeJetIndex × ℝ)
    (ts : List (NativeJetIndex × NativeJetIndex × ℝ)) (p q : Fin 4 → ℂ) :
    nativeLiteralFourier (t::u::ts) p-nativeLiteralFourier (t::u::ts) q=
      (nativeLiteralFourier [t] p-nativeLiteralFourier [t] q)+
        (nativeLiteralFourier (u::ts) p-nativeLiteralFourier (u::ts) q) :=
  literal_clock_diff_cons t (u::ts) p q

private theorem time_colour_auxiliary_matrix (mu : Fin 4) (pair : Fin 6) (k : PhysicalMomentum) :
    (nativeLiteralFourier (timeColourTerms mu pair) (physicalFrequencyMomentum 1 k)-
      nativeLiteralFourier (timeColourTerms mu pair) (physicalFrequencyMomentum 0 k)).submatrix
        gaugeAuxiliaryIndex nativeRestIndex=temporalColourMatrix mu pair := by
  unfold timeColourTerms
  simp only [literal_clock_diff_cons_two,Matrix.submatrix_add,Pi.add_apply,time_term_auxiliary_matrix]
  simp only [Complex.ofReal_ofNat,temporalColourMatrix]
  ext b r
  simp only [Matrix.add_apply,Complex.ofReal_one,mul_one]
  abel

private theorem temporal_colour_read (mu : Fin 4) (pair a : Fin 6) (i : Fin 12) (r : Fin 217 → ℂ) :
    (temporalColourMatrix mu pair*ᵥr) (a,i)=
      if pair=a then -Complex.I*auxiliaryLieReader (fun j => r (gaugeRestIndex mu j)) i else 0 := by
  by_cases same : pair=a
  · subst a
    fin_cases i <;> simp [temporalColourMatrix,Matrix.add_mulVec,Matrix.single_mulVec,auxiliaryLieReader] <;> ring1
  · simp [temporalColourMatrix,Matrix.add_mulVec,Matrix.single_mulVec,same,Ne.symm same]

private theorem literal_clock_diff_append (a b : List (NativeJetIndex × NativeJetIndex × ℝ)) (p q : Fin 4 → ℂ) :
    nativeLiteralFourier (a++b) p-nativeLiteralFourier (a++b) q=
      (nativeLiteralFourier a p-nativeLiteralFourier a q)+
        (nativeLiteralFourier b p-nativeLiteralFourier b q) := by
  simp only [nativeLiteralFourier,List.map_append,List.sum_append]
  abel

private theorem actual_auxiliary_clock_matrix (k : PhysicalMomentum) :
    nativeAuxiliaryRestClockFirst k=temporalColourMatrix 1 3+temporalColourMatrix 2 4+temporalColourMatrix 3 5 := by
  have full : nativeAuxiliaryRestClockFirst k=
      (nativeLiteralFourier sourceTimeTerms (physicalFrequencyMomentum 1 k)-
        nativeLiteralFourier sourceTimeTerms (physicalFrequencyMomentum 0 k)).submatrix gaugeAuxiliaryIndex nativeRestIndex := by
    ext i j
    have high : 217 ≤ (gaugeAuxiliaryIndex i).val := by dsimp only [gaugeAuxiliaryIndex,gaugeBSlot];omega
    exact actual_native_clock_auxiliary_flux k (gaugeAuxiliaryIndex i) (nativeRestIndex j) (Or.inl high)
  rw [full]
  simp only [sourceTimeTerms,literal_clock_diff_append,Matrix.submatrix_add,Pi.add_apply,time_colour_auxiliary_matrix]

/-- Every original auxiliary time row consumes the full remaining gauge components and the fixed colour metric. -/
theorem actual_native_auxiliary_time_reader (k : PhysicalMomentum) (r : Fin 217 → ℂ) :
    nativeAuxiliaryRestClockFirst k*ᵥr=fun i =>
      if i.1=3 then -Complex.I*auxiliaryLieReader (fun a => r (gaugeRestIndex 1 a)) i.2 else
      if i.1=4 then -Complex.I*auxiliaryLieReader (fun a => r (gaugeRestIndex 2 a)) i.2 else
      if i.1=5 then -Complex.I*auxiliaryLieReader (fun a => r (gaugeRestIndex 3 a)) i.2 else 0 := by
  rw [actual_auxiliary_clock_matrix]
  funext i
  rcases i with ⟨a,i⟩
  simp only [Matrix.add_mulVec,Pi.add_apply,temporal_colour_read]
  fin_cases a <;> simp

private theorem single_time_skew (t : NativeJetIndex × NativeJetIndex × ℝ) (k : PhysicalMomentum)
    (slots : t.1.1=some 0 ∧ t.2.1.1=none) (i j : Fin 289) :
    nativeLiteralFourier [t] (physicalFrequencyMomentum 1 k) i j-
      nativeLiteralFourier [t] (physicalFrequencyMomentum 0 k) i j=
    -(nativeLiteralFourier [t] (physicalFrequencyMomentum 1 k) j i-
      nativeLiteralFourier [t] (physicalFrequencyMomentum 0 k) j i) := by
  simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    slots.1,slots.2,jetSymbol,physicalFrequencyMomentum,Fin.cases_zero,Pi.neg_apply,
    Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,Matrix.single_zero,add_zero,
    Matrix.add_apply,Matrix.zero_apply]
  simp only [Matrix.single_apply,and_comm]
  split_ifs <;> ring1

private theorem list_time_skew (ts : List (NativeJetIndex × NativeJetIndex × ℝ)) (k : PhysicalMomentum)
    (slots : ts.all (fun t => decide (t.1.1=some 0 ∧ t.2.1.1=none))=true) (i j : Fin 289) :
    nativeLiteralFourier ts (physicalFrequencyMomentum 1 k) i j-
      nativeLiteralFourier ts (physicalFrequencyMomentum 0 k) i j=
    -(nativeLiteralFourier ts (physicalFrequencyMomentum 1 k) j i-
      nativeLiteralFourier ts (physicalFrequencyMomentum 0 k) j i) := by
  induction ts with
  | nil => simp [nativeLiteralFourier]
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true] at slots
    have head : t.1.1=some 0 ∧ t.2.1.1=none := by simpa only [decide_eq_true_eq] using slots.1
    have single := single_time_skew t k head i j
    have tail := ih slots.2
    change (nativeLiteralFourier (t::ts) (physicalFrequencyMomentum 1 k)-
      nativeLiteralFourier (t::ts) (physicalFrequencyMomentum 0 k)) i j=
      -((nativeLiteralFourier (t::ts) (physicalFrequencyMomentum 1 k)-
        nativeLiteralFourier (t::ts) (physicalFrequencyMomentum 0 k)) j i)
    rw [literal_clock_diff_cons]
    simp only [Matrix.add_apply,Matrix.sub_apply]
    linear_combination single+tail

/-- The two original time-flux slots are independent transpose-dual action slots, with the physical Fourier sign. -/
theorem actual_native_time_flux_transpose (k : PhysicalMomentum) :
    nativeRestAuxiliaryClockFirst k=-(nativeAuxiliaryRestClockFirst k).transpose := by
  ext i j
  have high : 217 ≤ (gaugeAuxiliaryIndex j).val := by dsimp only [gaugeAuxiliaryIndex,gaugeBSlot];omega
  change emOriginalJacobi (physicalFrequencyMomentum 1 k) (nativeRestIndex i) (gaugeAuxiliaryIndex j)-
    emOriginalJacobi (physicalFrequencyMomentum 0 k) (nativeRestIndex i) (gaugeAuxiliaryIndex j)=
    -(emOriginalJacobi (physicalFrequencyMomentum 1 k) (gaugeAuxiliaryIndex j) (nativeRestIndex i)-
      emOriginalJacobi (physicalFrequencyMomentum 0 k) (gaugeAuxiliaryIndex j) (nativeRestIndex i))
  rw [actual_native_clock_auxiliary_flux k _ _ (Or.inr high),
    actual_native_clock_auxiliary_flux k _ _ (Or.inl high)]
  have slots : sourceTimeTerms.all (fun t => decide (t.1.1=some 0 ∧ t.2.1.1=none))=true := by decide +kernel
  exact list_time_skew _ k slots _ _

private theorem temporal_colour_dual_read (mu nu : Fin 4) (pair : Fin 6) (i : Fin 12)
    (b : (Fin 6 × Fin 12) → ℂ) :
    ((temporalColourMatrix nu pair).transpose*ᵥb) (gaugeRestIndex mu i)=
      if nu=mu then -Complex.I*auxiliaryLieReader (fun j => b (pair,j)) i else 0 := by
  have slots (a c : Fin 12) : gaugeRestIndex nu a=gaugeRestIndex mu c ↔ nu=mu ∧ a=c := by
    constructor
    · intro h
      have e:=congrArg Fin.val h
      dsimp only [gaugeRestIndex] at e
      have A:=a.isLt
      have C:=c.isLt
      constructor <;> apply Fin.ext <;> omega
    · rintro ⟨rfl,rfl⟩;rfl
  by_cases same : nu=mu
  · subst nu
    fin_cases i <;> simp [temporalColourMatrix,Matrix.transpose_add,Matrix.transpose_single,
      Matrix.add_mulVec,Matrix.single_mulVec,slots,auxiliaryLieReader] <;> ring1
  · have outside (j : Fin 12) : gaugeRestIndex mu i≠gaugeRestIndex nu j := by
      intro h
      exact same ((slots j i).mp h.symm).1
    simp [temporalColourMatrix,Matrix.transpose_add,Matrix.transpose_single,
      Matrix.add_mulVec,Matrix.single_mulVec,outside,same]

/-- The original rest time slots read all auxiliary colours, with the independently generated Fourier sign. -/
theorem actual_native_rest_time_reader (k : PhysicalMomentum) (b : (Fin 6 × Fin 12) → ℂ)
    (mu : Fin 4) (i : Fin 12) :
    (nativeRestAuxiliaryClockFirst k*ᵥb) (gaugeRestIndex mu i)=
      if mu=0 then 0 else
      if mu=1 then Complex.I*auxiliaryLieReader (fun j => b (3,j)) i else
      if mu=2 then Complex.I*auxiliaryLieReader (fun j => b (4,j)) i else
        Complex.I*auxiliaryLieReader (fun j => b (5,j)) i := by
  rw [actual_native_time_flux_transpose,actual_auxiliary_clock_matrix]
  simp only [Matrix.neg_mulVec,Matrix.transpose_add,Matrix.add_mulVec,Pi.neg_apply,
    Pi.add_apply,temporal_colour_dual_read]
  fin_cases mu <;> simp

end LowEnergy.GaussComposite.ActualDressedEMNativePrincipal
