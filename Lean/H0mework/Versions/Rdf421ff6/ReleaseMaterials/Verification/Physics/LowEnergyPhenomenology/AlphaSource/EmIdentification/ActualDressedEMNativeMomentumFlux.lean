import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativePrincipal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeMomentum
open SourcePropagationNativeActionHessian ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMClockDispersion
open ActualDressedEMNativeSchurClock ActualDressedEMNativePrincipal
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

private def derivativeAuxiliaryTerm (t : NativeJetIndex × NativeJetIndex × ℝ) : Bool :=
  decide ((t.1.1≠none ∧ t.2.1.1=none ∧ 217 ≤ t.2.1.2.val) ∨
    (t.2.1.1≠none ∧ t.1.1=none ∧ 217 ≤ t.1.2.val))

private def pairDerivativeTerms (d e mu nu : Fin 4) (pair : Fin 6) : List (NativeJetIndex × NativeJetIndex × ℝ) :=
  let t := fun a b : Fin 12 => ((some d,gaugeSlot mu a),(none,gaugeBSlot pair b),(2 : ℝ))
  let c := fun a b : Fin 12 => ((some d,gaugeSlot mu a),(none,gaugeBSlot pair b),(1 : ℝ))
  let u := fun a b : Fin 12 => ((some e,gaugeSlot nu a),(none,gaugeBSlot pair b),(-2 : ℝ))
  let v := fun a b : Fin 12 => ((some e,gaugeSlot nu a),(none,gaugeBSlot pair b),(-1 : ℝ))
  [t 0 0,u 0 0,t 1 1,u 1 1,t 2 2,u 2 2,t 3 3,u 3 3,t 4 4,u 4 4,t 5 5,u 5 5,
    t 6 6,c 6 7,u 6 6,v 6 7,c 7 6,t 7 7,v 7 6,u 7 7,
    t 8 8,u 8 8,t 9 9,u 9 9,t 10 10,u 10 10,c 11 11,v 11 11]

private def sourceDerivativeTerms : List (NativeJetIndex × NativeJetIndex × ℝ) :=
  pairDerivativeTerms 0 1 1 0 3++pairDerivativeTerms 0 2 2 0 4++pairDerivativeTerms 0 3 3 0 5++
    pairDerivativeTerms 2 3 3 2 0++pairDerivativeTerms 3 1 1 3 1++pairDerivativeTerms 1 2 2 1 2

private theorem actual_derivative_auxiliary_terms :
    nativeCompleteLiteralTerms.filter derivativeAuxiliaryTerm=sourceDerivativeTerms := by
  run_tac
    let proof ← Lean.Meta.mkEqRefl (Lean.mkConst ``sourceDerivativeTerms)
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

private theorem excluded_derivative_support : nativeCompleteLiteralTerms.all (fun t =>
    derivativeAuxiliaryTerm t || decide ((t.1.2.val<217 ∧ t.2.1.2.val<217) ∨
      (t.1.1=none ∧ t.2.1.1=none)))=true := by decide +kernel

private theorem literal_cons (t : NativeJetIndex × NativeJetIndex × ℝ)
    (ts : List (NativeJetIndex × NativeJetIndex × ℝ)) (p : Fin 4 → ℂ) :
    nativeLiteralFourier (t::ts) p=
      (Matrix.single t.1.2 t.2.1.2 ((t.2.2 : ℂ)*jetSymbol t.1.1 (-p)*jetSymbol t.2.1.1 p)+
        Matrix.single t.2.1.2 t.1.2 ((t.2.2 : ℂ)*jetSymbol t.2.1.1 (-p)*jetSymbol t.1.1 p))+
      nativeLiteralFourier ts p := rfl

private theorem excluded_term_constant (t : NativeJetIndex × NativeJetIndex × ℝ)
    (p : Fin 4 → ℂ) (i j : Fin 289) (high : 217 ≤ i.val ∨ 217 ≤ j.val)
    (support : (t.1.2.val<217 ∧ t.2.1.2.val<217) ∨ (t.1.1=none ∧ t.2.1.1=none)) :
    nativeLiteralFourier [t] p i j=nativeLiteralFourier [t] 0 i j := by
  rcases support with outside | algebraic
  · rcases high with row | col
    · have L : t.1.2≠i := by intro h;have e:=congrArg Fin.val h;omega
      have R : t.2.1.2≠i := by intro h;have e:=congrArg Fin.val h;omega
      simp [nativeLiteralFourier,L,R]
    · have L : t.1.2≠j := by intro h;have e:=congrArg Fin.val h;omega
      have R : t.2.1.2≠j := by intro h;have e:=congrArg Fin.val h;omega
      simp [nativeLiteralFourier,L,R]
  · simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      algebraic.1,algebraic.2,jetSymbol]

private theorem derivative_auxiliary_filter (ts : List (NativeJetIndex × NativeJetIndex × ℝ))
    (support : ts.all (fun t => derivativeAuxiliaryTerm t || decide
      ((t.1.2.val<217 ∧ t.2.1.2.val<217) ∨ (t.1.1=none ∧ t.2.1.1=none)))=true)
    (p : Fin 4 → ℂ) (i j : Fin 289) (high : 217 ≤ i.val ∨ 217 ≤ j.val) :
    nativeLiteralFourier ts p i j-nativeLiteralFourier ts 0 i j=
      nativeLiteralFourier (ts.filter derivativeAuxiliaryTerm) p i j-
        nativeLiteralFourier (ts.filter derivativeAuxiliaryTerm) 0 i j := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true] at support
    have tail := ih support.2
    by_cases keep : derivativeAuxiliaryTerm t=true
    · rw [List.filter_cons_of_pos keep,literal_cons,literal_cons,literal_cons,literal_cons]
      simp only [Matrix.add_apply]
      linear_combination tail
    · rw [List.filter_cons_of_neg keep,literal_cons,literal_cons]
      simp only [Matrix.add_apply]
      have outside : (t.1.2.val<217 ∧ t.2.1.2.val<217) ∨ (t.1.1=none ∧ t.2.1.1=none) := by
        simpa only [keep,Bool.false_or,decide_eq_true_eq] using support.1
      have equal := excluded_term_constant t p i j high outside
      simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Matrix.add_apply,Matrix.zero_apply,add_zero] at equal
      linear_combination tail+equal

/-- The complete original action generates every B-incident momentum difference, including all space/time fluxes. -/
theorem actual_native_momentum_auxiliary_flux (p : Fin 4 → ℂ) (i j : Fin 289)
    (high : 217 ≤ i.val ∨ 217 ≤ j.val) :
    emOriginalJacobi p i j-emOriginalJacobi 0 i j=
      nativeLiteralFourier sourceDerivativeTerms p i j-nativeLiteralFourier sourceDerivativeTerms 0 i j := by
  have source (q : Fin 4 → ℂ) : emOriginalJacobi q=nativeLiteralFourier nativeCompleteLiteralTerms q := by
    unfold emOriginalJacobi
    rw [em_hessian_source,nativeHessian_complete_literal,nativeLiteralFourier_sound]
  rw [source p,source 0,← actual_derivative_auxiliary_terms]
  exact derivative_auxiliary_filter _ excluded_derivative_support p i j high

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
  exact Fin.ext (congrArg (fun x : Fin 289 => x.val) h)

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

private theorem derivative_term_auxiliary_matrix (d mu : Fin 4) (pair : Fin 6) (a b : Fin 12)
    (h : ℝ) (p : Fin 4 → ℂ) :
    (nativeLiteralFourier [((some d,gaugeSlot mu a),(none,gaugeBSlot pair b),h)] p-
      nativeLiteralFourier [((some d,gaugeSlot mu a),(none,gaugeBSlot pair b),h)] 0).submatrix
        gaugeAuxiliaryIndex nativeRestIndex=Matrix.single (pair,b) (gaugeRestIndex mu a) ((h : ℂ)*p d) := by
  have positive : nativeLiteralFourier [((some d,gaugeSlot mu a),(none,gaugeBSlot pair b),h)] p=
      Matrix.single (gaugeSlot mu a) (gaugeAuxiliaryIndex (pair,b)) (-(h : ℂ)*p d)+
        Matrix.single (gaugeAuxiliaryIndex (pair,b)) (gaugeSlot mu a) ((h : ℂ)*p d) := by
    simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      jetSymbol,Pi.neg_apply,mul_one,add_zero]
    congr 2
    all_goals ring1
  have zero : nativeLiteralFourier [((some d,gaugeSlot mu a),(none,gaugeBSlot pair b),h)] 0=0 := by
    simp [nativeLiteralFourier,jetSymbol]
  rw [positive,zero,sub_zero,Matrix.submatrix_add]
  simp only [Pi.add_apply,gauge_auxiliary_single_zero,auxiliary_gauge_single,zero_add]

private def derivativeColourMatrix (d mu : Fin 4) (pair : Fin 6) (p : Fin 4 → ℂ) : Matrix (Fin 6 × Fin 12) (Fin 217) ℂ :=
  let t := fun a b : Fin 12 => Matrix.single (pair,b) (gaugeRestIndex mu a) (2*p d)
  let c := fun a b : Fin 12 => Matrix.single (pair,b) (gaugeRestIndex mu a) (p d)
  t 0 0+t 1 1+t 2 2+t 3 3+t 4 4+t 5 5+t 6 6+c 6 7+c 7 6+t 7 7+t 8 8+t 9 9+t 10 10+c 11 11

private theorem literal_diff_cons_two (t u : NativeJetIndex × NativeJetIndex × ℝ)
    (ts : List (NativeJetIndex × NativeJetIndex × ℝ)) (p : Fin 4 → ℂ) :
    nativeLiteralFourier (t::u::ts) p-nativeLiteralFourier (t::u::ts) 0=
      (nativeLiteralFourier [t] p-nativeLiteralFourier [t] 0)+
        (nativeLiteralFourier (u::ts) p-nativeLiteralFourier (u::ts) 0) := by
  simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  abel

private theorem rectangular_single_neg {R C : Type*} [DecidableEq R] [DecidableEq C]
    (i : R) (j : C) (z : ℂ) : Matrix.single i j (-z)=-Matrix.single i j z := by
  ext a b
  change (if i=a ∧ j=b then -z else 0)=-(if i=a ∧ j=b then z else 0)
  split_ifs <;> simp

private theorem pair_auxiliary_matrix (d e mu nu : Fin 4) (pair : Fin 6) (p : Fin 4 → ℂ) :
    (nativeLiteralFourier (pairDerivativeTerms d e mu nu pair) p-
      nativeLiteralFourier (pairDerivativeTerms d e mu nu pair) 0).submatrix gaugeAuxiliaryIndex nativeRestIndex=
      derivativeColourMatrix d mu pair p-derivativeColourMatrix e nu pair p := by
  unfold pairDerivativeTerms
  simp only [literal_diff_cons_two,Matrix.submatrix_add,Pi.add_apply,derivative_term_auxiliary_matrix]
  simp only [Complex.ofReal_ofNat,Complex.ofReal_neg,Complex.ofReal_one,one_mul,neg_mul,
    rectangular_single_neg,derivativeColourMatrix]
  abel

private theorem colour_read (d mu : Fin 4) (pair a : Fin 6) (i : Fin 12) (p : Fin 4 → ℂ) (r : Fin 217 → ℂ) :
    (derivativeColourMatrix d mu pair p*ᵥr) (a,i)=
      if pair=a then p d*auxiliaryLieReader (fun j => r (gaugeRestIndex mu j)) i else 0 := by
  by_cases same : pair=a
  · subst a
    fin_cases i <;> simp [derivativeColourMatrix,Matrix.add_mulVec,Matrix.single_mulVec,auxiliaryLieReader] <;> ring1
  · simp [derivativeColourMatrix,Matrix.add_mulVec,Matrix.single_mulVec,same,Ne.symm same]

private theorem literal_diff_append (a b : List (NativeJetIndex × NativeJetIndex × ℝ)) (p : Fin 4 → ℂ) :
    nativeLiteralFourier (a++b) p-nativeLiteralFourier (a++b) 0=
      (nativeLiteralFourier a p-nativeLiteralFourier a 0)+(nativeLiteralFourier b p-nativeLiteralFourier b 0) := by
  simp only [nativeLiteralFourier,List.map_append,List.sum_append]
  abel

def nativeAuxiliaryMomentumFirst (p : Fin 4 → ℂ) : Matrix (Fin 6 × Fin 12) (Fin 217) ℂ :=
  nativeAuxiliaryRest p-nativeAuxiliaryRest 0

def nativeRestMomentumFirst (p : Fin 4 → ℂ) : Matrix (Fin 217) (Fin 6 × Fin 12) ℂ :=
  nativeRestAuxiliary p-nativeRestAuxiliary 0

private theorem actual_auxiliary_momentum_matrix (p : Fin 4 → ℂ) :
    nativeAuxiliaryMomentumFirst p=
      (derivativeColourMatrix 0 1 3 p-derivativeColourMatrix 1 0 3 p)+
      (derivativeColourMatrix 0 2 4 p-derivativeColourMatrix 2 0 4 p)+
      (derivativeColourMatrix 0 3 5 p-derivativeColourMatrix 3 0 5 p)+
      (derivativeColourMatrix 2 3 0 p-derivativeColourMatrix 3 2 0 p)+
      (derivativeColourMatrix 3 1 1 p-derivativeColourMatrix 1 3 1 p)+
      (derivativeColourMatrix 1 2 2 p-derivativeColourMatrix 2 1 2 p) := by
  have full : nativeAuxiliaryMomentumFirst p=
      (nativeLiteralFourier sourceDerivativeTerms p-nativeLiteralFourier sourceDerivativeTerms 0).submatrix
        gaugeAuxiliaryIndex nativeRestIndex := by
    ext i j
    have high : 217 ≤ (gaugeAuxiliaryIndex i).val := by dsimp only [gaugeAuxiliaryIndex,gaugeBSlot];omega
    exact actual_native_momentum_auxiliary_flux p (gaugeAuxiliaryIndex i) (nativeRestIndex j) (Or.inl high)
  rw [full]
  simp only [sourceDerivativeTerms,literal_diff_append,Matrix.submatrix_add,Pi.add_apply,pair_auxiliary_matrix]

/-- These are the six source-owned oriented curl components, in the actual auxiliary pair order. -/
def nativeMomentumCurl {K : Type*} [Field K] (p v : Fin 4 → K) : Fin 6 → K :=
  ![p 2*v 3-p 3*v 2,p 3*v 1-p 1*v 3,p 1*v 2-p 2*v 1,
    p 0*v 1-p 1*v 0,p 0*v 2-p 2*v 0,p 0*v 3-p 3*v 0]

private theorem lie_reader_scale (z : ℂ) (v : Fin 12 → ℂ) :
    auxiliaryLieReader (fun a => z*v a)=fun a => z*auxiliaryLieReader v a := by
  funext a
  unfold auxiliaryLieReader
  split_ifs <;> ring1

/-- All original momentum fluxes preserve the complete colour metric and all remaining gauge components. -/
theorem actual_native_auxiliary_momentum_reader (p : Fin 4 → ℂ) (r : Fin 217 → ℂ) :
    nativeAuxiliaryMomentumFirst p*ᵥr=fun i =>
      auxiliaryLieReader (fun a => nativeMomentumCurl p (fun mu => r (gaugeRestIndex mu a)) i.1) i.2 := by
  rw [actual_auxiliary_momentum_matrix]
  funext i
  rcases i with ⟨pair,i⟩
  simp only [Matrix.add_mulVec,Matrix.sub_mulVec,Pi.add_apply,Pi.sub_apply,colour_read]
  fin_cases pair <;> simp only [Fin.reduceFinMk,Fin.reduceEq,if_true,if_false,
    sub_zero,add_zero,zero_add]
  all_goals dsimp only [nativeMomentumCurl,Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals unfold auxiliaryLieReader
  all_goals split_ifs <;> ring1

private theorem single_derivative_skew (t : NativeJetIndex × NativeJetIndex × ℝ) (p : Fin 4 → ℂ)
    (slots : t.1.1≠none ∧ t.2.1.1=none) (i j : Fin 289) :
    nativeLiteralFourier [t] p i j-nativeLiteralFourier [t] 0 i j=
      -(nativeLiteralFourier [t] p j i-nativeLiteralFourier [t] 0 j i) := by
  cases left : t.1.1 with
  | none => exact False.elim (slots.1 left)
  | some d =>
    simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      left,slots.2,jetSymbol,Pi.neg_apply,Pi.zero_apply,mul_one,mul_zero,Matrix.single_zero,
      add_zero,Matrix.add_apply,Matrix.zero_apply]
    simp only [Matrix.single_apply,and_comm]
    split_ifs <;> ring1

private theorem list_derivative_skew (ts : List (NativeJetIndex × NativeJetIndex × ℝ)) (p : Fin 4 → ℂ)
    (slots : ts.all (fun t => decide (t.1.1≠none ∧ t.2.1.1=none))=true) (i j : Fin 289) :
    nativeLiteralFourier ts p i j-nativeLiteralFourier ts 0 i j=
      -(nativeLiteralFourier ts p j i-nativeLiteralFourier ts 0 j i) := by
  induction ts with
  | nil => simp [nativeLiteralFourier]
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true] at slots
    have head : t.1.1≠none ∧ t.2.1.1=none := by simpa only [decide_eq_true_eq] using slots.1
    have single := single_derivative_skew t p head i j
    have tail := ih slots.2
    simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Matrix.add_apply,Matrix.zero_apply,add_zero] at single
    simp only [literal_cons,Matrix.add_apply]
    linear_combination single+tail

/-- Both original momentum slots are transpose-dual with their source Fourier signs. -/
theorem actual_native_momentum_flux_transpose (p : Fin 4 → ℂ) :
    nativeRestMomentumFirst p=-(nativeAuxiliaryMomentumFirst p).transpose := by
  ext i j
  have high : 217 ≤ (gaugeAuxiliaryIndex j).val := by dsimp only [gaugeAuxiliaryIndex,gaugeBSlot];omega
  change emOriginalJacobi p (nativeRestIndex i) (gaugeAuxiliaryIndex j)-
    emOriginalJacobi 0 (nativeRestIndex i) (gaugeAuxiliaryIndex j)=
    -(emOriginalJacobi p (gaugeAuxiliaryIndex j) (nativeRestIndex i)-
      emOriginalJacobi 0 (gaugeAuxiliaryIndex j) (nativeRestIndex i))
  rw [actual_native_momentum_auxiliary_flux p _ _ (Or.inr high),
    actual_native_momentum_auxiliary_flux p _ _ (Or.inl high)]
  have slots : sourceDerivativeTerms.all (fun t => decide (t.1.1≠none ∧ t.2.1.1=none))=true := by decide +kernel
  exact list_derivative_skew _ p slots _ _

/-- The adjoint oriented divergence uses the same six source pairs as the curl. -/
def nativeMomentumDivergence {K : Type*} [Field K] (p : Fin 4 → K) (b : Fin 6 → K) : Fin 4 → K :=
  ![-p 1*b 3-p 2*b 4-p 3*b 5,p 3*b 1-p 2*b 2+p 0*b 3,
    -p 3*b 0+p 1*b 2+p 0*b 4,p 2*b 0-p 1*b 1+p 0*b 5]

private theorem colour_dual_read (d mu nu : Fin 4) (pair : Fin 6) (i : Fin 12)
    (p : Fin 4 → ℂ) (b : (Fin 6 × Fin 12) → ℂ) :
    ((derivativeColourMatrix d nu pair p).transpose*ᵥb) (gaugeRestIndex mu i)=
      if nu=mu then p d*auxiliaryLieReader (fun j => b (pair,j)) i else 0 := by
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
    fin_cases i <;> simp [derivativeColourMatrix,Matrix.transpose_add,Matrix.transpose_single,
      Matrix.add_mulVec,Matrix.single_mulVec,slots,auxiliaryLieReader] <;> ring1
  · have outside (j : Fin 12) : gaugeRestIndex mu i≠gaugeRestIndex nu j := by
      intro h
      exact same ((slots j i).mp h.symm).1
    simp [derivativeColourMatrix,Matrix.transpose_add,Matrix.transpose_single,
      Matrix.add_mulVec,Matrix.single_mulVec,outside,same]

/-- Every original gauge momentum row keeps all auxiliary colours and the source transpose-dual sign. -/
theorem actual_native_rest_momentum_reader (p : Fin 4 → ℂ) (b : (Fin 6 × Fin 12) → ℂ)
    (mu : Fin 4) (a : Fin 12) :
    (nativeRestMomentumFirst p*ᵥb) (gaugeRestIndex mu a)=
      -nativeMomentumDivergence p (fun pair => auxiliaryLieReader (fun i => b (pair,i)) a) mu := by
  rw [actual_native_momentum_flux_transpose,actual_auxiliary_momentum_matrix]
  simp only [Matrix.neg_mulVec,Matrix.transpose_add,Matrix.transpose_sub,Matrix.add_mulVec,
    Matrix.sub_mulVec,Pi.neg_apply,Pi.add_apply,Pi.sub_apply,colour_dual_read]
  fin_cases mu <;> simp only [Fin.reduceFinMk,Fin.reduceEq,if_true,if_false,
    sub_zero,zero_sub,add_zero,zero_add]
  all_goals dsimp only [nativeMomentumDivergence,Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals ring1

theorem native_momentum_curl_neg (p v : Fin 4 → ℂ) :
    nativeMomentumCurl (-p) v=-nativeMomentumCurl p v := by
  funext pair
  fin_cases pair
  all_goals dsimp only [nativeMomentumCurl,Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,
    Fin.cases,Fin.induction,Fin.induction.go,Pi.neg_apply]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals ring1

/-- The full original mixed momentum flux is odd, while its original background is retained separately. -/
theorem actual_native_auxiliary_momentum_odd (p : Fin 4 → ℂ) :
    nativeAuxiliaryMomentumFirst (-p)=-nativeAuxiliaryMomentumFirst p := by
  apply Matrix.mulVec_injective
  funext r
  rw [actual_native_auxiliary_momentum_reader,Matrix.neg_mulVec,actual_native_auxiliary_momentum_reader]
  funext i
  have negCurl : (fun a => nativeMomentumCurl (-p) (fun mu => r (gaugeRestIndex mu a)) i.1)=
      fun a => (-1 : ℂ)*nativeMomentumCurl p (fun mu => r (gaugeRestIndex mu a)) i.1 := by
    funext a
    simp only [native_momentum_curl_neg,Pi.neg_apply,neg_one_mul]
  rw [negCurl,lie_reader_scale]
  simp only [neg_one_mul,Pi.neg_apply]

theorem actual_native_rest_momentum_odd (p : Fin 4 → ℂ) :
    nativeRestMomentumFirst (-p)=-nativeRestMomentumFirst p := by
  rw [actual_native_momentum_flux_transpose,actual_native_momentum_flux_transpose,
    actual_native_auxiliary_momentum_odd]
  simp only [Matrix.transpose_neg,neg_neg]

end LowEnergy.GaussComposite.ActualDressedEMNativeMomentum
