import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeMomentumFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeMomentum
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open SourcePropagationNativeActionHessian ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMClockDispersion
open ActualDressedEMNativeSchurClock ActualDressedEMNativePrincipal ActualEMCarrierOwn
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

/-- The source second momentum coefficient retains all original fields before the gauge read. -/
def nativeMomentumEven (p : Fin 4 → ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  (1/2 : ℂ) • (emOriginalJacobi p+emOriginalJacobi (-p))-emOriginalJacobi 0

private theorem original_gauge_derivative_support : nativeCompleteLiteralTerms.all (fun t =>
    decide (((t.1.2.val<9 ∨ 57 ≤ t.1.2.val) ∧ (t.2.1.2.val<9 ∨ 57 ≤ t.2.1.2.val)) ∨
      t.1.1=none ∨ t.2.1.1=none))=true := by decide +kernel

private theorem literal_cons (t : NativeJetIndex × NativeJetIndex × ℝ)
    (ts : List (NativeJetIndex × NativeJetIndex × ℝ)) (p : Fin 4 → ℂ) :
    nativeLiteralFourier (t::ts) p=nativeLiteralFourier [t] p+nativeLiteralFourier ts p := by
  simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

private theorem literal_single_gauge_even (t : NativeJetIndex × NativeJetIndex × ℝ)
    (p : Fin 4 → ℂ) (i j : Fin 289) (low : 9 ≤ i.val) (high : i.val<57)
    (support : ((t.1.2.val<9 ∨ 57 ≤ t.1.2.val) ∧ (t.2.1.2.val<9 ∨ 57 ≤ t.2.1.2.val)) ∨
      t.1.1=none ∨ t.2.1.1=none) :
    (1/2 : ℂ)*(nativeLiteralFourier [t] p i j+nativeLiteralFourier [t] (-p) i j)-
      nativeLiteralFourier [t] 0 i j=0 := by
  rcases support with outside | left | right
  · have L : t.1.2≠i := by intro h;have e:=congrArg Fin.val h;rcases outside.1 with h|h <;> omega
    have R : t.2.1.2≠i := by intro h;have e:=congrArg Fin.val h;rcases outside.2 with h|h <;> omega
    simp [nativeLiteralFourier,L,R]
  · cases second : t.2.1.1 <;>
      simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        left,second,jetSymbol,Pi.neg_apply,Pi.zero_apply,neg_neg,mul_one,mul_zero,
        Matrix.add_apply,Matrix.zero_apply,add_zero,Matrix.single_apply]
    all_goals split_ifs <;> ring1
  · cases first : t.1.1 <;>
      simp only [nativeLiteralFourier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        right,first,jetSymbol,Pi.neg_apply,Pi.zero_apply,neg_neg,mul_one,mul_zero,
        Matrix.add_apply,Matrix.zero_apply,add_zero,Matrix.single_apply]
    all_goals split_ifs <;> ring1

private theorem literal_gauge_even (ts : List (NativeJetIndex × NativeJetIndex × ℝ))
    (support : ts.all (fun t => decide (((t.1.2.val<9 ∨ 57 ≤ t.1.2.val) ∧
      (t.2.1.2.val<9 ∨ 57 ≤ t.2.1.2.val)) ∨ t.1.1=none ∨ t.2.1.1=none))=true)
    (p : Fin 4 → ℂ) (i j : Fin 289) (low : 9 ≤ i.val) (high : i.val<57) :
    (1/2 : ℂ)*(nativeLiteralFourier ts p i j+nativeLiteralFourier ts (-p) i j)-
      nativeLiteralFourier ts 0 i j=0 := by
  induction ts with
  | nil => simp [nativeLiteralFourier]
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true] at support
    have head := of_decide_eq_true support.1
    have single := literal_single_gauge_even t p i j low high head
    have tail := ih support.2
    rw [literal_cons t ts p,literal_cons t ts (-p),literal_cons t ts 0]
    simp only [Matrix.add_apply]
    linear_combination single+tail

/-- The complete original action has no second momentum term on any gauge-potential row. -/
theorem actual_native_gauge_momentum_even_zero (p : Fin 4 → ℂ) (mu : Fin 4) (a : Fin 12) (j : Fin 289) :
    nativeMomentumEven p (gaugeSlot mu a) j=0 := by
  have source (q : Fin 4 → ℂ) : emOriginalJacobi q=nativeLiteralFourier nativeCompleteLiteralTerms q := by
    unfold emOriginalJacobi
    rw [em_hessian_source,nativeHessian_complete_literal,nativeLiteralFourier_sound]
  have low : 9 ≤ (gaugeSlot mu a).val := by dsimp only [gaugeSlot];omega
  have high : (gaugeSlot mu a).val<57 := by have M:=mu.isLt;have A:=a.isLt;dsimp only [gaugeSlot];omega
  change (1/2 : ℂ)*(emOriginalJacobi p (gaugeSlot mu a) j+emOriginalJacobi (-p) (gaugeSlot mu a) j)-
    emOriginalJacobi 0 (gaugeSlot mu a) j=0
  rw [source p,source (-p),source 0]
  exact literal_gauge_even _ original_gauge_derivative_support p _ j low high

/-- All remaining fields stay in this source-generated native principal matrix. -/
def nativeMomentumPrincipal (p : Fin 4 → ℂ) : Matrix (Fin 217) (Fin 217) ℂ :=
  (nativeMomentumEven p).submatrix nativeRestIndex nativeRestIndex-
    nativeRestMomentumFirst p*nativeAuxiliaryInverseMatrix*nativeAuxiliaryMomentumFirst p

/-- The curl matrix is the literal source curl evaluated on the four coordinate inputs. -/
def nativeMomentumCurlMatrix (p : Fin 4 → ℂ) : Matrix (Fin 6) (Fin 4) ℂ :=
  fun pair mu => nativeMomentumCurl p (Pi.single mu 1) pair

theorem native_momentum_curl_matrix_action (p v : Fin 4 → ℂ) :
    nativeMomentumCurlMatrix p*ᵥv=nativeMomentumCurl p v := by
  funext pair
  fin_cases pair <;>
    simp [nativeMomentumCurlMatrix,nativeMomentumCurl,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Pi.single_apply] <;> ring1

theorem native_momentum_divergence_matrix_action (p : Fin 4 → ℂ) (b : Fin 6 → ℂ) :
    (nativeMomentumCurlMatrix p).transpose*ᵥb=nativeMomentumDivergence p b := by
  funext mu
  fin_cases mu <;>
    simp [nativeMomentumCurlMatrix,nativeMomentumCurl,nativeMomentumDivergence,Matrix.mulVec,dotProduct,
      Matrix.transpose_apply,Fin.sum_univ_succ] <;> ring1

/-- The original colour inverse has already cancelled; the six actual lapse weights remain. -/
def nativeEMMomentumMatrix (p : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (nativeMomentumCurlMatrix p).transpose*
    Matrix.diagonal (fun pair => (nativeAuxiliaryWeight pair)⁻¹)*nativeMomentumCurlMatrix p

theorem actual_native_em_momentum_matrix_action (p v : Fin 4 → ℂ) :
    nativeEMMomentumMatrix p*ᵥv=
      nativeMomentumDivergence p (fun pair => (nativeAuxiliaryWeight pair)⁻¹*nativeMomentumCurl p v pair) := by
  unfold nativeEMMomentumMatrix
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,native_momentum_curl_matrix_action]
  have diagonal : (Matrix.diagonal (fun pair => (nativeAuxiliaryWeight pair)⁻¹)*ᵥnativeMomentumCurl p v)=
      fun pair => (nativeAuxiliaryWeight pair)⁻¹*nativeMomentumCurl p v pair := by
    funext pair
    exact Matrix.mulVec_diagonal _ _ _
  rw [diagonal,native_momentum_divergence_matrix_action]

/-- The original W consumes all72 momentum rows before any direction or observer is selected. -/
theorem actual_native_inverse_momentum_reader (p : Fin 4 → ℂ) (r : Fin 217 → ℂ) :
    nativeAuxiliaryInverseMatrix*ᵥ(nativeAuxiliaryMomentumFirst p*ᵥr)=fun i =>
      (nativeAuxiliaryWeight i.1)⁻¹*nativeMomentumCurl p (fun mu => r (gaugeRestIndex mu i.2)) i.1 := by
  rw [native_auxiliary_inverse_matrix_action,actual_native_auxiliary_momentum_reader]
  funext i
  change (nativeAuxiliaryWeight i.1)⁻¹*
    auxiliaryLieInverse (auxiliaryLieReader (fun a => nativeMomentumCurl p (fun mu => r (gaugeRestIndex mu a)) i.1)) i.2=_
  rw [auxiliary_lie_inverse_left]

private theorem lie_reader_scale (z : ℂ) (v : Fin 12 → ℂ) :
    auxiliaryLieReader (fun a => z*v a)=fun a => z*auxiliaryLieReader v a := by
  funext a
  unfold auxiliaryLieReader
  split_ifs <;> ring1

private theorem lie_reader_curl (p : Fin 4 → ℂ) (r : Fin 217 → ℂ) (pair : Fin 6) (i : Fin 12) :
    auxiliaryLieReader (fun a => nativeMomentumCurl p (fun mu => r (gaugeRestIndex mu a)) pair) i=
      nativeMomentumCurl p (fun mu => auxiliaryLieReader (fun a => r (gaugeRestIndex mu a)) i) pair := by
  fin_cases pair
  all_goals dsimp only [nativeMomentumCurl,Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals unfold auxiliaryLieReader
  all_goals split_ifs <;> ring1

/-- Every gauge row of the complete217 principal retains the source colour metric and full constraint structure. -/
theorem actual_native_gauge_momentum_principal (p : Fin 4 → ℂ) (r : Fin 217 → ℂ) (mu : Fin 4) (a : Fin 12) :
    (nativeMomentumPrincipal p*ᵥr) (gaugeRestIndex mu a)=
      (nativeEMMomentumMatrix p*ᵥ(fun nu => auxiliaryLieReader (fun i => r (gaugeRestIndex nu i)) a)) mu := by
  have zero : ((nativeMomentumEven p).submatrix nativeRestIndex nativeRestIndex*ᵥr) (gaugeRestIndex mu a)=0 := by
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_eq_zero
    intro j _
    have embed : nativeRestIndex (gaugeRestIndex mu a)=gaugeSlot mu a := by apply Fin.ext;rfl
    simp only [Matrix.submatrix_apply,embed,actual_native_gauge_momentum_even_zero,zero_mul]
  unfold nativeMomentumPrincipal
  rw [Matrix.sub_mulVec]
  simp only [Pi.sub_apply]
  rw [zero,zero_sub,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,actual_native_rest_momentum_reader,
    actual_native_inverse_momentum_reader,neg_neg,actual_native_em_momentum_matrix_action]
  simp only [lie_reader_scale,lie_reader_curl]

private theorem actual_rest_em_projection (r : Fin 217 → ℂ) (mu : Fin 4) :
    (nativeEMRestInsertion.transpose*ᵥr) mu=
      (1/2 : ℂ)*(-r (gaugeRestIndex mu 6)+r (gaugeRestIndex mu 7)-r (gaugeRestIndex mu 11)) := by
  let full : Fin 289 → ℂ := fun j => Fin.addCases r (fun _ : Fin 72 => 0) j
  have same : (emInsertion.transpose*ᵥfull) mu=(nativeEMRestInsertion.transpose*ᵥr) mu := by
    change (∑ j : Fin (217+72),emInsertion j mu*Fin.addCases r (fun _ : Fin 72 => 0) j)=_
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,mul_zero,Finset.sum_const_zero,add_zero]
    rfl
  rw [← same,em_projection_coordinates]
  have embed (a : Fin 12) : gaugeSlot mu a=Fin.castAdd 72 (gaugeRestIndex mu a) := by apply Fin.ext;rfl
  simp only [embed,full,Fin.addCases_left]

/-- The actual EM observer of the full remaining-field principal is the fixed source weighted curl-divergence. -/
theorem actual_native_em_momentum_principal (p : Fin 4 → ℂ) (r : Fin 217 → ℂ) :
    nativeEMRestInsertion.transpose*ᵥ(nativeMomentumPrincipal p*ᵥr)=
      nativeEMMomentumMatrix p*ᵥ(nativeEMRestInsertion.transpose*ᵥr) := by
  let v := fun a : Fin 12 => fun nu : Fin 4 => auxiliaryLieReader (fun i => r (gaugeRestIndex nu i)) a
  have projection : (1/2 : ℂ) • (-v 6+v 7-v 11)=nativeEMRestInsertion.transpose*ᵥr := by
    funext mu
    rw [actual_rest_em_projection]
    simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.add_apply,Pi.neg_apply,v,auxiliaryLieReader,
      Fin.reduceEq,if_true,if_false]
    ring1
  funext mu
  rw [actual_rest_em_projection]
  simp only [actual_native_gauge_momentum_principal]
  change (1/2 : ℂ)*(-(nativeEMMomentumMatrix p*ᵥv 6) mu+(nativeEMMomentumMatrix p*ᵥv 7) mu-
    (nativeEMMomentumMatrix p*ᵥv 11) mu)=_
  calc
    _=(nativeEMMomentumMatrix p*ᵥ((1/2 : ℂ) • (-v 6+v 7-v 11))) mu := by
      simp only [Matrix.mulVec_smul,Matrix.mulVec_sub,Matrix.mulVec_add,Matrix.mulVec_neg,
        Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.add_apply,Pi.neg_apply]
    _=_ := by rw [projection]

end LowEnergy.GaussComposite.ActualDressedEMNativeMomentum
