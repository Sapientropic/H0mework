import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationRationalWTimeBounds

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumRationalW
open PreparationVacuumCoframeBudget GaussNativeEnergy GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open PreparationScalarCoordinates PreparationVacuumLowerLeaves
open scoped BigOperators ContDiff Topology Matrix

abbrev QTimeTerms := List (TimeTerms × Powers)
structure WEntry where
  numerator : QTimeTerms
  poles : Powers

def wNumerator (ts : QTimeTerms) (n : ℝ) (b : Fin 3 → ℝ) : Symbol := fun x =>
  (ts.map (fun t => timeValue t.1 n b*monomial false t.2 x)).sum

def wNumeratorArray (ts : QTimeTerms) (m : ℕ) : ℕ :=
  (ts.map (fun t => timeAmplitude t.1*(degree t.2).descFactorial m*15^(degree t.2-m))).sum

def wValue (e : WEntry) (n : ℝ) (b : Fin 3 → ℝ) : Symbol := fun x =>
  wNumerator e.numerator n b x*monomial true e.poles x

def wArray (e : WEntry) (m : ℕ) : ℕ :=
  ∑ k∈Finset.range (m+1),m.choose k*wNumeratorArray e.numerator k*reciprocalArray (degree e.poles) (m-k)

def WSupported (e : WEntry) : Prop := poleSupported e.poles ∧
  ∀ t∈e.numerator,∀ u∈t.1,CoefficientSupported u.1

instance (e : WEntry) : Decidable (WSupported e) := by
  unfold WSupported poleSupported CoefficientSupported
  infer_instance

theorem wNumerator_smooth (ts : QTimeTerms) (n : ℝ) (b : Fin 3 → ℝ) :
    ContDiffOn ℝ ∞ (wNumerator ts n b) coframeDomain := by
  induction ts with
  | nil => exact contDiffOn_const
  | cons t ts ih => exact (contDiffOn_const.mul (monomial_smooth false t.2 (by simp))).add ih

theorem wValue_smooth (e : WEntry) (supported : WSupported e) (n : ℝ) (b : Fin 3 → ℝ) :
    ContDiffOn ℝ ∞ (wValue e n b) coframeDomain :=
  (wNumerator_smooth e.numerator n b).mul (monomial_smooth true e.poles (fun _ => supported.1))

theorem wNumerator_budget (ts : QTimeTerms)
    (supported : ∀ t∈ts,∀ u∈t.1,CoefficientSupported u.1)
    (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈coframeDomain) (bound : ∀ i,|qCoordinate i x| ≤ 15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹| ≤ 15) :
    |jet m (wNumerator ts n b) w x| ≤ (wNumeratorArray ts m : ℝ) := by
  induction ts with
  | nil =>
    rw [show wNumerator [] n b=(fun _ : Phase => 0) by funext y; rfl,jet_zero]
    simp [wNumeratorArray]
  | cons t ts ih =>
    have smooth := (monomial_smooth false t.2 (by simp) x hx).contDiffAt (coframeDomain_open.mem_nhds hx)
    have tail := (wNumerator_smooth ts n b x hx).contDiffAt (coframeDomain_open.mem_nhds hx)
    have read : jet m (wNumerator (t::ts) n b) w x=
        timeValue t.1 n b*jet m (monomial false t.2) w x+jet m (wNumerator ts n b) w x := by
      change jet m (fun y => timeValue t.1 n b*monomial false t.2 y+wNumerator ts n b y) w x=_
      rw [jet_add _ _ _ _ _ (contDiffAt_const.mul smooth) tail,jet_scale _ _ _ _ _ smooth]
    rw [read]
    have estimate := mul_le_mul (timeValue_budget t.1 (supported t (by simp)) n b time)
      (actual_monomial_budget false t.2 (by simp) m w x hx bound inverse) (abs_nonneg _) (Nat.cast_nonneg _)
    refine (abs_add_le _ _).trans ((add_le_add (by simpa only [abs_mul] using estimate)
      (ih (fun t ht => supported t (by simp [ht])))).trans_eq ?_)
    simp [wNumeratorArray,monomialBound,numeratorBound,Nat.cast_add,Nat.cast_mul,mul_assoc]

theorem wValue_budget (e : WEntry) (supported : WSupported e)
    (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈coframeDomain) (bound : ∀ i,|qCoordinate i x| ≤ 15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹| ≤ 15) :
    |jet m (wValue e n b) w x| ≤ (wArray e m : ℝ) := by
  have result := product_jet_budget (wNumerator e.numerator n b) (monomial true e.poles)
    (wNumerator_smooth e.numerator n b) (monomial_smooth true e.poles (fun _ => supported.1))
    (fun m => (wNumeratorArray e.numerator m : ℝ)) (fun m => (reciprocalArray (degree e.poles) m : ℝ))
    (fun _ => Nat.cast_nonneg _) x hx
    (fun m w => wNumerator_budget e.numerator supported.2 n b time m w x hx bound inverse)
    (fun m w => by simpa [reciprocalArray,monomialBound,reciprocalBound] using
      actual_monomial_budget true e.poles (fun _ => supported.1) m w x hx bound inverse) m w
  exact result.trans_eq (by simp [convolution,wArray,Nat.cast_sum,Nat.cast_mul])

def electricEntries : Matrix (Fin 3) (Fin 3) WEntry :=
  !![⟨[([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,2,0,0])],![0,0,1,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([((-1/2 : ℚ),![0,1,1,0])],![1,0,0,0,0,1]),([((-1/2 : ℚ),![2,0,0,0]),((1/2 : ℚ),![0,2,0,0])],![0,1,0,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([((-1/2 : ℚ),![0,1,0,1])],![1,0,1,0,0,0]),([((1/2 : ℚ),![0,1,1,0])],![1,0,0,0,1,0]),([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,2,0,0])],![0,1,0,0,1,0]),([((-1/2 : ℚ),![2,0,0,0]),((1/2 : ℚ),![0,2,0,0])],![0,0,1,1,0,0])],![1,0,0,0,0,0]⟩;
    ⟨[([((-1/2 : ℚ),![0,1,1,0])],![1,0,0,0,0,1]),([((-1/2 : ℚ),![2,0,0,0]),((1/2 : ℚ),![0,2,0,0])],![0,1,0,0,0,1])],![1,0,0,0,0,0]⟩, ⟨[([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,0,2,0])],![2,0,0,0,0,1]),([((1 : ℚ),![0,1,1,0])],![1,1,0,0,0,1]),([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,2,0,0])],![0,2,0,0,0,1])],![1,0,1,0,0,0]⟩, ⟨[([((-1/2 : ℚ),![0,0,1,1])],![2,0,1,0,0,0]),([((-1/2 : ℚ),![2,0,0,0]),((1/2 : ℚ),![0,0,2,0])],![2,0,0,0,1,0]),([((1/2 : ℚ),![0,1,0,1])],![1,1,1,0,0,0]),([((-1 : ℚ),![0,1,1,0])],![1,1,0,0,1,0]),([((1/2 : ℚ),![0,1,1,0])],![1,0,1,1,0,0]),([((-1/2 : ℚ),![2,0,0,0]),((1/2 : ℚ),![0,2,0,0])],![0,2,0,0,1,0]),([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,2,0,0])],![0,1,1,1,0,0])],![1,0,1,0,0,0]⟩;
    ⟨[([((-1/2 : ℚ),![0,1,0,1])],![1,0,1,0,0,0]),([((1/2 : ℚ),![0,1,1,0])],![1,0,0,0,1,0]),([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,2,0,0])],![0,1,0,0,1,0]),([((-1/2 : ℚ),![2,0,0,0]),((1/2 : ℚ),![0,2,0,0])],![0,0,1,1,0,0])],![1,0,0,0,0,0]⟩, ⟨[([((-1/2 : ℚ),![0,0,1,1])],![2,0,1,0,0,0]),([((-1/2 : ℚ),![2,0,0,0]),((1/2 : ℚ),![0,0,2,0])],![2,0,0,0,1,0]),([((1/2 : ℚ),![0,1,0,1])],![1,1,1,0,0,0]),([((-1 : ℚ),![0,1,1,0])],![1,1,0,0,1,0]),([((1/2 : ℚ),![0,1,1,0])],![1,0,1,1,0,0]),([((-1/2 : ℚ),![2,0,0,0]),((1/2 : ℚ),![0,2,0,0])],![0,2,0,0,1,0]),([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,2,0,0])],![0,1,1,1,0,0])],![1,0,1,0,0,0]⟩, ⟨[([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,0,0,2])],![2,0,2,0,0,0]),([((1 : ℚ),![0,0,1,1])],![2,0,1,0,1,0]),([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,0,2,0])],![2,0,0,0,2,0]),([((-1 : ℚ),![0,1,0,1])],![1,1,1,0,1,0]),([((1 : ℚ),![0,1,1,0])],![1,1,0,0,2,0]),([((1 : ℚ),![0,1,0,1])],![1,0,2,1,0,0]),([((-1 : ℚ),![0,1,1,0])],![1,0,1,1,1,0]),([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,2,0,0])],![0,2,0,0,2,0]),([((-1 : ℚ),![2,0,0,0]),((1 : ℚ),![0,2,0,0])],![0,1,1,1,1,0]),([((1/2 : ℚ),![2,0,0,0]),((-1/2 : ℚ),![0,2,0,0])],![0,0,2,2,0,0])],![1,0,1,0,0,1]⟩]

def electricArray (m : ℕ) : ℕ :=
  max (Finset.univ.sup (fun i => ∑ j,wArray (electricEntries i j) m))
      (Finset.univ.sup (fun j => ∑ i,wArray (electricEntries i j) m))

theorem electric_supported (i j : Fin 3) : WSupported (electricEntries i j) := by
  constructor
  · revert i j
    unfold poleSupported
    decide
  · fin_cases i <;> fin_cases j <;>
      norm_num [electricEntries,CoefficientSupported,and_imp,or_imp,forall_and]

def actualElectric (n : ℝ) (b : Fin 3 → ℝ) (i j : Fin 3) : Symbol := fun x =>
  (originalElectricBlock n b (fullCoordinates.symm x.1))⁻¹ i j

theorem electric_readback (n : ℝ) (b : Fin 3 → ℝ) (i j : Fin 3)
    (x : Phase) (hx : x∈coframeDomain) :
    wValue (electricEntries i j) n b x=generatedElectricInverse n b (fullCoordinates.symm x.1) i j := by
  have h0 : x.1 0≠0 := hx 0 (by decide)
  have h2 : x.1 2≠0 := hx 2 (by decide)
  have h5 : x.1 5≠0 := hx 5 (by decide)
  have sigma : sourceSigma=(1/2 : ℝ) :=
    SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.sourceCoupling_eq
  unfold generatedElectricInverse
  rw [sigma]
  simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.sub_apply,
    Matrix.vecMulVec_apply,Matrix.one_apply,smul_eq_mul,Fin.sum_univ_three]
  have q (k : Fin 6) : (fullCoordinates.symm x.1).1 k=x.1 (Fin.castAdd 94 k) := rfl
  fin_cases i <;> fin_cases j <;>
    norm_num [electricEntries,wValue,wNumerator,timeValue,timeMonomial,timeCoordinate,delta,
      monomial,powerFactor,Fin.prod_univ_succ,qCoordinate,qSlot,degree,
      triadInverse,volume,q,Fin.sum_univ_three]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals field_simp [h0,h2,h5]
  all_goals ring

theorem actual_electric_jet (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (i j : Fin 3) (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) :
    jet m (actualElectric n b i j) w x=jet m (wValue (electricEntries i j) n b) w x := by
  have physical : x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase :=
    (PreparationPhaseScalar.phaseChart x.1 box).property
  apply jet_germ
  filter_upwards [PreparationVacuumMoyalSymmetry.originalPhysicalPhase_open.mem_nhds physical] with y hy
  have coframe : y∈coframeDomain := by
    intro k hk
    rcases hk with rfl|rfl|rfl
    · exact hy.1.ne'
    · exact hy.2.1.ne'
    · exact hy.2.2.1.ne'
  have hz : fullCoordinates.symm y.1∈physicalChart := hy
  have equal := originalElectricInverse_generated n b ⟨_,hz⟩ (time_positive n b time).1.ne'
    (time_positive n b time).2.ne'
  have point : actualElectric n b i j y=generatedElectricInverse n b (fullCoordinates.symm y.1) i j :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) equal
  exact point.trans (electric_readback n b i j y coframe).symm

theorem actual_electric_row_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) (i : Fin 3) :
    (∑ j,|jet m (actualElectric n b i j) w x|) ≤ (electricArray m : ℝ) := by
  obtain ⟨hx,bound,inverse⟩ := sourceBox_guards x box
  simp only [actual_electric_jet n b time _ _ m w x box]
  refine (Finset.sum_le_sum (fun j _ => wValue_budget (electricEntries i j) (electric_supported i j)
    n b time m w x hx bound inverse)).trans ?_
  rw [←Nat.cast_sum]
  exact_mod_cast (Finset.le_sup (f:=fun i => ∑ j,wArray (electricEntries i j) m) (Finset.mem_univ i)).trans
    (Nat.le_max_left _ _)

theorem actual_electric_column_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) (j : Fin 3) :
    (∑ i,|jet m (actualElectric n b i j) w x|) ≤ (electricArray m : ℝ) := by
  obtain ⟨hx,bound,inverse⟩ := sourceBox_guards x box
  simp only [actual_electric_jet n b time _ _ m w x box]
  refine (Finset.sum_le_sum (fun i _ => wValue_budget (electricEntries i j) (electric_supported i j)
    n b time m w x hx bound inverse)).trans ?_
  rw [←Nat.cast_sum]
  exact_mod_cast (Finset.le_sup (f:=fun j => ∑ i,wArray (electricEntries i j) m) (Finset.mem_univ j)).trans
    (Nat.le_max_right _ _)

theorem electric_array_zero : electricArray 0=18839455875 := by
  have entries (i j : Fin 3) : wArray (electricEntries i j) 0=
      (!![50625,60750,121500;60750,26578125,44803125;121500,44803125,18794531250] : Matrix (Fin 3) (Fin 3) ℕ) i j := by
    fin_cases i <;> fin_cases j <;>
      norm_num [wArray,wNumeratorArray,timeAmplitude,coefficientCeiling,electricEntries,degree,reciprocalArray,Fin.sum_univ_six]
    all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  unfold electricArray
  simp_rw [entries,Fin.sum_univ_three]
  rw [show (Finset.univ : Finset (Fin 3))={0,1,2} by decide]
  norm_num [Finset.sup_insert,Finset.sup_singleton,Finset.sup_empty]
  dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  norm_num

end LowEnergy.PreparationVacuumRationalW
