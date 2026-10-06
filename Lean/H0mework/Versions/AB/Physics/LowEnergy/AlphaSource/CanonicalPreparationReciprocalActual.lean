import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationReciprocalSplittings

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumReciprocalBudget
open PreparationActualFactor PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumClockGuard
open PreparationScalarCoordinates PreparationPhaseSource PreparationVacuumClockPole
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff GaussNativeEnergy
open scoped BigOperators ContDiff Topology

abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

private theorem primitive_smoothOn (j : Fin 3) : ContDiffOn ℝ ∞ (primitivePole j) poleDomain :=
  fun x hx => (primitivePole_smooth j x hx).contDiffWithinAt

private theorem primitive_list_bound (j : Fin 3) (x : Phase) (hx : x∈poleDomain)
    (B : ℕ → ℝ) (N : ℕ)
    (bounds : ∀ n≤N,∀ w : Word n,|jet n (primitivePole j) w x| ≤ B n)
    (vs : List Phase) (canonical : CanonicalList vs) (finite : vs.length ≤ N) :
    |listJet vs (primitivePole j) x| ≤ B vs.length := by
  let w : Word vs.length := fun i => Classical.choose
    (canonical (vs.get i) (List.get_mem vs i))
  have generated : List.ofFn (fun i => slotDirection (w i))=vs := by
    have same : (fun i => slotDirection (w i))=(fun i : Fin vs.length => vs.get i) := by
      funext i
      exact (Classical.choose_spec (canonical (vs.get i) (List.get_mem vs i))).symm
    rw [same]
    exact List.ofFn_getElem
  rw [←generated,listJet_ofFn poleDomain_open (primitive_smoothOn j) vs.length
    (fun i => slotDirection (w i)) x hx]
  simpa only [jet,List.length_ofFn] using bounds vs.length finite w

private theorem abs_sum_bound (ss : List Split) (F G : Split → ℝ)
    (bounds : ∀ s∈ss,|F s| ≤ G s) : |(ss.map F).sum| ≤ (ss.map G).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (bounds s (by simp))
      (ih (fun t ht => bounds t (by simp [ht]))))

theorem primitive_inverse_list_budget (j : Fin 3) (x : Phase) (hx : x∈poleDomain)
    (B : ℕ → ℝ) (N : ℕ) (u0 : ℝ)
    (zeroNonnegative : 0 ≤ u0) (nonnegative : ∀ n,0 ≤ B n)
    (zeroOrder : |(primitivePole j x)⁻¹| ≤ u0)
    (bounds : ∀ n≤N,∀ w : Word n,|jet n (primitivePole j) w x| ≤ B n) :
    ∀ n≤N,∀ vs : List Phase,CanonicalList vs → vs.length=n →
      |listJet vs (fun y => (primitivePole j y)⁻¹) x| ≤ inverseBudget B u0 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro finite vs canonical length
    cases vs with
    | nil =>
      have zero : n=0 := length.symm
      subst n
      simpa only [listJet,List.foldr_nil,List.length_nil,inverseBudget_zero] using zeroOrder
    | cons v vs =>
      have count : n=vs.length+1 := by simpa using length.symm
      subst n
      have recurrence := source_reciprocal_word j v vs x hx
      rw [recurrence,abs_mul,abs_neg,List.length_cons,inverseBudget_succ]
      have summands : ∀ s∈(wordSplittings (v::vs)).tail,
          |splitValue (primitivePole j) (fun y => (primitivePole j y)⁻¹) x s| ≤
            B s.1.length*inverseBudget B u0 s.2.length := by
        intro s hs
        have member := List.mem_of_mem_tail hs
        have parts := canonicalList_splits canonical s member
        have lengths := wordSplittings_lengths (v::vs) s member
        simp only [List.length_cons] at lengths
        have left := primitive_list_bound j x hx B N bounds s.1 parts.1 (by omega)
        have short := tail_split_short v vs s hs
        have right := ih s.2.length short (by omega) s.2 parts.2 rfl
        rw [splitValue,abs_mul]
        exact mul_le_mul left right (abs_nonneg _) (nonnegative _)
      calc
        _ ≤ u0*(((wordSplittings (v::vs)).tail).map
            (fun s => B s.1.length*inverseBudget B u0 s.2.length)).sum := by
          apply mul_le_mul zeroOrder (abs_sum_bound _ _ _ summands) (abs_nonneg _) zeroNonnegative
        _ = u0*∑ r : Fin (vs.length+1),((vs.length+1).choose (r.val+1) : ℝ)*B (r.val+1)*
            inverseBudget B u0 (vs.length-r.val) := by rw [tail_split_convolution]

theorem primitive_inverse_canonical_budget (j : Fin 3) (x : Phase) (hx : x∈poleDomain)
    (B : ℕ → ℝ) (N : ℕ) (u0 : ℝ)
    (zeroNonnegative : 0 ≤ u0) (nonnegative : ∀ n,0 ≤ B n)
    (zeroOrder : |(primitivePole j x)⁻¹| ≤ u0)
    (bounds : ∀ n≤N,∀ w : Word n,|jet n (primitivePole j) w x| ≤ B n)
    (m : ℕ) (finite : m≤N) (w : Word m) :
    |jet m (fun y => (primitivePole j y)⁻¹) w x| ≤ inverseBudget B u0 m := by
  have inverseSmooth : ContDiffOn ℝ ∞ (fun y => (primitivePole j y)⁻¹) poleDomain :=
    fun y hy => ((primitivePole_smooth j y hy).inv (primitivePole_nonzero j y hy)).contDiffWithinAt
  have canonical : CanonicalList (List.ofFn (slotDirection∘w)) := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact ⟨w i,rfl⟩
  have actual := primitive_inverse_list_budget j x hx B N u0 zeroNonnegative nonnegative zeroOrder
    bounds m finite (List.ofFn (slotDirection∘w)) canonical (List.length_ofFn)
  rw [listJet_ofFn poleDomain_open inverseSmooth m (slotDirection∘w) x hx] at actual
  exact actual

private theorem actualUnit_admitted (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) : (z,WithLp.toLp 2 u)∈poleDomain := by
  refine ⟨actual_closed_phase_cone z u zbox ubox unit,?_⟩
  have determinant := actual_clockMatrix_det_j15 z u zbox ubox
  have positive : 0 < (clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))).det := by
    linarith
  simpa only [sourceM,actualT,actualS,nativePhase,clockMatrix] using positive.ne'

theorem actual_T_inverse_budget (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (B : ℕ → ℝ) (N : ℕ)
    (nonnegative : ∀ n,0 ≤ B n)
    (sourceBounds : ∀ n≤N,∀ w : Word n,|jet n actualT w (z,WithLp.toLp 2 u)| ≤ B n)
    (m : ℕ) (finite : m≤N) (w : Word m) :
    |jet m (fun y => (actualT y)⁻¹) w (z,WithLp.toLp 2 u)| ≤ sourceTInverseBudget B m := by
  exact primitive_inverse_canonical_budget 1 _ (actualUnit_admitted z u zbox ubox unit)
    B N 15 (by norm_num) nonnegative (actual_T_inverse_j15 z u zbox ubox) sourceBounds m finite w

theorem actual_det_inverse_budget (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (B : ℕ → ℝ) (N : ℕ)
    (nonnegative : ∀ n,0 ≤ B n)
    (sourceBounds : ∀ n≤N,∀ w : Word n,|jet n sourceDet w (z,WithLp.toLp 2 u)| ≤ B n)
    (m : ℕ) (finite : m≤N) (w : Word m) :
    |jet m (fun y => (sourceDet y)⁻¹) w (z,WithLp.toLp 2 u)| ≤ sourceDetInverseBudget B m := by
  have zeroOrder : |(sourceDet (z,WithLp.toLp 2 u))⁻¹| ≤ 3375 := by
    simpa only [sourceDet,sourceM,actualT,actualS,nativePhase,clockMatrix] using
      actual_det_inverse_j15 z u zbox ubox
  exact primitive_inverse_canonical_budget 2 _ (actualUnit_admitted z u zbox ubox unit)
    B N 3375 (by norm_num) nonnegative zeroOrder sourceBounds m finite w

end LowEnergy.PreparationVacuumReciprocalBudget
