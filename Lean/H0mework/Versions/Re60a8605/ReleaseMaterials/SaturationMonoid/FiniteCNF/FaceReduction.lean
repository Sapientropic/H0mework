import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointMarginal
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Pruned

/-!
Pointwise parent/face cancellation in the actual signed source.  Unlike fibre
integration, this rule keeps the coordinate and commutes with every future
clause, including clauses which still mention that coordinate.
-/

namespace SaturationMonoid.ComplexityProjection.SATJoint

def restrictFace {n : ℕ} (c : Cube n) (v : Fin n) (bit : Bool) : Cube n :=
  Function.update c v {bit}

theorem fits_restrictFace {n : ℕ} (c : Cube n) (v : Fin n) (bit : Bool)
    (hfree : c v = Finset.univ) (x : Assignment n) :
    Fits (restrictFace c v bit) x ↔ Fits c x ∧ x v = bit := by
  constructor
  · intro h
    constructor
    · intro i
      by_cases hi : i = v
      · subst i
        simp [hfree]
      · simpa [restrictFace, Function.update_of_ne hi] using h i
    · simpa [restrictFace] using h v
  · rintro ⟨h, hb⟩ i
    by_cases hi : i = v
    · subst i
      simp [restrictFace, hb]
    · simpa [restrictFace, Function.update_of_ne hi] using h i

theorem parent_sub_face {n : ℕ} (c : Cube n) (v : Fin n) (bit : Bool)
    (hfree : c v = Finset.univ) (x : Assignment n) :
    cubeIndicator c x - cubeIndicator (restrictFace c v bit) x =
      cubeIndicator (restrictFace c v (!bit)) x := by
  simp only [cubeIndicator, fits_restrictFace c v bit hfree,
    fits_restrictFace c v (!bit) hfree]
  by_cases hc : Fits c x
  · cases bit <;> cases x v <;> simp [hc]
  · simp [hc]

def Cancellable {n : ℕ} (v : Fin n) (bit : Bool) (parent face : ℤ × Cube n) : Prop :=
  parent.2 v = Finset.univ ∧ face.2 = restrictFace parent.2 v bit ∧ face.1 = -parent.1

instance {n : ℕ} (v : Fin n) (bit : Bool) (parent face : ℤ × Cube n) :
    Decidable (Cancellable v bit parent face) :=
  inferInstanceAs (Decidable
    (parent.2 v = Finset.univ ∧ face.2 = restrictFace parent.2 v bit ∧ face.1 = -parent.1))

def complementaryTerm {n : ℕ} (v : Fin n) (bit : Bool) (parent : ℤ × Cube n) :
    ℤ × Cube n := (parent.1, restrictFace parent.2 v (!bit))

theorem complementaryTerm_at {n : ℕ} (v : Fin n) (bit : Bool)
    (parent face : ℤ × Cube n) (h : Cancellable v bit parent face) (x : Assignment n) :
    (complementaryTerm v bit parent).1 * cubeIndicator (complementaryTerm v bit parent).2 x =
      parent.1 * cubeIndicator parent.2 x + face.1 * cubeIndicator face.2 x := by
  rcases h with ⟨hf, hc, hw⟩
  simp only [complementaryTerm, hc, hw, ← parent_sub_face parent.2 v bit hf x]
  ring

def contractPair {n : ℕ} : List (Fin n × Bool) → (ℤ × Cube n) → (ℤ × Cube n) →
    Option (ℤ × Cube n)
  | [], _, _ => none
  | (v, bit) :: coords, t, u =>
      if Cancellable v bit t u then some (complementaryTerm v bit t)
      else if Cancellable v bit u t then some (complementaryTerm v bit u)
      else contractPair coords t u

theorem contractPair_at {n : ℕ} (coords : List (Fin n × Bool))
    (t u result : ℤ × Cube n) (h : contractPair coords t u = some result)
    (x : Assignment n) :
    result.1 * cubeIndicator result.2 x =
      t.1 * cubeIndicator t.2 x + u.1 * cubeIndicator u.2 x := by
  induction coords with
  | nil => simp [contractPair] at h
  | cons coord coords ih =>
      obtain ⟨v, bit⟩ := coord
      by_cases ht : Cancellable v bit t u
      · have he : complementaryTerm v bit t = result := by
          simpa [contractPair, ht] using h
        rw [← he]
        exact complementaryTerm_at v bit t u ht x
      · by_cases hu : Cancellable v bit u t
        · have he : complementaryTerm v bit u = result := by
            simpa [contractPair, ht, hu] using h
          rw [← he]
          simpa only [add_comm] using complementaryTerm_at v bit u t hu x
        · apply ih
          simpa [contractPair, ht, hu] using h

def insertFace {n : ℕ} (coords : List (Fin n × Bool)) (t : ℤ × Cube n) :
    Terms n → Terms n
  | [] => [t]
  | u :: terms =>
      match contractPair coords t u with
      | some result => result :: terms
      | none => u :: insertFace coords t terms

def facePass {n : ℕ} (coords : List (Fin n × Bool)) (terms : Terms n) : Terms n :=
  terms.foldr (insertFace coords) []

theorem insertFace_at {n : ℕ} (coords : List (Fin n × Bool)) (t : ℤ × Cube n)
    (terms : Terms n) (x : Assignment n) :
    termsAt (insertFace coords t terms) x = t.1 * cubeIndicator t.2 x + termsAt terms x := by
  induction terms with
  | nil => simp [insertFace, termsAt]
  | cons u terms ih =>
      cases hp : contractPair coords t u with
      | none =>
          simp only [insertFace, hp, termsAt, List.map_cons, List.sum_cons] at *
          rw [ih]
          ring
      | some result =>
          simp only [insertFace, hp, termsAt, List.map_cons, List.sum_cons]
          rw [contractPair_at coords t u result hp x]
          ring

theorem facePass_at {n : ℕ} (coords : List (Fin n × Bool)) (terms : Terms n)
    (x : Assignment n) : termsAt (facePass coords terms) x = termsAt terms x := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      simp only [facePass, List.foldr_cons, insertFace_at] at *
      rw [ih]
      rfl

theorem facePass_future {n : ℕ} (coords : List (Fin n × Bool))
    (future : CNFFormula n) (terms : Terms n) :
    formulaMass future (facePass coords terms) = formulaMass future terms := by
  simp only [formulaMass, termsMass_eq_sum, applyFormula_at, facePass_at]

theorem insertFace_length_le {n : ℕ} (coords : List (Fin n × Bool)) (t : ℤ × Cube n)
    (terms : Terms n) : (insertFace coords t terms).length ≤ terms.length + 1 := by
  induction terms with
  | nil => simp [insertFace]
  | cons u terms ih =>
      cases hp : contractPair coords t u <;> simp [insertFace, hp, ih]

theorem facePass_length_le {n : ℕ} (coords : List (Fin n × Bool)) (terms : Terms n) :
    (facePass coords terms).length ≤ terms.length := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      simp only [facePass, List.foldr_cons]
      exact (insertFace_length_le coords t _).trans (Nat.add_le_add_right ih 1)

theorem parent_face_contracts {n : ℕ} (c : Cube n) (v : Fin n) (bit : Bool)
    (w : ℤ) (hfree : c v = Finset.univ) :
    facePass [(v, bit)] [(w, c), (-w, restrictFace c v bit)] =
      [(w, restrictFace c v (!bit))] := by
  simp [facePass, insertFace, contractPair, Cancellable, complementaryTerm, hfree]

def sourceCoordinates {n : ℕ} (formula : CNFFormula n) : List (Fin n × Bool) :=
  (SATSource.Shared.sourceVars formula).flatMap fun v => [(v, false), (v, true)]

def faceMarginalRun {n : ℕ} (coords : List (Fin n × Bool)) :
    CNFFormula n → Terms n → Terms n
  | [], terms => terms
  | clause :: rest, terms => faceMarginalRun coords rest
      (retireTerms (retireAfter clause rest)
        (collectTerms (facePass coords (clauseStep clause terms))))

def faceReadout {n : ℕ} (formula : CNFFormula n) : ℤ :=
  termsMass (faceMarginalRun (sourceCoordinates formula) formula [(1, topCube n)])

theorem faceMarginalRun_mass {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (terms : Terms n) :
    termsMass (faceMarginalRun coords formula terms) = formulaMass formula terms := by
  induction formula generalizing terms with
  | nil => rfl
  | cons clause rest ih =>
      rw [faceMarginalRun, ih, retireTerms_preserves _ rest _ (retireAfter_absent clause rest),
        formulaMass_collect, facePass_future]
      rfl

theorem faceReadout_eq_count {n : ℕ} (formula : CNFFormula n) :
    faceReadout formula =
      ((Finset.univ.filter fun x : Assignment n =>
        CNFFormula.eval formula (extendAssignment x) = true).card : ℤ) := by
  rw [faceReadout, faceMarginalRun_mass]
  simp only [formulaMass, termsMass_eq_sum]
  simp only [applyFormula_at]
  simp only [termsAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    indicator_top, mul_one, add_zero, one_mul, Finset.sum_boole]

end SaturationMonoid.ComplexityProjection.SATJoint
