import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

theorem amount_nonnegative {Key : Type u} [DecidableEq Key] (bundle : Bundle Key)
    (nonnegative : NonnegativeBundle Key bundle) (key : Key) : 0 ≤ amount Key bundle key := by
  induction bundle with
  | nil => simp [amount]
  | cons item tail ih =>
      have first := nonnegative item List.mem_cons_self
      have later := ih (fun entry member => nonnegative entry (List.mem_cons_of_mem _ member))
      simp only [amount, List.map_cons, List.sum_cons]
      split_ifs <;> exact add_nonneg (by first | exact first | exact le_refl _) later

theorem amount_zero_of_absent {Key : Type u} [DecidableEq Key] (bundle : Bundle Key) (key : Key)
    (absent : ∀ item ∈ bundle, item.1 ≠ key) : amount Key bundle key = 0 := by
  induction bundle with
  | nil => simp [amount]
  | cons item tail ih =>
      have first := absent item List.mem_cons_self
      have later := ih (fun entry member => absent entry (List.mem_cons_of_mem _ member))
      simpa only [amount, List.map_cons, List.sum_cons, if_neg first, zero_add] using later

namespace RawLaw

variable (law : RawLaw Party Good Port Technology Instrument)

omit [DecidableEq Instrument] in
theorem debit_affordable (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (nonnegative : ∀ party good, 0 ≤ current.stock party good)
    (accepted : law.Valid current request) (party : Party) (good : Good) :
    flowAt (law.debit current request) party good ≤ current.stock party good := by
  by_cases member : ∃ item ∈ law.debit current request, item.1 = (party, good)
  · obtain ⟨⟨⟨p, g⟩, quantity⟩, inside, equal⟩ := member
    simp only [Prod.mk.injEq] at equal
    rcases equal with ⟨rfl, rfl⟩
    exact accepted.2.2.2.2.2 _ inside
  · have zero : flowAt (law.debit current request) party good = 0 := by
      apply amount_zero_of_absent
      intro item inside equal
      exact member ⟨item, inside, equal⟩
    rw [zero]
    exact nonnegative party good

theorem step_stock_nonnegative (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (nonnegative : ∀ party good, 0 ≤ current.stock party good) :
    ∀ party good, 0 ≤ (law.step current request).stock party good := by
  intro party good
  by_cases accepted : law.Valid current request
  · have debited := law.debit_affordable current request nonnegative accepted party good
    have supplied := amount_nonnegative (law.credit current request)
      accepted.2.2.2.2.1 (party, good)
    simp only [step, if_pos accepted, paidStep]
    exact add_nonneg (sub_nonneg.mpr debited) supplied
  · rw [law.rejected_preserves_current current request accepted]
    exact nonnegative party good

theorem nextClaims_nonnegative (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (nonnegative : ∀ code debtor creditor, 0 ≤ current.claims code debtor creditor)
    (accepted : law.Valid current request) :
    ∀ code debtor creditor, 0 ≤ nextClaims current request code debtor creditor := by
  intro code debtor creditor
  have base := nonnegative code debtor creditor
  have guard := accepted.2.2.1
  cases kind : request.operation with
  | issue instrument issuer beneficiary quantity =>
      simp only [ClaimGuard, kind] at guard
      simp only [nextClaims, kind]
      apply add_nonneg base
      split_ifs <;> first | exact guard | exact le_refl _
  | assign instrument issuer sender recipient quantity =>
      simp only [ClaimGuard, kind] at guard
      simp only [nextClaims, kind]
      have paid : (if (code, debtor, creditor) = (instrument, issuer, sender) then quantity else 0) ≤
          current.claims code debtor creditor := by
        split_ifs with equal
        · simp only [Prod.mk.injEq] at equal
          rcases equal with ⟨rfl, rfl, rfl⟩
          exact guard.2
        · exact base
      have supplied : 0 ≤
          (if (code, debtor, creditor) = (instrument, issuer, recipient) then quantity else 0) := by
        split_ifs <;> first | exact guard.1 | exact le_refl _
      exact add_nonneg (sub_nonneg.mpr paid) supplied
  | settle instrument originalDebtor originalCreditor quantity =>
      simp only [ClaimGuard, kind] at guard
      simp only [nextClaims, kind]
      apply sub_nonneg.mpr
      split_ifs with equal
      · simp only [Prod.mk.injEq] at equal
        rcases equal with ⟨rfl, rfl, rfl⟩
        exact guard.2.1
      · exact base
  | produce _ | transfer _ _ _ | use _ _ _ | revise _ _ | present =>
      simpa only [nextClaims, kind] using base

theorem step_claims_nonnegative (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (nonnegative : ∀ code debtor creditor, 0 ≤ current.claims code debtor creditor) :
    ∀ code debtor creditor, 0 ≤ (law.step current request).claims code debtor creditor := by
  by_cases accepted : law.Valid current request
  · simp only [step, if_pos accepted, paidStep]
    exact law.nextClaims_nonnegative current request nonnegative accepted
  · rw [law.rejected_preserves_current current request accepted]
    exact nonnegative

theorem execute_nonnegative (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument)
    (material : ∀ party good, 0 ≤ current.stock party good)
    (financial : ∀ code debtor creditor, 0 ≤ current.claims code debtor creditor) :
    (∀ party good, 0 ≤ (law.execute current index event).final.stock party good) ∧
      (∀ code debtor creditor, 0 ≤ (law.execute current index event).final.claims code debtor creditor) := by
  induction event generalizing current index with
  | nil => exact ⟨material, financial⟩
  | cons request tail ih =>
      exact ih (law.step current request) (index + 1)
        (law.step_stock_nonnegative current request material)
        (law.step_claims_nonnegative current request financial)

theorem next_nonnegative (current : RawCurrent Party Good Technology Instrument)
    (event : RawEvent Party Good Port Technology Instrument)
    (material : ∀ party good, 0 ≤ current.stock party good)
    (financial : ∀ code debtor creditor, 0 ≤ current.claims code debtor creditor) :
    (∀ party good, 0 ≤ (law.next current event).stock party good) ∧
      (∀ code debtor creditor, 0 ≤ (law.next current event).claims code debtor creditor) :=
  law.execute_nonnegative current 0 event material financial

end RawLaw

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
