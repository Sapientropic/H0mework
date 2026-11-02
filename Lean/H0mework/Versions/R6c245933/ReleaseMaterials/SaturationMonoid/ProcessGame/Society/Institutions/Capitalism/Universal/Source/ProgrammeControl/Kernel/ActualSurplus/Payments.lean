import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Discovery
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Costs.Vector

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Payments

open Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

def paymentIndex (witness : Witness law current word) : Option Nat :=
  match witness.evidence with
  | .financialReturn path => some path.payment.val.index
  | _ => none

/-- Mark the original payment, rather than summing relationship witnesses.
Several checked access/claim explanations may refer to the same cash flow. -/
def markedBy (witnesses : List (Witness law current word)) (position : OriginalItem law current word) : Bool :=
  witnesses.any fun witness => paymentIndex law current word witness == some position.val.index

/-- Scan the checked financial compiler image independently of the first successful
appropriation explanation. A consumption or retention witness cannot hide a later return. -/
def financialWitnesses : List (Witness law current word) :=
  (Discovery.accesses law current word).flatMap fun access =>
    (Financial.returnPaths law current word).flatMap fun path =>
      (Discovery.reciprocities law current word access).flatMap fun reciprocity =>
        (Discovery.disposals law current word access).filterMap fun disposal =>
          compileProposal law current word ⟨access, reciprocity, disposal⟩ (.financialReturn path)

theorem financialWitnesses_exact (witness : Witness law current word) :
    witness ∈ financialWitnesses law current word ↔
      ∃ access ∈ Discovery.accesses law current word,
        ∃ path ∈ Financial.returnPaths law current word,
          ∃ reciprocity ∈ Discovery.reciprocities law current word access,
            ∃ disposal ∈ Discovery.disposals law current word access,
              compileProposal law current word ⟨access, reciprocity, disposal⟩ (.financialReturn path) = some witness := by
  simp only [financialWitnesses, List.mem_flatMap, List.mem_filterMap]

def marked := markedBy law current word (financialWitnesses law current word)

def positions : List (OriginalItem law current word) :=
  (law.rawItems current word).attach.filter (marked law current word)

omit [DecidableEq Port] in
theorem markedBy_sound (witnesses : List (Witness law current word)) (position : OriginalItem law current word)
    (selected : markedBy law current word witnesses position = true) :
    ∃ witness ∈ witnesses, ∃ path : Financial.ReturnPath law current word,
      witness.evidence = .financialReturn path ∧ path.payment = position ∧
      Financial.ReturnPath.Checks law current word witness.dependency.proposal.access path ∧
      witness.dependency.financialOrigin law current word = some (path.claimOrigin law current word) := by
  obtain ⟨witness, member, found⟩ := List.any_eq_true.mp selected
  have key : paymentIndex law current word witness = some position.val.index := beq_iff_eq.mp found
  cases evidence : witness.evidence with
  | financialReturn path =>
      simp only [paymentIndex, evidence] at key
      have same : path.payment = position := Financial.original_index_injective law current word (Option.some.inj key)
      have checked := witness.checked.2.2.1
      simp only [evidence, evidenceChecks] at checked
      have aligned := witness.checked.2.2.2
      simp only [evidence, financialAlignment] at aligned
      exact ⟨witness, member, path, evidence, same, checked,
        Financial.ReturnPath.aligned_is_exact_original_claim law current word path _ aligned⟩
  | _ => simp only [paymentIndex, evidence, reduceCtorEq] at key

theorem selected_has_its_original_checked_payment (position : OriginalItem law current word)
    (selected : position ∈ positions law current word) :
    ∃ witness ∈ financialWitnesses law current word, ∃ path : Financial.ReturnPath law current word,
      witness.evidence = .financialReturn path ∧ path.payment = position ∧
      Financial.ReturnPath.Checks law current word witness.dependency.proposal.access path ∧
      witness.dependency.financialOrigin law current word = some (path.claimOrigin law current word) :=
  markedBy_sound law current word _ position (List.mem_filter.mp selected).2

theorem selected_is_a_real_accepted_settlement (position : OriginalItem law current word)
    (selected : position ∈ positions law current word) :
    law.Valid position.val.before position.val.request ∧
    ∃ instrument debtor creditor quantity,
      position.val.request.operation = .settle instrument debtor creditor quantity ∧ 0 < quantity := by
  obtain ⟨witness, _, path, _, same, checked, _⟩ := selected_has_its_original_checked_payment law current word position selected
  have actual := Financial.ReturnPath.actual_financial_return_has_original_payment law current word
    witness.dependency.proposal.access path checked
  rw [same] at actual
  obtain ⟨accepted, instrument, debtor, quantity, operation, positive, _⟩ := actual
  exact ⟨accepted, instrument, debtor, _, quantity, operation, positive⟩

omit [DecidableEq Port] in
theorem duplicate_evidence_does_not_duplicate_a_payment
    (witnesses : List (Witness law current word)) (position : OriginalItem law current word) :
    markedBy law current word (witnesses ++ witnesses) position = markedBy law current word witnesses position := by
  simp only [markedBy, List.any_append, Bool.or_self]

omit [DecidableEq Port] in
private theorem execution_indices (start : Nat) :
    ((law.execute current start word).items.map ExecutionItem.index) = List.range' start word.length := by
  induction word generalizing current start with
  | nil => rfl
  | cons request tail ih =>
      simpa only [RawLaw.execute, List.map_cons, List.length_cons, List.range'_succ] using
        congrArg (List.cons start) (ih (law.step current request) (start + 1))

theorem positions_have_distinct_original_indices :
    ((positions law current word).map (fun position => position.val.index)).Nodup := by
  have all : ((law.rawItems current word).attach.map (fun position => position.val.index)).Nodup := by
    have same : (law.rawItems current word).attach.map (fun position => position.val.index) =
        (law.rawItems current word).map ExecutionItem.index := by simp only [List.attach_map_val]
    rw [same, RawLaw.rawItems, execution_indices]
    exact List.nodup_range'
  exact all.sublist ((List.filter_sublist (p := marked law current word) (l := (law.rawItems current word).attach)).map (fun position => position.val.index))

private def rawFlow (credit : Bool) (item : ExecutionItem Party Good Port Technology Instrument) (party : Party) (good : Good) : ℚ :=
  match item.request.operation with
  | .settle .. => flowAt (if credit then law.actualCredit item.before item.request else
      law.actualDebit item.before item.request) party good
  | _ => 0

def flow (credit : Bool) (position : OriginalItem law current word) (party : Party) (good : Good) : ℚ :=
  rawFlow law credit position.val party good

def settlementTotal (credit : Bool) (party : Party) (good : Good) : ℚ :=
  ((law.rawItems current word).attach.map (fun position => flow law current word credit position party good)).sum

def amountBy (witnesses : List (Witness law current word)) (selected credit : Bool) (party : Party) (good : Good) : ℚ :=
  ((law.rawItems current word).attach.map fun position =>
    if markedBy law current word witnesses position = selected then flow law current word credit position party good else 0).sum

def amount := amountBy law current word (financialWitnesses law current word)

omit [DecidableEq Port] in
theorem duplicate_evidence_does_not_change_the_billing
    (witnesses : List (Witness law current word)) (selected credit : Bool) (party : Party) (good : Good) :
    amountBy law current word (witnesses ++ witnesses) selected credit party good =
      amountBy law current word witnesses selected credit party good := by
  simp only [amountBy, duplicate_evidence_does_not_duplicate_a_payment]

theorem exact_partition (credit : Bool) (party : Party) (good : Good) :
    amount law current word true credit party good + amount law current word false credit party good =
      settlementTotal law current word credit party good := by
  unfold amount amountBy
  have join (entries : List (OriginalItem law current word)) :
      (entries.map (fun position => if marked law current word position = true then flow law current word credit position party good else 0)).sum +
        (entries.map (fun position => if marked law current word position = false then flow law current word credit position party good else 0)).sum =
      (entries.map (fun position => flow law current word credit position party good)).sum := by
    induction entries with
    | nil => simp only [List.map_nil, List.sum_nil, add_zero]
    | cons position rest ih =>
        simp only [List.map_cons, List.sum_cons]
        have head : (if marked law current word position = true then flow law current word credit position party good else 0) +
            (if marked law current word position = false then flow law current word credit position party good else 0) =
          flow law current word credit position party good := by cases marked law current word position <;> simp
        linarith
  change _ + _ = _
  rw [show markedBy law current word (financialWitnesses law current word) = marked law current word from rfl]
  rw [join]
  rfl

theorem amount_nonnegative (selected credit : Bool) (party : Party) (good : Good) :
    0 ≤ amount law current word selected credit party good := by
  unfold amount amountBy
  apply List.sum_nonneg
  intro value inside
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp inside
  split
  · unfold flow rawFlow
    split
    · by_cases accepted : law.Valid position.val.before position.val.request
      · cases credit <;>
          simp only [Bool.false_eq_true, ↓reduceIte, RawLaw.actualDebit, RawLaw.actualCredit, if_pos accepted, flowAt]
        · exact Program.amount_nonnegative (law.debit position.val.before position.val.request) accepted.2.2.2.1 (party, good)
        · exact Program.amount_nonnegative (law.credit position.val.before position.val.request) accepted.2.2.2.2.1 (party, good)
      · cases credit <;> simp [RawLaw.actualDebit, RawLaw.actualCredit, accepted, flowAt, Program.amount]
    · exact le_rfl
  · exact le_rfl

theorem selected_bounded_by_actual_settlements (credit : Bool) (party : Party) (good : Good) :
    amount law current word true credit party good ≤ settlementTotal law current word credit party good := by
  have part := exact_partition law current word credit party good
  have positive := amount_nonnegative law current word false credit party good
  linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Payments
