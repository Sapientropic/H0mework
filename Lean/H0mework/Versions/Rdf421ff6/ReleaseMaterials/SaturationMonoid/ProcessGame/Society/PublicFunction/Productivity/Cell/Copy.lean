import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Domain

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell

open Institutions.Capitalism.Universal.Source.Program

private theorem audit_valid (current : Current) (parent : Party)
    (labor : 1 ≤ current.stock parent .labor) : law.Valid current (audit parent) := by
  simpa [audit, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    law, NonnegativeBundle, locate, flowAt, amount] using labor

structure CopyResources (current : Current) (parent child : Party) : Prop where
  technology : current.technology = (true, true)
  distinct : parent ≠ child
  ordinary : child ≠ 3
  seed : 2 ≤ current.stock parent .seed
  feed : 8 ≤ current.stock parent .feed
  energy : 1 ≤ current.stock parent .energy
  labor : 2 ≤ current.stock parent .labor
  life : 2 ≤ current.stock parent .life
  spare : 2 ≤ current.stock parent .spare
  child_stock : ∀ good, 0 ≤ current.stock child good

def copyKit : Bundle Good :=
  [(.seed, 1), (.feed, 8), (.energy, 1), (.labor, 1), (.life, 1), (.spare, 1)]

private theorem kit_valid (current : Current) (parent child : Party)
    (seed : 1 ≤ current.stock parent .seed) (feed : 8 ≤ current.stock parent .feed)
    (energy : 1 ≤ current.stock parent .energy) (labor : 1 ≤ current.stock parent .labor)
    (life : 1 ≤ current.stock parent .life) (spare : 1 ≤ current.stock parent .spare) :
    law.Valid current (transfer parent parent child copyKit) := by
  simp [transfer, copyKit, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    law, NonnegativeBundle, locate, flowAt, amount, seed, feed, energy, labor, life, spare]

private theorem production_valid (current : Current) (child : Party)
    (ordinary : child ≠ 3)
    (technology : current.technology = (true, true))
    (seed : 1 ≤ current.stock child .seed) (feed : 8 ≤ current.stock child .feed)
    (energy : 1 ≤ current.stock child .energy) (labor : 1 ≤ current.stock child .labor) :
    law.Valid current (production child) := by
  simp [production, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    law, ordinary, technology, NonnegativeBundle, locate, flowAt, amount, seed, feed, energy, labor]

private theorem necessity_valid (current : Current) (child : Party) (ordinary : child ≠ 3)
    (life : 1 ≤ current.stock child .life) : law.Valid current (necessity child) := by
  simp [necessity, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    law, ordinary, NonnegativeBundle, locate, flowAt, amount, life]

private theorem maintenance_valid (current : Current) (child : Party) (ordinary : child ≠ 3)
    (spare : 1 ≤ current.stock child .spare) : law.Valid current (maintenance child) := by
  simp [maintenance, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    law, ordinary, NonnegativeBundle, locate, flowAt, amount, spare]

structure CopyEffect (current : Current) (parent child : Party) : Prop where
  accepted : ∀ item ∈ law.rawItems current (copy parent child), law.Valid item.before item.request
  child_seed : (law.next current (copy parent child)).stock child .seed = current.stock child .seed + 3
  child_life : (law.next current (copy parent child)).stock child .life = current.stock child .life + 5
  child_spare : (law.next current (copy parent child)).stock child .spare = current.stock child .spare + 1
  parent_seed : (law.next current (copy parent child)).stock parent .seed = current.stock parent .seed - 1
  parent_feed : (law.next current (copy parent child)).stock parent .feed = current.stock parent .feed - 8
  parent_energy : (law.next current (copy parent child)).stock parent .energy = current.stock parent .energy - 1
  parent_labor : (law.next current (copy parent child)).stock parent .labor = current.stock parent .labor - 2
  parent_life : (law.next current (copy parent child)).stock parent .life = current.stock parent .life - 1
  parent_spare : (law.next current (copy parent child)).stock parent .spare = current.stock parent .spare - 1

theorem resources_generate_legal_copy (current : Current) (parent child : Party)
    (resources : CopyResources current parent child) : CopyEffect current parent child := by
  let a := law.paidStep current (audit parent)
  let b := law.paidStep a (transfer parent parent child copyKit)
  let c := law.paidStep b (production child)
  let d := law.paidStep c (necessity child)
  have va : law.Valid current (audit parent) := audit_valid current parent (by linarith [resources.labor])
  have vb : law.Valid a (transfer parent parent child copyKit) := by
    apply kit_valid
    all_goals simp [a, RawLaw.paidStep, RawLaw.debit, RawLaw.credit, audit, locate, flowAt, amount]
    all_goals linarith [resources.seed, resources.feed, resources.energy, resources.labor, resources.life, resources.spare]
  have vc : law.Valid b (production child) := by
    apply production_valid _ _ resources.ordinary
    · exact resources.technology
    all_goals simp [b, a, RawLaw.paidStep, RawLaw.debit, RawLaw.credit, audit, transfer,
      copyKit, locate, flowAt, amount, resources.distinct]
    all_goals linarith [resources.child_stock .seed, resources.child_stock .feed,
      resources.child_stock .energy, resources.child_stock .labor]
  have vd : law.Valid c (necessity child) := by
    apply necessity_valid c child resources.ordinary
    simp [c, b, a, RawLaw.paidStep, RawLaw.debit, RawLaw.credit, audit, transfer,
      production, copyKit, law, resources.technology, locate, flowAt, amount,
      resources.distinct, resources.ordinary]
    linarith [resources.child_stock .life]
  have ve : law.Valid d (maintenance child) := by
    apply maintenance_valid d child resources.ordinary
    simp [d, c, b, a, RawLaw.paidStep, RawLaw.debit, RawLaw.credit, audit, transfer,
      production, necessity, copyKit, law, resources.technology, locate, flowAt, amount,
      resources.distinct, resources.ordinary]
    linarith [resources.child_stock .spare]
  have steps :
      law.step current (audit parent) = a ∧
      law.step a (transfer parent parent child copyKit) = b ∧
      law.step b (production child) = c ∧
      law.step c (necessity child) = d ∧
      law.step d (maintenance child) = law.paidStep d (maintenance child) := by
    simp only [RawLaw.step, if_pos va, if_pos vb, if_pos vc, if_pos vd, if_pos ve, a, b, c, d,
      and_self]
  have execution : law.execute current 0 (copy parent child) =
      ⟨law.paidStep d (maintenance child),
        [⟨0, current, audit parent⟩, ⟨1, a, transfer parent parent child copyKit⟩,
          ⟨2, b, production child⟩, ⟨3, c, necessity child⟩, ⟨4, d, maintenance child⟩]⟩ := by
    change law.execute current 0 [audit parent, transfer parent parent child copyKit,
      production child, necessity child, maintenance child] = _
    simp only [RawLaw.execute, steps.1, steps.2.1, steps.2.2.1, steps.2.2.2.1, steps.2.2.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RawLaw.rawItems, execution, List.mem_cons, List.not_mem_nil, or_false]
    intro item inside
    rcases inside with rfl | rfl | rfl | rfl | rfl
    · exact va
    · exact vb
    · exact vc
    · exact vd
    · exact ve
  all_goals
    have different := resources.distinct
    have symmetric := Ne.symm resources.distinct
    have technology := resources.technology
    have ordinary := resources.ordinary
    change (law.execute current 0 (copy parent child)).final.stock _ _ = _
    rw [execution]
    simp_all [d, c, b, a, RawLaw.paidStep, RawLaw.debit, RawLaw.credit,
      audit, transfer, production, necessity, maintenance, copyKit, law, locate, flowAt, amount]
    <;> ring

def copyFrom (current : Current) (parent child : Party) :=
  IncomingWord.check law current (copy parent child)

theorem physical_resources_generate_the_copy_request (current : Current) (parent child : Party)
    (resources : CopyResources current parent child) :
    ∃ admitted, copyFrom current parent child = some admitted ∧
      admitted.word = copy parent child := by
  have accepted := (resources_generate_legal_copy current parent child resources).accepted
  unfold copyFrom IncomingWord.check
  rw [dif_pos (by simp [copy]), dif_pos accepted]
  exact ⟨_, rfl, rfl⟩

theorem copy_preserves_every_financial_position (current : Current) (parent child : Party)
    (resources : CopyResources current parent child) :
    (law.next current (copy parent child)).claims = current.claims := by
  funext code debtor creditor
  have account := law.accepted_next_financial_balance current (copy parent child)
    (resources_generate_legal_copy current parent child resources).accepted code debtor creditor
  simpa [copy, firstCycle, audit, transfer, production, necessity, maintenance, RawLaw.claimDelta] using account

inductive CopyAttempt (current : Current) (parent child : Party)
  | paid (accepted : ∀ item ∈ law.rawItems current (copy parent child), law.Valid item.before item.request)
  | blocked (item : ExecutionItem Party Good Port Technology Unit)
      (original : item ∈ law.rawItems current (copy parent child))
      (refused : ¬ law.Valid item.before item.request)

def attemptCopy (current : Current) (parent child : Party) : CopyAttempt current parent child :=
  match found : (law.rawItems current (copy parent child)).find?
      (fun item => decide (¬ law.Valid item.before item.request)) with
  | some item => .blocked item (List.mem_of_find?_eq_some found)
      (by simpa only [decide_eq_true_eq] using List.find?_some found)
  | none => .paid (by
      intro item inside
      have checked := (List.find?_eq_none.mp found) item inside
      simpa only [decide_eq_true_eq, not_not] using checked)

def CopyAttempt.word {current : Current} {parent child : Party} :
    CopyAttempt current parent child → RawEvent Party Good Port Technology Unit
  | .paid _ => copy parent child
  | .blocked .. => []

def CopyAttempt.isPaid {current : Current} {parent child : Party} : CopyAttempt current parent child → Bool
  | .paid _ => true
  | .blocked .. => false

theorem resources_generate_paid_attempt (current : Current) (parent child : Party)
    (resources : CopyResources current parent child) : (attemptCopy current parent child).isPaid = true := by
  have accepted := (resources_generate_legal_copy current parent child resources).accepted
  unfold attemptCopy
  split
  next item found =>
    have refused : ¬ law.Valid item.before item.request := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    exact False.elim (refused (accepted item (List.mem_of_find?_eq_some found)))
  next => rfl

theorem every_attempt_emits_only_legal_operations (current : Current) (parent child : Party) :
    ∀ item ∈ law.rawItems current (attemptCopy current parent child).word,
      law.Valid item.before item.request := by
  cases attemptCopy current parent child with
  | paid accepted => exact accepted
  | blocked item original refused => simp [CopyAttempt.word, RawLaw.rawItems, RawLaw.execute]

theorem every_attempt_preserves_old_financial_positions (current : Current) (parent child : Party) :
    (law.next current (attemptCopy current parent child).word).claims = current.claims := by
  cases attemptCopy current parent child with
  | paid accepted =>
      funext code debtor creditor
      have account := law.accepted_next_financial_balance current (copy parent child)
        accepted code debtor creditor
      simpa [CopyAttempt.word, copy, firstCycle, audit, transfer, production, necessity,
        maintenance, RawLaw.claimDelta] using account
  | blocked item original refused => rfl

theorem resource_generated_copy_pays_child_services (current : Current) (parent child : Party)
    (resources : CopyResources current parent child) :
    Institutions.Capitalism.Universal.Exit.Necessity.AllNeedsPaid law current [child] (copy parent child) := by
  have accepted := (resources_generate_legal_copy current parent child resources).accepted
  have present (request : RequestAt) (inside : request ∈ copy parent child) :
      ∃ item ∈ law.rawItems current (copy parent child), item.request = request := by
    apply List.mem_map.mp
    rw [RawLaw.rawItems, RawLaw.inventory_requests_exact]
    exact inside
  intro actor inside
  have same : actor = child := by simpa only [List.mem_singleton] using inside
  subst actor
  constructor
  · right
    obtain ⟨item, member, sameRequest⟩ := present (necessity child) (by simp [copy, firstCycle])
    refine ⟨item, member, accepted item member, ?_⟩
    simp [Institutions.Capitalism.Universal.Exit.Necessity.UseMatches, sameRequest, necessity,
      law, resources.ordinary]
  · right
    obtain ⟨item, member, sameRequest⟩ := present (maintenance child) (by simp [copy, firstCycle])
    refine ⟨item, member, accepted item member, ?_⟩
    simp [Institutions.Capitalism.Universal.Exit.Necessity.UseMatches, sameRequest, maintenance,
      law, resources.ordinary]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
