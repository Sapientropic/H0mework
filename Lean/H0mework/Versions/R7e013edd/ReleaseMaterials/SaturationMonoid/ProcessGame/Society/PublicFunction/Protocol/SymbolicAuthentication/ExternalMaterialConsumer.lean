import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialConsumer
open Institutions.Capitalism.Universal.Source.Program
open ExternalMaterialSource
open Delegation.Funded (Party)
open Repayment.Recovery (Good)

-- Only primitive stocks and the existing production permission enter this mouth.
structure Reserve (current : Current) (count : Nat) : Prop where
  material : ResupplyLaw.Restorable (RecycledQuorumMaterial.material (community current))
  communityFeed : 0 ≤ current.stock (.inl 0) .feedstock
  communityLabor : 1 ≤ current.stock (.inl 0) .labor
  communityEnergy : 0 ≤ current.stock (.inl 0) .energy
  waste : (count : ℚ) ≤ current.stock supplier .waste
  energy : (count : ℚ) ≤ current.stock supplier .energy
  labor : (count : ℚ) ≤ current.stock supplier .labor
  outsideFeed : 0 ≤ current.stock supplier .feedstock

def localBatch (current : Current) (work : Bool) : List RecycledQuorumMaterial.Action :=
  if work = true ∧ RenewedQuorumMaterial.Inputs (community current) then RenewedQuorumMaterial.word else []
def step (current : Current) (supply work : Bool) : Current :=
  let arrived := ExternalMaterialSource.next current supply
  install arrived ((FuelMandateLaw.law true).next (community arrived) (localBatch arrived work))

def expected (current : Current) (count : Nat) : Current := {current with
  stock := fun actor good => current.stock actor good + (if actor = .inl 1 ∧ good = .service then 3 * count else 0) -
    (if actor = supplier ∧ (good = .waste ∨ good = .energy ∨ good = .labor) then count else 0)
  clock := current.clock + 2 * count
  round := current.round + 2 * count}

theorem boundary_inputs (current : Current) (count : Nat) (reserve : Reserve current (count+1)) :
    ExternalMaterialSource.Inputs current := by
  have positive : (1 : ℚ) ≤ (count+1 : Nat) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le count)
  exact ⟨positive.trans reserve.waste,positive.trans reserve.energy,positive.trans reserve.labor,
    reserve.outsideFeed,reserve.material.willing⟩

set_option linter.unusedSimpArgs false in
theorem the_actual_boundary_generates_the_original_production_inputs (current : Current) (count : Nat)
    (reserve : Reserve current (count+1)) : RenewedQuorumMaterial.Inputs (community (ExternalMaterialSource.next current true)) := by
  rw [ExternalMaterialSource.actual_next current (boundary_inputs current count reserve)]
  obtain ⟨material,feed,labor,energy,_,_,_,_⟩ := reserve
  obtain ⟨pf,wf,ww,willing,waste,pe,pl,we,wl⟩ := material
  constructor
  · constructor <;> simp_all [community,ExternalMaterialSource.expected,RecycledQuorumMaterial.material,supplier,recipient]
  · simp [community,ExternalMaterialSource.expected,recipient,supplier];linarith
  · simpa [community,ExternalMaterialSource.expected,recipient,supplier] using labor
  · simpa [community,ExternalMaterialSource.expected,recipient,supplier] using energy

set_option linter.unusedSimpArgs false in
theorem actual_cycle (current : Current) (count : Nat) (reserve : Reserve current (count+1)) :
    step current true true = expected current 1 ∧
      localBatch (ExternalMaterialSource.next current true) true = RenewedQuorumMaterial.word ∧
      (∀ item ∈ ExternalMaterialSource.law.rawItems current ExternalMaterialSource.word,
        ExternalMaterialSource.law.Valid item.before item.request) ∧
      (∀ item ∈ (FuelMandateLaw.law true).rawItems (community (ExternalMaterialSource.next current true)) RenewedQuorumMaterial.word,
        (FuelMandateLaw.law true).Valid item.before item.request) := by
  have original := the_actual_boundary_generates_the_original_production_inputs current count reserve
  have chosen : localBatch (ExternalMaterialSource.next current true) true = RenewedQuorumMaterial.word :=
    if_pos ⟨rfl,original⟩
  have paid := FuelMandateLaw.original_material_recovery_is_preserved true _ original
  refine ⟨?_,chosen,ExternalMaterialSource.actual_items current (boundary_inputs current count reserve),paid.2⟩
  dsimp only [step]
  rw [chosen,paid.1,ExternalMaterialSource.actual_next current (boundary_inputs current count reserve)]
  apply RawCurrent.ext
  · funext actor good
    cases actor with
    | inl party => fin_cases party <;> cases good <;>
        simp [install,community,RenewedQuorumMaterial.successor,ExternalMaterialSource.expected,expected,supplier,recipient]
    | inr outside => cases outside;cases good <;>
        simp [install,ExternalMaterialSource.expected,expected,supplier,recipient]
  · funext instrument debtor creditor
    cases debtor <;> cases creditor <;> rfl
  · rfl
  · simp [install,community,RenewedQuorumMaterial.successor,ExternalMaterialSource.expected,expected];ring
  · simp [install,community,RenewedQuorumMaterial.successor,ExternalMaterialSource.expected,expected]

set_option linter.unusedSimpArgs false in
theorem next_reserve (current : Current) (count : Nat) (reserve : Reserve current (count+1)) :
    Reserve (step current true true) count := by
  rw [(actual_cycle current count reserve).1]
  obtain ⟨material,feed,labor,energy,waste,externalEnergy,externalLabor,externalFeed⟩ := reserve
  obtain ⟨pf,wf,ww,willing,oldWaste,pe,pl,we,wl⟩ := material
  constructor
  · constructor <;> simp_all [expected,community,RecycledQuorumMaterial.material,supplier]
  · simpa [expected,supplier] using feed
  · simpa [expected,supplier] using labor
  · simpa [expected,supplier] using energy
  · simp [expected,supplier,Nat.cast_add,Nat.cast_one] at waste ⊢;linarith
  · simp [expected,supplier,Nat.cast_add,Nat.cast_one] at externalEnergy ⊢;linarith
  · simp [expected,supplier,Nat.cast_add,Nat.cast_one] at externalLabor ⊢;linarith
  · simpa [expected,supplier] using externalFeed

def run (initial : Current) (count : Nat) : Current :=
  Nat.rec (fun state : Current => state) (fun _ prior state => prior (step state true true)) count initial

set_option linter.unusedSimpArgs false in
theorem the_actual_upstream_stock_generates_every_funded_cycle (current : Current) (count : Nat)
    (reserve : Reserve current count) : run current count = expected current count := by
  induction count generalizing current with
  | zero =>
    apply RawCurrent.ext
    · funext actor good;simp [run,expected]
    all_goals simp [run,expected]
  | succ count ih =>
    change run (step current true true) count = _
    rw [ih _ (next_reserve current count reserve),(actual_cycle current count reserve).1]
    apply RawCurrent.ext
    · funext actor good
      by_cases service : actor = .inl 1 ∧ good = .service <;>
        by_cases debit : actor = supplier ∧ (good = .waste ∨ good = .energy ∨ good = .labor) <;>
        simp [expected,service,debit,Nat.cast_add,Nat.cast_one] <;> ring
    · rfl
    · rfl
    · simp [expected,Nat.cast_add,Nat.cast_one];ring
    · simp [expected];omega

def capacity (current : Current) : Nat :=
  min ⌊current.stock supplier .waste⌋₊ (min ⌊current.stock supplier .energy⌋₊ ⌊current.stock supplier .labor⌋₊)

theorem the_source_generates_its_full_funded_reproduction_capacity (current : Current)
    (reserve : Reserve current 0) : run current (capacity current) = expected current (capacity current) := by
  apply the_actual_upstream_stock_generates_every_funded_cycle
  refine ⟨reserve.material,reserve.communityFeed,reserve.communityLabor,reserve.communityEnergy,?_,?_,?_,reserve.outsideFeed⟩
  · apply le_trans _ (Nat.floor_le reserve.waste)
    exact_mod_cast (Nat.min_le_left ⌊current.stock supplier .waste⌋₊ _)
  · apply le_trans _ (Nat.floor_le reserve.energy)
    exact_mod_cast (Nat.min_le_right ⌊current.stock supplier .waste⌋₊ _).trans (Nat.min_le_left ⌊current.stock supplier .energy⌋₊ _)
  · apply le_trans _ (Nat.floor_le reserve.labor)
    exact_mod_cast (Nat.min_le_right ⌊current.stock supplier .waste⌋₊ _).trans (Nat.min_le_right ⌊current.stock supplier .energy⌋₊ _)

def outsidePotential (current : Current) : ℚ := 6 * current.stock supplier .feedstock +
  2 * current.stock supplier .service + 3 * current.stock supplier .waste + 3 * current.stock supplier .energy

theorem actual_material_gain_is_paid_by_the_same_upstream_occurrences (current : Current) (count : Nat)
    (reserve : Reserve current count) :
    NativeMaterialPotentialSource.potential (community (run current count)) =
        NativeMaterialPotentialSource.potential (community current) + 6 * count ∧
      outsidePotential (run current count) + 6 * count = outsidePotential current := by
  rw [the_actual_upstream_stock_generates_every_funded_cycle current count reserve]
  constructor
  · simp [NativeMaterialPotentialSource.potential,NativeMaterialPotentialSource.total,community,expected,supplier]
    ring
  · simp [outsidePotential,expected,supplier]
    ring

theorem every_actual_cycle_preserves_the_entire_original_claim_matrix (current : Current) (supply work : Bool) :
    (community (step current supply work)).claims = (community current).claims := by
  dsimp only [step]
  rw [project_install]
  unfold localBatch
  split
  · rename_i paid
    rw [(FuelMandateLaw.original_material_recovery_is_preserved true _ paid.2).1]
    exact congrArg (fun claims => fun instrument debtor creditor => claims instrument (.inl debtor) (.inl creditor))
      (every_attempt_preserves_the_whole_claim_matrix current supply)
  · exact congrArg (fun claims => fun instrument debtor creditor => claims instrument (.inl debtor) (.inl creditor))
      (every_attempt_preserves_the_whole_claim_matrix current supply)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialConsumer
