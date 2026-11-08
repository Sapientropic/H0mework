import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Admission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Request" => Source.Program.Request Party Good Port Technology Instrument
local notation "Current" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument

def material (request : Request) : Flow Party Good :=
  match request.operation with
  | .use bearer goods _ => locate bearer goods
  | _ => []

def required (word : Word) (party : Party) (good : Good) : ℚ :=
  (word.map fun request => flowAt (material request) party good).sum

def IsService (request : Request) : Prop :=
  ∃ bearer goods purpose, request.operation = .use bearer goods purpose ∧ NonnegativeBundle Good goods

def Permitted (law : Law) (current : Current) (request : Request) : Prop :=
  (RawLaw.SignerMatches request ∧ law.operationAllowed current request = true) ∧
    (∀ port ∈ law.requiredPorts current request, law.allowed current.technology port request.signer = true ∨
      law.controller current.technology port ∈ request.consents) ∧ law.ClaimGuard current request

def Every (law : Law) (current : Current) (index : Nat) (word : Word)
    (predicate : Current → Request → Prop) : Prop :=
  ∀ item ∈ (law.execute current index word).items, predicate item.before item.request

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
private theorem service_material_is_original {request : Request} (isService : IsService request)
    (law : Law) (current : Current) :
    law.debit current request = material request ∧ law.credit current request = [] ∧
      NonnegativeBundle (Party × Good) (material request) := by
  obtain ⟨bearer, goods, purpose, operation, nonnegative⟩ := isService
  simp only [RawLaw.debit, RawLaw.credit, material, operation, true_and]
  intro item present
  obtain ⟨source, original, rfl⟩ := List.mem_map.mp present
  exact nonnegative source original

omit [DecidableEq Instrument] in
theorem required_nonnegative (word : Word) (services : ∀ request ∈ word, IsService request)
    (party : Party) (good : Good) : 0 ≤ required word party good := by
  induction word with
  | nil => exact le_rfl
  | cons request tail ih =>
    obtain ⟨bearer, goods, purpose, operation, nonnegative⟩ := services request List.mem_cons_self
    have first : NonnegativeBundle (Party × Good) (material request) := by
      unfold material
      rw [operation]
      intro item present
      obtain ⟨source, original, rfl⟩ := List.mem_map.mp present
      exact nonnegative source original
    exact add_nonneg (amount_nonnegative _ first _) (ih (fun later present =>
      services later (List.mem_cons_of_mem _ present)))

omit [DecidableEq Instrument] in
private theorem valid_of_permission_and_stock (law : Law) (current : Current) (request : Request)
    (service : IsService request) (permission : Permitted law current request)
    (stock : ∀ party good, flowAt (material request) party good ≤ current.stock party good) :
    law.Valid current request := by
  obtain ⟨debit, credit, materialNonnegative⟩ := service_material_is_original service law current
  refine ⟨permission.1, permission.2.1, permission.2.2, ?_, ?_, ?_⟩
  · rwa [debit]
  · simp [credit, NonnegativeBundle]
  · intro item _
    rw [debit]
    exact stock item.1.1 item.1.2

private theorem the_use_pays_its_exact_original_material (law : Law) (current : Current)
    (request : Request) (service : IsService request) (valid : law.Valid current request) (party : Party) (good : Good) :
    (law.step current request).stock party good = current.stock party good - flowAt (material request) party good := by
  obtain ⟨debit, credit, _⟩ := service_material_is_original service law current
  simp [RawLaw.step, valid, RawLaw.paidStep, debit, credit, flowAt, amount]

/-- Every service is a native use of original stock. The joint bound is
one sum per original bearer and good, with no same-word material credit. -/
theorem all_original_services_are_paid_exactly_when_authorized_and_funded
    (law : Law) (current : Current) (index : Nat) (word : Word)
    (services : ∀ request ∈ word, IsService request)
    (hold : Party → Good → ℚ) (holdNonnegative : ∀ party good, 0 ≤ hold party good) :
    (Every law current index word law.Valid ∧
      ∀ party good, hold party good ≤ (law.execute current index word).final.stock party good) ↔
    (Every law current index word (Permitted law) ∧
      ∀ party good, required word party good + hold party good ≤ current.stock party good) := by
  induction word generalizing current index with
  | nil => simp [Every, RawLaw.execute, required]
  | cons request tail previous =>
    let next := law.step current request
    let later := previous next (index + 1) (fun action present => services action (List.mem_cons_of_mem _ present))
    have head := services request List.mem_cons_self
    have stock (valid : law.Valid current request) (party : Party) (good : Good) :
        next.stock party good = current.stock party good - flowAt (material request) party good :=
      the_use_pays_its_exact_original_material law current request head valid party good
    have cost (party : Party) (good : Good) :
        required (request :: tail) party good = flowAt (material request) party good + required tail party good := rfl
    simp only [Every, RawLaw.execute, List.forall_mem_cons]
    change ((law.Valid current request ∧ Every law next (index + 1) tail law.Valid) ∧ _) ↔
      ((Permitted law current request ∧ Every law next (index + 1) tail (Permitted law)) ∧ _)
    constructor
    · rintro ⟨⟨valid, paid⟩, remaining⟩
      obtain ⟨permission, balance⟩ := later.mp ⟨paid, remaining⟩
      refine ⟨⟨⟨valid.1, valid.2.1, valid.2.2.1⟩, permission⟩, fun party good => ?_⟩
      have after := balance party good
      rw [stock valid] at after
      rw [cost]
      linarith only [after]
    · rintro ⟨⟨permission, permissions⟩, balance⟩
      have valid := valid_of_permission_and_stock law current request head permission (fun party good => by
        have funds := balance party good
        rw [cost] at funds
        have nonnegative := required_nonnegative tail
          (fun action present => services action (List.mem_cons_of_mem _ present)) party good
        linarith only [funds, nonnegative, holdNonnegative party good])
      have funded : ∀ party good, required tail party good + hold party good ≤ next.stock party good := by
        intro party good
        have funds := balance party good
        rw [stock valid]
        rw [cost] at funds
        linarith only [funds]
      obtain ⟨paid, remaining⟩ := later.mpr ⟨permissions, funded⟩
      exact ⟨⟨valid, paid⟩, remaining⟩

/-- Once admitted, the literal service word spends exactly its listed uses
and produces no material credit. -/
theorem the_paid_service_word_debits_exactly_its_required_stock
    (law : Law) (current : Current) (index : Nat) (word : Word)
    (services : ∀ request ∈ word, IsService request)
    (paid : Every law current index word law.Valid) (party : Party) (good : Good) :
    (law.execute current index word).final.stock party good = current.stock party good - required word party good := by
  induction word generalizing current index with
  | nil => simp [RawLaw.execute, required]
  | cons request tail previous =>
    have first : law.Valid current request := paid ⟨index, current, request⟩ List.mem_cons_self
    have later : Every law (law.step current request) (index + 1) tail law.Valid := by
      intro item original
      exact paid item (List.mem_cons_of_mem _ original)
    change (law.execute (law.step current request) (index + 1) tail).final.stock party good = _
    rw [previous _ _ (fun action present => services action (List.mem_cons_of_mem _ present)) later,
      the_use_pays_its_exact_original_material law current request (services request List.mem_cons_self) first]
    change current.stock party good - flowAt (material request) party good - required tail party good =
      current.stock party good - (flowAt (material request) party good + required tail party good)
    rw [sub_sub]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
