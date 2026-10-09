import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ResourceExecution.Machine

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CPS1AddressedChemicalReaction

/-- An inherited material carries an explicit missing lineage. Raw packets and
paid products are labelled before their consuming event, never after it. -/
inductive Material (S R : Type)
  | inherited (species : S)
  | raw (batch ordinal : Nat) (species : S)
  | product (event ordinal : Nat) (reaction : R) (species : S)
      (consumed : List (Material S R))

def Material.species {S R : Type} : Material S R → S
  | .inherited species | .raw _ _ species | .product _ _ _ species _ => species

def forget {S R : Type} (stock : List (Material S R)) : List S := stock.map Material.species

theorem forget_append {S R : Type} (left right : List (Material S R)) :
    forget (left ++ right) = forget left ++ forget right := List.map_append

def rawPacket {S R : Type} (batch : Nat) (stock : List S) : List (Material S R) :=
  stock.zipIdx.map (fun item => .raw batch item.2 item.1)

theorem raw_packet_forget {S R : Type} (batch : Nat) (stock : List S) :
    forget (rawPacket (R := R) batch stock) = stock := by
  simp only [forget,rawPacket,List.map_map]
  exact List.zipIdx_map_fst 0 stock

variable {S R : Type} [DecidableEq S]

/-- Select the first matching material occurrence, retaining its full lineage. -/
def take? (required : S) (stock : List (Material S R)) : Option (Material S R × List (Material S R)) :=
  List.rec none (fun material rest recur =>
    if material.species = required then some (material,rest)
    else recur.map (fun found => (found.1,material :: found.2))) stock

theorem take_nil (required : S) : take? (R := R) required [] = none := rfl

theorem take_cons (required : S) (material : Material S R) (rest : List (Material S R)) :
    take? required (material :: rest) =
      if material.species = required then some (material,rest)
      else (take? required rest).map (fun found => (found.1,material :: found.2)) := rfl

theorem take_none_iff (required : S) (stock : List (Material S R)) :
    take? required stock = none ↔ required ∉ forget stock := by
  induction stock with
  | nil => simp [take_nil,forget]
  | cons material rest ih =>
    by_cases matched : material.species = required
    · simp [take_cons,matched,forget]
    · simp [take_cons,matched,forget,ih,Ne.symm matched]

theorem take_paid (required : S) (stock : List (Material S R))
    (chosen : Material S R) (remainder : List (Material S R))
    (actual : take? required stock = some (chosen,remainder)) :
    chosen.species = required ∧ forget remainder = (forget stock).erase required ∧
      stock.Perm (chosen :: remainder) := by
  induction stock generalizing chosen remainder with
  | nil => cases actual
  | cons material rest ih =>
    by_cases matched : material.species = required
    · simp only [take_cons,if_pos matched,Option.some.injEq,Prod.mk.injEq] at actual
      rcases actual with ⟨rfl,rfl⟩
      refine ⟨matched,?_,List.Perm.refl _⟩
      simp [forget,matched]
    · simp only [take_cons,if_neg matched] at actual
      cases found : take? required rest with
      | none => simp [found] at actual
      | some pair =>
        rcases pair with ⟨selected,tail⟩
        simp only [found,Option.map_some,Option.some.injEq,Prod.mk.injEq] at actual
        rcases actual with ⟨rfl,rfl⟩
        have paid := ih _ _ found
        refine ⟨paid.1,?_,?_⟩
        · simp only [forget,List.map_cons,List.erase_cons,beq_eq_false_iff_ne.mpr matched]
          exact congrArg (material.species :: ·) paid.2.1
        · exact (paid.2.2.cons material).trans (List.Perm.swap selected material tail)

def reserve? (required : List S) (stock : List (Material S R)) :
    Except S (List (Material S R) × List (Material S R)) :=
  List.rec (motive := fun _ => List (Material S R) →
    Except S (List (Material S R) × List (Material S R)))
    (fun available => .ok ([],available))
    (fun kind _ recur available =>
      match take? kind available with
      | none => .error kind
      | some chosen =>
        match recur chosen.2 with
        | .error missing => .error missing
        | .ok result => .ok (chosen.1 :: result.1,result.2)) required stock

theorem reserve_nil (stock : List (Material S R)) : reserve? [] stock = .ok ([],stock) := rfl

theorem reserve_cons (kind : S) (required : List S) (stock : List (Material S R)) :
    reserve? (kind :: required) stock =
      match take? kind stock with
      | none => .error kind
      | some chosen =>
        match reserve? required chosen.2 with
        | .error missing => .error missing
        | .ok result => .ok (chosen.1 :: result.1,result.2) := rfl

theorem reserve_project (required : List S) (stock : List (Material S R)) :
    (reserve? required stock).map (fun paid => forget paid.2) =
      CPS1ResourceExecution.Inventory.consume required (forget stock) := by
  induction required generalizing stock with
  | nil => rfl
  | cons kind required ih =>
    cases chosen : take? kind stock with
    | none =>
      have absent := (take_none_iff kind stock).mp chosen
      simp only [reserve_cons,chosen,CPS1ResourceExecution.Inventory.consume,if_neg absent,Except.map]
    | some pair =>
      rcases pair with ⟨selected,remainder⟩
      have paid := take_paid kind stock selected remainder chosen
      have present : kind ∈ forget stock := by
        by_contra missing
        have absent := (take_none_iff kind stock).mpr missing
        rw [chosen] at absent
        cases absent
      simp only [reserve_cons,chosen,CPS1ResourceExecution.Inventory.consume,if_pos present]
      rw [← paid.2.1]
      change _ = CPS1ResourceExecution.Inventory.consume required (forget remainder)
      rw [← ih remainder]
      cases reserve? required remainder <;> rfl

theorem reserve_paid (required : List S) (stock consumed remainder : List (Material S R))
    (actual : reserve? required stock = .ok (consumed,remainder)) :
    forget consumed = required ∧ stock.Perm (consumed ++ remainder) := by
  induction required generalizing stock consumed remainder with
  | nil =>
    simp only [reserve_nil,Except.ok.injEq,Prod.mk.injEq] at actual
    rcases actual with ⟨rfl,rfl⟩
    exact ⟨rfl,List.Perm.refl _⟩
  | cons kind required ih =>
    cases chosen : take? kind stock with
    | none => simp [reserve_cons,chosen] at actual
    | some pair =>
      rcases pair with ⟨selected,rest⟩
      have selectedPaid := take_paid kind stock selected rest chosen
      simp only [reserve_cons,chosen] at actual
      cases later : reserve? required rest with
      | error missing => simp [later] at actual
      | ok pair =>
        rcases pair with ⟨tail,leftover⟩
        simp only [later,Except.ok.injEq,Prod.mk.injEq] at actual
        rcases actual with ⟨rfl,rfl⟩
        have tailPaid := ih _ _ _ later
        refine ⟨?_,selectedPaid.2.2.trans (tailPaid.2.cons selected)⟩
        change selected.species :: forget tail = kind :: required
        rw [selectedPaid.1,tailPaid.1]

end CPS1AddressedChemicalReaction
