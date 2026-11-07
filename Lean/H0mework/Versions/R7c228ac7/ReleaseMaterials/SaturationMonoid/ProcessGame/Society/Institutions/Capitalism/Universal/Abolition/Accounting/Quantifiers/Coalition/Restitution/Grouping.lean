import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.Vector

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

noncomputable section

variable {Key Entry Value : Type} [DecidableEq Key] [AddCommMonoid Value]

private theorem selected_sum (effect : Key → ℚ →+ Value) (keys : List Key)
    (unique : keys.Nodup) (key : Key) (member : key ∈ keys) (quantity : ℚ) :
    (keys.map fun candidate => effect candidate (if key = candidate then quantity else 0)).sum =
      effect key quantity := by
  induction keys with
  | nil => cases member
  | cons first rest inherited =>
      obtain ⟨absent,unique⟩ := List.nodup_cons.mp unique
      by_cases same : key = first
      · subst key
        have zero : (rest.map fun candidate => effect candidate (if first = candidate then quantity else 0)).sum = 0 := by
          apply List.sum_eq_zero
          intro value listed
          obtain ⟨candidate,inside,rfl⟩ := List.mem_map.mp listed
          have different : first ≠ candidate := by
            intro same
            subst candidate
            exact absent inside
          simp only [if_neg different,map_zero]
        simp [zero]
      · simp only [List.map_cons,List.sum_cons,if_neg same,map_zero,zero_add]
        exact inherited unique (List.mem_cons.mp member |>.resolve_left same)

theorem grouping_preserves_every_original_transfer
    (effect : Key → ℚ →+ Value) (keys : List Key) (unique : keys.Nodup)
    (entries : List Entry) (keyOf : Entry → Key) (quantity : Entry → ℚ)
    (covered : ∀ entry ∈ entries, keyOf entry ∈ keys) :
    (keys.map fun key => effect key
      ((entries.filter (fun entry => keyOf entry = key)).map quantity).sum).sum =
      (entries.map fun entry => effect (keyOf entry) (quantity entry)).sum := by
  induction entries with
  | nil => simp
  | cons first rest inherited =>
      have tail := inherited (fun entry inside => covered entry (List.mem_cons_of_mem _ inside))
      have split (key : Key) :
          (((first :: rest).filter (fun entry => keyOf entry = key)).map quantity).sum =
            (if keyOf first = key then quantity first else 0) +
              ((rest.filter (fun entry => keyOf entry = key)).map quantity).sum := by
        by_cases same : keyOf first = key <;> simp [same]
      simp only [split,map_add,List.sum_map_add,List.map_cons,List.sum_cons]
      rw [selected_sum effect keys unique (keyOf first) (covered first List.mem_cons_self),tail]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution
