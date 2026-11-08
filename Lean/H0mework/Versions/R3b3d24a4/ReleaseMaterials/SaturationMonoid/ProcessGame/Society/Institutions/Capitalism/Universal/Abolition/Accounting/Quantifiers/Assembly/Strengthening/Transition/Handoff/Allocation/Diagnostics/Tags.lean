import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

variable {Label Label' Item : Type*} {n : ℕ}

def attach (labels : List Label) (inequalities : List (Inequality n)) : List (Tagged Label n) :=
  labels.zipWith Tagged.mk inequalities

theorem attach_exact (labels : List Label) (inequalities : List (Inequality n))
    (aligned : labels.length = inequalities.length) :
    numeric (attach labels inequalities) = inequalities := by
  induction labels generalizing inequalities with
  | nil =>
      cases inequalities with
      | nil => rfl
      | cons row tail => simp at aligned
  | cons label labels ih =>
      cases inequalities with
      | nil => simp at aligned
      | cons row tail =>
          change row :: numeric (attach labels tail) = row :: tail
          rw [ih tail (Nat.succ.inj aligned)]

theorem attach_labels (labels : List Label) (inequalities : List (Inequality n))
    (aligned : labels.length = inequalities.length) :
    (attach labels inequalities).map Tagged.label = labels := by
  induction labels generalizing inequalities with
  | nil => rfl
  | cons label labels ih =>
      cases inequalities with
      | nil => simp at aligned
      | cons row tail =>
          change label :: (attach labels tail).map Tagged.label = label :: labels
          rw [ih tail (Nat.succ.inj aligned)]

def Tagged.mapLabel (map : Label → Label') (tagged : Tagged Label n) : Tagged Label' n :=
  ⟨map tagged.label, tagged.inequality⟩

theorem numeric_mapLabel (map : Label → Label') (rows : List (Tagged Label n)) :
    numeric (rows.map (Tagged.mapLabel map)) = numeric rows := by
  simp only [numeric, List.map_map, Function.comp_def, Tagged.mapLabel]

theorem numeric_append (first second : List (Tagged Label n)) :
    numeric (first ++ second) = numeric first ++ numeric second :=
  List.map_append ..

theorem numeric_flatMap (items : List Item) (read : Item → List (Tagged Label n)) :
    numeric (items.flatMap read) = items.flatMap (fun item => numeric (read item)) :=
  List.map_flatMap ..

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics
