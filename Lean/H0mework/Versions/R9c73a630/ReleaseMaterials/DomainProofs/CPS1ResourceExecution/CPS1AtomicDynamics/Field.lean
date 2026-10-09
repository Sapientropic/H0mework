import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Body
import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1AtomicDynamics.Field
noncomputable section
open Body

theorem force_singleton_swap (node other : Node) :
    Body.force node [other] = -Body.force other [node] := by
  by_cases same : other.particle.address = node.particle.address
  · simp only [Body.force,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      if_pos same,if_pos same.symm,neg_zero]
  · simp only [Body.force,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      if_neg same,if_neg (Ne.symm same)]
    exact Coulomb.pair_force_swap _ _ _ _

theorem force_self_singleton (node : Node) : Body.force node [node] = 0 := by
  simp [Body.force]

theorem force_cons (node other : Node) (rest : List Node) :
    Body.force node (other :: rest) = Body.force node [other] + Body.force node rest := by
  simp only [Body.force,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

theorem force_as_singletons (node : Node) (nodes : List Node) :
    Body.force node nodes = (nodes.map (fun other => Body.force node [other])).sum := by
  simp only [Body.force,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

theorem list_sum_neg {A B : Type} [AddCommGroup B] (items : List A) (f : A → B) :
    (items.map (fun item => -f item)).sum = -(items.map f).sum := by
  induction items with
  | nil => simp only [List.map_nil,List.sum_nil,neg_zero]
  | cons item rest ih => simp only [List.map_cons,List.sum_cons,ih,neg_add]

theorem opposite_field (node : Node) (nodes : List Node) :
    (nodes.map (fun other => Body.force other [node])).sum = -Body.force node nodes := by
  have flipped : nodes.map (fun other => Body.force other [node]) =
      nodes.map (fun other => -Body.force node [other]) :=
    List.map_congr_left (fun other _ => force_singleton_swap other node)
  rw [flipped,list_sum_neg,← force_as_singletons]

theorem total_force_zero (nodes : List Node) :
    (nodes.map (fun node => Body.force node nodes)).sum = 0 := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    have expanded : rest.map (fun other => Body.force other (node :: rest)) =
        rest.map (fun other => Body.force other [node] + Body.force other rest) :=
      List.map_congr_left (fun other _ => force_cons other node rest)
    change Body.force node (node :: rest) + (rest.map (fun other => Body.force other (node :: rest))).sum = 0
    rw [expanded,List.sum_map_add,ih,opposite_field,force_cons,force_self_singleton]
    simp only [zero_add,add_zero,add_neg_cancel]

def perturb (direction : Charged.Address → Coulomb.Point) (time : ℝ) (node : Node) : Node :=
  {node with row := {node.row with position := node.row.position + time • direction node.particle.address}}

theorem pair_line_derivative (first second : Node) (direction : Charged.Address → Coulomb.Point)
    (distinct : first.row.position ≠ second.row.position) :
    HasDerivAt (fun time => Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
        (perturb direction time first).row.position (perturb direction time second).row.position)
      (-(inner ℝ (Coulomb.pairForce (first.particle.charge : ℝ) (second.particle.charge : ℝ)
        first.row.position second.row.position)
        (direction first.particle.address-direction second.particle.address))) 0 := by
  let displacement := fun time : ℝ =>
    (first.row.position+time • direction first.particle.address) -
      (second.row.position+time • direction second.particle.address)
  have movement : HasDerivAt displacement
      (direction first.particle.address-direction second.particle.address) 0 := by
    simpa only [displacement,Pi.add_def,Pi.sub_def,id_eq,zero_add,one_smul,zero_sub,sub_zero] using
      ((hasDerivAt_const (0 : ℝ) first.row.position).add ((hasDerivAt_id (0 : ℝ)).smul_const (direction first.particle.address))).sub
        ((hasDerivAt_const (0 : ℝ) second.row.position).add ((hasDerivAt_id (0 : ℝ)).smul_const (direction second.particle.address)))
  have kernel := Coulomb.pair_energy_derivative (first.particle.charge : ℝ) (second.particle.charge : ℝ)
    (first.row.position-second.row.position) 0 (sub_ne_zero.mpr distinct)
  have atZero : displacement 0 = first.row.position-second.row.position := by
    simp only [displacement,zero_smul,add_zero]
  have composed := kernel.comp_hasDerivAt_of_eq (0 : ℝ) movement atZero.symm
  simpa only [perturb,displacement,Coulomb.pairEnergy,Coulomb.pairForce,sub_zero,
    Function.comp_def,neg_apply,innerSL_apply_apply] using composed

theorem list_sum_derivative {A : Type} (items : List A) (f : A → ℝ → ℝ) (derivative : A → ℝ)
    (paid : ∀ item ∈ items, HasDerivAt (f item) (derivative item) 0) :
    HasDerivAt (fun time => (items.map (fun item => f item time)).sum) (items.map derivative).sum 0 := by
  induction items with
  | nil => simpa only [List.map_nil,List.sum_nil] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  | cons item rest ih =>
    have head := paid item List.mem_cons_self
    have tail := ih (fun other member => paid other (List.mem_cons_of_mem _ member))
    simpa only [List.map_cons,List.sum_cons,Pi.add_def] using head.add tail

theorem list_sum_sub {A B : Type} [AddCommGroup B] (items : List A) (f g : A → B) :
    (items.map (fun item => f item-g item)).sum = (items.map f).sum-(items.map g).sum := by
  simp only [sub_eq_add_neg,List.sum_map_add,list_sum_neg]

theorem list_sum_inner {A : Type} (items : List A) (f : A → Coulomb.Point) (direction : Coulomb.Point) :
    inner ℝ (items.map f).sum direction = (items.map (fun item => inner ℝ (f item) direction)).sum := by
  induction items with
  | nil => simp only [List.map_nil,List.sum_nil,inner_zero_left]
  | cons item rest ih => simp only [List.map_cons,List.sum_cons,inner_add_left,ih]

theorem force_singleton_distinct (first second : Node)
    (different : second.particle.address ≠ first.particle.address) :
    Body.force first [second] = Coulomb.pairForce (first.particle.charge : ℝ) (second.particle.charge : ℝ)
      first.row.position second.row.position := by
  simp only [Body.force,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,if_neg different]

theorem pair_work_split (first second : Node) (direction : Charged.Address → Coulomb.Point) :
    -(inner ℝ (Body.force first [second]) (direction first.particle.address-direction second.particle.address)) =
      -(inner ℝ (Body.force first [second]) (direction first.particle.address)) -
        inner ℝ (Body.force second [first]) (direction second.particle.address) := by
  rw [force_singleton_swap second first]
  simp only [inner_sub_right,inner_neg_left]
  ring

theorem potential_cons (first : Node) (rest : List Node) :
    Body.potential (first::rest) =
      (rest.map (fun second => Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
        first.row.position second.row.position)).sum + Body.potential rest := rfl

theorem full_work_cons (first : Node) (rest : List Node) (direction : Charged.Address → Coulomb.Point) :
    ((first::rest).map (fun node => inner ℝ (Body.force node (first::rest)) (direction node.particle.address))).sum =
      inner ℝ (Body.force first rest) (direction first.particle.address) +
        (rest.map (fun node => inner ℝ (Body.force node [first]) (direction node.particle.address))).sum +
        (rest.map (fun node => inner ℝ (Body.force node rest) (direction node.particle.address))).sum := by
  change inner ℝ (Body.force first (first::rest)) (direction first.particle.address) +
    (rest.map (fun node => inner ℝ (Body.force node (first::rest)) (direction node.particle.address))).sum = _
  rw [force_cons,force_self_singleton,zero_add]
  have expanded : rest.map (fun node => inner ℝ (Body.force node (first::rest)) (direction node.particle.address)) =
      rest.map (fun node => inner ℝ (Body.force node [first]) (direction node.particle.address) +
        inner ℝ (Body.force node rest) (direction node.particle.address)) := by
    apply List.map_congr_left
    intro node _
    rw [force_cons,inner_add_left]
  rw [expanded,List.sum_map_add]
  ring

theorem potential_line_derivative (nodes : List Node)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup)
    (separated : Body.ready nodes) (direction : Charged.Address → Coulomb.Point) :
    HasDerivAt (fun time => Body.potential (nodes.map (perturb direction time)))
      (-(nodes.map (fun node => inner ℝ (Body.force node nodes) (direction node.particle.address))).sum) 0 := by
  induction nodes with
  | nil => simpa only [List.map_nil,Body.potential,List.rec, List.sum_nil,neg_zero] using
      hasDerivAt_const (0 : ℝ) (0 : ℝ)
  | cons first rest ih =>
    have nodup := List.nodup_cons.mp unique
    have ready := List.pairwise_cons.mp separated
    have tail := ih nodup.2 ready.2
    have pairs := list_sum_derivative rest
      (fun second time => Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
        (perturb direction time first).row.position (perturb direction time second).row.position)
      (fun second => -(inner ℝ (Body.force first [second]) (direction first.particle.address)) -
        inner ℝ (Body.force second [first]) (direction second.particle.address)) (by
      intro second member
      have different : second.particle.address ≠ first.particle.address := by
        intro same
        exact nodup.1 (List.mem_map.mpr ⟨second,member,same⟩)
      have paid := pair_line_derivative first second direction (ready.1 second member)
      have actual := force_singleton_distinct first second different
      rw [← actual,pair_work_split] at paid
      exact paid)
    have pairValue : (rest.map (fun second =>
        -(inner ℝ (Body.force first [second]) (direction first.particle.address)) -
          inner ℝ (Body.force second [first]) (direction second.particle.address))).sum =
        -(inner ℝ (Body.force first rest) (direction first.particle.address)) -
          (rest.map (fun second => inner ℝ (Body.force second [first]) (direction second.particle.address))).sum := by
      rw [list_sum_sub,list_sum_neg,← list_sum_inner,← force_as_singletons]
    rw [pairValue] at pairs
    have paid := pairs.add tail
    have derivative :
        -(inner ℝ (Body.force first rest) (direction first.particle.address)) -
          (rest.map (fun second => inner ℝ (Body.force second [first]) (direction second.particle.address))).sum +
          -(rest.map (fun node => inner ℝ (Body.force node rest) (direction node.particle.address))).sum =
        -((first::rest).map (fun node => inner ℝ (Body.force node (first::rest)) (direction node.particle.address))).sum := by
      rw [full_work_cons]
      ring
    rw [derivative] at paid
    simpa only [List.map_cons,potential_cons,List.map_map,Function.comp_def,Pi.add_def,perturb] using paid

end
end CPS1AtomicDynamics.Field
