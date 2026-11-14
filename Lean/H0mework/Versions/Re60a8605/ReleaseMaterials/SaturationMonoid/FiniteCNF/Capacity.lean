import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ConditionalPivot

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Capacity

open SaturationMonoid.ComplexityProjection.SATSource.Affine

def positives {n : Nat} (formula : CNFFormula n) : List (List (Fin n)) :=
  (formula.filter (fun clause => clause.all (·.positive))).map (fun clause => clause.map (·.var))

theorem positives_satisfied {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) (row : List (Fin n)) (member : row ∈ positives formula) :
    row.any (fun i => assignment i.val) = true := by
  obtain ⟨clause,filtered,rfl⟩ := List.mem_map.mp member
  have original := (List.mem_filter.mp filtered).1
  have positive := (List.mem_filter.mp filtered).2
  have value := List.all_eq_true.mp accepted clause original
  obtain ⟨literal,hit,read⟩ := List.any_eq_true.mp value
  have sign := List.all_eq_true.mp positive literal hit
  apply List.any_eq_true.mpr
  refine ⟨literal.var,List.mem_map.mpr ⟨literal,hit,rfl⟩,?_⟩
  simpa only [CNFLiteral.eval,sign,if_true] using read

def compatible {n : Nat} (formula : CNFFormula n) (a b : Fin n) : Bool :=
  (Extract.findClause [⟨a,false⟩,⟨b,false⟩] formula).accepted

theorem compatible_excludes {n : Nat} (formula : CNFFormula n) (a b : Fin n)
    (found : compatible formula a b = true) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) :
    ¬ (assignment a.val = true ∧ assignment b.val = true) := by
  have clause := Extract.findClause_eval [⟨a,false⟩,⟨b,false⟩] formula assignment accepted found
  rintro ⟨first,second⟩
  simp [CNFClause.eval,CNFLiteral.eval,first,second] at clause

def enabled {n : Nat} (assignment : Nat → Bool) : List (Fin n) → Nat
  | [] => 0
  | i :: rest => (if assignment i.val then 1 else 0) + enabled assignment rest

theorem enabled_append {n : Nat} (assignment : Nat → Bool) (left right : List (Fin n)) :
    enabled assignment (left++right) = enabled assignment left + enabled assignment right := by
  induction left with
  | nil => simp [enabled]
  | cons i rest ih => simp only [List.cons_append,enabled,ih,Nat.add_assoc]

theorem enabled_zero {n : Nat} (assignment : Nat → Bool) (row : List (Fin n))
    (zero : ∀ i ∈ row, assignment i.val = false) : enabled assignment row = 0 := by
  induction row with
  | nil => rfl
  | cons i rest ih => simp only [enabled,zero i (by simp),Bool.false_eq_true,if_false,Nat.zero_add]
                      exact ih (fun j member => zero j (by simp [member]))

theorem enabled_positive {n : Nat} (assignment : Nat → Bool) (row : List (Fin n))
    (positive : row.any (fun i => assignment i.val) = true) : 1 ≤ enabled assignment row := by
  induction row with
  | nil => cases positive
  | cons i rest ih =>
      rw [List.any_cons,Bool.or_eq_true] at positive
      rcases positive with first | tail
      · simp only [enabled,first,if_true]
        omega
      · have more := ih tail
        simp only [enabled]
        split <;> omega

theorem rows_lower {n : Nat} (assignment : Nat → Bool) (rows : List (List (Fin n)))
    (positive : ∀ row ∈ rows, row.any (fun i => assignment i.val) = true) :
    rows.length ≤ enabled assignment rows.flatten := by
  induction rows with
  | nil => simp [enabled]
  | cons row rest ih =>
      have head := enabled_positive assignment row (positive row (by simp))
      have tail := ih (fun other member => positive other (by simp [member]))
      simp only [List.length_cons,List.flatten_cons,enabled_append]
      omega

def GoodGroup {n : Nat} (formula : CNFFormula n) (group : List (Fin n)) : Prop :=
  group.Pairwise (fun a b => compatible formula a b = true)

def GoodGroups {n : Nat} (formula : CNFFormula n) (groups : List (List (Fin n))) : Prop :=
  ∀ group ∈ groups, GoodGroup formula group

theorem group_upper {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) (group : List (Fin n)) (good : GoodGroup formula group) :
    enabled assignment group ≤ 1 := by
  induction group with
  | nil => simp [enabled]
  | cons a rest ih =>
      have pairs := List.pairwise_cons.mp good
      by_cases first : assignment a.val = true
      · have tail : enabled assignment rest = 0 := by
          apply enabled_zero
          intro b member
          apply Bool.eq_false_iff.mpr
          intro second
          exact compatible_excludes formula a b (pairs.1 b member) assignment accepted ⟨first,second⟩
        simp [enabled,first,tail]
      · simpa [enabled,first] using ih pairs.2

theorem groups_upper {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) (groups : List (List (Fin n)))
    (good : GoodGroups formula groups) : enabled assignment groups.flatten ≤ groups.length := by
  induction groups with
  | nil => simp [enabled]
  | cons group rest ih =>
      have head := group_upper formula assignment accepted group (good group (by simp))
      have tail := ih (fun other member => good other (by simp [member]))
      simp only [List.flatten_cons,enabled_append,List.length_cons]
      omega

def fits {n : Nat} (formula : CNFFormula n) (i : Fin n) : List (Fin n) → Extract.Check
  | [] => ⟨true,1⟩
  | j :: rest =>
      let found := Extract.findClause [⟨i,false⟩,⟨j,false⟩] formula
      if found.accepted then
        let next := fits formula i rest
        ⟨next.accepted,found.visits+next.visits+1⟩
      else ⟨false,found.visits+1⟩

theorem fits_accepted {n : Nat} (formula : CNFFormula n) (i : Fin n) (group : List (Fin n)) :
    (fits formula i group).accepted = group.all (compatible formula i) := by
  induction group with
  | nil => rfl
  | cons j rest ih =>
      simp only [fits,compatible,List.all_cons]
      split <;> simp_all

def queryBudget {n : Nat} (formula : CNFFormula n) : Nat :=
  10*Extract.literalCount formula+8*formula.length+1

theorem fits_visits {n : Nat} (formula : CNFFormula n) (i : Fin n) (group : List (Fin n)) :
    (fits formula i group).visits ≤ group.length*(queryBudget formula+1)+1 := by
  induction group with
  | nil => simp [fits]
  | cons j rest ih =>
      have query := Extract.findClause_visits ([⟨i,false⟩,⟨j,false⟩] : CNFClause n) formula
      have bound : (Extract.findClause [⟨i,false⟩,⟨j,false⟩] formula).visits ≤ queryBudget formula := by
        simpa only [List.length_cons,List.length_nil,queryBudget] using query
      simp only [fits,List.length_cons]
      split <;> simp only <;> nlinarith

def put {n : Nat} (formula : CNFFormula n) (i : Fin n) : List (List (Fin n)) → List (List (Fin n))
  | [] => [[i]]
  | group :: rest =>
      if (fits formula i group).accepted then (i::group)::rest else group::put formula i rest

theorem put_good {n : Nat} (formula : CNFFormula n) (i : Fin n) (groups : List (List (Fin n)))
    (good : GoodGroups formula groups) : GoodGroups formula (put formula i groups) := by
  induction groups with
  | nil => simp [put,GoodGroups,GoodGroup]
  | cons group rest ih =>
      have head := good group (by simp)
      have tail : GoodGroups formula rest := fun other member => good other (by simp [member])
      simp only [put]
      split
      · rename_i found
        rw [fits_accepted] at found
        intro other member
        rcases List.mem_cons.mp member with equal | member
        · subst other
          exact List.pairwise_cons.mpr ⟨fun j hit => List.all_eq_true.mp found j hit,head⟩
        · exact tail other member
      · intro other member
        rcases List.mem_cons.mp member with equal | member
        · subst other
          exact head
        · exact ih tail other member

theorem put_enabled {n : Nat} (formula : CNFFormula n) (i : Fin n) (groups : List (List (Fin n)))
    (assignment : Nat → Bool) :
    enabled assignment (put formula i groups).flatten =
      (if assignment i.val then 1 else 0)+enabled assignment groups.flatten := by
  induction groups with
  | nil => simp [put,enabled]
  | cons group rest ih =>
      simp only [put]
      split
      · simp only [List.flatten_cons,enabled_append,enabled]
        omega
      · simp only [List.flatten_cons,enabled_append,ih]
        omega

def partition {n : Nat} (formula : CNFFormula n) : List (Fin n) → List (List (Fin n))
  | [] => []
  | i :: rest => put formula i (partition formula rest)

theorem partition_good {n : Nat} (formula : CNFFormula n) (items : List (Fin n)) :
    GoodGroups formula (partition formula items) := by
  induction items with
  | nil => simp [partition,GoodGroups]
  | cons i rest ih => exact put_good formula i _ ih

theorem partition_enabled {n : Nat} (formula : CNFFormula n) (items : List (Fin n)) (assignment : Nat → Bool) :
    enabled assignment (partition formula items).flatten = enabled assignment items := by
  induction items with
  | nil => rfl
  | cons i rest ih => rw [partition,put_enabled,ih,enabled]

def obstruction {n : Nat} (formula : CNFFormula n) : Bool :=
  let rows := positives formula
  let groups := partition formula rows.flatten
  decide (groups.length < rows.length)

theorem obstruction_unsatisfiable {n : Nat} (formula : CNFFormula n) (found : obstruction formula = true) :
    ¬ CNFSatisfiable formula := by
  rintro ⟨assignment,accepted⟩
  have lower := rows_lower assignment (positives formula) (positives_satisfied formula assignment accepted)
  have upper := groups_upper formula assignment accepted (partition formula (positives formula).flatten)
    (partition_good formula (positives formula).flatten)
  rw [partition_enabled] at upper
  simp only [obstruction,decide_eq_true_eq] at found
  omega

theorem enabled_true {n : Nat} (items : List (Fin n)) : enabled (fun _ => true) items = items.length := by
  induction items with
  | nil => rfl
  | cons i rest ih => simp [enabled,ih,Nat.add_comm]

theorem put_length {n : Nat} (formula : CNFFormula n) (i : Fin n) (groups : List (List (Fin n))) :
    (put formula i groups).length ≤ groups.length+1 := by
  induction groups with
  | nil => simp [put]
  | cons group rest ih =>
      simp only [put]
      split <;> simp only [List.length_cons] <;> omega

theorem partition_length {n : Nat} (formula : CNFFormula n) (items : List (Fin n)) :
    (partition formula items).length ≤ items.length := by
  induction items with
  | nil => rfl
  | cons i rest ih =>
      have next := put_length formula i (partition formula rest)
      simp only [partition,List.length_cons]
      omega

theorem partition_elements {n : Nat} (formula : CNFFormula n) (items : List (Fin n)) :
    (partition formula items).flatten.length = items.length := by
  simpa only [enabled_true] using partition_enabled formula items (fun _ => true)

def putVisits {n : Nat} (formula : CNFFormula n) (i : Fin n) : List (List (Fin n)) → Nat
  | [] => 2
  | group :: rest =>
      let found := fits formula i group
      if found.accepted then found.visits+2 else found.visits+putVisits formula i rest+2

theorem put_visits {n : Nat} (formula : CNFFormula n) (i : Fin n) (groups : List (List (Fin n))) :
    putVisits formula i groups ≤ groups.flatten.length*(queryBudget formula+1)+3*groups.length+2 := by
  induction groups with
  | nil => simp [putVisits]
  | cons group rest ih =>
      have head := fits_visits formula i group
      simp only [putVisits,List.flatten_cons,List.length_append,List.length_cons]
      split <;> nlinarith

def partitionVisits {n : Nat} (formula : CNFFormula n) : List (Fin n) → Nat
  | [] => 1
  | i :: rest => partitionVisits formula rest+putVisits formula i (partition formula rest)+2

theorem partition_visits {n : Nat} (formula : CNFFormula n) (items : List (Fin n)) :
    partitionVisits formula items ≤ (items.length+1)^2*(queryBudget formula+8) := by
  induction items with
  | nil => simp [partitionVisits]
  | cons i rest ih =>
      have inserted := put_visits formula i (partition formula rest)
      rw [partition_elements] at inserted
      have count := partition_length formula rest
      simp only [partitionVisits,List.length_cons]
      nlinarith

theorem positives_cons {n : Nat} (clause : CNFClause n) (formula : CNFFormula n) :
    positives (clause::formula) =
      if clause.all (·.positive) then clause.map (·.var) :: positives formula else positives formula := by
  simp only [positives,List.filter_cons]
  split <;> rfl

theorem positives_length {n : Nat} (formula : CNFFormula n) : (positives formula).length ≤ formula.length := by
  simpa only [positives,List.length_map] using List.length_filter_le (fun clause => clause.all (·.positive)) formula

theorem positives_literals {n : Nat} (formula : CNFFormula n) :
    (positives formula).flatten.length ≤ Extract.literalCount formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [positives_cons,Extract.literalCount,List.map_cons,List.sum_cons]
      change (if clause.all (·.positive) then clause.map (·.var)::positives rest else positives rest).flatten.length ≤
        clause.length+Extract.literalCount rest
      split
      · simp only [List.flatten_cons,List.length_append,List.length_map]
        omega
      · omega

theorem source_partition_visits {n : Nat} (formula : CNFFormula n) :
    partitionVisits formula (positives formula).flatten ≤
      (Extract.literalCount formula+1)^2*(10*Extract.literalCount formula+8*formula.length+9) := by
  have actual := partition_visits formula (positives formula).flatten
  have size := positives_literals formula
  apply actual.trans
  change _ ≤ (Extract.literalCount formula+1)^2*(queryBudget formula+8)
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.add_le_add_right size 1) 2)

theorem obstruction_eval {n : Nat} (formula : CNFFormula n) (found : obstruction formula = true)
    (assignment : Nat → Bool) : CNFFormula.eval formula assignment = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact obstruction_unsatisfiable formula found ⟨assignment,accepted⟩

theorem obstruction_projector {n : Nat} (formula : CNFFormula n) (found : obstruction formula = true) :
    zeroProjector formula = 0 := by
  apply LinearMap.ext
  intro source
  funext assignment
  rw [zeroProjector_apply,obstruction_eval formula found]
  rfl

theorem conservation {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) :
    (positives formula).length ≤ (partition formula (positives formula).flatten).length := by
  have lower := rows_lower assignment (positives formula) (positives_satisfied formula assignment accepted)
  have upper := groups_upper formula assignment accepted (partition formula (positives formula).flatten)
    (partition_good formula (positives formula).flatten)
  rw [partition_enabled] at upper
  omega

theorem groups_saturated {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) (groups : List (List (Fin n)))
    (good : GoodGroups formula groups) (full : groups.length ≤ enabled assignment groups.flatten) :
    ∀ group ∈ groups, enabled assignment group = 1 := by
  induction groups with
  | nil => simp
  | cons group rest ih =>
      have head := group_upper formula assignment accepted group (good group (by simp))
      have restGood : GoodGroups formula rest := fun other member => good other (by simp [member])
      have upper := groups_upper formula assignment accepted rest restGood
      simp only [List.length_cons,List.flatten_cons,enabled_append] at full
      have exactHead : enabled assignment group = 1 := by omega
      have exactTail : rest.length ≤ enabled assignment rest.flatten := by omega
      intro other member
      rcases List.mem_cons.mp member with equal | member
      · simpa only [equal] using exactHead
      · exact ih restGood exactTail other member

theorem rows_saturated {n : Nat} (assignment : Nat → Bool) (rows : List (List (Fin n)))
    (positive : ∀ row ∈ rows, row.any (fun i => assignment i.val) = true)
    (full : enabled assignment rows.flatten ≤ rows.length) :
    ∀ row ∈ rows, enabled assignment row = 1 := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
      have head := enabled_positive assignment row (positive row (by simp))
      have restPositive : ∀ other ∈ rest, other.any (fun i => assignment i.val) = true :=
        fun other member => positive other (by simp [member])
      have lower := rows_lower assignment rest restPositive
      simp only [List.flatten_cons,enabled_append,List.length_cons] at full
      have exactHead : enabled assignment row = 1 := by omega
      have exactTail : enabled assignment rest.flatten ≤ rest.length := by omega
      intro other member
      rcases List.mem_cons.mp member with equal | member
      · simpa only [equal] using exactHead
      · exact ih restPositive exactTail other member

theorem enabled_zero_parity {n : Nat} (assignment : Nat → Bool) (group : List (Fin n))
    (zero : enabled assignment group = 0) :
    InterferenceProgram.Parity.eval assignment (group.map (·.val)) = false := by
  induction group with
  | nil => rfl
  | cons i rest ih =>
      cases value : assignment i.val
      · have tail : enabled assignment rest = 0 := by simpa [enabled,value] using zero
        simp only [List.map_cons,InterferenceProgram.Parity.eval,value,Bool.false_xor,ih tail]
      · simp [enabled,value] at zero

theorem enabled_one_parity {n : Nat} (assignment : Nat → Bool) (group : List (Fin n))
    (one : enabled assignment group = 1) :
    InterferenceProgram.Parity.eval assignment (group.map (·.val)) = true := by
  induction group with
  | nil => cases one
  | cons i rest ih =>
      cases value : assignment i.val
      · have tail : enabled assignment rest = 1 := by simpa [enabled,value] using one
        simp only [List.map_cons,InterferenceProgram.Parity.eval,value,Bool.false_xor,ih tail]
      · have tail : enabled assignment rest = 0 := by simp [enabled,value] at one; omega
        simp only [List.map_cons,InterferenceProgram.Parity.eval,value,enabled_zero_parity assignment rest tail,Bool.xor_false]

def relations {n : Nat} (formula : CNFFormula n) : List Row :=
  let rows := positives formula
  let groups := partition formula rows.flatten
  if groups.length < rows.length then [⟨[],true⟩]
  else if rows.length = groups.length then (groups++rows).map (fun group => (⟨group.map (·.val),true⟩ : Row).normalize)
  else []

theorem relations_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : holds (relations formula) assignment = true := by
  have bound := conservation formula assignment accepted
  unfold relations
  dsimp only
  split
  · omega
  · split
    · rename_i tight
      have lower := rows_lower assignment (positives formula) (positives_satisfied formula assignment accepted)
      rw [← partition_enabled formula (positives formula).flatten assignment, tight] at lower
      have saturated := groups_saturated formula assignment accepted _
        (partition_good formula (positives formula).flatten) lower
      have upper := groups_upper formula assignment accepted _ (partition_good formula (positives formula).flatten)
      rw [partition_enabled,← tight] at upper
      have demands := rows_saturated assignment (positives formula)
        (positives_satisfied formula assignment accepted) upper
      apply (holds_iff _ _).mpr
      intro row member
      obtain ⟨group,groupMember,rfl⟩ := List.mem_map.mp member
      rw [Row.normalize_holds,Row.holds_iff]
      apply enabled_one_parity
      rcases List.mem_append.mp groupMember with capacity | demand
      · exact saturated group capacity
      · exact demands group demand
    · rfl

theorem relations_within {n : Nat} (formula : CNFFormula n) : RowsWithin n (relations formula) := by
  unfold relations
  dsimp only
  split
  · simp [RowsWithin,InterferenceProgram.Parity.Within]
  · split
    · intro row member
      obtain ⟨group,member,rfl⟩ := List.mem_map.mp member
      apply Row.normalize_within
      intro i member
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
      exact j.isLt
    · simp [RowsWithin]

theorem relations_length {n : Nat} (formula : CNFFormula n) :
    (relations formula).length ≤ Extract.literalCount formula+formula.length+1 := by
  have count := partition_length formula (positives formula).flatten
  have size := positives_literals formula
  have demands := positives_length formula
  unfold relations
  dsimp only
  split
  · simp
  · split <;> simp only [List.length_map,List.length_append,List.length_nil] <;> omega

def decideData (data : List (List Row)) : Bool :=
  let formula := Subsumption.reduce (Atoms.compile data)
  let image := AtomImage.generate (Atoms.table data)
  ConditionalPivot.decideRows formula (image.kernel ++ relations formula)

theorem holds_with_relations {n : Nat} (formula : CNFFormula n) (rows : List Row) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && holds (rows ++ relations formula) assignment) =
      (CNFFormula.eval formula assignment && holds rows assignment) := by
  by_cases accepted : CNFFormula.eval formula assignment = true
  · simp only [holds,List.all_append] at *
    have generated := relations_entails formula assignment accepted
    simp only [holds] at generated
    rw [generated]
    simp
  · simp [accepted]

theorem decideData_eq_original (n : Nat) (data : List (List Row))
    (valid : ∀ row ∈ data.flatten, Table.RowValid n row) :
    decideData data = ConditionalPivot.decideData data := by
  let formula := Subsumption.reduce (Atoms.compile data)
  let kernel := (AtomImage.generate (Atoms.table data)).kernel
  have originalWithin : RowsWithin (Atoms.keys data).length kernel := AtomSource.kernel_within n data valid
  have inside : RowsWithin (Atoms.keys data).length (kernel ++ relations formula) := by
    intro row member
    rcases List.mem_append.mp member with left | right
    · exact originalWithin row left
    · exact relations_within formula row right
  apply Bool.eq_iff_iff.mpr
  change ConditionalPivot.decideRows formula (kernel ++ relations formula) = true ↔
    ConditionalPivot.decideRows formula kernel = true
  rw [ConditionalPivot.decideRows_eq_original formula _ inside,
    ConditionalPivot.decideRows_eq_original formula _ originalWithin,
    BranchImage.decideRows_correct formula _ inside,BranchImage.decideRows_correct formula _ originalWithin]
  simp only [← Bool.and_eq_true,holds_with_relations]

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  if obstruction formula then false else
    match Atoms.generate formula with
    | .contradiction => false
    | .basis basis => decideData (Atoms.data basis formula)

theorem decideFormula_eq_original {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = ConditionalPivot.decideFormula formula := by
  unfold decideFormula
  split
  · rename_i rejected
    apply Bool.eq_iff_iff.mpr
    simp [ConditionalPivot.decideFormula_correct,obstruction_unsatisfiable formula rejected]
  · cases generated : Atoms.generate formula with
    | contradiction => simp [ConditionalPivot.decideFormula,generated]
    | basis basis =>
        simp only [ConditionalPivot.decideFormula,generated]
        exact decideData_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula_eq_original,ConditionalPivot.decideFormula_correct]


def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits,Encoding.decideBits,parsed]
  | some input =>
      simp only [decideBits,Encoding.decideBits,parsed]
      apply Bool.eq_iff_iff.mpr
      rw [decideFormula_correct,Dense.decideFormula_correct]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original,Encoding.decideBits_iff_rootVerify]

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔ ¬ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [decideBits_eq_original,Encoding.decideBits_no]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) : decideBits bits = false := by
  simp [decideBits,invalid]

def jointValue (data : List (List Row)) (target : Nat → Bool) : Bool :=
  let formula := Subsumption.reduce (Atoms.compile data)
  let image := AtomImage.generate (Atoms.table data)
  ConditionalPivot.readResult formula (BranchImage.generate formula (image.kernel++relations formula)) target

theorem jointValue_eq_original (n : Nat) (data : List (List Row))
    (valid : ∀ row ∈ data.flatten, Table.RowValid n row) (target : Nat → Bool) :
    jointValue data target = AtomSource.jointValue data target := by
  let formula := Subsumption.reduce (Atoms.compile data)
  let kernel := (AtomImage.generate (Atoms.table data)).kernel
  have inside : RowsWithin (Atoms.keys data).length (kernel++relations formula) := by
    intro row member
    rcases List.mem_append.mp member with left | right
    · exact AtomSource.kernel_within n data valid row left
    · exact relations_within formula row right
  have generated := BranchImage.generate_invariants formula _ inside
  change ConditionalPivot.readResult formula (BranchImage.generate formula (kernel++relations formula)) target = _
  rw [ConditionalPivot.readResult_value _ _ generated.1 generated.2,
    BranchImage.generate_holds _ _ inside,holds_with_relations,AtomSource.jointValue,Bool.and_comm]

def sourceAction {n : Nat} (formula : CNFFormula n) (basis : List Row) (source : Source n) : Source n :=
  fun assignment =>
    let input := extendAssignment assignment
    if holds basis input && jointValue (Atoms.data basis formula) (Atoms.read (Atoms.data basis formula) input)
    then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) (source : Source n) :
    zeroProjector formula source = sourceAction formula basis source := by
  rw [AtomSource.original_projector formula basis generated source]
  funext assignment
  simp only [AtomSource.sourceAction,sourceAction,
    jointValue_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)]

end SaturationMonoid.ComplexityProjection.SATSource.Capacity
