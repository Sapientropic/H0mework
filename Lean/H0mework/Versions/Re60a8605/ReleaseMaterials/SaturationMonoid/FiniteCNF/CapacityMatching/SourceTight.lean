import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.TightCost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.Decision

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.SourceTight

open SaturationMonoid.ComplexityProjection.SATSource.Affine

private theorem assignment_covers {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) :
    ∀ i, covers (Source.fromAssignment (Source.groups formula) assignment) i = true := by
  apply Source.assignment_covers _ _ _ (Source.groups_required formula assignment accepted)
  intro j
  exact Capacity.group_upper formula assignment accepted _ (Source.groups_good formula _ (List.get_mem _ _))

theorem group_from_demand {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true)
    (value : Cut (Capacity.positives formula).length (Source.groups formula).length)
    (tight : Tight.Correct (Source.graph formula) value) (j : Fin (Source.groups formula).length)
    (member : j ∈ value.groups) :
    ∃ i ∈ value.demands, Source.enabledFor assignment i ((Source.groups formula).get j) = true := by
  have valid := Source.assignment_valid (Source.groups formula) assignment
  have covered := assignment_covers formula assignment accepted
  obtain ⟨i,present,owned⟩ := Tight.filled (Source.graph formula) value tight _ valid covered j member
  exact ⟨i,present,Source.destination_spec _ assignment i j (Source.assigned_spec _ assignment j i owned)⟩

theorem group_saturated {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true)
    (value : Cut (Capacity.positives formula).length (Source.groups formula).length)
    (tight : Tight.Correct (Source.graph formula) value) (j : Fin (Source.groups formula).length)
    (member : j ∈ value.groups) :
    Capacity.enabled assignment (((Source.groups formula).get j).map (·.literal)) = 1 := by
  obtain ⟨_,_,enabled⟩ := group_from_demand formula assignment accepted value tight j member
  obtain ⟨item,present,read⟩ := List.any_eq_true.mp enabled
  simp only [Bool.and_eq_true] at read
  have lower := Source.enabled_member assignment _ item present read.2
  have upper := Capacity.group_upper formula assignment accepted _
    (Source.groups_good formula ((Source.groups formula).get j) (List.get_mem _ j))
  omega

theorem outside_false {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true)
    (value : Cut (Capacity.positives formula).length (Source.groups formula).length)
    (tight : Tight.Correct (Source.graph formula) value) (j : Fin (Source.groups formula).length)
    (member : j ∈ value.groups) (item : Source.Item n (Capacity.positives formula).length)
    (present : item ∈ (Source.groups formula).get j) (outside : item.demand ∉ value.demands) :
    assignment item.literal.val = false := by
  apply Bool.eq_false_iff.mpr
  intro enabled
  obtain ⟨i,origin,read⟩ := group_from_demand formula assignment accepted value tight j member
  have bounded := Capacity.group_upper formula assignment accepted _
    (Source.groups_good formula ((Source.groups formula).get j) (List.get_mem _ j))
  have current : Source.enabledFor assignment item.demand ((Source.groups formula).get j) = true :=
    List.any_eq_true.mpr ⟨item,present,by simp [enabled]⟩
  have same := Source.enabledFor_unique assignment _ bounded i item.demand read current
  exact outside (same ▸ origin)

def groupRow {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) : Row :=
  (⟨(data.get j).map (fun item => item.literal.val),true⟩ : Row).normalize

def outsideRows {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) : List Row :=
  value.groups.flatMap fun j => (data.get j).filterMap fun item =>
    if item.demand ∈ value.demands then none else some (⟨[item.literal.val],false⟩ : Row)

def one {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) : List Row :=
  value.groups.map (groupRow data) ++ outsideRows data value

theorem one_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true)
    (value : Cut (Capacity.positives formula).length (Source.groups formula).length)
    (tight : Tight.Correct (Source.graph formula) value) :
    holds (one (Source.groups formula) value) assignment = true := by
  apply (holds_iff _ _).mpr
  intro row member
  rcases List.mem_append.mp member with group | outside
  · obtain ⟨j,present,rfl⟩ := List.mem_map.mp group
    rw [groupRow,Row.normalize_holds,Row.holds_iff]
    have parity := Capacity.enabled_one_parity assignment _
      (group_saturated formula assignment accepted value tight j present)
    simpa only [Row.eval,List.map_map,Function.comp_def] using parity
  · obtain ⟨j,present,member⟩ := List.mem_flatMap.mp outside
    obtain ⟨item,inside,found⟩ := List.mem_filterMap.mp member
    by_cases owned : item.demand ∈ value.demands
    · simp [owned] at found
    · have same : (⟨[item.literal.val],false⟩ : Row) = row := by simpa [owned] using found
      subst row
      have disabled := outside_false formula assignment accepted value tight j present item inside owned
      simp [Row.holds,Row.eval,InterferenceProgram.Parity.eval,disabled]

theorem one_within {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) :
    RowsWithin n (one data value) := by
  intro row member
  rcases List.mem_append.mp member with group | outside
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp group
    apply Row.normalize_within
    intro i present
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp present
    exact item.literal.isLt
  · obtain ⟨j,_,member⟩ := List.mem_flatMap.mp outside
    obtain ⟨item,_,found⟩ := List.mem_filterMap.mp member
    split at found
    · cases found
    · cases Option.some.inj found
      intro i present
      have same : i = item.literal.val := List.mem_singleton.mp present
      simpa only [same] using item.literal.isLt

private theorem member_length {α : Type} (data : List (List α)) (group : List α) (member : group ∈ data) :
    group.length ≤ data.flatten.length := by
  induction data with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | present
      · simp
      · have bound := ih present
        simp only [List.flatten_cons,List.length_append]
        omega

theorem one_length {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) :
    (one data value).length ≤ value.groups.length*(data.flatten.length+1) := by
  have bound : ∀ selected : List (Fin data.length),
      (selected.flatMap (fun j => (data.get j).filterMap fun item =>
        if item.demand ∈ value.demands then none else some (⟨[item.literal.val],false⟩ : Row))).length ≤
      selected.length*data.flatten.length := by
    intro selected
    induction selected with
    | nil => simp
    | cons j rest ih =>
        have head := (List.length_filterMap_le
          (fun item : Source.Item n d => if item.demand ∈ value.demands then none else some (⟨[item.literal.val],false⟩ : Row))
          (data.get j)).trans (member_length data _ (List.get_mem _ j))
        simp only [List.flatMap_cons,List.length_append,List.length_cons]
        nlinarith
  have total := bound value.groups
  change (outsideRows data value).length ≤ _ at total
  simp only [one,List.length_append,List.length_map]
  nlinarith

def rows {n : Nat} (formula : CNFFormula n) : List Row :=
  let prepared := SourceCost.setup formula
  (TightCost.run prepared.graph).value.flatMap (one prepared.data)

theorem rows_value {n : Nat} (formula : CNFFormula n) :
    rows formula = (TightCost.run (Source.graph formula)).value.flatMap (one (Source.groups formula)) := by
  rw [rows,SourceCost.setup_graph,SourceCost.setup_data]
  exact congrArg (fun original =>
    let data := Source.partition formula (Source.tags original)
    (TightCost.run (Source.ofGroups data)).value.flatMap (one data)) (SourceCost.setup_rows formula)

theorem rows_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : holds (rows formula) assignment = true := by
  apply (holds_iff _ _).mpr
  intro row member
  rw [rows_value] at member
  obtain ⟨value,generated,present⟩ := List.mem_flatMap.mp member
  have tight := TightCost.run_correct (Source.graph formula) value generated
  exact (holds_iff _ _).mp (one_entails formula assignment accepted value tight) row present

theorem rows_within {n : Nat} (formula : CNFFormula n) : RowsWithin n (rows formula) := by
  intro row member
  rw [rows_value] at member
  obtain ⟨value,_,present⟩ := List.mem_flatMap.mp member
  exact one_within _ value row present

theorem rows_length {n : Nat} (formula : CNFFormula n) :
    (rows formula).length ≤ Extract.literalCount formula*Extract.literalCount formula*(Extract.literalCount formula+1) := by
  let data := Source.groups formula
  let cuts := (TightCost.run (Source.graph formula)).value
  have groupBound := Source.groups_length formula
  have itemBound : data.flatten.length ≤ Extract.literalCount formula := by
    rw [Source.groups_items]
    exact Capacity.positives_literals formula
  have cutBound : cuts.length ≤ Extract.literalCount formula :=
    (TightCost.run_length (Source.graph formula)).trans groupBound
  have each (value : Cut (Capacity.positives formula).length data.length) (member : value ∈ cuts) :
      (one data value).length ≤ (Extract.literalCount formula)*(Extract.literalCount formula+1) := by
    have correct := TightCost.run_correct (Source.graph formula) value member
    have count : value.groups.length ≤ data.length := by
      rw [correct.2.1]
      exact (List.length_filter_le _ _).trans_eq List.length_finRange
    exact (one_length data value).trans (Nat.mul_le_mul (count.trans groupBound) (Nat.add_le_add_right itemBound 1))
  have total : ∀ values : List (Cut (Capacity.positives formula).length data.length),
      (∀ value ∈ values, value ∈ cuts) → (values.flatMap (one data)).length ≤
        values.length*(Extract.literalCount formula* (Extract.literalCount formula+1)) := by
    intro values included
    induction values with
    | nil => simp
    | cons value rest ih =>
        have head := each value (included value (by simp))
        have tail := ih (fun other member => included other (by simp [member]))
        simp only [List.flatMap_cons,List.length_append,List.length_cons]
        nlinarith
  have bound := total cuts (fun _ member => member)
  have result := bound.trans (Nat.mul_le_mul_right _ cutBound)
  simpa only [rows_value,Nat.mul_assoc] using result

def prepare {n : Nat} (formula : CNFFormula n) : List Row :=
  SignedCapacity.relations formula ++ rows formula ++
    (rows (SignedCapacity.expand formula)).map (SignedCapacity.decode n)

theorem prepare_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : holds (prepare formula) assignment = true := by
  have previous := SignedCapacity.relations_entails formula assignment accepted
  have original := rows_entails formula assignment accepted
  have expanded := rows_entails (SignedCapacity.expand formula) (SignedCapacity.lift n assignment)
    ((SignedCapacity.expand_lift formula assignment).trans accepted)
  have decoded : holds ((rows (SignedCapacity.expand formula)).map (SignedCapacity.decode n)) assignment = true := by
    apply (holds_iff _ _).mpr
    intro row member
    obtain ⟨input,hit,rfl⟩ := List.mem_map.mp member
    rw [SignedCapacity.decode_holds n input (rows_within _ input hit)]
    exact (holds_iff _ _).mp expanded input hit
  simp only [holds] at previous original decoded
  simp only [prepare,holds,List.all_append,previous,original,decoded,Bool.true_and]

theorem prepare_within {n : Nat} (formula : CNFFormula n) : RowsWithin n (prepare formula) := by
  intro row member
  rcases List.mem_append.mp member with original | expanded
  · rcases List.mem_append.mp original with previous | current
    · exact SignedCapacity.relations_within formula row previous
    · exact rows_within formula row current
  · obtain ⟨input,_,rfl⟩ := List.mem_map.mp expanded
    exact (SignedCapacity.decode_valid n input).2

theorem prepare_length {n : Nat} (formula : CNFFormula n) :
    (prepare formula).length ≤ 2*Extract.literalCount formula+2*formula.length+6*n+1+
      Extract.literalCount formula*Extract.literalCount formula*(Extract.literalCount formula+1)+
      (2*Extract.literalCount formula+4*n)*(2*Extract.literalCount formula+4*n)*(2*Extract.literalCount formula+4*n+1) := by
  have previous := SignedCapacity.relations_length formula
  have original := rows_length formula
  have expanded := rows_length (SignedCapacity.expand formula)
  rw [SignedCapacity.expand_literals] at expanded
  simp only [prepare,List.length_append,List.length_map]
  omega

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  if Decision.possible formula then CapacityFeedback.decideRows formula (prepare formula) else false

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  unfold decideFormula
  split
  · rw [CapacityFeedback.decideRows_correct _ _ (prepare_within formula)]
    constructor
    · rintro ⟨assignment,accepted,_⟩
      exact ⟨extendAssignment assignment,accepted⟩
    · rintro ⟨assignment,accepted⟩
      let finite : Assignment n := fun i => assignment i.val
      have value : CNFFormula.eval formula (extendAssignment finite) = true :=
        (formula_eval_restrict _ assignment).trans accepted
      exact ⟨finite,value,prepare_entails _ _ value⟩
  · rename_i rejected
    simp [Decision.rejected_unsatisfiable formula (Bool.eq_false_iff.mpr rejected)]

def read {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) : Bool :=
  if Decision.possible formula then CapacityFeedback.readRows formula (prepare formula) assignment else false

theorem read_value {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    read formula assignment = CNFFormula.eval formula assignment := by
  unfold read
  split
  · rw [CapacityFeedback.readRows_value _ _ (prepare_within formula)]
    by_cases accepted : CNFFormula.eval formula assignment = true
    · rw [prepare_entails _ _ accepted,Bool.and_true]
    · simp [accepted]
  · rename_i rejected
    exact (Bool.eq_false_iff.mpr (fun accepted => rejected (Decision.possible_of_satisfied formula assignment accepted))).symm

def sourceAction {n : Nat} (formula : CNFFormula n)
    (source : SaturationMonoid.ComplexityProjection.SATSource.Source n) :
    SaturationMonoid.ComplexityProjection.SATSource.Source n :=
  fun assignment => if read formula (extendAssignment assignment) then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n)
    (source : SaturationMonoid.ComplexityProjection.SATSource.Source n) :
    zeroProjector formula source = sourceAction formula source := by
  funext assignment
  simp only [zeroProjector_apply,sourceAction,read_value]

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

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.SourceTight
