import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationExecutionEngineInvariant

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumExecutionGraph
open PreparationVacuumSharedPool PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient
open PreparationVacuumClockSymbol PreparationVacuumCanonicalMoyal
open scoped BigOperators Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def expanded (K : ℕ) (state : RawArena) (id : ℕ) : ArenaExpression K :=
  rawExpand K state.polynomials.length state id

def expandedNode (K : ℕ) (state : RawArena) (id : ℕ) : ArenaExpression K :=
  rawNodeExpression K (expanded K state) (rawNode state id).kind

def nativePolynomial (K : ℕ) (state : RawArena) (id : ℕ) : Phase → ℂ := arenaEvaluate (expanded K state id)

def nativeNode (K : ℕ) (state : RawArena) (id : ℕ) : Phase → ℂ := arenaEvaluate (expandedNode K state id)

theorem rawExpand_paid_fuel (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (id : ℕ) (valid : Handle state id) {low high : ℕ} (paid : id < low) (order : low ≤ high) :
    rawExpand K high state id=rawExpand K low state id := by
  induction order with
  | refl=>rfl
  | @step high order ih=>
    rw [rawExpand_stable K high state closed id valid (lt_of_lt_of_le paid order)]
    exact ih

theorem expanded_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (id : ℕ) (valid : Handle old id) :
    expanded K next id=expanded K old id := by
  unfold expanded
  rw [rawExpand_prefix K next.polynomials.length extension closed id valid]
  exact rawExpand_paid_fuel K old closed id valid valid extension.polynomials.length_le

theorem expandedNode_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (id : ℕ) (valid : id < old.nodes.length) :
    expandedNode K next id=expandedNode K old id := by
  unfold expandedNode
  rw [rawNode_preserved extension id valid]
  apply rawNodeExpression_congr
  intro dep member
  exact expanded_prefix K extension closed dep (closed.nodes _ (rawNode_member old id valid) dep member)

theorem nativePolynomial_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (id : ℕ) (valid : Handle old id) :
    nativePolynomial K next id=nativePolynomial K old id := congrArg arenaEvaluate (expanded_prefix K extension closed id valid)

theorem nativeNode_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (id : ℕ) (valid : id < old.nodes.length) :
    nativeNode K next id=nativeNode K old id := congrArg arenaEvaluate (expandedNode_prefix K extension closed id valid)

theorem native_rows_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (rows : List RawRow)
    (words : RawWords (fun id=>id < old.nodes.length) rows) (x : Phase) :
    rawRowsValue (fun id=>nativeNode K next id x) rows x=rawRowsValue (fun id=>nativeNode K old id x) rows x := by
  unfold rawRowsValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro row member
  unfold rawRowValue
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro id present
  exact congrFun (nativeNode_prefix K extension closed id (words row member id present)) x

theorem rawExpandStep_native_rows (K : ℕ) (state : RawArena) (id : ℕ) (x : Phase) :
    arenaEvaluate (rawExpandStep K state (expanded K state) id) x=
      rawRowsValue (fun node=>nativeNode K state node x) (rawRows state id) x := by
  unfold rawExpandStep
  generalize rawRows state id=rows
  induction rows with
  | nil=>rfl
  | cons row rows ih=>
    simp only [List.foldr_cons,arenaEvaluate_add,arenaEvaluate_row,rawRowsValue,List.map_cons,List.sum_cons,rawRowValue]
    rw [show (List.map (fun node=>rawNodeExpression K (expanded K state) (rawNode state node).kind) row.word).foldr
      (fun atom out=>arenaEvaluate atom x*out) 1=(row.word.map (fun node=>nativeNode K state node x)).prod by
      simp only [List.foldr_map,nativeNode,expandedNode,List.prod_eq_foldr]]
    exact congrArg ((coefficientValue row.coefficient x : ℂ)*(row.word.map (fun node=>nativeNode K state node x)).prod+·) ih

theorem nativePolynomial_rows (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (id : ℕ) (valid : Handle state id) (x : Phase) :
    nativePolynomial K state id x=rawRowsValue (fun node=>nativeNode K state node x) (rawRows state id) x := by
  unfold nativePolynomial expanded
  rw [rawExpand_equation K state closed id valid]
  exact rawExpandStep_native_rows K state id x

theorem nativePolynomial_extension_rows (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (oldClosed : RawMoyalClosed old) (newClosed : RawMoyalClosed next) (sameNodes : next.nodes=old.nodes)
    (id : ℕ) (valid : Handle next id) (x : Phase) :
    nativePolynomial K next id x=rawRowsValue (fun node=>nativeNode K old node x) (rawRows next id) x := by
  rw [nativePolynomial_rows K next newClosed id valid x]
  apply native_rows_prefix K extension oldClosed
  have words:=rawRows_words next newClosed id
  simpa only [sameNodes] using words

theorem rawScalar_native (K : ℕ) (c : NormalizedCoefficient) (state : RawArena) (closed : RawMoyalClosed state)
    (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawScalar c state).2 (rawScalar c state).1 x=(coefficientValue c x : ℂ) := by
  rw [nativePolynomial_extension_rows K (rawScalar_extends c state) closed (rawScalar_closed c state closed)
    rfl (rawScalar c state).1 (rawPoly_bound _ _) x]
  exact rawScalar_value c state _ x hx

theorem rawScale_native (K : ℕ) (c : NormalizedCoefficient) (id : ℕ) (state : RawArena)
    (closed : RawMoyalClosed state) (valid : Handle state id) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawScale c id state).2 (rawScale c id state).1 x=
      (coefficientValue c x : ℂ)*nativePolynomial K state id x := by
  rw [nativePolynomial_extension_rows K (rawScale_extends c id state) closed (rawScale_closed c id state closed)
    rfl (rawScale c id state).1 (rawPoly_bound _ _) x,rawScale_value c id state _ x hx,nativePolynomial_rows K state closed id valid x]

theorem rawAdd_native (K : ℕ) (ids : List ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (valid : ListHandles state ids) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawAdd ids state).2 (rawAdd ids state).1 x=(ids.map (fun id=>nativePolynomial K state id x)).sum := by
  rw [nativePolynomial_extension_rows K (rawAdd_extends ids state) closed (rawAdd_closed ids state closed)
    rfl (rawAdd ids state).1 (rawPoly_bound _ _) x,rawAdd_value ids state _ x hx]
  apply congrArg List.sum
  apply List.map_congr_left
  intro id member
  exact (nativePolynomial_rows K state closed id (valid id member) x).symm

theorem rawMultiply_native (K left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (leftValid : Handle state left) (rightValid : Handle state right) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawMultiply left right state).2 (rawMultiply left right state).1 x=
      nativePolynomial K state left x*nativePolynomial K state right x := by
  rw [nativePolynomial_extension_rows K (rawMultiply_extends left right state) closed
    (rawMultiply_closed left right state closed) rfl (rawMultiply left right state).1 (rawPoly_bound _ _) x,
    rawMultiply_value left right state _ x hx,nativePolynomial_rows K state closed left leftValid x,
    nativePolynomial_rows K state closed right rightValid x]


theorem rawPoly_native (K : ℕ) (rows : List RawRow) (state : RawArena) (closed : RawMoyalClosed state)
    (words : RawWords (fun id=>id < state.nodes.length) rows) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawPoly rows state).2 (rawPoly rows state).1 x=
      rawRowsValue (fun node=>nativeNode K state node x) rows x := by
  rw [nativePolynomial_extension_rows K (rawPoly_extends rows state) closed (rawPoly_closed rows state closed words)
    rfl (rawPoly rows state).1 (rawPoly_bound _ _) x]
  exact rawPoly_value rows state _ x hx

def insertedNodeId (node : RawNode) (state : RawArena) : ℕ := by
  classical
  exact (PreparationVacuumSourceSerialization.intern node state.nodes).idxOf node

theorem insertedNodeId_bound (node : RawNode) (state : RawArena) :
    insertedNodeId node state < (rawInternNode node state).nodes.length := by
  classical
  exact List.idxOf_lt_length_of_mem (PreparationVacuumSourceSerialization.intern_member node state.nodes)

theorem rawInternNode_read (node : RawNode) (state : RawArena) :
    rawNode (rawInternNode node state) (insertedNodeId node state)=node := by
  classical
  rw [rawNode,List.getD_eq_getElem _ _ (insertedNodeId_bound node state)]
  exact List.getElem_idxOf (insertedNodeId_bound node state)

theorem rawAtom_native (K : ℕ) (kind : RawKind) (central : Bool) (state : RawArena) (closed : RawMoyalClosed state)
    (dependencies : ∀ dep,dep∈kind.dependencies → Handle state dep) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawAtom kind central state).2 (rawAtom kind central state).1 x=
      arenaEvaluate (rawNodeExpression K (expanded K state) kind) x := by
  let node : RawNode:=⟨kind,central⟩
  let next:=rawInternNode node state
  let index:=insertedNodeId node state
  have nextClosed:=rawInternNode_closed node state closed dependencies
  have words : RawWords (fun id=>id < next.nodes.length) [⟨polynomialCoefficient 1,[index]⟩] := by
    intro row member id present
    have hr:=List.mem_singleton.mp member
    subst row
    have hi:=List.mem_singleton.mp present
    subst id
    exact insertedNodeId_bound node state
  change nativePolynomial K (rawPoly [⟨polynomialCoefficient 1,[index]⟩] next).2
    (rawPoly [⟨polynomialCoefficient 1,[index]⟩] next).1 x=_
  rw [rawPoly_native K _ next nextClosed words x hx]
  simp only [rawRowsValue,rawRowValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.prod_cons,List.prod_nil,
    mul_one,add_zero,polynomialCoefficient_source,polynomialSymbol,map_one,Complex.ofReal_one,one_mul]
  unfold nativeNode expandedNode
  rw [show rawNode next index=node from rawInternNode_read node state]
  apply congrArg (fun e=>arenaEvaluate e x)
  apply rawNodeExpression_congr
  intro dep member
  exact expanded_prefix K (rawInternNode_extends node state) closed dep (dependencies dep member)

theorem rawAtom_source_native (K : ℕ) (degree : Fin 2) (slot : Fin 14) (state : RawArena)
    (closed : RawMoyalClosed state) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawAtom (.source degree slot) false state).2 (rawAtom (.source degree slot) false state).1 x=
      (originalLeaf degree.castSucc slot x : ℂ) := by
  rw [rawAtom_native K _ _ state closed (by intro dep member;cases member) x hx]
  rfl

theorem rawAtom_clock_native (K level : ℕ) (axis : Fin 4) (state : RawArena)
    (closed : RawMoyalClosed state) (bound : level < K) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawAtom (.clock level axis) false state).2 (rawAtom (.clock level axis) false state).1 x=
      arenaEvaluate (.clock (Fin.succ ⟨level,bound⟩) axis : ArenaExpression K) x := by
  rw [rawAtom_native K _ _ state closed (by intro dep member;cases member) x hx]
  simp only [rawNodeExpression,dif_pos bound]

theorem rawAtom_clock_actual (K level : ℕ) (axis : Fin 4) (state : RawArena)
    (closed : RawMoyalClosed state) (bound : level < K) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawAtom (.clock level axis) false state).2 (rawAtom (.clock level axis) false state).1 x=
      (PreparationVacuumEngineSource.sourceEngine K axis (Fin.succ ⟨level,bound⟩) x : ℂ) := by
  rw [rawAtom_clock_native K level axis state closed bound x hx,arena_clock_readback]

theorem rawAtom_moyal_native (K r left right : ℕ) (central : Bool) (state : RawArena)
    (closed : RawMoyalClosed state) (leftValid : Handle state left) (rightValid : Handle state right)
    (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawAtom (.moyal r left right) central state).2 (rawAtom (.moyal r left right) central state).1 x=
      complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) x := by
  rw [rawAtom_native K _ _ state closed (by
    intro dep member
    simp only [RawKind.dependencies,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst dep;exact leftValid
    · subst dep;exact rightValid) x hx]
  rfl

theorem native_zero (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state) (initialized : RawInitialized state) :
    nativePolynomial K state 0=0 := by
  funext x
  rw [nativePolynomial_rows K state closed 0 (rawInitialized_positive state initialized) x,
    rawInitialized_zero state initialized]
  rfl

theorem native_one (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state) (initialized : RawInitialized state) :
    nativePolynomial K state 1=1 := by
  funext x
  have bound : Handle state 1 := by
    have size:=initialized.polynomials.length_le
    rw [rawInitial_polynomials] at size
    simp only [List.length_cons,List.length_nil] at size
    omega
  rw [nativePolynomial_rows K state closed 1 bound x,rawInitialized_one state initialized]
  simp only [rawRowsValue,rawRowValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.prod_nil,
    mul_one,add_zero,polynomialCoefficient_source,polynomialSymbol,map_one,Complex.ofReal_one,Pi.one_apply]


open PreparationVacuumMoyalNormalization PreparationVacuumArenaBudget PreparationVacuumArenaRows

def rawHeadRow (state : RawArena) (id : ℕ) : RawRow :=
  (rawRows state id).getD 0 ⟨polynomialCoefficient 0,[]⟩

theorem native_headRow (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state) (id : ℕ)
    (valid : Handle state id) (single : (rawRows state id).length ≤ 1) (x : Phase) :
    nativePolynomial K state id x=rawRowValue (fun node=>nativeNode K state node x) (rawHeadRow state id) x := by
  rw [nativePolynomial_rows K state closed id valid x]
  unfold rawHeadRow
  cases equation : rawRows state id with
  | nil=>
    simp only [List.getD_nil,rawRowsValue,List.map_nil,List.sum_nil,rawRowValue,List.prod_nil,mul_one,
      polynomialCoefficient_source,polynomialSymbol,map_zero,Complex.ofReal_zero]
  | cons row rows=>
    have empty : rows=[] := by
      rw [equation,List.length_cons] at single
      have length : rows.length=0 := by omega
      exact List.length_eq_zero_iff.mp length
    subst rows
    simp only [List.getD_cons_zero,rawRowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

theorem rawStrip_native_split (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state) (id : ℕ)
    (valid : Handle state id) (single : (rawRows state id).length ≤ 1) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K state id x=(rawNumber (rawHeadRow state id) : ℂ)*
      nativePolynomial K (rawStrip id (rawHeadRow state id) state).2 (rawStrip id (rawHeadRow state id) state).1 x := by
  classical
  by_cases numeric : numericCoefficient (rawHeadRow state id).coefficient
  · simp only [rawNumber,rawStrip,if_pos numeric]
    have words : RawWords (fun node=>node < state.nodes.length)
        [⟨polynomialCoefficient 1,(rawHeadRow state id).word⟩] := by
      intro row member node present
      have equal:=List.mem_singleton.mp member
      subst row
      exact rawHead_words state closed id node present
    rw [rawPoly_native K _ state closed words x hx,native_headRow K state closed id valid single x]
    simp only [rawRowsValue,rawRowValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,polynomialCoefficient_source,polynomialSymbol,map_one,Complex.ofReal_one,one_mul,
      numericCoefficient_value _ numeric]
    rfl
  · simp only [rawNumber,rawStrip,if_neg numeric,Rat.cast_one,one_mul]

theorem rawStrip_native_split_germ (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state) (id : ℕ)
    (valid : Handle state id) (single : (rawRows state id).length ≤ 1) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K state id=ᶠ[𝓝 x]
      (fun y=>(rawNumber (rawHeadRow state id) : ℂ)*
        nativePolynomial K (rawStrip id (rawHeadRow state id) state).2 (rawStrip id (rawHeadRow state id) state).1 y) := by
  filter_upwards [poleDomain_open.mem_nhds hx] with y hy
  exact rawStrip_native_split K state closed id valid single y hy

theorem nativePolynomial_smooth (K : ℕ) (state : RawArena) (id : ℕ) : SmoothComplex (nativePolynomial K state id) :=
  arena_smooth (expanded K state id)


-- This is exactly the post-strip branch of RawArena.rawPair.
def pairTail (r left right : ℕ) (scalar : ℚ) : RawAction := fun state=>
  if left=1 ∨ right=1 then (0,state) else
    let ca:=rawCentral state left
    let cb:=rawCentral state right
    let swap:=(!ca && cb)||(ca && cb && decide (left>right))
    let first:=if swap then right else left
    let second:=if swap then left else right
    let factor:=if swap then scalar*(-1)^r else scalar
    if decide (first=second) && ca && decide (r%2=1) then (0,state) else
      let atom:=rawAtom (.moyal r first second) (ca && cb) state
      rawScale (polynomialCoefficient (MvPolynomial.C factor)) atom.1 atom.2

theorem rawPair_tail (r left right : ℕ) (state : RawArena) :
    rawPair r left right state=
      let a:=rawHeadRow state left
      let b:=rawHeadRow state right
      let one:=rawStrip left a state
      let two:=rawStrip right b one.2
      pairTail r one.1 two.1 (rawNumber a*rawNumber b) two.2 := rfl

theorem native_moyal_constant_left (K r id : ℕ) (state : RawArena) (x : Phase) :
    complexMoyal (r+1) (1 : Phase→ℂ) (nativePolynomial K state id) x=0 := by
  exact arena_moyal_constant_left r 1 (expanded K state id) x

theorem native_moyal_constant_right (K r id : ℕ) (state : RawArena) (x : Phase) :
    complexMoyal (r+1) (nativePolynomial K state id) (1 : Phase→ℂ) x=0 := by
  exact arena_moyal_constant_right r 1 (expanded K state id) x

theorem pairTail_native (K r left right : ℕ) (scalar : ℚ) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state)
    (leftValid : Handle state left) (rightValid : Handle state right) (positive : r≠0)
    (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (pairTail r left right scalar state).2 (pairTail r left right scalar state).1 x=
      (scalar : ℂ)*complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) x := by
  by_cases identity : left=1 ∨ right=1
  · simp only [pairTail,if_pos identity]
    rw [native_zero K state closed initialized]
    obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero positive
    rcases identity with hl|hr
    · subst left
      rw [native_one K state closed initialized,native_moyal_constant_left,mul_zero]
      rfl
    · subst right
      rw [native_one K state closed initialized,native_moyal_constant_right,mul_zero]
      rfl
  · simp only [pairTail,if_neg identity]
    let ca:=rawCentral state left
    let cb:=rawCentral state right
    let swap:=(!ca && cb)||(ca && cb && decide (left>right))
    let first:=if swap then right else left
    let second:=if swap then left else right
    let factor:=if swap then scalar*(-1)^r else scalar
    have firstValid : Handle state first := by dsimp only [first];split_ifs <;> assumption
    have secondValid : Handle state second := by dsimp only [second];split_ifs <;> assumption
    have atomClosed : RawMoyalClosed (rawAtom (.moyal r first second) (ca && cb) state).2 :=
      rawAtom_closed _ _ _ closed (by
        intro dep member
        simp only [RawKind.dependencies,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with same|same
        · subst dep;exact firstValid
        · subst dep;exact secondValid)
    change nativePolynomial K
      (if decide (first=second) && ca && decide (r%2=1) then (0,state) else
        let atom:=rawAtom (.moyal r first second) (ca && cb) state
        rawScale (polynomialCoefficient (MvPolynomial.C factor)) atom.1 atom.2).2
      (if decide (first=second) && ca && decide (r%2=1) then (0,state) else
        let atom:=rawAtom (.moyal r first second) (ca && cb) state
        rawScale (polynomialCoefficient (MvPolynomial.C factor)) atom.1 atom.2).1 x=_
    split_ifs with diagonal
    · have hd : (first=second ∧ ca=true) ∧ r%2=1 := by
        simpa only [Bool.and_eq_true,decide_eq_true_eq] using diagonal
      have same : left=right := by
        have h:=hd.1.1
        dsimp only [first,second] at h
        split_ifs at h <;> first | exact h | exact h.symm
      subst right
      have odd : Odd r := Nat.odd_iff.mpr hd.2
      obtain ⟨n,hn⟩:=odd
      have order : r=2*n+1 := by omega
      rw [native_zero K state closed initialized,order]
      have vanish:=arena_moyal_odd_self n (expanded K state left) x
      change (0 : ℂ)=(scalar : ℂ)*complexMoyal (2*n+1) (nativePolynomial K state left) (nativePolynomial K state left) x
      rw [show complexMoyal (2*n+1) (nativePolynomial K state left) (nativePolynomial K state left) x=0 from vanish,mul_zero]
    · rw [rawScale_native K (polynomialCoefficient (MvPolynomial.C factor))
        (rawAtom (.moyal r first second) (ca && cb) state).1
        (rawAtom (.moyal r first second) (ca && cb) state).2 atomClosed (rawPoly_bound _ _) x hx,
        rawAtom_moyal_native K r first second (ca && cb) state closed firstValid secondValid x hx]
      simp only [polynomialCoefficient_source,polynomialSymbol]
      rw [show evalAt x (MvPolynomial.C factor)=(factor : ℝ) by simp [evalAt]]
      simp only [Complex.ofReal_ratCast]
      by_cases swapped : swap=true
      · dsimp only [factor,first,second]
        simp only [swapped,if_true,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_one]
        rw [complexMoyal_swap r (nativePolynomial K state left) (nativePolynomial K state right) x]
        have sign : (-1 : ℂ)^r*(-1 : ℂ)^r=1 := by rw [←mul_pow];norm_num
        calc
          _=(scalar : ℂ)*(((-1 : ℂ)^r*(-1 : ℂ)^r)*complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) x) := by ring
          _=_ := by rw [sign,one_mul]
      · have no : swap=false := Bool.eq_false_iff.mpr swapped
        simp only [factor,first,second,no,Bool.false_eq_true,if_false]


theorem rawHeadRow_prefix {old next : RawArena} (extension : RawExtends old next)
    (id : ℕ) (valid : Handle old id) : rawHeadRow next id=rawHeadRow old id := by
  unfold rawHeadRow
  rw [rawRows_preserved extension id valid]

theorem rawPair_native (K r left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (initialized : RawInitialized state) (leftValid : Handle state left) (rightValid : Handle state right)
    (leftSingle : (rawRows state left).length ≤ 1) (rightSingle : (rawRows state right).length ≤ 1)
    (positive : r≠0) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawPair r left right state).2 (rawPair r left right state).1 x=
      complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) x := by
  let a:=rawHeadRow state left
  let b:=rawHeadRow state right
  let one:=rawStrip left a state
  let two:=rawStrip right b one.2
  have oneClosed : RawMoyalClosed one.2 := rawStrip_closed left a state closed (rawHead_words state closed left)
  have bWords : ∀ node,node∈b.word → node < one.2.nodes.length := by
    rw [show one.2.nodes=state.nodes from rawStrip_nodes _ _ _]
    exact rawHead_words state closed right
  have twoClosed : RawMoyalClosed two.2 := rawStrip_closed right b one.2 oneClosed bWords
  have oneGrows:=rawStrip_extends left a state
  have twoGrows:=rawStrip_extends right b one.2
  have rightOld : Handle one.2 right := handle_extend oneGrows rightValid
  have oneBound : Handle one.2 one.1 := rawStrip_bound left a state leftValid
  have leftFinal : Handle two.2 one.1 := handle_extend twoGrows oneBound
  have rightFinal : Handle two.2 two.1 := rawStrip_bound right b one.2 rightOld
  have leftGerm : nativePolynomial K state left=ᶠ[𝓝 x]
      (fun y=>(rawNumber a : ℂ)*nativePolynomial K two.2 one.1 y) := by
    have h:=rawStrip_native_split_germ K state closed left leftValid leftSingle x hx
    rw [nativePolynomial_prefix K twoGrows oneClosed one.1 oneBound]
    exact h
  have rightGerm : nativePolynomial K state right=ᶠ[𝓝 x]
      (fun y=>(rawNumber b : ℂ)*nativePolynomial K two.2 two.1 y) := by
    have single : (rawRows one.2 right).length ≤ 1 := by rw [rawRows_preserved oneGrows right rightValid];exact rightSingle
    have h:=rawStrip_native_split_germ K one.2 oneClosed right rightOld single x hx
    rw [rawHeadRow_prefix oneGrows right rightValid,nativePolynomial_prefix K oneGrows closed right rightValid] at h
    exact h
  have factorized : complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) x=
      ((rawNumber a : ℂ)*(rawNumber b : ℂ))*complexMoyal r (nativePolynomial K two.2 one.1) (nativePolynomial K two.2 two.1) x := by
    rw [moyal_germ r _ _ _ _ x leftGerm rightGerm]
    rw [moyal_scale_left r (rawNumber a : ℂ) _ _ (nativePolynomial_smooth _ _ _)
      (contDiffOn_const.mul (nativePolynomial_smooth _ _ _)) x hx,
      moyal_scale_right r (rawNumber b : ℂ) _ _ (nativePolynomial_smooth _ _ _) (nativePolynomial_smooth _ _ _) x hx]
    ring
  rw [rawPair_tail]
  change nativePolynomial K (pairTail r one.1 two.1 (rawNumber a*rawNumber b) two.2).2
    (pairTail r one.1 two.1 (rawNumber a*rawNumber b) two.2).1 x=_
  rw [pairTail_native K r one.1 two.1 (rawNumber a*rawNumber b) two.2 twoClosed
    ((initialized.trans oneGrows).trans twoGrows) leftFinal rightFinal positive x hx,Rat.cast_mul]
  exact factorized.symm


theorem rawPair_native_germ (K r left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (initialized : RawInitialized state) (leftValid : Handle state left) (rightValid : Handle state right)
    (leftSingle : (rawRows state left).length ≤ 1) (rightSingle : (rawRows state right).length ≤ 1)
    (positive : r≠0) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawPair r left right state).2 (rawPair r left right state).1=ᶠ[𝓝 x]
      complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) := by
  filter_upwards [poleDomain_open.mem_nhds hx] with y hy
  exact rawPair_native K r left right state closed initialized leftValid rightValid leftSingle rightSingle positive y hy

theorem actual_pair_native_all_jets (order r : ℕ)
    (left right : Fin (originalEngine order).runtime.arena.polynomials.length)
    (leftSingle : (rawRows (originalEngine order).runtime.arena left.val).length ≤ 1)
    (rightSingle : (rawRows (originalEngine order).runtime.arena right.val).length ≤ 1)
    (positive : r≠0) (x : Phase) (hx : x∈poleDomain) (directions : List Phase) :
    complexListJet directions
      (nativePolynomial order (rawPair r left.val right.val (originalEngine order).runtime.arena).2
        (rawPair r left.val right.val (originalEngine order).runtime.arena).1) x=
      complexListJet directions (complexMoyal r
        (nativePolynomial order (originalEngine order).runtime.arena left.val)
        (nativePolynomial order (originalEngine order).runtime.arena right.val)) x :=
  (complexListJet_germ (rawPair_native_germ order r left.val right.val (originalEngine order).runtime.arena
    (originalEngine_graph_closed order) (originalEngine_initialized order) left.isLt right.isLt
    leftSingle rightSingle positive x hx) directions).eq_of_nhds

def originalFiveNative (k : ℕ) (i : Fin 5) : Phase → ℂ :=
  nativePolynomial (k+1) (originalEngine (k+1)).runtime.arena (originalFiveId k i)

theorem originalFiveNative_rows (k : ℕ) (i : Fin 5) (x : Phase) :
    originalFiveNative k i x=
      rawRowsValue (fun node=>nativeNode (k+1) (originalEngine (k+1)).runtime.arena node x) (originalFiveRows k i) x :=
  nativePolynomial_rows (k+1) _ (originalEngine_graph_closed (k+1)) _ (originalFive_handle k i) x

end LowEnergy.PreparationVacuumExecutionGraph
