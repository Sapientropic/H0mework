import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationMemoEngineCache

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSetupValues
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumNativeMemo
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumClockSymbol
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineSource PreparationVacuumArenaBudget PreparationVacuumArenaRows
open scoped BigOperators Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def angleExponent (u : RawAngle) : AngularExponent := Finsupp.equivFunOnFinite.symm u

@[simp] theorem angleExponent_apply (u : RawAngle) (j : Fin 3) : angleExponent u j=u j := rfl

theorem angleExponent_injective : Function.Injective angleExponent := by
  intro u v same
  funext j
  exact congrArg (fun a : AngularExponent=>a j) same

def angularValue (K : ℕ) (state : RawArena) (rows : RawAngular) (u : RawAngle) : Phase → ℂ := by
  classical
  exact fun x=>(rows.map (fun row=>if row.1=u then nativePolynomial K state row.2 x else 0)).sum

def seriesValue (K : ℕ) (state : RawArena) (rows : RawSeries) : List (RawAngle → Phase → ℂ) :=
  rows.map (angularValue K state)

@[simp] theorem angularValue_nil (K : ℕ) (state : RawArena) (u : RawAngle) (x : Phase) :
    angularValue K state [] u x=0 := rfl

theorem angularValue_cons (K : ℕ) (state : RawArena) (row : RawAngle × ℕ) (rows : RawAngular) (u : RawAngle) (x : Phase) :
    angularValue K state (row::rows) u x=(if row.1=u then nativePolynomial K state row.2 x else 0)+angularValue K state rows u x := by
  classical
  rfl

theorem angularValue_perm (K : ℕ) (state : RawArena) {left right : RawAngular} (same : left.Perm right) :
    angularValue K state left=angularValue K state right := by
  classical
  funext u x
  exact (same.map (fun row=>if row.1=u then nativePolynomial K state row.2 x else 0)).sum_eq

theorem angularValue_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (rows : RawAngular) (valid : AngularHandles old rows) :
    angularValue K next rows=angularValue K old rows := by
  classical
  funext u x
  unfold angularValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro row member
  split_ifs
  · exact congrFun (nativePolynomial_prefix K extension closed row.2 (valid row member)) x
  · rfl

theorem seriesValue_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (rows : RawSeries) (valid : SeriesHandles old rows) :
    seriesValue K next rows=seriesValue K old rows := by
  unfold seriesValue
  apply List.map_congr_left
  intro polynomial member
  exact angularValue_prefix K extension closed polynomial (valid polynomial member)

def angleTriple (u : RawAngle) : ℕ × ℕ × ℕ := (u 0,u 1,u 2)
def tripleAngle (u : ℕ × ℕ × ℕ) : RawAngle := ![u.1,u.2.1,u.2.2]

@[simp] theorem tripleAngle_angleTriple (u : RawAngle) : tripleAngle (angleTriple u)=u := by
  funext j
  fin_cases j <;> rfl

@[simp] theorem angleTriple_tripleAngle (u : ℕ × ℕ × ℕ) : angleTriple (tripleAngle u)=u := rfl

def decodeKeyPolynomial (key : List ((ℕ × ℕ × ℕ) × ℕ)) : RawAngular :=
  key.map (fun row=>(tripleAngle row.1,row.2))

def decodeSeriesKey (key : SeriesKey) : RawSeries := key.map decodeKeyPolynomial

theorem keyPolynomial_perm (rows : RawAngular) :
    (decodeKeyPolynomial ((rows.map (fun row=>(angleTriple row.1,row.2))).mergeSort
      (fun a b=>decide (List.Lex (· < ·) (seriesEntryWord a) (seriesEntryWord b) ∨ seriesEntryWord a=seriesEntryWord b)))).Perm rows := by
  have perm:=(List.mergeSort_perm (rows.map (fun row=>(angleTriple row.1,row.2)))
    (fun a b=>decide (List.Lex (· < ·) (seriesEntryWord a) (seriesEntryWord b) ∨ seriesEntryWord a=seriesEntryWord b))).map
      (fun row=>(tripleAngle row.1,row.2))
  have identity : ((fun row : (ℕ × ℕ × ℕ) × ℕ=>(tripleAngle row.1,row.2)) ∘
      fun row : RawAngle × ℕ=>(angleTriple row.1,row.2))=id := by
    funext row
    simp only [Function.comp_def,tripleAngle_angleTriple]
    rfl
  rw [List.map_map,identity,List.map_id] at perm
  exact perm

theorem seriesKey_value (K : ℕ) (state : RawArena) (rows : RawSeries) :
    seriesValue K state (decodeSeriesKey (seriesKey rows))=seriesValue K state rows := by
  unfold seriesValue decodeSeriesKey seriesKey
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro polynomial member
  exact angularValue_perm K state (keyPolynomial_perm polynomial)

theorem seriesKey_same_input (K : ℕ) (state : RawArena) (left right : RawSeries)
    (same : seriesKey left=seriesKey right) : seriesValue K state left=seriesValue K state right := by
  rw [←seriesKey_value K state left,same,seriesKey_value]

def UniqueAngles (rows : RawAngular) : Prop := (rows.map Prod.fst).Nodup

theorem angularInsert_keys (key : RawAngle) (id : ℕ) (rows : RawAngular) :
    (angularInsert key id rows).map Prod.fst=
      if key∈rows.map Prod.fst then rows.map Prod.fst else rows.map Prod.fst++[key] := by
  classical
  induction rows with
  | nil=>simp [angularInsert]
  | cons head tail ih=>
    by_cases same : head.1=key
    · subst key
      simp [angularInsert]
    · simp only [angularInsert,if_neg same,List.map_cons]
      change head.1::((angularInsert key id tail).map Prod.fst)=_
      rw [ih]
      by_cases member : key∈tail.map Prod.fst
      · simp [member,Ne.symm same]
      · simp [member,Ne.symm same]

theorem angularInsert_unique (key : RawAngle) (id : ℕ) (rows : RawAngular) (unique : UniqueAngles rows) :
    UniqueAngles (angularInsert key id rows) := by
  classical
  unfold UniqueAngles
  rw [angularInsert_keys]
  split_ifs with member
  · exact unique
  · rw [List.nodup_append]
    refine ⟨unique,by simp,?_⟩
    intro a ha b hb same
    exact member ((same.trans (List.mem_singleton.mp hb)) ▸ ha)

theorem angularValue_absent (K : ℕ) (state : RawArena) (rows : RawAngular) (u : RawAngle)
    (absent : u∉rows.map Prod.fst) (x : Phase) : angularValue K state rows u x=0 := by
  classical
  unfold angularValue
  apply List.sum_eq_zero
  intro value member
  obtain ⟨row,hr,rfl⟩:=List.mem_map.mp member
  have different : row.1≠u := by
    intro same
    exact absent (same ▸ List.mem_map.mpr ⟨row,hr,rfl⟩)
  simp only [if_neg different]

theorem angularLookup_insert (key wanted : RawAngle) (id : ℕ) (rows : RawAngular) :
    angularLookup wanted (angularInsert key id rows)=if wanted=key then id else angularLookup wanted rows := by
  classical
  induction rows with
  | nil=>
    by_cases same : wanted=key <;> simp [angularInsert,angularLookup,same,eq_comm]
  | cons head tail ih=>
    by_cases same : head.1=key
    · by_cases wantedSame : wanted=key
      · subst wanted;simp [angularInsert,angularLookup,same]
      · simp [angularInsert,angularLookup,same,wantedSame,Ne.symm wantedSame]
    · by_cases wantedHead : head.1=wanted
      · have different : wanted≠key := by intro h;exact same (wantedHead.trans h)
        simp [angularInsert,angularLookup,wantedHead,different]
      · simp only [angularInsert,if_neg same]
        change angularLookup wanted (head::angularInsert key id tail)=_
        have skip (xs : RawAngular) : angularLookup wanted (head::xs)=angularLookup wanted xs := by
          simp [angularLookup,wantedHead]
        rw [skip,ih,skip]


theorem angularValue_lookup (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (initialized : RawInitialized state) (rows : RawAngular) (unique : UniqueAngles rows) (u : RawAngle) (x : Phase) :
    angularValue K state rows u x=nativePolynomial K state (angularLookup u rows) x := by
  classical
  induction rows with
  | nil=>
    change 0=nativePolynomial K state 0 x
    rw [native_zero K state closed initialized]
    rfl
  | cons head tail ih=>
    have pair : head.1∉tail.map Prod.fst ∧ UniqueAngles tail := List.nodup_cons.mp unique
    by_cases same : head.1=u
    · have absent : u∉tail.map Prod.fst := same ▸ pair.1
      rw [angularValue_cons,if_pos same,angularValue_absent K state tail u absent x,add_zero]
      simp [angularLookup,same]
    · rw [angularValue_cons,if_neg same,zero_add,ih pair.2]
      simp [angularLookup,same]

theorem angularInsert_value (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (initialized : RawInitialized state) (rows : RawAngular) (unique : UniqueAngles rows)
    (key : RawAngle) (id : ℕ) (u : RawAngle) (x : Phase) :
    angularValue K state (angularInsert key id rows) u x=
      if u=key then nativePolynomial K state id x else angularValue K state rows u x := by
  classical
  rw [angularValue_lookup K state closed initialized _ (angularInsert_unique key id rows unique) u x,
    angularLookup_insert]
  split_ifs
  · rfl
  · exact (angularValue_lookup K state closed initialized rows unique u x).symm

theorem angularNonzero_value (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (initialized : RawInitialized state) (rows : RawAngular) :
    angularValue K state (angularNonzero rows)=angularValue K state rows := by
  classical
  funext u x
  induction rows with
  | nil=>rfl
  | cons row rows ih=>
    by_cases zero : row.2=0
    · simp [angularNonzero,zero,angularValue_cons,native_zero K state closed initialized]
      simpa [angularNonzero] using ih
    · simp [angularNonzero,zero,angularValue_cons]
      simpa [angularNonzero] using ih

theorem angularNonzero_unique (rows : RawAngular) (unique : UniqueAngles rows) : UniqueAngles (angularNonzero rows) :=
  ((List.filter_sublist (p:=fun row : RawAngle × ℕ=>decide (row.2≠0)) (l:=rows)).map Prod.fst).nodup unique

theorem angularLookup_bound (state : RawArena) (initialized : RawInitialized state)
    (rows : RawAngular) (valid : AngularHandles state rows) (u : RawAngle) : Handle state (angularLookup u rows) := by
  classical
  unfold angularLookup
  cases found : rows.find? (fun row=>row.1=u) with
  | none=>exact rawInitialized_positive state initialized
  | some row=>exact valid row (List.mem_of_find?_eq_some found)


theorem angularValue_smooth (K : ℕ) (state : RawArena) (rows : RawAngular) (u : RawAngle) :
    SmoothComplex (angularValue K state rows u) := by
  classical
  induction rows with
  | nil=>exact contDiffOn_const
  | cons row rows ih=>
    have formula : angularValue K state (row::rows) u=(fun x=>(if row.1=u then nativePolynomial K state row.2 x else 0)+angularValue K state rows u x) :=
      funext (fun x=>angularValue_cons K state row rows u x)
    rw [formula]
    by_cases same : row.1=u
    · simp only [if_pos same]
      exact (nativePolynomial_smooth _ _ _).add ih
    · simp only [if_neg same,zero_add]
      exact ih

theorem angleExponent_add (u v : RawAngle) : angleExponent (u+v)=angleExponent u+angleExponent v := by
  ext j
  rfl

theorem angleExponent_zero : angleExponent angleZero=0 := by ext j;rfl

theorem angleExponent_unit (j : Fin 3) : angleExponent (angleUnit j)=Finsupp.single j 1 := by
  ext i
  simp [angleExponent_apply,angleUnit,Finsupp.single_apply,eq_comm]

theorem rawMoment_source (u : RawAngle) : (rawMoment u : ℝ)=angularMoment (angleExponent u) := by
  classical
  unfold rawMoment angularMoment
  simp only [angleExponent_apply]
  split_ifs
  · push_cast
    rfl
  · simp only [Rat.cast_zero]


def angularAddStep (out : RawAngular × RawArena) (row : RawAngle × ℕ) : RawAngular × RawArena :=
  let added:=rawAdd [angularLookup row.1 out.1,row.2] out.2
  (angularInsert row.1 added.1 out.1,added.2)

theorem angularAdd_as_fold (inputs : List RawAngular) (state : RawArena) :
    angularAdd inputs state=
      let result:=inputs.flatten.foldl angularAddStep ([],state)
      (angularNonzero result.1,result.2) := rfl

theorem angularAddStep_grows (out : RawAngular × RawArena) (row : RawAngle × ℕ) :
    RawExtends out.2 (angularAddStep out row).2 := rawAdd_extends _ _

theorem angularAddStep_properties (out : RawAngular × RawArena) (row : RawAngle × ℕ)
    (closed : RawMoyalClosed out.2) (initialized : RawInitialized out.2)
    (unique : UniqueAngles out.1) (valid : AngularHandles out.2 out.1) :
    RawMoyalClosed (angularAddStep out row).2 ∧ RawInitialized (angularAddStep out row).2 ∧
      UniqueAngles (angularAddStep out row).1 ∧ AngularHandles (angularAddStep out row).2 (angularAddStep out row).1 :=
  ⟨rawAdd_closed _ _ closed,initialized.trans (rawAdd_extends _ _),angularInsert_unique _ _ _ unique,
    angularInsert_handles (angular_extend (rawAdd_extends _ _) valid) _ _ (rawPoly_bound _ _)⟩

theorem angularAddStep_value (K : ℕ) (out : RawAngular × RawArena) (row : RawAngle × ℕ)
    (closed : RawMoyalClosed out.2) (initialized : RawInitialized out.2)
    (unique : UniqueAngles out.1) (valid : AngularHandles out.2 out.1) (rowValid : Handle out.2 row.2)
    (u : RawAngle) (x : Phase) (hx : x∈poleDomain) :
    angularValue K (angularAddStep out row).2 (angularAddStep out row).1 u x=
      angularValue K out.2 out.1 u x+(if row.1=u then nativePolynomial K out.2 row.2 x else 0) := by
  classical
  let added:=rawAdd [angularLookup row.1 out.1,row.2] out.2
  have growth : RawExtends out.2 added.2 := rawAdd_extends _ _
  have bounds : ListHandles out.2 [angularLookup row.1 out.1,row.2] := by
    intro id member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with equal|equal
    · subst id;exact angularLookup_bound out.2 initialized out.1 valid row.1
    · subst id;exact rowValid
  have generated:=rawAdd_native K [angularLookup row.1 out.1,row.2] out.2 closed bounds x hx
  change angularValue K added.2 (angularInsert row.1 added.1 out.1) u x=_
  rw [angularInsert_value K added.2 (rawAdd_closed _ _ closed) (initialized.trans growth) out.1 unique]
  by_cases same : u=row.1
  · subst u
    simp only [ite_true]
    rw [show nativePolynomial K added.2 added.1 x=nativePolynomial K out.2 (angularLookup row.1 out.1) x+
      nativePolynomial K out.2 row.2 x by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using generated]
    rw [angularValue_lookup K out.2 closed initialized out.1 unique row.1 x]
  · rw [if_neg same,if_neg (Ne.symm same),add_zero,
      angularValue_prefix K growth closed out.1 valid]

theorem angularAddFold_value (K : ℕ) (items : RawAngular) (initial : RawAngular × RawArena)
    (closed : RawMoyalClosed initial.2) (initialized : RawInitialized initial.2)
    (unique : UniqueAngles initial.1) (valid : AngularHandles initial.2 initial.1)
    (itemsValid : AngularHandles initial.2 items) :
    let result:=items.foldl angularAddStep initial
    RawMoyalClosed result.2 ∧ RawInitialized result.2 ∧ UniqueAngles result.1 ∧ AngularHandles result.2 result.1 ∧
      ∀ u x,x∈poleDomain → angularValue K result.2 result.1 u x=
        angularValue K initial.2 initial.1 u x+angularValue K initial.2 items u x := by
  induction items generalizing initial with
  | nil=>
    refine ⟨closed,initialized,unique,valid,?_⟩
    intro u x hx
    rw [angularValue_nil,add_zero]
    rfl
  | cons row items ih=>
    have step:=angularAddStep_properties initial row closed initialized unique valid
    have growth:=angularAddStep_grows initial row
    have tailValid : AngularHandles initial.2 items := fun r hr=>itemsValid r (List.mem_cons_of_mem _ hr)
    have result:=ih (angularAddStep initial row) step.1 step.2.1 step.2.2.1 step.2.2.2 (angular_extend growth tailValid)
    refine ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,?_⟩
    intro u x hx
    change angularValue K (items.foldl angularAddStep (angularAddStep initial row)).2
      (items.foldl angularAddStep (angularAddStep initial row)).1 u x=_
    rw [result.2.2.2.2 u x hx,
      angularAddStep_value K initial row closed initialized unique valid (itemsValid row (by simp)) u x hx,
      angularValue_prefix K growth closed items tailValid,angularValue_cons]
    exact add_assoc _ _ _

theorem angularValue_flatten (K : ℕ) (state : RawArena) (inputs : List RawAngular) (u : RawAngle) (x : Phase) :
    angularValue K state inputs.flatten u x=(inputs.map (fun rows=>angularValue K state rows u x)).sum := by
  classical
  induction inputs with
  | nil=>rfl
  | cons rows inputs ih=>
    simp only [List.flatten_cons,angularValue,List.map_append,List.sum_append,List.map_cons,List.sum_cons] at ih ⊢
    exact congrArg ((rows.map (fun row=>if row.1=u then nativePolynomial K state row.2 x else 0)).sum+·) ih

theorem angularAdd_native (K : ℕ) (inputs : List RawAngular) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state)
    (valid : ∀ rows,rows∈inputs → AngularHandles state rows) :
    UniqueAngles (angularAdd inputs state).1 ∧
      ∀ u x,x∈poleDomain → angularValue K (angularAdd inputs state).2 (angularAdd inputs state).1 u x=
        (inputs.map (fun rows=>angularValue K state rows u x)).sum := by
  have flattened : AngularHandles state inputs.flatten := by
    intro row member
    obtain ⟨rows,hrows,hrow⟩:=List.mem_flatten.mp member
    exact valid rows hrows row hrow
  have result:=angularAddFold_value K inputs.flatten ([],state) closed initialized (by simp [UniqueAngles])
    (fun row member=>False.elim (List.not_mem_nil member)) flattened
  rw [angularAdd_as_fold]
  refine ⟨angularNonzero_unique _ result.2.2.1,?_⟩
  intro u x hx
  rw [angularNonzero_value K _ result.1 result.2.1,result.2.2.2.2 u x hx,angularValue_nil,zero_add,angularValue_flatten]


theorem angularValue_append (K : ℕ) (state : RawArena) (left right : RawAngular) (u : RawAngle) (x : Phase) :
    angularValue K state (left++right) u x=angularValue K state left u x+angularValue K state right u x := by
  classical
  simp only [angularValue,List.map_append,List.sum_append]

def angularScaleStep (c : NormalizedCoefficient) (out : RawAngular × RawArena) (row : RawAngle × ℕ) : RawAngular × RawArena :=
  let tested:=rawScale c row.2 out.2
  if tested.1=0 then (out.1,tested.2) else
    let value:=rawScale c row.2 tested.2
    (out.1++[(row.1,value.1)],value.2)

theorem angularScale_as_fold (c : NormalizedCoefficient) (rows : RawAngular) (state : RawArena) :
    angularScale c rows state=rows.foldl (angularScaleStep c) ([],state) := rfl

theorem angularScaleStep_grows (c : NormalizedCoefficient) (out : RawAngular × RawArena) (row : RawAngle × ℕ) :
    RawExtends out.2 (angularScaleStep c out row).2 := by
  dsimp only [angularScaleStep]
  split_ifs
  · exact rawScale_extends _ _ _
  · exact (rawScale_extends _ _ _).trans (rawScale_extends _ _ _)

theorem angularScaleStep_properties (c : NormalizedCoefficient) (out : RawAngular × RawArena) (row : RawAngle × ℕ)
    (closed : RawMoyalClosed out.2) (initialized : RawInitialized out.2) (valid : AngularHandles out.2 out.1) :
    RawMoyalClosed (angularScaleStep c out row).2 ∧ RawInitialized (angularScaleStep c out row).2 ∧
      AngularHandles (angularScaleStep c out row).2 (angularScaleStep c out row).1 := by
  dsimp only [angularScaleStep]
  split_ifs
  · exact ⟨rawScale_closed _ _ _ closed,initialized.trans (rawScale_extends _ _ _),angular_extend (rawScale_extends _ _ _) valid⟩
  · refine ⟨rawScale_closed _ _ _ (rawScale_closed _ _ _ closed),
      (initialized.trans (rawScale_extends _ _ _)).trans (rawScale_extends _ _ _),?_⟩
    intro result member
    rcases List.mem_append.mp member with old|fresh
    · exact angular_extend ((rawScale_extends _ _ _).trans (rawScale_extends _ _ _)) valid result old
    · have same:=List.mem_singleton.mp fresh
      subst result
      exact rawPoly_bound _ _

theorem angularScaleStep_value (K : ℕ) (c : NormalizedCoefficient) (out : RawAngular × RawArena) (row : RawAngle × ℕ)
    (closed : RawMoyalClosed out.2) (initialized : RawInitialized out.2) (valid : AngularHandles out.2 out.1)
    (rowValid : Handle out.2 row.2) (u : RawAngle) (x : Phase) (hx : x∈poleDomain) :
    angularValue K (angularScaleStep c out row).2 (angularScaleStep c out row).1 u x=
      angularValue K out.2 out.1 u x+(if row.1=u then (coefficientValue c x : ℂ)*nativePolynomial K out.2 row.2 x else 0) := by
  classical
  let tested:=rawScale c row.2 out.2
  let value:=rawScale c row.2 tested.2
  have firstGrow : RawExtends out.2 tested.2 := rawScale_extends _ _ _
  have secondGrow : RawExtends tested.2 value.2 := rawScale_extends _ _ _
  have firstClosed : RawMoyalClosed tested.2 := rawScale_closed _ _ _ closed
  have firstNative : nativePolynomial K tested.2 tested.1 x=(coefficientValue c x : ℂ)*nativePolynomial K out.2 row.2 x :=
    rawScale_native K c row.2 out.2 closed rowValid x hx
  dsimp only [angularScaleStep]
  by_cases zero : tested.1=0
  · have hz : (rawScale c row.2 out.2).1=0 := zero
    rw [if_pos hz]
    change angularValue K tested.2 out.1 u x=_
    have vanished : (coefficientValue c x : ℂ)*nativePolynomial K out.2 row.2 x=0 := by
      rw [zero,native_zero K tested.2 firstClosed (initialized.trans firstGrow)] at firstNative
      exact firstNative.symm
    rw [angularValue_prefix K firstGrow closed out.1 valid,vanished]
    simp
  · have hz : (rawScale c row.2 out.2).1≠0 := zero
    rw [if_neg hz]
    change angularValue K value.2 (out.1++[(row.1,value.1)]) u x=_
    rw [angularValue_append,angularValue_prefix K (firstGrow.trans secondGrow) closed out.1 valid,
      angularValue_cons,angularValue_nil,add_zero]
    have secondNative : nativePolynomial K value.2 value.1 x=(coefficientValue c x : ℂ)*nativePolynomial K out.2 row.2 x := by
      rw [show nativePolynomial K value.2 value.1 x=(coefficientValue c x : ℂ)*nativePolynomial K tested.2 row.2 x from
        rawScale_native K c row.2 tested.2 firstClosed (handle_extend firstGrow rowValid) x hx,
        nativePolynomial_prefix K firstGrow closed row.2 rowValid]
    rw [secondNative]

theorem angularScaleFold_value (K : ℕ) (c : NormalizedCoefficient) (items : RawAngular) (initial : RawAngular × RawArena)
    (closed : RawMoyalClosed initial.2) (initialized : RawInitialized initial.2)
    (valid : AngularHandles initial.2 initial.1) (itemsValid : AngularHandles initial.2 items) :
    let result:=items.foldl (angularScaleStep c) initial
    RawMoyalClosed result.2 ∧ RawInitialized result.2 ∧ AngularHandles result.2 result.1 ∧
      ∀ u x,x∈poleDomain → angularValue K result.2 result.1 u x=
        angularValue K initial.2 initial.1 u x+(coefficientValue c x : ℂ)*angularValue K initial.2 items u x := by
  induction items generalizing initial with
  | nil=>
    refine ⟨closed,initialized,valid,?_⟩
    intro u x hx
    rw [angularValue_nil,mul_zero,add_zero]
    rfl
  | cons row items ih=>
    have step:=angularScaleStep_properties c initial row closed initialized valid
    have growth:=angularScaleStep_grows c initial row
    have tailValid : AngularHandles initial.2 items := fun r hr=>itemsValid r (List.mem_cons_of_mem _ hr)
    have result:=ih (angularScaleStep c initial row) step.1 step.2.1 step.2.2 (angular_extend growth tailValid)
    refine ⟨result.1,result.2.1,result.2.2.1,?_⟩
    intro u x hx
    change angularValue K (items.foldl (angularScaleStep c) (angularScaleStep c initial row)).2
      (items.foldl (angularScaleStep c) (angularScaleStep c initial row)).1 u x=_
    rw [result.2.2.2 u x hx,
      angularScaleStep_value K c initial row closed initialized valid (itemsValid row (by simp)) u x hx,
      angularValue_prefix K growth closed items tailValid,angularValue_cons]
    split_ifs <;> ring

theorem angularScale_native (K : ℕ) (c : NormalizedCoefficient) (input : RawAngular) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) (valid : AngularHandles state input)
    (u : RawAngle) (x : Phase) (hx : x∈poleDomain) :
    angularValue K (angularScale c input state).2 (angularScale c input state).1 u x=
      (coefficientValue c x : ℂ)*angularValue K state input u x := by
  have result:=angularScaleFold_value K c input ([],state) closed initialized
    (fun row member=>False.elim (List.not_mem_nil member)) valid
  rw [angularScale_as_fold,result.2.2.2 u x hx,angularValue_nil,zero_add]


theorem angularScaleFold_keys (c : NormalizedCoefficient) (items : RawAngular) (initial : RawAngular × RawArena) :
    ((items.foldl (angularScaleStep c) initial).1.map Prod.fst).Sublist
      (initial.1.map Prod.fst++items.map Prod.fst) := by
  induction items generalizing initial with
  | nil=>simp
  | cons row items ih=>
    change ((items.foldl (angularScaleStep c) (angularScaleStep c initial row)).1.map Prod.fst).Sublist _
    have tail:=ih (angularScaleStep c initial row)
    dsimp only [angularScaleStep] at tail ⊢
    split_ifs at tail ⊢
    · exact tail.trans ((List.sublist_cons_self row.1 (items.map Prod.fst)).append_left (initial.1.map Prod.fst))
    · simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using tail

theorem angularScale_unique (c : NormalizedCoefficient) (rows : RawAngular) (state : RawArena)
    (unique : UniqueAngles rows) : UniqueAngles (angularScale c rows state).1 := by
  rw [angularScale_as_fold]
  have keys:=angularScaleFold_keys c rows ([],state)
  simp only [List.map_nil,List.nil_append] at keys
  exact keys.nodup unique

theorem angularShift_native (K : ℕ) (state : RawArena) (rows : RawAngular) (shift u : RawAngle) (x : Phase) :
    angularValue K state (angularShift rows shift) u x=
      (rows.map (fun row=>if row.1+shift=u then nativePolynomial K state row.2 x else 0)).sum := by
  classical
  simp only [angularValue,angularShift,List.map_map,Function.comp_def]

theorem angularShift_unique (rows : RawAngular) (shift : RawAngle) (unique : UniqueAngles rows) :
    UniqueAngles (angularShift rows shift) := by
  change ((rows.map (fun row=>(row.1+shift,row.2))).map Prod.fst).Nodup
  simpa only [List.map_map,Function.comp_def] using
    unique.map (f:=fun u=>u+shift) (fun _ _ same=>add_right_cancel same)

def weightedStep (r : ℕ) (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ)) :
    RawAngular × RawRuntime :=
  let key:=pair.1.1+pair.2.1
  let product:=memoJordan r pair.1.2 pair.2.2 out.2
  let added:=runArena (rawAdd [angularLookup key out.1,product.1]) product.2
  (angularInsert key added.1 out.1,added.2)

theorem runtimeWeighted_as_fold (r : ℕ) (left right : RawAngular) (runtime : RawRuntime) :
    runtimeWeighted r left right runtime=
      let result:=(left.flatMap (fun a=>right.map (fun b=>(a,b)))).foldl (weightedStep r) ([],runtime)
      (angularNonzero result.1,result.2) := rfl

def jordanValue (K r : ℕ) (state : RawArena) (left right : ℕ) : Phase → ℂ := fun x=>
  (1/2 : ℂ)*(complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) x+
    complexMoyal r (nativePolynomial K state right) (nativePolynomial K state left) x)

theorem jordanValue_prefix (K r : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (left right : ℕ) (leftValid : Handle old left) (rightValid : Handle old right) :
    jordanValue K r next left right=jordanValue K r old left right := by
  unfold jordanValue
  rw [nativePolynomial_prefix K extension closed left leftValid,nativePolynomial_prefix K extension closed right rightValid]

theorem weightedStep_grows (r : ℕ) (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ)) :
    RawExtends out.2.arena (weightedStep r out pair).2.arena :=
  (memoJordan_grows r pair.1.2 pair.2.2 out.2).trans (rawAdd_extends _ _)

theorem weightedStep_properties (K r : ℕ) (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ))
    (cached : CachedNative K out.2) (unique : UniqueAngles out.1) (valid : AngularHandles out.2.arena out.1)
    (leftValid : Handle out.2.arena pair.1.2) (rightValid : Handle out.2.arena pair.2.2) :
    CachedNative K (weightedStep r out pair).2 ∧ UniqueAngles (weightedStep r out pair).1 ∧
      AngularHandles (weightedStep r out pair).2.arena (weightedStep r out pair).1 := by
  let product:=memoJordan r pair.1.2 pair.2.2 out.2
  let added:=runArena (rawAdd [angularLookup (pair.1.1+pair.2.1) out.1,product.1]) product.2
  have hp:=memoJordan_native K r pair.1.2 pair.2.2 out.2 cached leftValid rightValid
  have ha:=runAdd_cached [angularLookup (pair.1.1+pair.2.1) out.1,product.1] product.2 hp.1
  exact ⟨ha.1,angularInsert_unique _ _ _ unique,
    angularInsert_handles (angular_extend (weightedStep_grows r out pair) valid) _ _ ha.2⟩

theorem weightedStep_value (K r : ℕ) (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ))
    (cached : CachedNative K out.2) (unique : UniqueAngles out.1) (valid : AngularHandles out.2.arena out.1)
    (leftValid : Handle out.2.arena pair.1.2) (rightValid : Handle out.2.arena pair.2.2)
    (u : RawAngle) (x : Phase) (hx : x∈poleDomain) :
    angularValue K (weightedStep r out pair).2.arena (weightedStep r out pair).1 u x=
      angularValue K out.2.arena out.1 u x+
        if pair.1.1+pair.2.1=u then jordanValue K r out.2.arena pair.1.2 pair.2.2 x else 0 := by
  let product:=memoJordan r pair.1.2 pair.2.2 out.2
  have hp:=memoJordan_native K r pair.1.2 pair.2.2 out.2 cached leftValid rightValid
  have growth : RawExtends out.2.arena product.2.arena := memoJordan_grows _ _ _ _
  change angularValue K
    (angularAddStep (out.1,product.2.arena) (pair.1.1+pair.2.1,product.1)).2
    (angularAddStep (out.1,product.2.arena) (pair.1.1+pair.2.1,product.1)).1 u x=_
  rw [angularAddStep_value K _ _ hp.1.handles.closed hp.1.handles.initialized unique
    (angular_extend growth valid) hp.2.1 u x hx,angularValue_prefix K growth cached.handles.closed out.1 valid,hp.2.2 x hx]
  rfl

theorem weightedFold_value (K r : ℕ) (pairs : List ((RawAngle × ℕ) × (RawAngle × ℕ))) (initial : RawAngular × RawRuntime)
    (cached : CachedNative K initial.2) (unique : UniqueAngles initial.1) (valid : AngularHandles initial.2.arena initial.1)
    (inputs : ∀ pair,pair∈pairs → Handle initial.2.arena pair.1.2 ∧ Handle initial.2.arena pair.2.2) :
    let result:=pairs.foldl (weightedStep r) initial
    CachedNative K result.2 ∧ UniqueAngles result.1 ∧ AngularHandles result.2.arena result.1 ∧
      ∀ u x,x∈poleDomain → angularValue K result.2.arena result.1 u x=
        angularValue K initial.2.arena initial.1 u x+
          (pairs.map (fun pair=>if pair.1.1+pair.2.1=u then jordanValue K r initial.2.arena pair.1.2 pair.2.2 x else 0)).sum := by
  classical
  induction pairs generalizing initial with
  | nil=>
    refine ⟨cached,unique,valid,?_⟩
    intro u x hx
    simp only [List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
  | cons pair pairs ih=>
    have ip:=inputs pair (by simp)
    have step:=weightedStep_properties K r initial pair cached unique valid ip.1 ip.2
    have growth:=weightedStep_grows r initial pair
    have tailInputs : ∀ p,p∈pairs → Handle initial.2.arena p.1.2 ∧ Handle initial.2.arena p.2.2 :=
      fun p hp=>inputs p (List.mem_cons_of_mem _ hp)
    have result:=ih (weightedStep r initial pair) step.1 step.2.1 step.2.2
      (fun p hp=>⟨handle_extend growth (tailInputs p hp).1,handle_extend growth (tailInputs p hp).2⟩)
    refine ⟨result.1,result.2.1,result.2.2.1,?_⟩
    intro u x hx
    change angularValue K (pairs.foldl (weightedStep r) (weightedStep r initial pair)).2.arena
      (pairs.foldl (weightedStep r) (weightedStep r initial pair)).1 u x=_
    rw [result.2.2.2 u x hx,weightedStep_value K r initial pair cached unique valid ip.1 ip.2 u x hx]
    have same : (pairs.map (fun p=>if p.1.1+p.2.1=u then jordanValue K r (weightedStep r initial pair).2.arena p.1.2 p.2.2 x else 0))=
        pairs.map (fun p=>if p.1.1+p.2.1=u then jordanValue K r initial.2.arena p.1.2 p.2.2 x else 0) := by
      apply List.map_congr_left
      intro p hp
      rw [jordanValue_prefix K r growth cached.handles.closed p.1.2 p.2.2 (tailInputs p hp).1 (tailInputs p hp).2]
    rw [same]
    simp only [List.map_cons,List.sum_cons]
    exact add_assoc _ _ _

theorem runtimeWeighted_native (K r : ℕ) (left right : RawAngular) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (leftValid : AngularHandles runtime.arena left) (rightValid : AngularHandles runtime.arena right) :
    UniqueAngles (runtimeWeighted r left right runtime).1 ∧
      ∀ u x,x∈poleDomain → angularValue K (runtimeWeighted r left right runtime).2.arena (runtimeWeighted r left right runtime).1 u x=
        ((left.flatMap (fun a=>right.map (fun b=>(a,b)))).map
          (fun pair=>if pair.1.1+pair.2.1=u then jordanValue K r runtime.arena pair.1.2 pair.2.2 x else 0)).sum := by
  have result:=weightedFold_value K r (left.flatMap (fun a=>right.map (fun b=>(a,b)))) ([],runtime)
    cached (by simp [UniqueAngles]) (fun row member=>False.elim (List.not_mem_nil member)) (by
      intro pair member
      obtain ⟨a,ha,hm⟩:=List.mem_flatMap.mp member
      obtain ⟨b,hb,same⟩:=List.mem_map.mp hm
      subst pair
      exact ⟨leftValid a ha,rightValid b hb⟩)
  rw [runtimeWeighted_as_fold]
  refine ⟨angularNonzero_unique _ result.2.1,?_⟩
  intro u x hx
  rw [angularNonzero_value K _ result.1.handles.closed result.1.handles.initialized,
    result.2.2.2 u x hx,angularValue_nil,zero_add]

theorem momentCoefficient_value (u : RawAngle) (x : Phase) :
    (coefficientValue (polynomialCoefficient (MvPolynomial.C (rawMoment u))) x : ℂ)=(rawMoment u : ℂ) := by
  rw [polynomialCoefficient_source]
  simp [polynomialSymbol,evalAt]

theorem angularAverage_native (K : ℕ) (rows : RawAngular) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) (valid : AngularHandles state rows)
    (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (angularAverage rows state).2 (angularAverage rows state).1 x=
      (rows.map (fun row=>(rawMoment row.1 : ℂ)*nativePolynomial K state row.2 x)).sum := by
  classical
  let selected:=rows.filter (fun row=>∀ j,Even (row.1 j))
  let action:=fun row : RawAngle × ℕ=>rawScale (polynomialCoefficient (MvPolynomial.C (rawMoment row.1))) row.2
  let value:=fun row : RawAngle × ℕ=>fun y=>(rawMoment row.1 : ℂ)*nativePolynomial K state row.2 y
  have generated:=rawSequence_native_values K state state selected action value (RawExtends.refl _) closed initialized
    (fun _ _ _=>rawScale_extends _ _ _)
    (fun row member arena grow hc hi=>⟨rawScale_closed _ _ _ hc,rawPoly_bound _ _⟩)
    (by
      intro row member arena grow hc hi y hy
      have rowValid:=valid row (List.mem_of_mem_filter member)
      rw [show nativePolynomial K (action row arena).2 (action row arena).1 y=
          (coefficientValue (polynomialCoefficient (MvPolynomial.C (rawMoment row.1))) y : ℂ)*nativePolynomial K arena row.2 y from
        rawScale_native K _ row.2 arena hc (handle_extend grow rowValid) y hy,
        momentCoefficient_value,nativePolynomial_prefix K grow closed row.2 rowValid])
  change nativePolynomial K (rawAdd (rawSequence (selected.map action) state).1 (rawSequence (selected.map action) state).2).2
    (rawAdd (rawSequence (selected.map action) state).1 (rawSequence (selected.map action) state).2).1 x=_
  rw [rawAdd_native K _ _ generated.1 generated.2.2.1 x hx,generated.2.2.2 x hx]
  change ((rows.filter (fun row=>∀ j,Even (row.1 j))).map (fun row=>(rawMoment row.1 : ℂ)*nativePolynomial K state row.2 x)).sum=_
  clear generated selected valid
  induction rows with
  | nil=>rfl
  | cons row tail ih=>
    by_cases even : ∀ j,Even (row.1 j)
    · simp [even,ih]
    · have vanish : rawMoment row.1=0 := by simp only [rawMoment,if_neg even]
      simp [even,vanish,ih]

def actualAngular (order : ℕ)
    (rows : List (RawAngle × Fin (originalEngine order).runtime.arena.polynomials.length)) : RawAngular :=
  rows.map (fun row=>(row.1,row.2.val))

theorem actualAngular_handles (order : ℕ)
    (rows : List (RawAngle × Fin (originalEngine order).runtime.arena.polynomials.length)) :
    AngularHandles (originalEngine order).runtime.arena (actualAngular order rows) := by
  intro row member
  obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
  exact entry.2.isLt

theorem actual_weighted_native (order r : ℕ)
    (left right : List (RawAngle × Fin (originalEngine order).runtime.arena.polynomials.length)) :
    let runtime:=(originalEngine order).runtime
    let ls:=actualAngular order left
    let rs:=actualAngular order right
    UniqueAngles (runtimeWeighted r ls rs runtime).1 ∧
      ∀ u x,x∈poleDomain →
        angularValue (order+1) (runtimeWeighted r ls rs runtime).2.arena (runtimeWeighted r ls rs runtime).1 u x=
          ((ls.flatMap (fun a=>rs.map (fun b=>(a,b)))).map (fun pair=>
            if pair.1.1+pair.2.1=u then jordanValue (order+1) r runtime.arena pair.1.2 pair.2.2 x else 0)).sum :=
  runtimeWeighted_native (order+1) r _ _ _ (originalEngine_cached (order+1) order)
    (actualAngular_handles order left) (actualAngular_handles order right)

theorem actual_average_native (order : ℕ)
    (rows : List (RawAngle × Fin (originalEngine order).runtime.arena.polynomials.length))
    (x : Phase) (hx : x∈poleDomain) :
    let state:=(originalEngine order).runtime.arena
    let input:=actualAngular order rows
    nativePolynomial (order+1) (angularAverage input state).2 (angularAverage input state).1 x=
      (input.map (fun row=>(rawMoment row.1 : ℂ)*nativePolynomial (order+1) state row.2 x)).sum :=
  angularAverage_native (order+1) _ _ (originalEngine_cached (order+1) order).handles.closed
    (originalEngine_cached (order+1) order).handles.initialized (actualAngular_handles order rows) x hx

end LowEnergy.PreparationVacuumSetupValues
