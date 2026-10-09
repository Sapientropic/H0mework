import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSetupJordanValues

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumKernelValues
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumNativeMemo PreparationVacuumSetupValues
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumArenaBudget PreparationVacuumArenaRows
open scoped BigOperators Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def sourcePrincipal (slot : Fin 13) : RawAction := fun state=>
  if slot.val=0 ∨ (4 ≤ slot.val ∧ slot.val ≤ 9) then rawScalar (principalCoefficient slot) state else (0,state)

theorem principalCoefficient_outside (slot : Fin 13) (outside : ¬(slot.val=0 ∨ (4 ≤ slot.val ∧ slot.val ≤ 9))) :
    principalCoefficient slot=polynomialCoefficient 0 := by
  fin_cases slot <;> simp_all [principalCoefficient]

theorem sourcePrincipal_grows (slot : Fin 13) (state : RawArena) : RawExtends state (sourcePrincipal slot state).2 := by
  unfold sourcePrincipal
  split_ifs
  · exact rawScalar_extends _ _
  · exact RawExtends.refl _

theorem sourcePrincipal_native (K : ℕ) (slot : Fin 13) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) :
    RawMoyalClosed (sourcePrincipal slot state).2 ∧ Handle (sourcePrincipal slot state).2 (sourcePrincipal slot state).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (sourcePrincipal slot state).2 (sourcePrincipal slot state).1 x=(engineSource 0 slot x : ℂ) := by
  unfold sourcePrincipal
  split_ifs with present
  · refine ⟨rawScalar_closed _ _ closed,rawPoly_bound _ _,?_⟩
    intro x hx
    rw [rawScalar_native K _ state closed x hx,principalCoefficient_native]
  · refine ⟨closed,rawInitialized_positive state initialized,?_⟩
    intro x hx
    rw [native_zero K state closed initialized,←principalCoefficient_native slot x,principalCoefficient_outside slot present,
      polynomialCoefficient_source]
    simp [polynomialSymbol]

def sourceLower (slot : Fin 13) : RawAction := fun state=>
  let lower:=rawAtom (.source 0 (Fin.castSucc slot)) false state
  if slot=0 then
    let extra:=rawAtom (.source 0 (Fin.last 13)) false lower.2
    rawAdd [lower.1,extra.1] extra.2 else lower

theorem sourceLower_grows (slot : Fin 13) (state : RawArena) : RawExtends state (sourceLower slot state).2 := by
  unfold sourceLower
  split_ifs
  · exact (rawAtom_extends _ _ _).trans ((rawAtom_extends _ _ _).trans (rawAdd_extends _ _))
  · exact rawAtom_extends _ _ _

theorem sourceLower_native (K : ℕ) (slot : Fin 13) (state : RawArena) (closed : RawMoyalClosed state) :
    RawMoyalClosed (sourceLower slot state).2 ∧ Handle (sourceLower slot state).2 (sourceLower slot state).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (sourceLower slot state).2 (sourceLower slot state).1 x=(engineSource 2 slot x : ℂ) := by
  let lower:=rawAtom (.source 0 (Fin.castSucc slot)) false state
  have lowerClosed : RawMoyalClosed lower.2 := rawAtom_closed _ _ _ closed (by intro _ member;cases member)
  have lowerValid : Handle lower.2 lower.1 := rawPoly_bound _ _
  unfold sourceLower
  split_ifs with zero
  · let extra:=rawAtom (.source 0 (Fin.last 13)) false lower.2
    have extraClosed : RawMoyalClosed extra.2 := rawAtom_closed _ _ _ lowerClosed (by intro _ member;cases member)
    have growth : RawExtends lower.2 extra.2 := rawAtom_extends _ _ _
    refine ⟨rawAdd_closed _ _ extraClosed,rawPoly_bound _ _,?_⟩
    intro x hx
    have ids : ListHandles extra.2 [lower.1,extra.1] := by
      intro id member
      rcases List.mem_cons.mp member with left|right
      · subst id;exact handle_extend growth lowerValid
      · have same:=List.mem_singleton.mp right
        subst id;exact rawPoly_bound _ _
    change nativePolynomial K (rawAdd [lower.1,extra.1] extra.2).2 (rawAdd [lower.1,extra.1] extra.2).1 x=_
    rw [rawAdd_native K _ extra.2 extraClosed ids x hx]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [nativePolynomial_prefix K growth lowerClosed lower.1 lowerValid,
      rawAtom_source_native K 0 (Fin.castSucc slot) state closed x hx,
      rawAtom_source_native K 0 (Fin.last 13) lower.2 lowerClosed x hx]
    simp only [engineSource,if_pos zero,Complex.ofReal_add]
    rfl
  · refine ⟨lowerClosed,lowerValid,?_⟩
    intro x hx
    rw [rawAtom_source_native K 0 (Fin.castSucc slot) state closed x hx]
    simp only [engineSource,if_neg zero,add_zero]
    rfl

def sourceBody (slot : Fin 13) (state : RawArena) : (ℕ × ℕ × ℕ) × RawArena :=
  let principal:=sourcePrincipal slot state
  let first:=rawAtom (.source 1 (Fin.castSucc slot)) false principal.2
  let lower:=sourceLower slot first.2
  ((principal.1,first.1,lower.1),lower.2)

def sourceBodyRows (ids : ℕ × ℕ × ℕ) : RawSeries :=
  [angularConstant ids.1,[(angleZero,ids.2.1)],[(angleZero,ids.2.2)]]

theorem originalSource_body (depth : ℕ) (slot : Fin 13) (state : RawArena) :
    originalSource depth slot state=
      let result:=sourceBody slot state
      ((sourceBodyRows result.1).take (depth+1)++List.replicate (depth-2) [],result.2) := rfl

theorem sourceBody_native (K : ℕ) (slot : Fin 13) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) :
    RawMoyalClosed (sourceBody slot state).2 ∧ RawInitialized (sourceBody slot state).2 ∧
      ∀ x,x∈poleDomain →
        nativePolynomial K (sourceBody slot state).2 (sourceBody slot state).1.1 x=(engineSource 0 slot x : ℂ) ∧
        nativePolynomial K (sourceBody slot state).2 (sourceBody slot state).1.2.1 x=(engineSource 1 slot x : ℂ) ∧
        nativePolynomial K (sourceBody slot state).2 (sourceBody slot state).1.2.2 x=(engineSource 2 slot x : ℂ) := by
  let principal:=sourcePrincipal slot state
  let first:=rawAtom (.source 1 (Fin.castSucc slot)) false principal.2
  let lower:=sourceLower slot first.2
  have hp:=sourcePrincipal_native K slot state closed initialized
  have hf : RawMoyalClosed first.2 := rawAtom_closed _ _ _ hp.1 (by intro _ member;cases member)
  have hl:=sourceLower_native K slot first.2 hf
  have fg : RawExtends principal.2 first.2 := rawAtom_extends _ _ _
  have lg : RawExtends first.2 lower.2 := sourceLower_grows _ _
  refine ⟨hl.1,initialized.trans (((sourcePrincipal_grows slot state).trans fg).trans lg),?_⟩
  intro x hx
  change nativePolynomial K lower.2 principal.1 x=_ ∧ nativePolynomial K lower.2 first.1 x=_ ∧ nativePolynomial K lower.2 lower.1 x=_
  rw [nativePolynomial_prefix K (fg.trans lg) hp.1 principal.1 hp.2.1,
    nativePolynomial_prefix K lg hf first.1 (rawPoly_bound _ _)]
  exact ⟨hp.2.2 x hx,rawAtom_source_native K 1 (Fin.castSucc slot) principal.2 hp.1 x hx,hl.2.2 x hx⟩

theorem readAngular_constant (K : ℕ) (state : RawArena) (id : ℕ)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) :
    readAngular K state (angularConstant id)=singletonField 0 (nativePolynomial K state id) := by
  classical
  unfold angularConstant
  by_cases zero : id=0
  · rw [if_pos zero,readAngular_nil,zero,native_zero K state closed initialized]
    funext u x
    simp [singletonField]
  · rw [if_neg zero,readAngular_cons,readAngular_nil,add_zero,angleExponent_zero]

theorem realCoefficients_constant (f : PreparationVacuumCanonicalMoyal.Symbol) :
    realCoefficients (MvPolynomial.C f)=singletonField 0 (fun x=>(f x : ℂ)) := by
  classical
  funext u x
  by_cases zero : u=0
  · subst u
    simp [realCoefficients,singletonField]
  · simp [realCoefficients,singletonField,MvPolynomial.coeff_C,Ne.symm zero]

def sourcePolynomials (slot : Fin 13) : List AngularPolynomial :=
  [MvPolynomial.C (engineSource 0 slot),MvPolynomial.C (engineSource 1 slot),MvPolynomial.C (engineSource 2 slot)]

theorem sourceBody_coefficients (K : ℕ) (slot : Fin 13) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) :
    SeriesAgrees (readAngularSeries K (sourceBody slot state).2 (sourceBodyRows (sourceBody slot state).1))
      ((sourcePolynomials slot).map realCoefficients) := by
  have paid:=sourceBody_native K slot state closed initialized
  intro u x hx
  unfold readAngularSeries sourceBodyRows sourcePolynomials
  simp only [List.map_cons,List.map_nil,realCoefficients_constant]
  rw [readAngular_constant K _ _ paid.1 paid.2.1,readAngular_cons,readAngular_cons,
    readAngular_nil,add_zero,add_zero,angleExponent_zero]
  have values:=paid.2.2 x hx
  unfold singletonField
  split_ifs <;> simp only [values.1,values.2.1,values.2.2,Pi.zero_apply]

theorem getD_take_append_default {α : Type} (rows : List α) (default : α) (limit extra n : ℕ) (within : n < limit) :
    ((rows.take limit)++List.replicate extra default).getD n default=rows.getD n default := by
  by_cases present : n < rows.length
  · have bound : n < (rows.take limit).length := by simp only [List.length_take];omega
    rw [List.getD_append _ _ _ _ bound,List.getD_eq_getElem _ _ bound,List.getD_eq_getElem _ _ present]
    simp only [List.getElem_take]
  · have outside : rows.length ≤ n := by omega
    have bound : (rows.take limit).length ≤ n := by simp only [List.length_take];omega
    rw [List.getD_append_right _ _ _ _ bound,List.getD_eq_default _ _ outside]
    by_cases small : n-(rows.take limit).length < extra
    · exact List.getD_replicate default small
    · exact List.getD_eq_default _ _ (by simp only [List.length_replicate];omega)

theorem realCoefficients_zero : realCoefficients (0 : AngularPolynomial)=0 := by
  funext u x
  simp [realCoefficients]

theorem realSeries_getD (polynomials : List AngularPolynomial) (n : ℕ) :
    (polynomials.map realCoefficients).getD n 0=realCoefficients (polynomials.getD n 0) := by
  calc
    (polynomials.map realCoefficients).getD n 0=(polynomials.map realCoefficients).getD n (realCoefficients 0) := by
      rw [realCoefficients_zero]
    _=realCoefficients (polynomials.getD n 0) := List.getD_map polynomials 0 realCoefficients

theorem originalSource_coefficients (K depth : ℕ) (slot : Fin 13) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) (n : ℕ) (within : n≤depth) :
    AngularAgrees (readAngular K (originalSource depth slot state).2 ((originalSource depth slot state).1.getD n []))
      (realCoefficients ((sourcePolynomials slot).getD n 0)) := by
  rw [originalSource_body]
  dsimp only
  rw [getD_take_append_default _ [] (depth+1) (depth-2) n (by omega)]
  have same:=(sourceBody_coefficients K slot state closed initialized).getD n
  rw [readAngularSeries_getD,realSeries_getD] at same
  exact same

abbrev kernelSourceSeries : Fin 13 → List AngularPolynomial := smooth_program_const% "sourceSeries"

theorem sourcePolynomials_kernel (slot : Fin 13) : sourcePolynomials slot=kernelSourceSeries slot := rfl

theorem actual_source_coefficients (order depth : ℕ) (slot : Fin 13) (n : ℕ) (within : n≤depth) :
    let state:=(originalEngine order).runtime.arena
    AngularAgrees (readAngular (order+1) (originalSource depth slot state).2 ((originalSource depth slot state).1.getD n []))
      (realCoefficients ((kernelSourceSeries slot).getD n 0)) := by
  rw [←sourcePolynomials_kernel]
  exact originalSource_coefficients (order+1) depth slot _ (originalEngine_cached (order+1) order).handles.closed
    (originalEngine_cached (order+1) order).handles.initialized n within

theorem angularSequence_values {α : Type} (K : ℕ) (base current : RawArena) (items : List α)
    (action : α → AngularAction) (value : α → AngularField)
    (extension : RawExtends base current) (closed : RawMoyalClosed current) (initialized : RawInitialized current)
    (grows : ∀ item,item∈items → ∀ state,RawExtends state (action item state).2)
    (step : ∀ item,item∈items → ∀ state,RawExtends base state → RawMoyalClosed state → RawInitialized state →
      RawMoyalClosed (action item state).2 ∧ AngularHandles (action item state).2 (action item state).1 ∧
        AngularAgrees (readAngular K (action item state).2 (action item state).1) (value item)) :
    let result:=angularSequence (items.map action) current
    RawMoyalClosed result.2 ∧ RawInitialized result.2 ∧ SeriesHandles result.2 result.1 ∧
      SeriesAgrees (readAngularSeries K result.2 result.1) (items.map value) := by
  induction items generalizing current with
  | nil=>exact ⟨closed,initialized,fun _ member=>False.elim (List.not_mem_nil member),fun _ _ _=>rfl⟩
  | cons item items ih=>
    have one:=step item (by simp) current extension closed initialized
    have oneGrow:=grows item (by simp) current
    have tail:=ih (action item current).2 (extension.trans oneGrow) one.1 (initialized.trans oneGrow)
      (fun a h=>grows a (List.mem_cons_of_mem _ h)) (fun a h=>step a (List.mem_cons_of_mem _ h))
    have growth : RawExtends (action item current).2 (angularSequence (items.map action) (action item current).2).2 := by
      apply angularSequence_grows
      intro a member state
      obtain ⟨entry,h,rfl⟩:=List.mem_map.mp member
      exact grows entry (List.mem_cons_of_mem _ h) state
    refine ⟨tail.1,tail.2.1,?_,?_⟩
    · intro rows member
      rcases List.mem_cons.mp member with equal|old
      · subst rows;exact angular_extend growth one.2.1
      · exact tail.2.2.1 rows old
    · intro u x hx
      change readAngular K (angularSequence (items.map action) (action item current).2).2 (action item current).1 u x::
        ((readAngularSeries K (angularSequence (items.map action) (action item current).2).2
          (angularSequence (items.map action) (action item current).2).1).map (fun f=>f u x))=_
      rw [readAngular_prefix K growth one.1 _ one.2.1,one.2.2 u hx,tail.2.2.2 u x hx]
      rfl

def tracePolynomials : List AngularPolynomial :=
  [MvPolynomial.C (engineTrace 0),MvPolynomial.C (engineTrace 1),MvPolynomial.C (engineTrace 2)]

abbrev kernelTraceSeries : List AngularPolynomial := smooth_program_const% "traceSeries"

theorem tracePolynomials_kernel : tracePolynomials=kernelTraceSeries := rfl

theorem sourcePolynomials_getD (slot : Fin 13) (n : ℕ) :
    (sourcePolynomials slot).getD n 0=MvPolynomial.C (engineSource n slot) := by
  rcases n with _|_|_|n
  · rfl
  · rfl
  · rfl
  · have zero : engineSource (n+1+1+1) slot=0 := rfl
    rw [zero]
    simp [sourcePolynomials]

theorem tracePolynomials_getD (n : ℕ) : tracePolynomials.getD n 0=MvPolynomial.C (engineTrace n) := by
  rcases n with _|_|_|n
  · rfl
  · rfl
  · rfl
  · have zero : engineTrace (n+1+1+1)=0 := by
      funext x
      simp [engineTrace,engineSource]
    rw [zero]
    simp [tracePolynomials]

theorem originalTrace_values (K depth : ℕ) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) :
    SeriesAgrees (readAngularSeries K (originalTrace depth state).2 (originalTrace depth state).1)
      ((List.range (depth+1)).map (fun n=>realCoefficients (MvPolynomial.C (engineTrace n)))) := by
  let four:=originalSource depth 4 state
  let five:=originalSource depth 5 four.2
  let six:=originalSource depth 6 five.2
  have fourGrow : RawExtends state four.2 := originalSource_grows _ _ _
  have fourPaid:=originalSource_closed_handles depth 4 state initialized closed
  have fiveInit:=initialized.trans fourGrow
  have fiveGrow : RawExtends four.2 five.2 := originalSource_grows _ _ _
  have fivePaid:=originalSource_closed_handles depth 5 four.2 fiveInit fourPaid.1
  have sixInit:=fiveInit.trans fiveGrow
  have sixGrow : RawExtends five.2 six.2 := originalSource_grows _ _ _
  have sixPaid:=originalSource_closed_handles depth 6 five.2 sixInit fivePaid.1
  have result:=angularSequence_values K six.2 six.2 (List.range (depth+1))
    (fun n=>angularAdd [four.1.getD n [],five.1.getD n [],six.1.getD n []])
    (fun n=>realCoefficients (MvPolynomial.C (engineTrace n))) (RawExtends.refl _) sixPaid.1 (sixInit.trans sixGrow)
    (fun _ _ _=>angularAdd_grows _ _) (by
      intro n member current extension currentClosed currentInit
      have within : n≤depth := by have h:=List.mem_range.mp member;omega
      have validFour:=angular_extend ((fiveGrow.trans sixGrow).trans extension) (series_getD fourPaid.2 n)
      have validFive:=angular_extend (sixGrow.trans extension) (series_getD fivePaid.2 n)
      have validSix:=angular_extend extension (series_getD sixPaid.2 n)
      have valid : SeriesHandles current [four.1.getD n [],five.1.getD n [],six.1.getD n []] := by
        intro rows present
        simp only [List.mem_cons,List.not_mem_nil,or_false] at present
        rcases present with same|same|same <;> subst rows
        · exact validFour
        · exact validFive
        · exact validSix
      have paid:=angularAdd_closed_handles [four.1.getD n [],five.1.getD n [],six.1.getD n []] current currentClosed
      refine ⟨paid.1,paid.2,?_⟩
      intro u x hx
      change angularValue K (angularAdd _ current).2 (angularAdd _ current).1 (fun j=>u j) x=_
      rw [(angularAdd_native K _ current currentClosed currentInit valid).2 _ x hx]
      change readAngular K current (four.1.getD n []) u x+(readAngular K current (five.1.getD n []) u x+
        (readAngular K current (six.1.getD n []) u x+0))=_
      rw [readAngular_prefix K ((fiveGrow.trans sixGrow).trans extension) fourPaid.1 _ (series_getD fourPaid.2 n),
        readAngular_prefix K (sixGrow.trans extension) fivePaid.1 _ (series_getD fivePaid.2 n),
        readAngular_prefix K extension sixPaid.1 _ (series_getD sixPaid.2 n),
        originalSource_coefficients K depth 4 state closed initialized n within u hx,
        originalSource_coefficients K depth 5 four.2 fourPaid.1 fiveInit n within u hx,
        originalSource_coefficients K depth 6 five.2 fivePaid.1 sixInit n within u hx]
      simp only [sourcePolynomials_getD,realCoefficients_constant]
      unfold singletonField
      split_ifs
      · simp only [engineTrace,Complex.ofReal_add,add_zero,add_assoc]
      · simp)
  exact result.2.2.2

theorem originalTrace_coefficients (K depth : ℕ) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) (n : ℕ) (within : n≤depth) :
    AngularAgrees (readAngular K (originalTrace depth state).2 ((originalTrace depth state).1.getD n []))
      (realCoefficients (kernelTraceSeries.getD n 0)) := by
  have same:=(originalTrace_values K depth state closed initialized).getD n
  rw [readAngularSeries_getD] at same
  have bounded : n < (List.range (depth+1)).length := by simp only [List.length_range];omega
  rw [List.getD_eq_getElem ((List.range (depth+1)).map (fun n=>realCoefficients (MvPolynomial.C (engineTrace n))))
    (0 : AngularField) (by simpa only [List.length_map] using bounded),List.getElem_map,List.getElem_range] at same
  rw [←tracePolynomials_kernel,tracePolynomials_getD]
  exact same

theorem actual_trace_coefficients (order depth n : ℕ) (within : n≤depth) :
    let state:=(originalEngine order).runtime.arena
    AngularAgrees (readAngular (order+1) (originalTrace depth state).2 ((originalTrace depth state).1.getD n []))
      (realCoefficients (kernelTraceSeries.getD n 0)) :=
  originalTrace_coefficients (order+1) depth _ (originalEngine_cached (order+1) order).handles.closed
    (originalEngine_cached (order+1) order).handles.initialized n within

def kernelInput (slot : Option (Fin 13)) : List AngularPolynomial :=
  match slot with
  | none=>kernelTraceSeries
  | some j=>kernelSourceSeries j

theorem sourceInput_coefficients (K : ℕ) (setup : RawSetup) (slot : Option (Fin 13)) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (n : ℕ) (within : n ≤ setup.depth) :
    AngularAgrees (readAngular K (sourceInput setup slot runtime).2.arena ((sourceInput setup slot runtime).1.getD n []))
      (realCoefficients ((kernelInput slot).getD n 0)) := by
  cases slot with
  | none=>exact originalTrace_coefficients K setup.depth runtime.arena cached.handles.closed cached.handles.initialized n within
  | some j=>
    change AngularAgrees (readAngular K (originalSource setup.depth j runtime.arena).2
      ((originalSource setup.depth j runtime.arena).1.getD n [])) (realCoefficients ((kernelSourceSeries j).getD n 0))
    rw [←sourcePolynomials_kernel]
    exact originalSource_coefficients K setup.depth j runtime.arena cached.handles.closed cached.handles.initialized n within

theorem actual_engine_input_coefficients (k : ℕ) (slot : Option (Fin 13)) (n : ℕ)
    (within : n≤(engineNextSetup k (originalEngine k)).depth) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    AngularAgrees (readAngular (k+1) (sourceInput setup slot runtime).2.arena ((sourceInput setup slot runtime).1.getD n []))
      (realCoefficients ((kernelInput slot).getD n 0)) :=
  sourceInput_coefficients (k+1) _ slot _ (originalEngine_full_native (k+1) k).operations.cached n within

end LowEnergy.PreparationVacuumKernelValues
