import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationKernelSourceInputs

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumKernelValues
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumNativeMemo PreparationVacuumSetupValues
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumArenaBudget PreparationVacuumArenaRows
open PreparationVacuumEngineResponse PreparationVacuumEnginePaidDepth
open scoped BigOperators Topology

abbrev ClockField := ℕ → Fin 4 → Phase → ℂ

def kernelClockAt (K : ℕ) (axis : Fin 4) (n : ℕ) : PreparationVacuumCanonicalMoyal.Symbol :=
  (smooth_program_const% "clockAt") (sourceEngine K) axis n

def clockMask (K order : ℕ) (done : List (Fin 4)) : ClockField := by
  classical
  exact fun n a=>if n≤order ∨ (n=order+1 ∧ a∈done) then (fun x=>(kernelClockAt K a n x : ℂ)) else 0

def ClockValues (K : ℕ) (state : RawArena) (clocks : RawClocks) (values : ClockField) : Prop :=
  ∀ n a,Set.EqOn (nativePolynomial K state (clockLookup clocks n a)) (values n a) poleDomain

theorem clockLookup_handles (state : RawArena) (clocks : RawClocks) (initialized : RawInitialized state)
    (valid : ClockHandles state clocks) (n : ℕ) (a : Fin 4) : Handle state (clockLookup clocks n a) := by
  unfold clockLookup
  cases found : clocks.find? (fun row=>row.1=(n,a)) with
  | none=>exact rawInitialized_positive state initialized
  | some entry=>exact valid entry (List.mem_of_find?_eq_some found)

theorem ClockValues.extend {K : ℕ} {old next : RawArena} {clocks : RawClocks} {values : ClockField}
    (native : ClockValues K old clocks values) (growth : RawExtends old next)
    (closed : RawMoyalClosed old) (initialized : RawInitialized old) (valid : ClockHandles old clocks) :
    ClockValues K next clocks values := by
  intro n a x hx
  rw [nativePolynomial_prefix K growth closed _ (clockLookup_handles old clocks initialized valid n a)]
  exact native n a hx

theorem clockLookup_insert (clocks : RawClocks) (level n : ℕ) (axis a : Fin 4) (id : ℕ) :
    clockLookup (clockInsert clocks level axis id) n a=if (level,axis)=(n,a) then id else clockLookup clocks n a := by
  classical
  unfold clockInsert
  by_cases same : (level,axis)=(n,a)
  · simp [clockLookup,same]
  · have filterSame : ((clocks.filter (fun row=>row.1≠(level,axis))).find? (fun row=>row.1=(n,a)))=
        clocks.find? (fun row=>row.1=(n,a)) := by
      rw [List.find?_filter]
      apply congrArg (fun p=>clocks.find? p)
      funext row
      by_cases wanted : row.1=(n,a)
      · rw [wanted]
        simp [Ne.symm same]
      · simp [wanted]

    simp only [clockLookup,List.find?_cons,same,decide_false,ite_false]
    rw [filterSame]

theorem clockLookup_singleton (id n : ℕ) (a : Fin 4) :
    clockLookup [((0,0),id)] n a=if n=0 ∧ a=0 then id else 0 := by
  classical
  have same : ((0,0) : ℕ × Fin 4)=(n,a) ↔ n=0 ∧ a=0 := by
    constructor
    · intro h;exact ⟨(congrArg Prod.fst h).symm,(congrArg Prod.snd h).symm⟩
    · rintro ⟨rfl,rfl⟩;rfl
  simp only [clockLookup,List.find?_cons,List.find?_nil,same]
  by_cases hit : n=0 ∧ a=0 <;> simp [hit]


theorem kernelClockAt_seed (K : ℕ) (a : Fin 4) : kernelClockAt K a 0=if a=0 then sourceClock else 0 := by
  unfold kernelClockAt
  program_unfold "clockAt"
  simp only [show 0<K+1 by omega,dif_pos,sourceEngine_seed_preserved]

theorem kernelClockAt_inside (K n : ℕ) (a : Fin 4) (bound : n ≤ K) :
    kernelClockAt K a n=sourceEngine K a ⟨n,by omega⟩ := by
  unfold kernelClockAt
  program_unfold "clockAt"
  simp only [show n<K+1 by omega,dif_pos]

theorem kernelClockAt_outside (K n : ℕ) (a : Fin 4) (outside : K < n) : kernelClockAt K a n=0 := by
  unfold kernelClockAt
  program_unfold "clockAt"
  rw [dif_neg (show ¬ n<K+1 by omega)]

theorem kernelClockAt_paid (small big : ℕ) (paid : small ≤ big) (a : Fin 4) (n : ℕ) (bound : n ≤ small) :
    kernelClockAt big a n=kernelClockAt small a n := sourceEngine_preserves_paid small big paid a n bound

theorem rawAtom_clock_kernel (K k : ℕ) (a : Fin 4) (state : RawArena) (closed : RawMoyalClosed state)
    (bound : k < K) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawAtom (.clock k a) false state).2 (rawAtom (.clock k a) false state).1 x=(kernelClockAt K a (k+1) x : ℂ) := by
  rw [rawAtom_clock_actual K k a state closed bound x hx,kernelClockAt_inside K (k+1) a (by omega)]
  rfl

theorem clockMask_insert (K order : ℕ) (done : List (Fin 4)) (axis : Fin 4) (n : ℕ) (a : Fin 4) :
    (if (order+1,axis)=(n,a) then (fun x=>(kernelClockAt K axis (order+1) x : ℂ)) else clockMask K order done n a)=
      clockMask K order (done++[axis]) n a := by
  classical
  by_cases same : (order+1,axis)=(n,a)
  · have hn : n=order+1 := (congrArg Prod.fst same).symm
    have ha : a=axis := (congrArg Prod.snd same).symm
    subst n
    subst a
    simp [clockMask]
  · have absent : ¬(n=order+1 ∧ a=axis) := by
      intro h
      exact same (Prod.ext h.1.symm h.2.symm)
    simp only [if_neg same,clockMask,List.mem_append,List.mem_singleton]
    have condition : (n≤order ∨ n=order+1 ∧ (a∈done ∨ a=axis)) ↔ (n≤order ∨ n=order+1 ∧ a∈done) := by tauto
    simp only [condition]

theorem installStep_clock_native (K k : ℕ) (residualIds : List ℕ)
    (out : RawClocks × List ℕ × List ℕ × RawRuntime) (done : List (Fin 4)) (a : Fin 4)
    (bound : k < K) (cached : CachedNative K out.2.2.2) (valid : ClockHandles out.2.2.2.arena out.1)
    (native : ClockValues K out.2.2.2.arena out.1 (clockMask K k done)) :
    let result:=installStep k residualIds out a
    CachedNative K result.2.2.2 ∧ ClockHandles result.2.2.2.arena result.1 ∧
      ClockValues K result.2.2.2.arena result.1 (clockMask K k (done++[a])) := by
  let atom:=runArena (rawAtom (.clock k a) false) out.2.2.2
  let actions:=(List.finRange 4).map (fun b=>runArena (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))
  let scaled:=runtimeSequence actions atom.2
  let definition:=runArena (rawAdd scaled.1) scaled.2
  have atomPaid:=runAtom_cached (.clock k a) false out.2.2.2 cached (by intro id member;cases member)
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_extends _ _ _
  have scaledPaid:=runtimeSequence_cached K Handle (fun h _ hv=>handle_extend h hv)
    atom.2 atom.2 actions (RawExtends.refl _) atomPaid.1 grows (by
      intro action member current extension currentValid
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
      exact runScale_cached _ _ current currentValid)
  have definitionPaid:=runAdd_cached scaled.1 scaled.2 scaledPaid.1
  have tailGrow : RawExtends atom.2.arena definition.2.arena :=
    (runtimeSequence_grows actions grows atom.2).trans (rawAdd_extends _ _)
  have growth : RawExtends out.2.2.2.arena definition.2.arena := (rawAtom_extends _ _ _).trans tailGrow
  refine ⟨definitionPaid.1,clockInsert_handles (clocks_extend growth valid) (k+1) a atom.1 (handle_extend tailGrow atomPaid.2),?_⟩
  intro n axis x hx
  change nativePolynomial K definition.2.arena (clockLookup (clockInsert out.1 (k+1) a atom.1) n axis) x=_
  rw [clockLookup_insert,←clockMask_insert K k done a n axis]
  by_cases same : (k+1,a)=(n,axis)
  · simp only [if_pos same]
    rw [nativePolynomial_prefix K tailGrow atomPaid.1.handles.closed atom.1 atomPaid.2]
    exact rawAtom_clock_kernel K k a out.2.2.2.arena cached.handles.closed bound x hx
  · simp only [if_neg same]
    rw [nativePolynomial_prefix K growth cached.handles.closed _
      (clockLookup_handles out.2.2.2.arena out.1 cached.handles.initialized valid n axis)]
    exact native n axis hx

theorem installFold_clock_native (K k : ℕ) (residualIds : List ℕ) (axes : List (Fin 4))
    (out : RawClocks × List ℕ × List ℕ × RawRuntime) (done : List (Fin 4))
    (bound : k < K) (cached : CachedNative K out.2.2.2) (valid : ClockHandles out.2.2.2.arena out.1)
    (native : ClockValues K out.2.2.2.arena out.1 (clockMask K k done)) :
    let result:=axes.foldl (installStep k residualIds) out
    CachedNative K result.2.2.2 ∧ ClockHandles result.2.2.2.arena result.1 ∧
      ClockValues K result.2.2.2.arena result.1 (clockMask K k (done++axes)) := by
  induction axes generalizing out done with
  | nil=>simpa only [List.foldl_nil,List.append_nil] using And.intro cached (And.intro valid native)
  | cons a axes ih=>
    have step:=installStep_clock_native K k residualIds out done a bound cached valid native
    have next:=ih (installStep k residualIds out a) (done++[a]) step.1 step.2.1 step.2.2
    simpa only [List.foldl_cons,List.append_assoc,List.singleton_append] using next

theorem clockMask_complete (K k : ℕ) : clockMask K k (List.finRange 4)=clockMask K (k+1) [] := by
  classical
  funext n a
  unfold clockMask
  simp only [List.mem_finRange,and_true,List.not_mem_nil,and_false,or_false]
  have same : (n≤k ∨ n=k+1) ↔ n≤k+1 := by omega
  simp only [same]

theorem originalInstall_clock_native (K k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (bound : k < K) (cached : CachedNative K runtime) (valid : ClockHandles runtime.arena clocks)
    (native : ClockValues K runtime.arena clocks (clockMask K k [])) :
    let result:=originalInstall k residualIds clocks runtime
    CachedNative K result.2.2.2 ∧ ClockHandles result.2.2.2.arena result.1 ∧
      ClockValues K result.2.2.2.arena result.1 (clockMask K (k+1) []) := by
  have generated:=installFold_clock_native K k residualIds (List.finRange 4) (clocks,[],[],runtime) [] bound cached valid native
  rw [List.nil_append,clockMask_complete] at generated
  rw [originalInstall_as_fold]
  exact generated

theorem seedCoefficient_value (x : Phase) : coefficientValue (polynomialCoefficient (MvPolynomial.X 0)) x=sourceClock x := by
  rw [polynomialCoefficient_source]
  simp [polynomialSymbol,evalAt,sourceVariables,PreparationVacuumClockJacobian.actualC,sourceClock]

attribute [local irreducible] originalForceOrEnergy runtimeSequence runtimeSetup
set_option backward.isDefEq.respectTransparency true

theorem originalEngineInitial_clock_values (K : ℕ) :
    ClockValues K originalEngineInitial.runtime.arena originalEngineInitial.clocks (clockMask K 0 []) := by
  let seeded:=runArena (rawScalar (polynomialCoefficient (MvPolynomial.X 0))) (⟨rawInitial,[],[],[],[]⟩ : RawRuntime)
  let clocks : RawClocks:=[((0,0),seeded.1)]
  have paid:=runScalar_cached (polynomialCoefficient (MvPolynomial.X 0)) _ (initial_cachedNative K)
  have valid : ClockHandles seeded.2.arena clocks := by
    intro entry member
    have same:=List.mem_singleton.mp member
    subst entry
    exact paid.2
  have seedValue (x : Phase) (hx : x∈poleDomain) : nativePolynomial K seeded.2.arena seeded.1 x=(sourceClock x : ℂ) := by
    rw [show nativePolynomial K seeded.2.arena seeded.1 x=(coefficientValue (polynomialCoefficient (MvPolynomial.X 0)) x : ℂ) from
      rawScalar_native K _ rawInitial (initial_cachedNative K).handles.closed x hx,seedCoefficient_value]
  have native : ClockValues K seeded.2.arena clocks (clockMask K 0 []) := by
    intro n a x hx
    change nativePolynomial K seeded.2.arena (clockLookup [((0,0),seeded.1)] n a) x=_
    rw [clockLookup_singleton]
    by_cases zero : n=0
    · subst n
      by_cases axis : a=0
      · subst a
        simp only [and_self,if_true]
        rw [seedValue x hx]
        simp [clockMask,kernelClockAt_seed]
      · simp only [axis,and_false,if_false,native_zero K seeded.2.arena paid.1.handles.closed paid.1.handles.initialized,Pi.zero_apply]
        simp [clockMask,kernelClockAt_seed,axis]
    · simp only [zero,false_and,if_false,native_zero K seeded.2.arena paid.1.handles.closed paid.1.handles.initialized,Pi.zero_apply]
      simp [clockMask,zero]
  change ClockValues K (originalBoot clocks seeded.2).runtime.arena clocks (clockMask K 0 [])
  exact native.extend (originalBoot_grows clocks seeded.2) paid.1.handles.closed paid.1.handles.initialized valid

theorem originalEngineNext_clock_values (K k : ℕ) (engine : RawEngineState)
    (bound : k < K) (cached : CachedNative K engine.runtime) (valid : ClockHandles engine.runtime.arena engine.clocks)
    (native : ClockValues K engine.runtime.arena engine.clocks (clockMask K k [])) :
    ClockValues K (originalEngineNext k engine).runtime.arena (originalEngineNext k engine).clocks (clockMask K (k+1) []) := by
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))
  let residuals:=runtimeSequence actions before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  let checked:=originalChecks after.1 (k+1) residualIds installed.2.1 after.2
  let energy:=originalForceOrEnergy after.1 none checked.2.2
  have hb:=runtimeSetup_cached (k+1) engine.clocks engine.runtime cached valid
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  have hr:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    before.2 before.2 actions (RawExtends.refl _) hb.1 grows (by
      intro action member current extension currentValid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalForceOrEnergy_cached K before.1 (some a) current currentValid (hb.2.extend extension))
  have residualGrow : RawExtends engine.runtime.arena residuals.2.arena :=
    (runtimeSetup_grows _ _ _).trans (runtimeSequence_grows actions grows before.2)
  have hi:=originalInstall_clock_native K k residualIds engine.clocks residuals.2 bound hr.1 (clocks_extend residualGrow valid)
    (native.extend residualGrow cached.handles.closed cached.handles.initialized valid)
  have afterGrow : RawExtends installed.2.2.2.arena energy.2.arena :=
    ((runtimeSetup_grows _ _ _).trans (originalChecks_grows _ _ _ _ _)).trans (originalForceOrEnergy_grows _ _ _)
  exact hi.2.2.extend afterGrow hi.1.handles.closed hi.1.handles.initialized hi.2.1

theorem originalEngine_clock_values (K order : ℕ) (within : order ≤ K) :
    ClockValues K (originalEngine order).runtime.arena (originalEngine order).clocks (clockMask K order []) := by
  induction order with
  | zero=>exact originalEngineInitial_clock_values K
  | succ order ih=>
    exact originalEngineNext_clock_values K order (originalEngine order) (by omega)
      (originalEngine_cached K order) (originalEngine_handles order).clocks (ih (by omega))

theorem originalEngine_clock_kernel (K order : ℕ) (within : order ≤ K) (n : ℕ) (a : Fin 4)
    (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalEngine order).runtime.arena (clockLookup (originalEngine order).clocks n a) x=
      (kernelClockAt order a n x : ℂ) := by
  rw [originalEngine_clock_values K order within n a hx]
  by_cases earlier : n≤order
  · simp only [clockMask,earlier,true_or,if_true]
    rw [kernelClockAt_paid order K within a n earlier]
  · simp only [clockMask,earlier,List.not_mem_nil,and_false,or_self,if_false,Pi.zero_apply]
    rw [kernelClockAt_outside order n a (by omega)]
    rfl

def kernelClockPolynomial (K : ℕ) (a : Fin 4) (n : ℕ) : AngularPolynomial :=
  (smooth_program_const% "clockPolynomial") (sourceEngine K) a n

def kernelEllPolynomial (K n : ℕ) : AngularPolynomial :=
  (smooth_program_const% "ellPolynomial") (sourceEngine K) n

theorem kernelClockPolynomial_constant (K : ℕ) (a : Fin 4) (n : ℕ) :
    kernelClockPolynomial K a n=MvPolynomial.C (kernelClockAt K a n) := rfl

theorem kernelEllPolynomial_expansion (K n : ℕ) : kernelEllPolynomial K n=
    kernelClockPolynomial K 0 n+(MvPolynomial.X 0*kernelClockPolynomial K 1 n+
      (MvPolynomial.X 1*kernelClockPolynomial K 2 n+MvPolynomial.X 2*kernelClockPolynomial K 3 n)) := by
  unfold kernelEllPolynomial
  program_unfold "ellPolynomial"
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl

theorem realCoefficients_monomial (u : AngularExponent) (f : PreparationVacuumCanonicalMoyal.Symbol) :
    realCoefficients (MvPolynomial.monomial u f)=singletonField u (fun x=>(f x : ℂ)) := by
  classical
  funext v x
  by_cases same : u=v <;> simp [realCoefficients,MvPolynomial.coeff_monomial,singletonField,same]

theorem realCoefficients_add (P Q : AngularPolynomial) : realCoefficients (P+Q)=realCoefficients P+realCoefficients Q := by
  funext u x
  simp [realCoefficients]

theorem realCoefficients_X_constant (a : Fin 3) (f : PreparationVacuumCanonicalMoyal.Symbol) :
    realCoefficients (MvPolynomial.X a*MvPolynomial.C f)=singletonField (Finsupp.single a 1) (fun x=>(f x : ℂ)) := by
  rw [show MvPolynomial.X a*MvPolynomial.C f=MvPolynomial.monomial (Finsupp.single a 1) f by
    rw [MvPolynomial.X,←MvPolynomial.monomial_zero',MvPolynomial.monomial_mul,add_zero,one_mul]]
  exact realCoefficients_monomial _ _

theorem readAngular_shift_constant (K : ℕ) (state : RawArena) (id : ℕ) (shift : RawAngle)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) :
    readAngular K state (angularShift (angularConstant id) shift)=singletonField (angleExponent shift) (nativePolynomial K state id) := by
  classical
  unfold angularConstant
  by_cases zero : id=0
  · rw [if_pos zero,zero,native_zero K state closed initialized]
    change readAngular K state []=_
    rw [readAngular_nil]
    funext u x
    simp [singletonField]
  · rw [if_neg zero]
    change readAngular K state [(angleZero+shift,id)]=_
    rw [readAngular_cons,readAngular_nil,add_zero]
    have equal : angleZero+shift=shift := by funext i;simp [angleZero]
    rw [equal]

structure SetupCoefficients (K order : ℕ) (state : RawArena) (setup : RawSetup) : Prop where
  jordan : ∀ a n,n ≤ setup.depth → AngularAgrees (readAngular K state ((setup.jclocks a).getD n []))
    (realCoefficients (kernelClockPolynomial order a n))
  ell : ∀ n,n ≤ setup.depth → AngularAgrees (readAngular K state (setup.ellclock.getD n []))
    (realCoefficients (kernelEllPolynomial order n))

theorem SetupCoefficients.extend {K order : ℕ} {old next : RawArena} {setup : RawSetup}
    (values : SetupCoefficients K order old setup) (growth : RawExtends old next) (closed : RawMoyalClosed old)
    (jclocks : ∀ a,SeriesHandles old (setup.jclocks a)) (ellclock : SeriesHandles old setup.ellclock) :
    SetupCoefficients K order next setup := by
  constructor
  · intro a n within
    rw [readAngular_prefix K growth closed _ (series_getD (jclocks a) n)]
    exact values.jordan a n within
  · intro n within
    rw [readAngular_prefix K growth closed _ (series_getD ellclock n)]
    exact values.ell n within

theorem clockConstant_coefficients (K order : ℕ) (state : RawArena) (clocks : RawClocks)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state)
    (values : ClockValues K state clocks (fun n a x=>(kernelClockAt order a n x : ℂ))) (a : Fin 4) (n : ℕ) :
    AngularAgrees (readAngular K state (angularConstant (clockLookup clocks n a))) (realCoefficients (kernelClockPolynomial order a n)) := by
  rw [readAngular_constant K state _ closed initialized,kernelClockPolynomial_constant,realCoefficients_constant]
  intro u x hx
  unfold singletonField
  split_ifs
  · exact values n a hx
  · rfl

theorem shiftedClock_coefficients (K order : ℕ) (state : RawArena) (clocks : RawClocks)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state)
    (values : ClockValues K state clocks (fun n a x=>(kernelClockAt order a n x : ℂ))) (a : Fin 3) (n : ℕ) :
    AngularAgrees (readAngular K state (angularShift (angularConstant (clockLookup clocks n (Fin.succ a))) (angleUnit a)))
      (realCoefficients (MvPolynomial.X a*kernelClockPolynomial order (Fin.succ a) n)) := by
  rw [readAngular_shift_constant K state _ _ closed initialized,angleExponent_unit,kernelClockPolynomial_constant,realCoefficients_X_constant]
  intro u x hx
  unfold singletonField
  split_ifs
  · exact values n (Fin.succ a) hx
  · rfl

theorem originalSetup_coefficients (K order depth : ℕ) (clocks : RawClocks) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) (valid : ClockHandles state clocks)
    (values : ClockValues K state clocks (fun n a x=>(kernelClockAt order a n x : ℂ))) :
    SetupCoefficients K order (originalSetup depth clocks state).2 (originalSetup depth clocks state).1 := by
  let js:=fun a : Fin 4=>(List.range (depth+1)).map (fun n=>angularConstant (clockLookup clocks n a))
  have jsRead (a : Fin 4) (n : ℕ) (within : n≤depth) : (js a).getD n []=angularConstant (clockLookup clocks n a) := by
    have length : n < (js a).length := by simp only [js,List.length_map,List.length_range];omega
    rw [List.getD_eq_getElem _ _ length]
    simp only [js,List.getElem_map,List.getElem_range]
  let action:=fun n=>angularAdd [(js 0).getD n [],angularShift ((js 1).getD n []) (angleUnit 0),
    angularShift ((js 2).getD n []) (angleUnit 1),angularShift ((js 3).getD n []) (angleUnit 2)]
  have generated:=angularSequence_values K state state (List.range (depth+1)) action
    (fun n=>realCoefficients (kernelEllPolynomial order n)) (RawExtends.refl _) closed initialized
    (fun _ _ _=>angularAdd_grows _ _) (by
      intro n member current extension currentClosed currentInit
      have within : n≤depth := by have h:=List.mem_range.mp member;omega
      have currentValues:=values.extend extension closed initialized valid
      have currentClocks:=clocks_extend extension valid
      have handles (a : Fin 4) : AngularHandles current ((js a).getD n []) := by
        rw [jsRead a n within]
        exact angularConstant_handles _ (clockLookup_handles current clocks currentInit currentClocks n a)
      have allHandles : SeriesHandles current [(js 0).getD n [],angularShift ((js 1).getD n []) (angleUnit 0),
          angularShift ((js 2).getD n []) (angleUnit 1),angularShift ((js 3).getD n []) (angleUnit 2)] := by
        intro rows present
        simp only [List.mem_cons,List.not_mem_nil,or_false] at present
        rcases present with same|same|same|same <;> subst rows
        · exact handles 0
        · exact angularShift_handles (handles 1) _
        · exact angularShift_handles (handles 2) _
        · exact angularShift_handles (handles 3) _
      have structural:=angularAdd_closed_handles [(js 0).getD n [],angularShift ((js 1).getD n []) (angleUnit 0),
        angularShift ((js 2).getD n []) (angleUnit 1),angularShift ((js 3).getD n []) (angleUnit 2)] current currentClosed
      refine ⟨structural.1,structural.2,?_⟩
      intro u x hx
      change angularValue K (angularAdd _ current).2 (angularAdd _ current).1 (fun j=>u j) x=_
      rw [(angularAdd_native K _ current currentClosed currentInit allHandles).2 _ x hx]
      change readAngular K current ((js 0).getD n []) u x+(readAngular K current (angularShift ((js 1).getD n []) (angleUnit 0)) u x+
        (readAngular K current (angularShift ((js 2).getD n []) (angleUnit 1)) u x+
          (readAngular K current (angularShift ((js 3).getD n []) (angleUnit 2)) u x+0)))=_
      have shift0:=shiftedClock_coefficients K order current clocks currentClosed currentInit currentValues 0 n u hx
      have shift1:=shiftedClock_coefficients K order current clocks currentClosed currentInit currentValues 1 n u hx
      have shift2:=shiftedClock_coefficients K order current clocks currentClosed currentInit currentValues 2 n u hx
      simp only [show Fin.succ (0 : Fin 3)=(1 : Fin 4) from rfl] at shift0
      simp only [show Fin.succ (1 : Fin 3)=(2 : Fin 4) from rfl] at shift1
      simp only [show Fin.succ (2 : Fin 3)=(3 : Fin 4) from rfl] at shift2
      rw [jsRead 0 n within,jsRead 1 n within,jsRead 2 n within,jsRead 3 n within,
        clockConstant_coefficients K order current clocks currentClosed currentInit currentValues 0 n u hx,
        shift0,shift1,shift2,kernelEllPolynomial_expansion,realCoefficients_add,realCoefficients_add,realCoefficients_add]
      simp only [Pi.add_apply,add_zero])
  constructor
  · intro a n within
    change n≤depth at within
    change AngularAgrees (readAngular K (originalSetup depth clocks state).2 ((js a).getD n [])) _
    rw [jsRead a n within]
    have structural:=originalSetup_closed_handles depth clocks state initialized closed valid
    exact clockConstant_coefficients K order _ clocks structural.1
      (initialized.trans (originalSetup_grows depth clocks state))
      (values.extend (originalSetup_grows depth clocks state) closed initialized valid) a n
  · intro n within
    change n≤depth at within
    have same:=generated.2.2.2.getD n
    rw [readAngularSeries_getD] at same
    have length : n < ((List.range (depth+1)).map (fun n=>realCoefficients (kernelEllPolynomial order n))).length := by
      simp only [List.length_map,List.length_range];omega
    rw [List.getD_eq_getElem ((List.range (depth+1)).map (fun n=>realCoefficients (kernelEllPolynomial order n)))
      (0 : AngularField) length,List.getElem_map,List.getElem_range] at same
    exact same

theorem actual_reset_setup_coefficients (K order depth : ℕ) (within : order ≤ K) :
    SetupCoefficients K order (actualSetup order depth).2.arena (actualSetup order depth).1 := by
  unfold actualSetup runtimeSetup
  apply originalSetup_coefficients K order depth (originalEngine order).clocks (originalEngine order).runtime.arena
    (originalEngine_cached K order).handles.closed (originalEngine_cached K order).handles.initialized (originalEngine_handles order).clocks
  intro n a x hx
  exact originalEngine_clock_kernel K order within n a x hx

theorem ClockValues.kernel {K order : ℕ} {state : RawArena} {clocks : RawClocks}
    (native : ClockValues K state clocks (clockMask K order [])) (within : order ≤ K) :
    ClockValues K state clocks (fun n a x=>(kernelClockAt order a n x : ℂ)) := by
  intro n a x hx
  rw [native n a hx]
  by_cases earlier : n≤order
  · simp only [clockMask,earlier,true_or,if_true]
    rw [kernelClockAt_paid order K within a n earlier]
  · simp only [clockMask,earlier,List.not_mem_nil,and_false,or_self,if_false,Pi.zero_apply]
    rw [kernelClockAt_outside order n a (by omega)]
    rfl

theorem originalEngineNext_setup_coefficients (K k : ℕ) (engine : RawEngineState)
    (bound : k < K) (cached : CachedNative K engine.runtime) (valid : ClockHandles engine.runtime.arena engine.clocks)
    (native : ClockValues K engine.runtime.arena engine.clocks (clockMask K k [])) :
    SetupCoefficients K (k+1) (originalEngineNext k engine).runtime.arena (engineNextSetup k engine) := by
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))
  let residuals:=runtimeSequence actions before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  let checked:=originalChecks after.1 (k+1) residualIds installed.2.1 after.2
  let energy:=originalForceOrEnergy after.1 none checked.2.2
  have hb:=runtimeSetup_cached (k+1) engine.clocks engine.runtime cached valid
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  have hr:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    before.2 before.2 actions (RawExtends.refl _) hb.1 grows (by
      intro action member current extension currentValid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalForceOrEnergy_cached K before.1 (some a) current currentValid (hb.2.extend extension))
  have residualGrow : RawExtends engine.runtime.arena residuals.2.arena :=
    (runtimeSetup_grows _ _ _).trans (runtimeSequence_grows actions grows before.2)
  have hi:=originalInstall_clock_native K k residualIds engine.clocks residuals.2 bound hr.1 (clocks_extend residualGrow valid)
    (native.extend residualGrow cached.handles.closed cached.handles.initialized valid)
  have ha:=runtimeSetup_cached (k+1) installed.1 installed.2.2.2 hi.1 hi.2.1
  have afterValues : SetupCoefficients K (k+1) after.2.arena after.1 := by
    unfold after runtimeSetup
    exact originalSetup_coefficients K (k+1) (k+1) installed.1 installed.2.2.2.arena
      hi.1.handles.closed hi.1.handles.initialized hi.2.1 (hi.2.2.kernel (by omega))
  have tailGrow : RawExtends after.2.arena energy.2.arena :=
    (originalChecks_grows _ _ _ _ _).trans (originalForceOrEnergy_grows _ _ _)
  exact afterValues.extend tailGrow ha.1.handles.closed ha.2.jclocks ha.2.ellclock

theorem originalEngine_setup_coefficients (K k : ℕ) (bound : k < K) :
    SetupCoefficients K (k+1) (originalEngine (k+1)).runtime.arena (engineNextSetup k (originalEngine k)) :=
  originalEngineNext_setup_coefficients K k (originalEngine k) bound (originalEngine_cached K k) (originalEngine_handles k).clocks
    (originalEngine_clock_values K k (by omega))

theorem actual_engine_jordan_coefficients (k : ℕ) (a : Fin 4) (n : ℕ)
    (within : n ≤ (engineNextSetup k (originalEngine k)).depth) :
    AngularAgrees (readAngular (k+1) (originalEngine (k+1)).runtime.arena
      (((engineNextSetup k (originalEngine k)).jclocks a).getD n []))
      (realCoefficients (kernelClockPolynomial (k+1) a n)) :=
  (originalEngine_setup_coefficients (k+1) k (by omega)).jordan a n within

theorem actual_engine_ell_coefficients (k n : ℕ)
    (within : n ≤ (engineNextSetup k (originalEngine k)).depth) :
    AngularAgrees (readAngular (k+1) (originalEngine (k+1)).runtime.arena
      ((engineNextSetup k (originalEngine k)).ellclock.getD n []))
      (realCoefficients (kernelEllPolynomial (k+1) n)) :=
  (originalEngine_setup_coefficients (k+1) k (by omega)).ell n within

end LowEnergy.PreparationVacuumKernelValues
