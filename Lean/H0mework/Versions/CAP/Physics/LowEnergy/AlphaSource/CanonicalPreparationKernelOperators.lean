import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationKernelClockInputs

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumKernelValues
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumNativeMemo PreparationVacuumSetupValues
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumArenaBudget PreparationVacuumArenaRows
open scoped BigOperators Topology

abbrev kernelJ (depth order : ℕ) (a : Fin 4) (input : List AngularPolynomial) : List AngularPolynomial :=
  (smooth_program_const% "js") depth (sourceEngine order) a input
abbrev kernelResolvent (depth order : ℕ) (input : List AngularPolynomial) : List AngularPolynomial :=
  (smooth_program_const% "resolvent") depth (sourceEngine order) input
abbrev kernelResolventNext (order : ℕ) (input answers : List AngularPolynomial) (n : ℕ) : AngularPolynomial :=
  (smooth_program_const% "resolventNext") (sourceEngine order) input answers n
abbrev kernelOperation (depth order : ℕ) (token : Token) (input : List AngularPolynomial) : List AngularPolynomial :=
  (smooth_program_const% "act") depth (sourceEngine order) token input
abbrev kernelWord (depth order : ℕ) (tokens : List Token) (input : List AngularPolynomial) : List AngularPolynomial :=
  (smooth_program_const% "word") depth (sourceEngine order) tokens input

def KernelSeries (depth : ℕ) (fields : List AngularField) (polynomials : List AngularPolynomial) : Prop :=
  ∀ n,n≤depth → AngularAgrees (fields.getD n 0) (realCoefficients (polynomials.getD n 0))

theorem range_sum {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum=∑ i∈Finset.range n,f i := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [List.range_succ,List.map_append,List.sum_append,Finset.sum_range_succ,ih]
    simp

theorem jordanIndices_sum {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ × ℕ → α) :
    ((jordanIndices n).map f).sum=∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1-i),f (i,j) := by
  simp only [jordanIndices,List.map_flatMap,List.map_map,Function.comp_def]
  have flattenSum (indices : List ℕ) :
      (indices.flatMap (fun i=>(List.range (n+1-i)).map (fun j=>f (i,j)))).sum=
        (indices.map (fun i=>((List.range (n+1-i)).map (fun j=>f (i,j))).sum)).sum := by
    induction indices with
    | nil=>rfl
    | cons i indices ih=>simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]
  rw [flattenSum,range_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact range_sum _ _

theorem kernelJ_getD (depth order : ℕ) (a : Fin 4) (input : List AngularPolynomial) (n : ℕ) (within : n≤depth) :
    (kernelJ depth order a input).getD n 0=
      ∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1-i),
        weighted (n-i-j) (kernelClockPolynomial order a i) (input.getD j 0) := by
  change (List.ofFn (fun m : Fin (depth+1)=>∑ i∈Finset.range (m.val+1),∑ j∈Finset.range (m.val+1-i),
    weighted (m.val-i-j) (kernelClockPolynomial order a i) (input.getD j 0))).getD n 0=_
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,show n<depth+1 by omega,dif_pos,Option.getD_some]

theorem jordanValues_getD (depth : ℕ) (clock input : List AngularField) (n : ℕ) (within : n≤depth) :
    (jordanValues depth clock input).getD n 0=
      (fun u x=>((jordanIndices n).map (fun pair=>convolution (n-pair.1-pair.2)
        (clock.getD pair.1 0) (input.getD pair.2 0) u x)).sum) := by
  rw [List.getD_eq_getElem _ _ (by simp only [jordanValues,List.length_map,List.length_range];omega)]
  simp only [jordanValues,List.getElem_map,List.getElem_range]

theorem realCoefficients_sum {α : Type} (s : Finset α) (P : α → AngularPolynomial) (u : AngularExponent) (x : Phase) :
    realCoefficients (∑ i∈s,P i) u x=∑ i∈s,realCoefficients (P i) u x := by
  simp only [realCoefficients,MvPolynomial.coeff_sum,Finset.sum_apply,Complex.ofReal_sum]

theorem jordanValues_kernel (depth order : ℕ) (axis : Fin 4) (clock input : List AngularField) (polynomials : List AngularPolynomial)
    (hc : ∀ n,n≤depth → AngularAgrees (clock.getD n 0) (realCoefficients (kernelClockPolynomial order axis n)))
    (hi : KernelSeries depth input polynomials) :
    KernelSeries depth (jordanValues depth clock input) (kernelJ depth order axis polynomials) := by
  intro n within u x hx
  rw [jordanValues_getD depth clock input n within,kernelJ_getD depth order axis polynomials n within]
  simp only [realCoefficients_sum]
  rw [jordanIndices_sum]
  apply Finset.sum_congr rfl
  intro i im
  apply Finset.sum_congr rfl
  intro j jm
  have ib : i≤depth := by have h:=Finset.mem_range.mp im;omega
  have jb : j≤depth := by have h:=Finset.mem_range.mp jm;omega
  rw [convolution_congr _ _ _ _ _ (hc i ib) (hi j jb) u hx,convolution_weighted]

theorem realCoefficients_sub (P Q : AngularPolynomial) : realCoefficients (P-Q)=realCoefficients P-realCoefficients Q := by
  funext u x
  simp [realCoefficients]

theorem realCoefficients_scale (f : PreparationVacuumCanonicalMoyal.Symbol) (P : AngularPolynomial) (u : AngularExponent) (x : Phase) :
    realCoefficients (MvPolynomial.C f*P) u x=(f x : ℂ)*realCoefficients P u x := by
  simp [realCoefficients,MvPolynomial.coeff_C_mul]

theorem inverseClock_value (x : Phase) : coefficientValue (inversePoleCoefficient 0) x=(sourceClock x)⁻¹ := by
  rw [inversePoleCoefficient_source]
  rfl

theorem filter_sum {α β : Type} [AddCommMonoid β] (items : List α) (p : α → Bool) (f : α → β) :
    ((items.filter p).map f).sum=(items.map (fun a=>if p a then f a else 0)).sum := by
  induction items with
  | nil=>rfl
  | cons a items ih=>
    cases test : p a <;> simp [test,ih]

theorem resolventIndices_sum {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ × ℕ → α) :
    ((resolventIndices n).map f).sum=∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1-i),
      if i=0 ∧ n-i-j=0 then 0 else f (i,j) := by
  unfold resolventIndices
  rw [filter_sum,jordanIndices_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases excluded : i=0 ∧ n-i-j=0 <;> simp [excluded]

theorem resolventNext_kernel (depth order : ℕ) (ell input answers : List AngularField)
    (polynomials earlier : List AngularPolynomial) (n : ℕ) (within : n≤depth)
    (he : ∀ i,i≤depth → AngularAgrees (ell.getD i 0) (realCoefficients (kernelEllPolynomial order i)))
    (hi : KernelSeries depth input polynomials) (ha : KernelSeries depth answers earlier) :
    AngularAgrees (resolventNextValue ell input answers n) (realCoefficients (kernelResolventNext order polynomials earlier n)) := by
  intro u x hx
  change (coefficientValue (inversePoleCoefficient 0) x : ℂ)*
    ((input.getD n 0) u x-((resolventIndices n).map (fun pair=>
      convolution (n-pair.1-pair.2) (ell.getD pair.1 0) (answers.getD pair.2 0) u x)).sum)=
    realCoefficients (MvPolynomial.C (fun y=>(sourceClock y)⁻¹)*(polynomials.getD n 0-
      ∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1-i),if i=0 ∧ n-i-j=0 then 0 else
        weighted (n-i-j) (kernelEllPolynomial order i) (earlier.getD j 0))) u x
  rw [realCoefficients_scale,realCoefficients_sub]
  simp only [Pi.sub_apply,realCoefficients_sum]
  rw [inverseClock_value,hi n within u hx,resolventIndices_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i im
  apply Finset.sum_congr rfl
  intro j jm
  by_cases excluded : i=0 ∧ n-i-j=0
  · simp only [if_pos excluded,realCoefficients_zero,Pi.zero_apply]
  · rw [if_neg excluded,if_neg excluded]
    have ib : i≤depth := by have h:=Finset.mem_range.mp im;omega
    have jb : j≤depth := by have h:=Finset.mem_range.mp jm;omega
    rw [convolution_congr _ _ _ _ _ (he i ib) (ha j jb) u hx,convolution_weighted]

theorem KernelSeries.appendOne {depth : ℕ} {fields : List AngularField} {polynomials : List AngularPolynomial}
    (sameLength : fields.length=polynomials.length) (same : KernelSeries depth fields polynomials)
    (field : AngularField) (polynomial : AngularPolynomial) (value : AngularAgrees field (realCoefficients polynomial)) :
    KernelSeries depth (fields++[field]) (polynomials++[polynomial]) := by
  intro n within
  by_cases old : n < fields.length
  · rw [List.getD_append _ _ _ _ old,List.getD_append _ _ _ _ (by omega)]
    exact same n within
  · have fieldBound : fields.length ≤ n := by omega
    have polynomialBound : polynomials.length ≤ n := by omega
    rw [List.getD_append_right _ _ _ _ fieldBound,List.getD_append_right _ _ _ _ polynomialBound,←sameLength]
    by_cases newest : n=fields.length
    · rw [newest,Nat.sub_self,List.getD_cons_zero,List.getD_cons_zero]
      exact value
    · rw [List.getD_eq_default [field] 0 (by simp only [List.length_cons,List.length_nil];omega),
        List.getD_eq_default [polynomial] 0 (by simp only [List.length_cons,List.length_nil];omega),realCoefficients_zero]
      intro u x hx
      rfl

theorem resolventValues_kernel (depth order : ℕ) (ell input : List AngularField) (polynomials : List AngularPolynomial)
    (he : ∀ i,i≤depth → AngularAgrees (ell.getD i 0) (realCoefficients (kernelEllPolynomial order i)))
    (hi : KernelSeries depth input polynomials) :
    KernelSeries depth (resolventValues depth ell input) (kernelResolvent depth order polynomials) := by
  have loop (indices : List ℕ) (members : ∀ n,n∈indices → n≤depth)
      (fields : List AngularField) (earlier : List AngularPolynomial)
      (sameLength : fields.length=earlier.length) (same : KernelSeries depth fields earlier) :
      KernelSeries depth (indices.foldl (fun answers n=>answers++[resolventNextValue ell input answers n]) fields)
        (indices.foldl (fun answers n=>answers++[kernelResolventNext order polynomials answers n]) earlier) := by
    induction indices generalizing fields earlier with
    | nil=>exact same
    | cons n indices ih=>
      exact ih (fun i h=>members i (List.mem_cons_of_mem _ h))
        (fields++[resolventNextValue ell input fields n]) (earlier++[kernelResolventNext order polynomials earlier n])
        (by simp only [List.length_append,List.length_cons,List.length_nil,sameLength])
        (same.appendOne sameLength _ _ (resolventNext_kernel depth order ell input fields polynomials earlier n
          (members n (by simp)) he hi same))
  apply loop (List.range (depth+1)) (fun n h=>by have hn:=List.mem_range.mp h;omega) [] [] rfl
  intro n within
  rw [List.getD_nil,List.getD_nil,realCoefficients_zero]
  intro u x hx
  rfl

theorem operationValue_kernel (depth order : ℕ) (clock : Fin 4 → List AngularField) (ell input : List AngularField)
    (token : Token) (polynomials : List AngularPolynomial)
    (hc : ∀ a n,n≤depth → AngularAgrees ((clock a).getD n 0) (realCoefficients (kernelClockPolynomial order a n)))
    (he : ∀ n,n≤depth → AngularAgrees (ell.getD n 0) (realCoefficients (kernelEllPolynomial order n)))
    (hi : KernelSeries depth input polynomials) :
    KernelSeries depth (operationValue depth clock ell token input) (kernelOperation depth order token polynomials) := by
  cases token with
  | inverse=>exact resolventValues_kernel depth order ell input polynomials he hi
  | jordan a=>exact jordanValues_kernel depth order a (clock a) input polynomials (hc a) hi

theorem wordValues_cons (depth : ℕ) (clock : Fin 4 → List AngularField) (ell : List AngularField)
    (token : Token) (tokens : List Token) (input : List AngularField) :
    wordValues depth clock ell (token::tokens) input=operationValue depth clock ell token (wordValues depth clock ell tokens input) := by
  simp only [wordValues,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem wordValues_kernel (depth order : ℕ) (clock : Fin 4 → List AngularField) (ell input : List AngularField)
    (tokens : List Token) (polynomials : List AngularPolynomial)
    (hc : ∀ a n,n≤depth → AngularAgrees ((clock a).getD n 0) (realCoefficients (kernelClockPolynomial order a n)))
    (he : ∀ n,n≤depth → AngularAgrees (ell.getD n 0) (realCoefficients (kernelEllPolynomial order n)))
    (hi : KernelSeries depth input polynomials) :
    KernelSeries depth (wordValues depth clock ell tokens input) (kernelWord depth order tokens polynomials) := by
  induction tokens with
  | nil=>exact hi
  | cons token tokens ih=>
    rw [wordValues_cons]
    exact operationValue_kernel depth order clock ell (wordValues depth clock ell tokens input) token
      (kernelWord depth order tokens polynomials) hc he ih

theorem KernelSeries.transport {depth : ℕ} {left right : List AngularField} {polynomials : List AngularPolynomial}
    (same : SeriesAgrees left right) (kernel : KernelSeries depth right polynomials) : KernelSeries depth left polynomials :=
  fun n within u _x hx=>(same.getD n u hx).trans (kernel n within u hx)

theorem sourceWord_kernel (K order : ℕ) (setup : RawSetup) (query : SourceWordRequest) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (coefficients : SetupCoefficients K order runtime.arena setup) :
    KernelSeries setup.depth (readAngularSeries K (sourceWord setup query runtime).2.arena (sourceWord setup query runtime).1)
      (kernelWord setup.depth order query.2 (kernelInput query.1)) := by
  let source:=sourceInput setup query.1 runtime
  have sourcePaid:=sourceInput_full_native K setup query.1 runtime native
  have setupValues:=coefficients.extend (sourceInput_grows setup query.1 runtime) native.operations.cached.handles.closed
    native.operations.handles.jclocks native.operations.handles.ellclock
  have inputValues : KernelSeries setup.depth (readAngularSeries K source.2.arena source.1) (kernelInput query.1) := by
    intro n within
    rw [readAngularSeries_getD]
    exact sourceInput_coefficients K setup query.1 runtime native.operations.cached n within
  have kernel:=wordValues_kernel setup.depth order (fun a=>readAngularSeries K source.2.arena (setup.jclocks a))
    (readAngularSeries K source.2.arena setup.ellclock) (readAngularSeries K source.2.arena source.1) query.2 (kernelInput query.1)
    (by
      intro a n within
      rw [readAngularSeries_getD]
      exact setupValues.jordan a n within)
    (by
      intro n within
      rw [readAngularSeries_getD]
      exact setupValues.ell n within) inputValues
  exact KernelSeries.transport (sourceWord_native K setup query runtime native).2.2 kernel

theorem actual_engine_source_word_kernel (k : ℕ) (query : SourceWordRequest) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    KernelSeries setup.depth (readAngularSeries (k+1) (sourceWord setup query runtime).2.arena (sourceWord setup query runtime).1)
      (kernelWord setup.depth (k+1) query.2 (kernelInput query.1)) :=
  sourceWord_kernel (k+1) (k+1) _ query _ (originalEngine_full_native (k+1) k)
    (originalEngine_setup_coefficients (k+1) k (by omega))

theorem actual_engine_source_word_kernel_all_jets (k : ℕ) (query : SourceWordRequest) (n m : ℕ)
    (within : n ≤ (engineNextSetup k (originalEngine k)).depth) (u : AngularExponent) (x : Phase) (hx : x∈poleDomain)
    (directions : Fin m → Phase) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    let result:=sourceWord setup query runtime
    iteratedFDeriv ℝ m ((readAngularSeries (k+1) result.2.arena result.1).getD n 0 u) x directions=
      iteratedFDeriv ℝ m (fun y=>(MvPolynomial.coeff u ((kernelWord setup.depth (k+1) query.2 (kernelInput query.1)).getD n 0) y : ℂ)) x directions := by
  have same : ((readAngularSeries (k+1) (sourceWord (engineNextSetup k (originalEngine k)) query (originalEngine (k+1)).runtime).2.arena
      (sourceWord (engineNextSetup k (originalEngine k)) query (originalEngine (k+1)).runtime).1).getD n 0) u=ᶠ[𝓝 x]
      (realCoefficients ((kernelWord (engineNextSetup k (originalEngine k)).depth (k+1) query.2 (kernelInput query.1)).getD n 0)) u := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact actual_engine_source_word_kernel k query n within u hy
  exact congrArg (fun D=>D directions) (same.iteratedFDeriv ℝ m).eq_of_nhds

abbrev PointPolynomial := MvPolynomial (Fin 3) ℂ

def phaseCast (x : Phase) : PreparationVacuumCanonicalMoyal.Symbol →+* ℂ where
  toFun f:=(f x : ℂ)
  map_one' :=rfl
  map_mul' f g:=Complex.ofReal_mul (f x) (g x)
  map_zero' :=rfl
  map_add' f g:=Complex.ofReal_add (f x) (g x)

def pointPolynomial (P : AngularPolynomial) (x : Phase) : PointPolynomial := MvPolynomial.map (phaseCast x) P

def pointAngular (K : ℕ) (state : RawArena) (rows : RawAngular) (x : Phase) : PointPolynomial :=
  (rows.map (fun row=>MvPolynomial.monomial (angleExponent row.1) (nativePolynomial K state row.2 x))).sum

theorem pointPolynomial_coefficient (P : AngularPolynomial) (x : Phase) (u : AngularExponent) :
    MvPolynomial.coeff u (pointPolynomial P x)=realCoefficients P u x := by
  rw [pointPolynomial,MvPolynomial.coeff_map]
  rfl

theorem pointAngular_coefficient (K : ℕ) (state : RawArena) (rows : RawAngular) (x : Phase) (u : AngularExponent) :
    MvPolynomial.coeff u (pointAngular K state rows x)=readAngular K state rows u x := by
  classical
  induction rows with
  | nil=>simp [pointAngular,readAngular,angularValue]
  | cons row rows ih=>
    change MvPolynomial.coeff u (MvPolynomial.monomial (angleExponent row.1) (nativePolynomial K state row.2 x)+pointAngular K state rows x)=_
    rw [MvPolynomial.coeff_add,MvPolynomial.coeff_monomial,ih,readAngular_cons]
    simp only [Pi.add_apply,singletonField]
    split_ifs <;> rfl

theorem angularAgrees_pointPolynomial {K : ℕ} {state : RawArena} {rows : RawAngular} {P : AngularPolynomial}
    (same : AngularAgrees (readAngular K state rows) (realCoefficients P)) (x : Phase) (hx : x∈poleDomain) :
    pointAngular K state rows x=pointPolynomial P x := by
  apply MvPolynomial.ext
  intro u
  rw [pointAngular_coefficient,pointPolynomial_coefficient]
  exact same u hx

theorem pointPolynomial_monomial (u : AngularExponent) (f : PreparationVacuumCanonicalMoyal.Symbol) (x : Phase) :
    pointPolynomial (MvPolynomial.monomial u f) x=MvPolynomial.monomial u (f x : ℂ) := by
  simp [pointPolynomial,phaseCast]

theorem pointAngular_shift (K : ℕ) (state : RawArena) (rows : RawAngular) (shift : RawAngle) (x : Phase) :
    pointAngular K state (angularShift rows shift) x=
      MvPolynomial.monomial (angleExponent shift) 1*pointAngular K state rows x := by
  induction rows with
  | nil=>simp [pointAngular,angularShift]
  | cons row rows ih=>
    change MvPolynomial.monomial (angleExponent (row.1+shift)) (nativePolynomial K state row.2 x)+
      pointAngular K state (angularShift rows shift) x=_
    change _=MvPolynomial.monomial (angleExponent shift) 1*
      (MvPolynomial.monomial (angleExponent row.1) (nativePolynomial K state row.2 x)+pointAngular K state rows x)
    rw [ih,mul_add,MvPolynomial.monomial_mul,one_mul,angleExponent_add,add_comm (angleExponent row.1) (angleExponent shift)]

theorem angularShift_kernel (K : ℕ) (state : RawArena) (rows : RawAngular) (shift : RawAngle) (P : AngularPolynomial)
    (same : AngularAgrees (readAngular K state rows) (realCoefficients P)) :
    AngularAgrees (readAngular K state (angularShift rows shift))
      (realCoefficients (MvPolynomial.monomial (angleExponent shift) 1*P)) := by
  intro u x hx
  rw [←pointAngular_coefficient,pointAngular_shift,angularAgrees_pointPolynomial same x hx,←pointPolynomial_coefficient]
  congr 1
  simp only [pointPolynomial,map_mul]
  rw [show (MvPolynomial.map (phaseCast x)) (MvPolynomial.monomial (angleExponent shift) (1 : PreparationVacuumCanonicalMoyal.Symbol))=
      MvPolynomial.monomial (angleExponent shift) 1 by
    simpa only [pointPolynomial,Pi.one_apply,Complex.ofReal_one] using pointPolynomial_monomial (angleExponent shift) 1 x]

def angularMean : PointPolynomial →+ ℂ :=
  (Finsupp.linearCombination ℂ (fun u : AngularExponent=>(angularMoment u : ℂ))).toAddMonoidHom.comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem angularMean_monomial (u : AngularExponent) (c : ℂ) :
    angularMean (MvPolynomial.monomial u c)=c*(angularMoment u : ℂ) := by
  change Finsupp.linearCombination ℂ (fun u : AngularExponent=>(angularMoment u : ℂ)) (Finsupp.single u c)=_
  rw [Finsupp.linearCombination_single]
  rfl

theorem angularMean_pointAngular (K : ℕ) (state : RawArena) (rows : RawAngular) (x : Phase) :
    angularMean (pointAngular K state rows x)=
      (rows.map (fun row=>(rawMoment row.1 : ℂ)*nativePolynomial K state row.2 x)).sum := by
  induction rows with
  | nil=>exact map_zero angularMean
  | cons row rows ih=>
    change angularMean (MvPolynomial.monomial (angleExponent row.1) (nativePolynomial K state row.2 x)+pointAngular K state rows x)=_
    rw [map_add,angularMean_monomial,ih]
    simp only [List.map_cons,List.sum_cons]
    congr 1
    rw [←rawMoment_source,Complex.ofReal_ratCast,mul_comm]

theorem angularMean_pointPolynomial (P : AngularPolynomial) (x : Phase) :
    angularMean (pointPolynomial P x)=(average P x : ℂ) := by
  classical
  conv_lhs=>rw [MvPolynomial.as_sum P]
  simp only [pointPolynomial,map_sum]
  simp only [MvPolynomial.map_monomial,angularMean_monomial]
  simp only [average,Finset.sum_apply,Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro u _
  exact mul_comm _ _

theorem angularAverage_kernel (K : ℕ) (state : RawArena) (rows : RawAngular) (P : AngularPolynomial)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) (valid : AngularHandles state rows)
    (same : AngularAgrees (readAngular K state rows) (realCoefficients P)) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (angularAverage rows state).2 (angularAverage rows state).1 x=(average P x : ℂ) := by
  rw [angularAverage_native K rows state closed initialized valid x hx,←angularMean_pointAngular,
    angularAgrees_pointPolynomial same x hx,angularMean_pointPolynomial]

theorem originalWord_kernel (K order : ℕ) (setup : RawSetup) (tokens : List Token) (input : RawSeries)
    (P : List AngularPolynomial) (runtime : RawRuntime) (native : FullSetupNative K setup runtime)
    (valid : SeriesHandles runtime.arena input) (coefficients : SetupCoefficients K order runtime.arena setup)
    (inputKernel : KernelSeries setup.depth (readAngularSeries K runtime.arena input) P) :
    KernelSeries setup.depth (readAngularSeries K (originalWord setup tokens input runtime).2.arena
      (originalWord setup tokens input runtime).1) (kernelWord setup.depth order tokens P) := by
  have kernel:=wordValues_kernel setup.depth order (fun a=>readAngularSeries K runtime.arena (setup.jclocks a))
    (readAngularSeries K runtime.arena setup.ellclock) (readAngularSeries K runtime.arena input) tokens P
    (by intro a n within;rw [readAngularSeries_getD];exact coefficients.jordan a n within)
    (by intro n within;rw [readAngularSeries_getD];exact coefficients.ell n within) inputKernel
  exact KernelSeries.transport (originalWord_full_native K setup tokens input runtime native valid).2.2 kernel

theorem KernelSeries.extend {K depth : ℕ} {old next : RawArena} {rows : RawSeries} {P : List AngularPolynomial}
    (same : KernelSeries depth (readAngularSeries K old rows) P) (growth : RawExtends old next)
    (closed : RawMoyalClosed old) (valid : SeriesHandles old rows) :
    KernelSeries depth (readAngularSeries K next rows) P := by
  rw [readAngularSeries_prefix K growth closed rows valid]
  exact same

theorem angularAdd_two_kernel (K : ℕ) (state : RawArena) (left right : RawAngular) (P Q : AngularPolynomial)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state)
    (hl : AngularHandles state left) (hr : AngularHandles state right)
    (leftKernel : AngularAgrees (readAngular K state left) (realCoefficients P))
    (rightKernel : AngularAgrees (readAngular K state right) (realCoefficients Q)) :
    AngularAgrees (readAngular K (angularAdd [left,right] state).2 (angularAdd [left,right] state).1)
      (realCoefficients (P+Q)) := by
  intro u x hx
  have valid : SeriesHandles state [left,right] := by
    intro rows member
    rcases List.mem_cons.mp member with equal|last
    · subst rows;exact hl
    · have equal:=List.mem_singleton.mp last
      subst rows;exact hr
  change angularValue K (angularAdd [left,right] state).2 (angularAdd [left,right] state).1 (fun j=>u j) x=_
  rw [(angularAdd_native K [left,right] state closed initialized valid).2 _ x hx]
  change readAngular K state left u x+(readAngular K state right u x+0)=_
  rw [leftKernel u hx,rightKernel u hx,realCoefficients_add]
  simp only [Pi.add_apply,add_zero]

theorem rationalCoefficient_value (q : ℚ) (x : Phase) :
    coefficientValue (polynomialCoefficient (MvPolynomial.C q)) x=(q : ℝ) := by
  rw [polynomialCoefficient_source]
  simp [polynomialSymbol,evalAt]

theorem angularScale_rat_kernel (K : ℕ) (state : RawArena) (q : ℚ) (rows : RawAngular) (P : AngularPolynomial)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) (valid : AngularHandles state rows)
    (same : AngularAgrees (readAngular K state rows) (realCoefficients P)) :
    AngularAgrees (readAngular K (angularScale (polynomialCoefficient (MvPolynomial.C q)) rows state).2
      (angularScale (polynomialCoefficient (MvPolynomial.C q)) rows state).1)
      (realCoefficients (MvPolynomial.C (fun _ : Phase=>(q : ℝ))*P)) := by
  intro u x hx
  change angularValue K (angularScale (polynomialCoefficient (MvPolynomial.C q)) rows state).2
    (angularScale (polynomialCoefficient (MvPolynomial.C q)) rows state).1 (fun j=>u j) x=_
  rw [angularScale_native K _ rows state closed initialized valid _ x hx,rationalCoefficient_value]
  change (q : ℂ)*readAngular K state rows u x=_
  rw [same u hx,realCoefficients_scale]
  simp only [Complex.ofReal_ratCast]

def rawTermPolynomial (depth order : ℕ) (input : List AngularPolynomial) (term : RawTemporalTerm) (n : ℕ) : AngularPolynomial :=
  MvPolynomial.C (fun _ : Phase=>(term.coefficient : ℝ))*
    (MvPolynomial.monomial (angleExponent term.exponent) 1*(kernelWord depth order term.tokens input).getD n 0)

def rawTablePolynomial (depth order : ℕ) (input : List AngularPolynomial) (table : List RawTemporalTerm) (n : ℕ) : AngularPolynomial :=
  table.foldl (fun P term=>P+rawTermPolynomial depth order input term n) 0

def NativeArray (K depth : ℕ) (state : RawArena) (rows : RawSeries) (target : ℕ → AngularPolynomial) : Prop :=
  ∀ n,n≤depth → AngularAgrees (readAngular K state (rows.getD n [])) (realCoefficients (target n))

theorem NativeArray.extend {K depth : ℕ} {old next : RawArena} {rows : RawSeries} {target : ℕ → AngularPolynomial}
    (same : NativeArray K depth old rows target) (growth : RawExtends old next) (closed : RawMoyalClosed old)
    (valid : SeriesHandles old rows) : NativeArray K depth next rows target := by
  intro n within
  rw [readAngular_prefix K growth closed _ (series_getD valid n)]
  exact same n within

theorem NativeArray.set {K depth : ℕ} {state : RawArena} {rows : RawSeries} {target : ℕ → AngularPolynomial}
    (same : NativeArray K depth state rows target) (length : rows.length=depth+1) (index : ℕ)
    (value : RawAngular) (P : AngularPolynomial) (read : AngularAgrees (readAngular K state value) (realCoefficients P)) :
    NativeArray K depth state (rows.set index value) (Function.update target index P) := by
  intro n within
  have inside : n < rows.length := by omega
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_set] using inside),List.getElem_set]
  by_cases hit : index=n
  · subst n
    simp only [ite_true,Function.update_self]
    exact read
  · rw [if_neg hit,Function.update_of_ne (Ne.symm hit),←List.getD_eq_getElem rows [] inside]
    exact same n within

def temporalDegreeStep (term : RawTemporalTerm) (operated : RawSeries)
    (acc : RawSeries × RawRuntime) (index : ℕ) : RawSeries × RawRuntime :=
  let scaled:=runAngular (angularScale (polynomialCoefficient (MvPolynomial.C term.coefficient))
    (angularShift (operated.getD index []) term.exponent)) acc.2
  let added:=runAngular (angularAdd [acc.1.getD index [],scaled.1]) scaled.2
  (acc.1.set index added.1,added.2)

def polynomialDegreeStep (contribution target : ℕ → AngularPolynomial) (index : ℕ) : ℕ → AngularPolynomial :=
  Function.update target index (target index+contribution index)

theorem temporalDegreeStep_grows (term : RawTemporalTerm) (operated : RawSeries)
    (acc : RawSeries × RawRuntime) (index : ℕ) : RawExtends acc.2.arena (temporalDegreeStep term operated acc index).2.arena :=
  (angularScale_grows _ _ _).trans (angularAdd_grows _ _)

theorem temporalDegreeStep_native (K order : ℕ) (setup : RawSetup) (term : RawTemporalTerm) (input : List AngularPolynomial)
    (operated : RawSeries) (acc : RawSeries × RawRuntime) (target : ℕ → AngularPolynomial) (index : ℕ)
    (within : index ≤ setup.depth) (native : FullSetupNative K setup acc.2)
    (length : acc.1.length=setup.depth+1) (valid : SeriesHandles acc.2.arena acc.1)
    (operatedValid : SeriesHandles acc.2.arena operated)
    (operatedKernel : KernelSeries setup.depth (readAngularSeries K acc.2.arena operated) (kernelWord setup.depth order term.tokens input))
    (values : NativeArray K setup.depth acc.2.arena acc.1 target) :
    let result:=temporalDegreeStep term operated acc index
    FullSetupNative K setup result.2 ∧ result.1.length=setup.depth+1 ∧ SeriesHandles result.2.arena result.1 ∧
      NativeArray K setup.depth result.2.arena result.1 (polynomialDegreeStep (rawTermPolynomial setup.depth order input term) target index) := by
  let shifted:=angularShift (operated.getD index []) term.exponent
  let c:=polynomialCoefficient (MvPolynomial.C term.coefficient)
  let scaled:=runAngular (angularScale c shifted) acc.2
  let added:=runAngular (angularAdd [acc.1.getD index [],scaled.1]) scaled.2
  have shiftedValid:=angularShift_handles (series_getD operatedValid index) term.exponent
  have operatedRead:=operatedKernel index within
  rw [readAngularSeries_getD] at operatedRead
  have shiftedRead:=angularShift_kernel K acc.2.arena (operated.getD index []) term.exponent _ operatedRead
  have scaledRead:=angularScale_rat_kernel K acc.2.arena term.coefficient shifted _ native.operations.cached.handles.closed
    native.operations.cached.handles.initialized shiftedValid shiftedRead
  have scaledPaid:=runAngularScale_cached c shifted acc.2 native.operations.cached
  have scaledNative:=runAngularScale_full_native K setup c shifted acc.2 native
  have scaleGrow : RawExtends acc.2.arena scaled.2.arena := angularScale_grows _ _ _
  have accValid:=series_extend scaleGrow valid
  have accValues:=values.extend scaleGrow native.operations.cached.handles.closed valid
  have addedRead:=angularAdd_two_kernel K scaled.2.arena (acc.1.getD index []) scaled.1 _ _ scaledPaid.1.handles.closed
    scaledPaid.1.handles.initialized (series_getD accValid index) scaledPaid.2 (accValues index within) scaledRead
  have addedPaid:=runAngularAdd_cached [acc.1.getD index [],scaled.1] scaled.2 scaledPaid.1
  have addedNative:=runAngularAdd_full_native K setup [acc.1.getD index [],scaled.1] scaled.2 scaledNative
  have addGrow : RawExtends scaled.2.arena added.2.arena := angularAdd_grows _ _
  have totalGrow : RawExtends acc.2.arena added.2.arena := scaleGrow.trans addGrow
  refine ⟨addedNative,?_,series_set_handles (series_extend totalGrow valid) index added.1 addedPaid.2,?_⟩
  · exact List.length_set.trans length
  · exact (values.extend totalGrow native.operations.cached.handles.closed valid).set length index added.1
      (target index+rawTermPolynomial setup.depth order input term index) addedRead

theorem polynomialDegreeFold (indices : List ℕ) (distinct : indices.Nodup) (contribution target : ℕ → AngularPolynomial) (n : ℕ) :
    (indices.foldl (polynomialDegreeStep contribution) target) n=
      if n∈indices then target n+contribution n else target n := by
  classical
  induction indices generalizing target with
  | nil=>rfl
  | cons i indices ih=>
    rw [List.foldl_cons,ih (List.nodup_cons.mp distinct).2]
    by_cases hit : n=i
    · subst n
      have absent:= (List.nodup_cons.mp distinct).1
      simp [absent,polynomialDegreeStep]
    · simp [hit,polynomialDegreeStep,Function.update_of_ne]

theorem temporalDegreeFold_native (K order : ℕ) (setup : RawSetup) (term : RawTemporalTerm) (input : List AngularPolynomial)
    (operated : RawSeries) (base : RawRuntime) (indices : List ℕ) (members : ∀ n,n∈indices → n ≤ setup.depth)
    (acc : RawSeries × RawRuntime) (target : ℕ → AngularPolynomial)
    (baseClosed : RawMoyalClosed base.arena) (growth : RawExtends base.arena acc.2.arena)
    (native : FullSetupNative K setup acc.2) (length : acc.1.length=setup.depth+1) (valid : SeriesHandles acc.2.arena acc.1)
    (operatedValid : SeriesHandles base.arena operated)
    (operatedKernel : KernelSeries setup.depth (readAngularSeries K base.arena operated) (kernelWord setup.depth order term.tokens input))
    (values : NativeArray K setup.depth acc.2.arena acc.1 target) :
    let result:=indices.foldl (temporalDegreeStep term operated) acc
    FullSetupNative K setup result.2 ∧ result.1.length=setup.depth+1 ∧ SeriesHandles result.2.arena result.1 ∧
      RawExtends base.arena result.2.arena ∧
      NativeArray K setup.depth result.2.arena result.1
        (indices.foldl (polynomialDegreeStep (rawTermPolynomial setup.depth order input term)) target) := by
  induction indices generalizing acc target with
  | nil=>exact ⟨native,length,valid,growth,values⟩
  | cons index indices ih=>
    have step:=temporalDegreeStep_native K order setup term input operated acc target index (members index (by simp))
      native length valid (series_extend growth operatedValid) (operatedKernel.extend growth baseClosed operatedValid) values
    exact ih (fun n h=>members n (List.mem_cons_of_mem _ h)) (temporalDegreeStep term operated acc index) _
      (growth.trans (temporalDegreeStep_grows term operated acc index)) step.1 step.2.1 step.2.2.1 step.2.2.2

def temporalRowStep (setup : RawSetup) (input : RawSeries) (out : RawSeries × RawRuntime) (term : RawTemporalTerm) : RawSeries × RawRuntime :=
  let operated:=originalWord setup term.tokens input out.2
  (List.range (setup.depth+1)).foldl (temporalDegreeStep term operated.1) (out.1,operated.2)

def temporalProgram (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4)) (runtime : RawRuntime) :
    RawSeries × RawRuntime := (rawTemporalTable a b equation).foldl (temporalRowStep setup input)
      (List.replicate (setup.depth+1) [],runtime)

theorem originalApplyT_program (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4)) (runtime : RawRuntime) :
    originalApplyT setup a b input equation runtime=
      let result:=temporalProgram setup a b input equation runtime
      runtimeSequence (result.1.map (fun row=>runArena (angularAverage row))) result.2 := rfl

theorem temporalRowStep_native (K order : ℕ) (setup : RawSetup) (input : RawSeries) (P : List AngularPolynomial)
    (base : RawRuntime) (out : RawSeries × RawRuntime) (term : RawTemporalTerm) (target : ℕ → AngularPolynomial)
    (baseNative : FullSetupNative K setup base) (baseCoefficients : SetupCoefficients K order base.arena setup)
    (inputValid : SeriesHandles base.arena input) (inputKernel : KernelSeries setup.depth (readAngularSeries K base.arena input) P)
    (growth : RawExtends base.arena out.2.arena) (native : FullSetupNative K setup out.2)
    (length : out.1.length=setup.depth+1) (valid : SeriesHandles out.2.arena out.1)
    (values : NativeArray K setup.depth out.2.arena out.1 target) :
    let result:=temporalRowStep setup input out term
    FullSetupNative K setup result.2 ∧ result.1.length=setup.depth+1 ∧ SeriesHandles result.2.arena result.1 ∧
      RawExtends out.2.arena result.2.arena ∧
      NativeArray K setup.depth result.2.arena result.1 (fun n=>target n+rawTermPolynomial setup.depth order P term n) := by
  let operated:=originalWord setup term.tokens input out.2
  have wordPaid:=originalWord_full_native K setup term.tokens input out.2 native (series_extend growth inputValid)
  have wordGrow:=originalWord_grows setup term.tokens input out.2
  have wordKernel:=originalWord_kernel K order setup term.tokens input P out.2 native (series_extend growth inputValid)
    (baseCoefficients.extend growth baseNative.operations.cached.handles.closed baseNative.operations.handles.jclocks baseNative.operations.handles.ellclock)
    (inputKernel.extend growth baseNative.operations.cached.handles.closed inputValid)
  have degrees:=temporalDegreeFold_native K order setup term P operated.1 operated.2 (List.range (setup.depth+1))
    (fun n h=>by have hn:=List.mem_range.mp h;omega) (out.1,operated.2) target
    wordPaid.1.operations.cached.handles.closed (RawExtends.refl _) wordPaid.1 length (series_extend wordGrow valid)
    wordPaid.2.1 wordKernel (values.extend wordGrow native.operations.cached.handles.closed valid)
  refine ⟨degrees.1,degrees.2.1,degrees.2.2.1,wordGrow.trans degrees.2.2.2.1,?_⟩
  intro n within
  have value:=degrees.2.2.2.2 n within
  rw [polynomialDegreeFold _ List.nodup_range _ _ n,if_pos (List.mem_range.mpr (by omega))] at value
  exact value

theorem polynomialTableFold_apply (depth order : ℕ) (P : List AngularPolynomial) (terms : List RawTemporalTerm)
    (target : ℕ → AngularPolynomial) (n : ℕ) :
    (terms.foldl (fun F term=>fun i=>F i+rawTermPolynomial depth order P term i) target) n=
      terms.foldl (fun Q term=>Q+rawTermPolynomial depth order P term n) (target n) := by
  induction terms generalizing target with
  | nil=>rfl
  | cons term terms ih=>exact ih (fun i=>target i+rawTermPolynomial depth order P term i)

theorem temporalFold_native (K order : ℕ) (setup : RawSetup) (input : RawSeries) (P : List AngularPolynomial)
    (base : RawRuntime) (terms : List RawTemporalTerm) (out : RawSeries × RawRuntime) (target : ℕ → AngularPolynomial)
    (baseNative : FullSetupNative K setup base) (baseCoefficients : SetupCoefficients K order base.arena setup)
    (inputValid : SeriesHandles base.arena input) (inputKernel : KernelSeries setup.depth (readAngularSeries K base.arena input) P)
    (growth : RawExtends base.arena out.2.arena) (native : FullSetupNative K setup out.2)
    (length : out.1.length=setup.depth+1) (valid : SeriesHandles out.2.arena out.1)
    (values : NativeArray K setup.depth out.2.arena out.1 target) :
    let result:=terms.foldl (temporalRowStep setup input) out
    FullSetupNative K setup result.2 ∧ result.1.length=setup.depth+1 ∧ SeriesHandles result.2.arena result.1 ∧
      NativeArray K setup.depth result.2.arena result.1
        (fun n=>terms.foldl (fun Q term=>Q+rawTermPolynomial setup.depth order P term n) (target n)) := by
  induction terms generalizing out target with
  | nil=>exact ⟨native,length,valid,values⟩
  | cons term terms ih=>
    have step:=temporalRowStep_native K order setup input P base out term target baseNative baseCoefficients inputValid inputKernel
      growth native length valid values
    exact ih (temporalRowStep setup input out term) _ (growth.trans step.2.2.2.1) step.1 step.2.1 step.2.2.1 step.2.2.2.2

theorem temporalProgram_native (K order : ℕ) (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (P : List AngularPolynomial)
    (equation : Option (Fin 4)) (runtime : RawRuntime) (native : FullSetupNative K setup runtime)
    (coefficients : SetupCoefficients K order runtime.arena setup) (valid : SeriesHandles runtime.arena input)
    (inputKernel : KernelSeries setup.depth (readAngularSeries K runtime.arena input) P) :
    let result:=temporalProgram setup a b input equation runtime
    FullSetupNative K setup result.2 ∧ result.1.length=setup.depth+1 ∧ SeriesHandles result.2.arena result.1 ∧
      NativeArray K setup.depth result.2.arena result.1 (rawTablePolynomial setup.depth order P (rawTemporalTable a b equation)) := by
  apply temporalFold_native K order setup input P runtime _ (List.replicate (setup.depth+1) [],runtime) (fun _=>0)
    native coefficients valid inputKernel (RawExtends.refl _) native (List.length_replicate ..)
  · intro rows member
    have empty:rows=[] := (List.mem_replicate.mp member).2
    subst rows
    intro row present
    exact False.elim (List.not_mem_nil present)
  · intro n within
    rw [List.getD_replicate [] (by omega),readAngular_nil,realCoefficients_zero]
    intro u x hx
    rfl

theorem runtimeSequence_scalar_values {α : Type} (K : ℕ) (base current : RawRuntime) (items : List α)
    (action : α → RuntimeAction ℕ) (value : α → Phase → ℂ)
    (extension : RawExtends base.arena current.arena) (cached : CachedNative K current)
    (grows : ∀ item,item∈items → RuntimeGrows (action item))
    (step : ∀ item,item∈items → ∀ runtime,RawExtends base.arena runtime.arena → CachedNative K runtime →
      CachedNative K (action item runtime).2 ∧ Handle (action item runtime).2.arena (action item runtime).1 ∧
        Set.EqOn (nativePolynomial K (action item runtime).2.arena (action item runtime).1) (value item) poleDomain) :
    let result:=runtimeSequence (items.map action) current
    CachedNative K result.2 ∧ ListHandles result.2.arena result.1 ∧
      ∀ x,x∈poleDomain → (result.1.map (fun id=>nativePolynomial K result.2.arena id x))=items.map (fun item=>value item x) := by
  induction items generalizing current with
  | nil=>exact ⟨cached,fun _ member=>False.elim (List.not_mem_nil member),fun _ _=>rfl⟩
  | cons item items ih=>
    have one:=step item (by simp) current extension cached
    have tail:=ih (action item current).2 (extension.trans (grows item (by simp) current)) one.1
      (fun a h=>grows a (List.mem_cons_of_mem _ h)) (fun a h=>step a (List.mem_cons_of_mem _ h))
    have growth : RawExtends (action item current).2.arena (runtimeSequence (items.map action) (action item current).2).2.arena := by
      apply runtimeSequence_grows
      intro a member runtime
      obtain ⟨entry,h,rfl⟩:=List.mem_map.mp member
      exact grows entry (List.mem_cons_of_mem _ h) runtime
    refine ⟨tail.1,?_,?_⟩
    · intro id member
      rcases List.mem_cons.mp member with equal|old
      · subst id;exact handle_extend growth one.2.1
      · exact tail.2.1 id old
    · intro x hx
      change nativePolynomial K (runtimeSequence (items.map action) (action item current).2).2.arena (action item current).1 x::
        ((runtimeSequence (items.map action) (action item current).2).1.map (fun id=>nativePolynomial K
          (runtimeSequence (items.map action) (action item current).2).2.arena id x))=_
      rw [nativePolynomial_prefix K growth one.1.handles.closed _ one.2.1,one.2.2 hx,tail.2.2 x hx]
      rfl

theorem averages_native (K : ℕ) (rows : RawSeries) (runtime : RawRuntime) (cached : CachedNative K runtime)
    (valid : SeriesHandles runtime.arena rows) :
    let result:=runtimeSequence (rows.map (fun row=>runArena (angularAverage row))) runtime
    CachedNative K result.2 ∧ ListHandles result.2.arena result.1 ∧
      ∀ x,x∈poleDomain → (result.1.map (fun id=>nativePolynomial K result.2.arena id x))=
        rows.map (fun row=>angularMean (pointAngular K runtime.arena row x)) := by
  apply runtimeSequence_scalar_values K runtime runtime rows _ _ (RawExtends.refl _) cached
    (fun _ _ _=>angularAverage_grows _ _)
  intro row member current growth paid
  have output:=runAverage_cached row current paid
  refine ⟨output.1,output.2,?_⟩
  intro x hx
  rw [show nativePolynomial K (runArena (angularAverage row) current).2.arena (runArena (angularAverage row) current).1 x=
      (row.map (fun entry=>(rawMoment entry.1 : ℂ)*nativePolynomial K current.arena entry.2 x)).sum from
    angularAverage_native K row current.arena paid.handles.closed paid.handles.initialized (angular_extend growth (valid row member)) x hx]
  change (row.map (fun entry=>(rawMoment entry.1 : ℂ)*nativePolynomial K current.arena entry.2 x)).sum=angularMean (pointAngular K runtime.arena row x)
  rw [angularMean_pointAngular]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry present
  rw [nativePolynomial_prefix K growth cached.handles.closed entry.2 (valid row member entry present)]

theorem originalApplyT_raw_table_value (K order : ℕ) (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (P : List AngularPolynomial)
    (equation : Option (Fin 4)) (runtime : RawRuntime) (native : FullSetupNative K setup runtime)
    (coefficients : SetupCoefficients K order runtime.arena setup) (valid : SeriesHandles runtime.arena input)
    (inputKernel : KernelSeries setup.depth (readAngularSeries K runtime.arena input) P)
    (n : ℕ) (within : n ≤ setup.depth) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalApplyT setup a b input equation runtime).2.arena
      ((originalApplyT setup a b input equation runtime).1.getD n 0) x=
        (average (rawTablePolynomial setup.depth order P (rawTemporalTable a b equation) n) x : ℂ) := by
  let generated:=temporalProgram setup a b input equation runtime
  have paid:=temporalProgram_native K order setup a b input P equation runtime native coefficients valid inputKernel
  have means:=averages_native K generated.1 generated.2 paid.1.operations.cached paid.2.2.1
  let result:=runtimeSequence (generated.1.map (fun row=>runArena (angularAverage row))) generated.2
  rw [originalApplyT_program]
  change nativePolynomial K result.2.arena (result.1.getD n 0) x=_
  have equality:=congrArg (fun values : List ℂ=>values.getD n 0) (means.2.2 x hx)
  have leftDefault : nativePolynomial K result.2.arena 0 x=0 := by
    rw [native_zero K result.2.arena means.1.handles.closed means.1.handles.initialized]
    rfl
  have rightDefault : angularMean (pointAngular K generated.2.arena [] x)=0 := map_zero angularMean
  rw [←leftDefault,List.getD_map] at equality
  rw [leftDefault,←rightDefault,List.getD_map] at equality
  rw [equality,angularAgrees_pointPolynomial (paid.2.2.2 n within) x hx,angularMean_pointPolynomial]

def constantSymbol : ℝ →+* PreparationVacuumCanonicalMoyal.Symbol where
  toFun c:=fun _=>c
  map_one' :=rfl
  map_mul' _ _:=rfl
  map_zero' :=rfl
  map_add' _ _:=rfl

def literalPolynomial : ℝ →+* AngularPolynomial := MvPolynomial.C.comp constantSymbol

def interpretRawTerm (term : RawTemporalTerm) : TableTerm :=
  ⟨angleExponent term.exponent,term.tokens,(term.coefficient : ℝ)⟩

def tableTermValue (F : AngularExponent → List Token → AngularPolynomial) (term : TableTerm) : AngularPolynomial :=
  literalPolynomial term.coefficient*F term.exponent term.tokens

def tableValue (F : AngularExponent → List Token → AngularPolynomial) (terms : List TableTerm) : AngularPolynomial :=
  (terms.map (tableTermValue F)).sum

def kernelDerivativeExponent (a : Fin 4) : AngularExponent :=
  if h : a.val=0 then 0 else Finsupp.single ⟨a.val-1,by omega⟩ 1

def kernelDifferentiate (a : Fin 4) (term : TableTerm) : List TableTerm :=
  term.tokens.zipIdx.flatMap (fun (token,j)=>match token with
    | .inverse=>[⟨kernelDerivativeExponent a,term.tokens.take j++[.inverse,.inverse]++term.tokens.drop (j+1),term.coefficient⟩]
    | .jordan b=>if b=a then [⟨0,term.tokens.take j++term.tokens.drop (j+1),-term.coefficient⟩] else [])

abbrev kernelTable (a b : Fin 4) (equation : Option (Fin 4)) : List TableTerm :=
  (smooth_program_const% "table") a b equation

theorem kernelTable_expansion (a b : Fin 4) (equation : Option (Fin 4)) :
    kernelTable a b equation=
      match equation with
      | none=>[⟨0,temporalWord a b,1⟩,⟨0,temporalWord b a,1⟩]
      | some axis=>kernelDifferentiate axis ⟨0,temporalWord a b,1⟩++kernelDifferentiate axis ⟨0,temporalWord b a,1⟩ := by
  cases equation with
  | none=>rfl
  | some axis=>
    unfold_response_table
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rfl

def rawDifferentiate (axis : Fin 4) (tokens : List Token) (coefficient : ℚ) : List RawTemporalTerm :=
  tokens.zipIdx.filterMap (fun token=>
    match token.1 with
    | .inverse=>some ⟨Fin.cases angleZero (fun i=>angleUnit i) axis,
      tokens.take token.2++[.inverse,.inverse]++tokens.drop (token.2+1),coefficient⟩
    | .jordan a=>if a=axis then some ⟨angleZero,tokens.take token.2++tokens.drop (token.2+1),-coefficient⟩ else none)

theorem derivativeExponent_source (a : Fin 4) :
    angleExponent (Fin.cases angleZero (fun i=>angleUnit i) a)=kernelDerivativeExponent a := by
  refine Fin.cases ?_ (fun i=>?_) a
  · exact angleExponent_zero
  · simp only [Fin.cases_succ,kernelDerivativeExponent]
    rw [dif_neg (show (Fin.succ i).val≠0 from Nat.succ_ne_zero i.val),angleExponent_unit]
    congr 1

theorem rawDifferentiate_kernel (axis : Fin 4) (tokens : List Token) (coefficient : ℚ) :
    (rawDifferentiate axis tokens coefficient).map interpretRawTerm=
      kernelDifferentiate axis ⟨0,tokens,(coefficient : ℝ)⟩ := by
  have loop (entries : List (Token × ℕ)) :
      (entries.filterMap (fun token=>match token.1 with
        | .inverse=>some (⟨Fin.cases angleZero (fun i=>angleUnit i) axis,
            tokens.take token.2++[.inverse,.inverse]++tokens.drop (token.2+1),coefficient⟩ : RawTemporalTerm)
        | .jordan a=>if a=axis then some ⟨angleZero,tokens.take token.2++tokens.drop (token.2+1),-coefficient⟩ else none)).map interpretRawTerm=
      entries.flatMap (fun token=>match token.1 with
        | .inverse=>[(⟨kernelDerivativeExponent axis,tokens.take token.2++[.inverse,.inverse]++tokens.drop (token.2+1),(coefficient : ℝ)⟩ : TableTerm)]
        | .jordan a=>if a=axis then [⟨0,tokens.take token.2++tokens.drop (token.2+1),-(coefficient : ℝ)⟩] else []) := by
    induction entries with
    | nil=>rfl
    | cons entry entries ih=>
      rcases entry with ⟨token,index⟩
      cases token with
      | inverse=>simp only [List.filterMap_cons,List.flatMap_cons,List.map_cons,List.singleton_append,interpretRawTerm,derivativeExponent_source,ih]
      | jordan a=>
        by_cases same : a=axis
        · simp only [List.filterMap_cons,List.flatMap_cons,if_pos same,List.map_cons,List.singleton_append,interpretRawTerm,angleExponent_zero,Rat.cast_neg,ih]
        · simp only [List.filterMap_cons,List.flatMap_cons,if_neg same,List.nil_append,ih]
  exact loop tokens.zipIdx

theorem tableValue_append (F : AngularExponent → List Token → AngularPolynomial) (left right : List TableTerm) :
    tableValue F (left++right)=tableValue F left+tableValue F right := by
  simp only [tableValue,List.map_append,List.sum_append]

theorem differentiate_value_two (F : AngularExponent → List Token → AngularPolynomial) (axis : Fin 4) (tokens : List Token) :
    tableValue F (kernelDifferentiate axis ⟨0,tokens,2⟩)=
      tableValue F (kernelDifferentiate axis ⟨0,tokens,1⟩)+tableValue F (kernelDifferentiate axis ⟨0,tokens,1⟩) := by
  let terms:=fun (c : ℝ) (entries : List (Token × ℕ))=>entries.flatMap (fun token=>match token.1 with
    | .inverse=>[(⟨kernelDerivativeExponent axis,tokens.take token.2++[.inverse,.inverse]++tokens.drop (token.2+1),c⟩ : TableTerm)]
    | .jordan a=>if a=axis then [⟨0,tokens.take token.2++tokens.drop (token.2+1),-c⟩] else [])
  have loop (entries : List (Token × ℕ)) : tableValue F (terms 2 entries)=tableValue F (terms 1 entries)+tableValue F (terms 1 entries) := by
    induction entries with
    | nil=>simp [terms,tableValue]
    | cons entry entries ih=>
      rcases entry with ⟨token,index⟩
      cases token with
      | inverse=>
        change tableValue F (_::terms 2 entries)=tableValue F (_::terms 1 entries)+tableValue F (_::terms 1 entries)
        simp only [tableValue,List.map_cons,List.sum_cons,tableTermValue,map_ofNat,map_one]
        change 2*F _ _+tableValue F (terms 2 entries)=(1*F _ _+tableValue F (terms 1 entries))+(1*F _ _+tableValue F (terms 1 entries))
        rw [ih]
        ring
      | jordan a=>
        by_cases same : a=axis
        · change tableValue F ((if a=axis then [_] else [])++terms 2 entries)=
            tableValue F ((if a=axis then [_] else [])++terms 1 entries)+tableValue F ((if a=axis then [_] else [])++terms 1 entries)
          simp only [if_pos same,List.singleton_append,tableValue,List.map_cons,List.sum_cons,tableTermValue,map_neg,map_ofNat,map_one]
          change -2*F _ _+tableValue F (terms 2 entries)=(-1*F _ _+tableValue F (terms 1 entries))+(-1*F _ _+tableValue F (terms 1 entries))
          rw [ih]
          ring
        · simpa only [terms,List.flatMap_cons,if_neg same,List.nil_append] using ih
  exact loop tokens.zipIdx

theorem rawTemporalTable_kernel_value (F : AngularExponent → List Token → AngularPolynomial) (a b : Fin 4) (equation : Option (Fin 4)) :
    tableValue F ((rawTemporalTable a b equation).map interpretRawTerm)=tableValue F (kernelTable a b equation) := by
  classical
  rw [kernelTable_expansion]
  cases equation with
  | none=>
    by_cases diagonal : a=b
    · subst b
      unfold rawTemporalTable
      rw [if_pos rfl]
      change tableValue F (([(temporalWord a a,(2 : ℚ))].map (fun row=>⟨angleZero,row.1,row.2⟩ : _)).map interpretRawTerm)=_
      simp only [List.map_cons,List.map_nil,interpretRawTerm,angleExponent_zero,Rat.cast_ofNat,tableValue,List.sum_cons,List.sum_nil,add_zero,tableTermValue,map_ofNat]
      simp only [map_one]
      ring
    · change tableValue F (((if a=b then [(temporalWord a b,(2 : ℚ))] else [(temporalWord a b,1),(temporalWord b a,1)]).map
        (fun row=>⟨angleZero,row.1,row.2⟩ : _)).map interpretRawTerm)=_
      rw [if_neg diagonal]
      simp only [List.map_cons,List.map_nil,interpretRawTerm,angleExponent_zero,Rat.cast_one]
  | some axis=>
    have source : (rawTemporalTable a b (some axis)).map interpretRawTerm=
        if a=b then kernelDifferentiate axis ⟨0,temporalWord a b,2⟩ else
          kernelDifferentiate axis ⟨0,temporalWord a b,1⟩++kernelDifferentiate axis ⟨0,temporalWord b a,1⟩ := by
      unfold rawTemporalTable
      split_ifs
      · dsimp only
        simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
        change (rawDifferentiate axis (temporalWord a b) 2).map interpretRawTerm=_
        rw [rawDifferentiate_kernel]
        norm_num
      · dsimp only
        simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
        change (rawDifferentiate axis (temporalWord a b) 1++rawDifferentiate axis (temporalWord b a) 1).map interpretRawTerm=_
        rw [List.map_append,rawDifferentiate_kernel,rawDifferentiate_kernel]
        norm_num
    rw [source]
    by_cases diagonal : a=b
    · subst b
      rw [if_pos rfl,differentiate_value_two]
      change _=tableValue F (kernelDifferentiate axis ⟨0,temporalWord a a,1⟩++kernelDifferentiate axis ⟨0,temporalWord a a,1⟩)
      rw [tableValue_append]
    · rw [if_neg diagonal]

theorem fold_add_sum {α β : Type} [AddMonoid β] (items : List α) (f : α → β) (initial : β) :
    items.foldl (fun out item=>out+f item) initial=initial+(items.map f).sum := by
  induction items generalizing initial with
  | nil=>simp
  | cons item items ih=>
    rw [List.foldl_cons,ih]
    simp only [List.map_cons,List.sum_cons,add_assoc]

def kernelTablePolynomial (depth order : ℕ) (a b : Fin 4) (equation : Option (Fin 4)) (input : List AngularPolynomial) (n : ℕ) : AngularPolynomial :=
  (kernelTable a b equation).foldl (fun P term=>P+literalPolynomial term.coefficient*
    (MvPolynomial.monomial term.exponent 1*(kernelWord depth order term.tokens input).getD n 0)) 0

theorem rawTablePolynomial_kernel (depth order : ℕ) (a b : Fin 4) (equation : Option (Fin 4)) (input : List AngularPolynomial) (n : ℕ) :
    rawTablePolynomial depth order input (rawTemporalTable a b equation) n=kernelTablePolynomial depth order a b equation input n := by
  let F:=fun u tokens=>MvPolynomial.monomial u 1*(kernelWord depth order tokens input).getD n 0
  calc
    rawTablePolynomial depth order input (rawTemporalTable a b equation) n=
        tableValue F ((rawTemporalTable a b equation).map interpretRawTerm) := by
      rw [rawTablePolynomial,fold_add_sum,zero_add]
      simp only [tableValue,List.map_map,Function.comp_def]
      rfl
    _=tableValue F (kernelTable a b equation) := rawTemporalTable_kernel_value F a b equation
    _=kernelTablePolynomial depth order a b equation input n := by
      rw [kernelTablePolynomial,fold_add_sum,zero_add]
      rfl

abbrev kernelApplyT (depth order : ℕ) (a b : Fin 4) (equation : Option (Fin 4)) (input : List AngularPolynomial)
    (n : Fin (depth+1)) : PreparationVacuumCanonicalMoyal.Symbol :=
  (smooth_program_const% "applyT") depth (sourceEngine order) a b equation input n

theorem kernelApplyT_average (depth order : ℕ) (a b : Fin 4) (equation : Option (Fin 4)) (input : List AngularPolynomial)
    (n : Fin (depth+1)) : kernelApplyT depth order a b equation input n=average (kernelTablePolynomial depth order a b equation input n.val) := rfl

theorem originalApplyT_kernel_value (K order : ℕ) (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (P : List AngularPolynomial)
    (equation : Option (Fin 4)) (runtime : RawRuntime) (native : FullSetupNative K setup runtime)
    (coefficients : SetupCoefficients K order runtime.arena setup) (valid : SeriesHandles runtime.arena input)
    (inputKernel : KernelSeries setup.depth (readAngularSeries K runtime.arena input) P)
    (n : Fin (setup.depth+1)) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalApplyT setup a b input equation runtime).2.arena ((originalApplyT setup a b input equation runtime).1.getD n.val 0) x=
      (kernelApplyT setup.depth order a b equation P n x : ℂ) := by
  rw [originalApplyT_raw_table_value K order setup a b input P equation runtime native coefficients valid inputKernel n.val (by omega) x hx,
    rawTablePolynomial_kernel,kernelApplyT_average]

def sourceApplyT (setup : RawSetup) (a b : Fin 4) (equation : Option (Fin 4)) (slot : Option (Fin 13)) : RuntimeAction (List ℕ) := fun runtime=>
  let source:=sourceInput setup slot runtime
  originalApplyT setup a b source.1 equation source.2

theorem sourceApplyT_kernel_value (K order : ℕ) (setup : RawSetup) (a b : Fin 4) (equation : Option (Fin 4))
    (slot : Option (Fin 13)) (runtime : RawRuntime) (native : FullSetupNative K setup runtime)
    (coefficients : SetupCoefficients K order runtime.arena setup) (n : Fin (setup.depth+1)) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (sourceApplyT setup a b equation slot runtime).2.arena ((sourceApplyT setup a b equation slot runtime).1.getD n.val 0) x=
      (kernelApplyT setup.depth order a b equation (kernelInput slot) n x : ℂ) := by
  let source:=sourceInput setup slot runtime
  have paid:=sourceInput_full_native K setup slot runtime native
  have setupValues:=coefficients.extend (sourceInput_grows setup slot runtime) native.operations.cached.handles.closed
    native.operations.handles.jclocks native.operations.handles.ellclock
  apply originalApplyT_kernel_value K order setup a b source.1 (kernelInput slot) equation source.2 paid.1 setupValues paid.2 ?_ n x hx
  intro index within
  rw [readAngularSeries_getD]
  exact sourceInput_coefficients K setup slot runtime native.operations.cached index within

theorem actual_engine_applyT_value (k : ℕ) (a b : Fin 4) (equation : Option (Fin 4)) (slot : Option (Fin 13))
    (n : Fin ((engineNextSetup k (originalEngine k)).depth+1)) (x : Phase) (hx : x∈poleDomain) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    nativePolynomial (k+1) (sourceApplyT setup a b equation slot runtime).2.arena ((sourceApplyT setup a b equation slot runtime).1.getD n.val 0) x=
      (kernelApplyT setup.depth (k+1) a b equation (kernelInput slot) n x : ℂ) :=
  sourceApplyT_kernel_value (k+1) (k+1) _ a b equation slot _ (originalEngine_full_native (k+1) k)
    (originalEngine_setup_coefficients (k+1) k (by omega)) n x hx

theorem actual_engine_applyT_all_jets (k : ℕ) (a b : Fin 4) (equation : Option (Fin 4)) (slot : Option (Fin 13))
    (n : Fin ((engineNextSetup k (originalEngine k)).depth+1)) (m : ℕ) (x : Phase) (hx : x∈poleDomain) (directions : Fin m → Phase) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    let result:=sourceApplyT setup a b equation slot runtime
    iteratedFDeriv ℝ m (nativePolynomial (k+1) result.2.arena (result.1.getD n.val 0)) x directions=
      iteratedFDeriv ℝ m (fun y=>(kernelApplyT setup.depth (k+1) a b equation (kernelInput slot) n y : ℂ)) x directions := by
  have same : nativePolynomial (k+1) (sourceApplyT (engineNextSetup k (originalEngine k)) a b equation slot (originalEngine (k+1)).runtime).2.arena
      ((sourceApplyT (engineNextSetup k (originalEngine k)) a b equation slot (originalEngine (k+1)).runtime).1.getD n.val 0)=ᶠ[𝓝 x]
      (fun y=>(kernelApplyT (engineNextSetup k (originalEngine k)).depth (k+1) a b equation (kernelInput slot) n y : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact actual_engine_applyT_value k a b equation slot n y hy
  exact congrArg (fun D=>D directions) (same.iteratedFDeriv ℝ m).eq_of_nhds

def SeriesUnique (rows : RawSeries) : Prop := ∀ row,row∈rows → UniqueAngles row

def JCacheUnique (runtime : RawRuntime) : Prop := ∀ entry,entry∈runtime.jMemo → SeriesUnique entry.2

theorem angularAdd_unique (inputs : List RawAngular) (state : RawArena) : UniqueAngles (angularAdd inputs state).1 := by
  have generated:=fold_invariant inputs.flatten angularAddStep (fun out=>UniqueAngles out.1)
    (fun out unique row _=>angularInsert_unique row.1 (rawAdd [angularLookup row.1 out.1,row.2] out.2).1 out.1 unique)
    ([],state) (by simp [UniqueAngles])
  rw [angularAdd_as_fold]
  exact angularNonzero_unique _ generated

theorem runtimeSequence_seriesUnique (actions : List (RuntimeAction RawAngular))
    (step : ∀ action,action∈actions → ∀ runtime,UniqueAngles (action runtime).1) (runtime : RawRuntime) :
    SeriesUnique (runtimeSequence actions runtime).1 := by
  induction actions generalizing runtime with
  | nil=>intro row member;exact False.elim (List.not_mem_nil member)
  | cons action actions ih=>
    intro row member
    rcases List.mem_cons.mp member with equal|tail
    · subst row;exact step action (by simp) runtime
    · exact ih (fun a h=>step a (List.mem_cons_of_mem _ h)) (action runtime).2 row tail

theorem jordanGenerated_unique (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime) :
    SeriesUnique (jordanGenerated setup axis input runtime).1 := by
  apply runtimeSequence_seriesUnique
  intro action member current
  obtain ⟨n,_,rfl⟩:=List.mem_map.mp member
  exact angularAdd_unique _ _

theorem originalJS_keys (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime)
    (keys : JCacheUnique runtime) : JCacheUnique (originalJS setup axis input runtime).2 ∧ SeriesUnique (originalJS setup axis input runtime).1 := by
  classical
  rw [originalJS_execution]
  split
  · rename_i output found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ output found
    exact ⟨keys,equal ▸ keys entry member⟩
  · let result:=jordanGenerated setup axis input runtime
    have unique:=jordanGenerated_unique setup axis input runtime
    refine ⟨?_,unique⟩
    intro entry member
    rcases List.mem_cons.mp member with equal|old
    · subst entry;exact unique
    · have same:=jordanGenerated_jMemo setup axis input runtime
      exact keys entry (same ▸ old)

theorem runtimeSequence_keys {α : Type} (actions : List (RuntimeAction α))
    (step : ∀ action,action∈actions → ∀ runtime,JCacheUnique runtime → JCacheUnique (action runtime).2)
    (runtime : RawRuntime) (keys : JCacheUnique runtime) : JCacheUnique (runtimeSequence actions runtime).2 := by
  induction actions generalizing runtime with
  | nil=>exact keys
  | cons action actions ih=>
    exact ih (fun a h=>step a (List.mem_cons_of_mem _ h)) (action runtime).2 (step action (by simp) runtime keys)

theorem operationOn_keys (setup : RawSetup) (token : Token) (input : RawSeries) (runtime : RawRuntime) (keys : JCacheUnique runtime) :
    JCacheUnique (operationOn setup token input runtime).2 := by
  cases token with
  | inverse=>
    intro entry member
    exact keys entry ((originalResolvent_jMemo setup input runtime) ▸ member)
  | jordan a=>exact (originalJS_keys setup a input runtime keys).1

theorem originalWord_keys (setup : RawSetup) (tokens : List Token) (input : RawSeries) (runtime : RawRuntime) (keys : JCacheUnique runtime) :
    JCacheUnique (originalWord setup tokens input runtime).2 := by
  rw [originalWord_execution]
  split
  · exact keys
  · have generated:=fold_invariant tokens.reverse (fun out token=>operationOn setup token out.1 out.2)
      (fun out=>JCacheUnique out.2) (fun out key token _=>operationOn_keys setup token out.1 out.2 key) (input,runtime) keys
    exact generated

theorem sourceInput_keys (setup : RawSetup) (slot : Option (Fin 13)) (runtime : RawRuntime) (keys : JCacheUnique runtime) :
    JCacheUnique (sourceInput setup slot runtime).2 := by
  cases slot <;> exact keys

theorem originalApplyT_keys (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4))
    (runtime : RawRuntime) (keys : JCacheUnique runtime) : JCacheUnique (originalApplyT setup a b input equation runtime).2 := by
  have generated:=fold_invariant (rawTemporalTable a b equation) (temporalRowStep setup input)
    (fun out=>JCacheUnique out.2) (by
      intro out paid term _
      have word:=originalWord_keys setup term.tokens input out.2 paid
      exact fold_invariant (List.range (setup.depth+1)) (temporalDegreeStep term (originalWord setup term.tokens input out.2).1)
        (fun out=>JCacheUnique out.2) (fun acc current n _=>current)
        (out.1,(originalWord setup term.tokens input out.2).2) word)
    (List.replicate (setup.depth+1) [],runtime) keys
  rw [originalApplyT_program]
  exact runtimeSequence_keys _ (by
    intro action member current paid
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact paid) _ generated

theorem originalAffine_keys (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime) (keys : JCacheUnique runtime) :
    JCacheUnique (originalAffine setup equation runtime).2 := by
  cases equation with
  | none=>
    let actions:=(List.finRange 4).map (fun a=>fun current=>
      let source:=runtimeSource setup.depth (Fin.castAdd 9 a) current
      originalJS setup a source.1 source.2)
    have generated:=runtimeSequence_keys actions (by
      intro action member current paid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact (originalJS_keys setup a (runtimeSource setup.depth (Fin.castAdd 9 a) current).1
        (runtimeSource setup.depth (Fin.castAdd 9 a) current).2 paid).1) runtime keys
    apply runtimeSequence_keys _ ?_ _ generated
    intro action member current paid
    obtain ⟨n,_,rfl⟩:=List.mem_map.mp member
    exact paid
  | some a=>
    apply runtimeSequence_keys _ ?_ (runtimeSource setup.depth (Fin.castAdd 9 a) runtime).2 keys
    intro action member current paid
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact paid

theorem sourceTemporal_keys (setup : RawSetup) (slot : Fin 13) (a b : Fin 4) (equation : Option (Fin 4))
    (runtime : RawRuntime) (keys : JCacheUnique runtime) :
    let source:=runtimeSource setup.depth slot runtime
    JCacheUnique (originalApplyT setup a b source.1 equation source.2).2 :=
  originalApplyT_keys setup a b (runtimeSource setup.depth slot runtime).1 equation (runtimeSource setup.depth slot runtime).2 keys

theorem numericSeriesSum_keys (depth : ℕ) (head : List ℕ) (terms : List (ℚ × List ℕ)) (runtime : RawRuntime) (keys : JCacheUnique runtime) :
    JCacheUnique (runtimeSequence ((List.range (depth+1)).map (fun k=>fun current=>
      let scaled:=runtimeSequence (terms.map (fun row=>runArena
        (rawScale (polynomialCoefficient (MvPolynomial.C row.1)) (row.2.getD k 0)))) current
      runArena (rawAdd ((head.getD k 0)::scaled.1)) scaled.2)) runtime).2 := by
  have equal : (runtimeSequence ((List.range (depth+1)).map (fun k=>fun current=>
      let scaled:=runtimeSequence (terms.map (fun row=>runArena
        (rawScale (polynomialCoefficient (MvPolynomial.C row.1)) (row.2.getD k 0)))) current
      runArena (rawAdd ((head.getD k 0)::scaled.1)) scaled.2)) runtime).2.jMemo=runtime.jMemo := by
    apply runtimeSequence_jMemo
    intro action member current
    obtain ⟨n,_,rfl⟩:=List.mem_map.mp member
    apply runtimeSequence_jMemo
    intro action member state
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    rfl
  intro entry member
  exact keys entry (equal ▸ member)

theorem originalForceOrEnergy_keys (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime) (keys : JCacheUnique runtime) :
    JCacheUnique (originalForceOrEnergy setup equation runtime).2 := by
  let affine:=originalAffine setup equation runtime
  let trace:=runtimeTrace setup.depth affine.2
  let first:=originalApplyT setup 0 0 trace.1 equation trace.2
  have ha:=originalAffine_keys setup equation runtime keys
  have hf:=originalApplyT_keys setup 0 0 trace.1 equation trace.2 ha
  let diagonalActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨4+i.val,by omega⟩ current
    originalApplyT setup (Fin.succ i) (Fin.succ i) source.1 equation source.2)
  let diagonal:=runtimeSequence diagonalActions first.2
  have hd:=runtimeSequence_keys diagonalActions (by
    intro action member current paid
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_keys setup ⟨4+i.val,by omega⟩ (Fin.succ i) (Fin.succ i) equation current paid) first.2 hf
  let crossIndices : List (Fin 4 × Fin 4 × Fin 13):=[(1,2,7),(1,3,8),(2,3,9)]
  let crossActions : List (RuntimeAction (List ℕ)) := crossIndices.map (fun entry=>fun current=>
    let source:=runtimeSource setup.depth entry.2.2 current
    originalApplyT setup entry.1 entry.2.1 source.1 equation source.2)
  let cross:=runtimeSequence crossActions diagonal.2
  have hc:=runtimeSequence_keys crossActions (by
    intro action member current paid
    obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_keys setup entry.2.2 entry.1 entry.2.1 equation current paid) diagonal.2 hd
  let timeActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨10+i.val,by omega⟩ current
    originalApplyT setup 0 (Fin.succ i) source.1 equation source.2)
  let time:=runtimeSequence timeActions cross.2
  have ht:=runtimeSequence_keys timeActions (by
    intro action member current paid
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_keys setup ⟨10+i.val,by omega⟩ 0 (Fin.succ i) equation current paid) cross.2 hc
  exact numericSeriesSum_keys setup.depth affine.1
    ([(1/2,first.1)]++diagonal.1.map (fun row=>(-1/2,row))++cross.1.map (fun row=>(-1,row))++time.1.map (fun row=>(-1,row))) time.2 ht

attribute [local irreducible] originalForceOrEnergy runtimeSequence runtimeSetup
set_option backward.isDefEq.respectTransparency true

theorem checksStep_jMemo (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ)
    (out : List ℕ × List Bool × RawRuntime) (a : Fin 4) :
    (checksStep setup order residualIds clockIds out a).2.2.jMemo=(originalForceOrEnergy setup (some a) out.2.2).2.jMemo := by
  unfold checksStep runtimeSequence
  rfl

theorem originalChecks_keys (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ) (runtime : RawRuntime) (keys : JCacheUnique runtime) :
    JCacheUnique (originalChecks setup order residualIds clockIds runtime).2.2 := by
  rw [originalChecks_as_fold]
  apply fold_invariant (List.finRange 4) (checksStep setup order residualIds clockIds)
    (fun out : List ℕ × List Bool × RawRuntime=>JCacheUnique out.2.2) ?_ ([],[],runtime) keys
  intro out paid a _ entry member
  rw [checksStep_jMemo] at member
  exact originalForceOrEnergy_keys setup (some a) out.2.2 paid entry member

theorem runtimeSetup_keys (depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime) : JCacheUnique (runtimeSetup depth clocks runtime).2 := by
  intro entry member
  unfold runtimeSetup at member
  exact False.elim (List.not_mem_nil member)

theorem originalEngineNext_keys (k : ℕ) (engine : RawEngineState) : JCacheUnique (originalEngineNext k engine).runtime := by
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let residuals:=runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))) before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  let checked:=originalChecks after.1 (k+1) residualIds installed.2.1 after.2
  exact originalForceOrEnergy_keys after.1 none checked.2.2
    (originalChecks_keys after.1 (k+1) residualIds installed.2.1 after.2 (runtimeSetup_keys _ _ _))

theorem originalBoot_keys (clocks : RawClocks) (runtime : RawRuntime) : JCacheUnique (originalBoot clocks runtime).runtime := by
  let setup:=runtimeSetup 0 clocks runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy setup.1 (some a))
  let forces:=runtimeSequence actions setup.2
  have key:=runtimeSequence_keys actions (by
    intro action member current paid
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_keys setup.1 (some a) current paid) setup.2 (runtimeSetup_keys _ _ _)
  exact originalForceOrEnergy_keys setup.1 none forces.2 key

theorem originalEngine_keys (order : ℕ) : JCacheUnique (originalEngine order).runtime := by
  cases order with
  | zero=>exact originalBoot_keys _ _
  | succ k=>exact originalEngineNext_keys k (originalEngine k)

attribute [local semireducible] originalForceOrEnergy runtimeSequence runtimeSetup
set_option backward.isDefEq.respectTransparency false

theorem SeriesUnique.getD {rows : RawSeries} (unique : SeriesUnique rows) (n : ℕ) : UniqueAngles (rows.getD n []) := by
  by_cases within : n < rows.length
  · rw [List.getD_eq_getElem _ _ within]
    exact unique _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [UniqueAngles]

theorem originalSource_unique (depth : ℕ) (slot : Fin 13) (state : RawArena) : SeriesUnique (originalSource depth slot state).1 := by
  rw [originalSource_body]
  intro rows member
  rcases List.mem_append.mp member with body|empty
  · have inside:=List.mem_of_mem_take body
    simp only [sourceBodyRows,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with equal|equal|equal <;> subst rows
    · unfold angularConstant
      split_ifs <;> simp [UniqueAngles]
    · simp [UniqueAngles]
    · simp [UniqueAngles]
  · have same:rows=[] := (List.mem_replicate.mp empty).2
    subst rows
    simp [UniqueAngles]

theorem originalJS_kernel (K order : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (P : List AngularPolynomial)
    (runtime : RawRuntime) (native : FullSetupNative K setup runtime) (valid : SeriesHandles runtime.arena input)
    (coefficients : SetupCoefficients K order runtime.arena setup)
    (inputKernel : KernelSeries setup.depth (readAngularSeries K runtime.arena input) P) :
    KernelSeries setup.depth (readAngularSeries K (originalJS setup axis input runtime).2.arena (originalJS setup axis input runtime).1)
      (kernelJ setup.depth order axis P) := by
  have kernel:=operationValue_kernel setup.depth order (fun a=>readAngularSeries K runtime.arena (setup.jclocks a))
    (readAngularSeries K runtime.arena setup.ellclock) (readAngularSeries K runtime.arena input) (.jordan axis) P
    (by intro a n within;rw [readAngularSeries_getD];exact coefficients.jordan a n within)
    (by intro n within;rw [readAngularSeries_getD];exact coefficients.ell n within) inputKernel
  exact KernelSeries.transport (operationOn_native K setup (.jordan axis) input runtime native.operations valid).2.2 kernel

def sourceJ (setup : RawSetup) (axis : Fin 4) : RuntimeAction RawSeries := fun runtime=>
  let source:=runtimeSource setup.depth (Fin.castAdd 9 axis) runtime
  originalJS setup axis source.1 source.2

theorem sourceJ_grows (setup : RawSetup) (axis : Fin 4) (runtime : RawRuntime) :
    RawExtends runtime.arena (sourceJ setup axis runtime).2.arena :=
  (runtimeSource_grows setup.depth (Fin.castAdd 9 axis) runtime).trans
    (originalJS_grows setup axis _ (runtimeSource setup.depth (Fin.castAdd 9 axis) runtime).2)

theorem sourceJ_properties (K : ℕ) (setup : RawSetup) (axis : Fin 4) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (keys : JCacheUnique runtime) :
    FullSetupNative K setup (sourceJ setup axis runtime).2 ∧ JCacheUnique (sourceJ setup axis runtime).2 ∧
      SeriesHandles (sourceJ setup axis runtime).2.arena (sourceJ setup axis runtime).1 ∧ SeriesUnique (sourceJ setup axis runtime).1 := by
  let source:=runtimeSource setup.depth (Fin.castAdd 9 axis) runtime
  have paid:=sourceInput_full_native K setup (some (Fin.castAdd 9 axis)) runtime native
  have unique:=originalJS_keys setup axis source.1 source.2 keys
  exact ⟨originalJS_full_native K setup axis source.1 source.2 paid.1 paid.2,unique.1,
    (originalJS_cached K setup axis source.1 source.2 paid.1.operations.cached paid.1.operations.handles paid.2).2,unique.2⟩

theorem sourceJ_kernel (K order : ℕ) (setup : RawSetup) (axis : Fin 4) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (coefficients : SetupCoefficients K order runtime.arena setup) :
    KernelSeries setup.depth (readAngularSeries K (sourceJ setup axis runtime).2.arena (sourceJ setup axis runtime).1)
      (kernelJ setup.depth order axis (kernelSourceSeries (Fin.castAdd 9 axis))) := by
  let source:=runtimeSource setup.depth (Fin.castAdd 9 axis) runtime
  have paid:=sourceInput_full_native K setup (some (Fin.castAdd 9 axis)) runtime native
  apply originalJS_kernel K order setup axis source.1 _ source.2 paid.1 paid.2
    (coefficients.extend (runtimeSource_grows setup.depth (Fin.castAdd 9 axis) runtime) native.operations.cached.handles.closed
      native.operations.handles.jclocks native.operations.handles.ellclock)
  intro n within
  rw [readAngularSeries_getD]
  exact sourceInput_coefficients K setup (some (Fin.castAdd 9 axis)) runtime native.operations.cached n within

def seriesZeroId (rows : RawSeries) (n : ℕ) : ℕ := angularLookup angleZero (rows.getD n [])

def kernelAffineTerm (depth order : ℕ) (axis : Fin 4) (n : ℕ) : PreparationVacuumCanonicalMoyal.Symbol :=
  MvPolynomial.coeff 0 ((kernelJ depth order axis (kernelSourceSeries (Fin.castAdd 9 axis))).getD n 0)

theorem sourceJ_zero_value (K order : ℕ) (setup : RawSetup) (axis : Fin 4) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (keys : JCacheUnique runtime) (coefficients : SetupCoefficients K order runtime.arena setup)
    (n : ℕ) (within : n ≤ setup.depth) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (sourceJ setup axis runtime).2.arena (seriesZeroId (sourceJ setup axis runtime).1 n) x=
      (kernelAffineTerm setup.depth order axis n x : ℂ) := by
  have paid:=sourceJ_properties K setup axis runtime native keys
  have value:=sourceJ_kernel K order setup axis runtime native coefficients n within
  rw [readAngularSeries_getD] at value
  rw [seriesZeroId,←angularValue_lookup K _ paid.1.operations.cached.handles.closed paid.1.operations.cached.handles.initialized
    _ (paid.2.2.2.getD n) angleZero x]
  exact value 0 hx

theorem seriesZeroId_bound (state : RawArena) (rows : RawSeries) (n : ℕ) (initialized : RawInitialized state) (valid : SeriesHandles state rows) :
    Handle state (seriesZeroId rows n) := angularLookup_bound state initialized (rows.getD n []) (series_getD valid n) angleZero

def affineSources (setup : RawSetup) (axes : List (Fin 4)) : RuntimeAction (List RawSeries) := runtimeSequence (axes.map (sourceJ setup))

theorem affineSources_values (K order : ℕ) (setup : RawSetup) (base : RawRuntime) (axes : List (Fin 4)) (runtime : RawRuntime)
    (baseNative : FullSetupNative K setup base) (baseCoefficients : SetupCoefficients K order base.arena setup)
    (growth : RawExtends base.arena runtime.arena) (native : FullSetupNative K setup runtime) (keys : JCacheUnique runtime) :
    let result:=affineSources setup axes runtime
    FullSetupNative K setup result.2 ∧ JCacheUnique result.2 ∧
      (∀ rows,rows∈result.1 → SeriesHandles result.2.arena rows) ∧
      ∀ n,n ≤ setup.depth → ∀ x,x∈poleDomain → (result.1.map (fun rows=>nativePolynomial K result.2.arena (seriesZeroId rows n) x))=
        axes.map (fun a=>(kernelAffineTerm setup.depth order a n x : ℂ)) := by
  induction axes generalizing runtime with
  | nil=>exact ⟨native,keys,fun _ h=>False.elim (List.not_mem_nil h),fun _ _ _ _=>rfl⟩
  | cons a axes ih=>
    have one:=sourceJ_properties K setup a runtime native keys
    have oneGrow:=sourceJ_grows setup a runtime
    have tail:=ih (sourceJ setup a runtime).2 (growth.trans oneGrow) one.1 one.2.1
    have tailGrow : RawExtends (sourceJ setup a runtime).2.arena (affineSources setup axes (sourceJ setup a runtime).2).2.arena := by
      apply runtimeSequence_grows
      intro action member current
      obtain ⟨axis,_,rfl⟩:=List.mem_map.mp member
      exact sourceJ_grows setup axis current
    refine ⟨tail.1,tail.2.1,?_,?_⟩
    · intro rows member
      rcases List.mem_cons.mp member with equal|old
      · subst rows;exact series_extend tailGrow one.2.2.1
      · exact tail.2.2.1 rows old
    · intro n within x hx
      change nativePolynomial K (affineSources setup axes (sourceJ setup a runtime).2).2.arena (seriesZeroId (sourceJ setup a runtime).1 n) x::
        ((affineSources setup axes (sourceJ setup a runtime).2).1.map (fun rows=>nativePolynomial K
          (affineSources setup axes (sourceJ setup a runtime).2).2.arena (seriesZeroId rows n) x))=_
      rw [nativePolynomial_prefix K tailGrow one.1.operations.cached.handles.closed _
        (seriesZeroId_bound _ _ n one.1.operations.cached.handles.initialized one.2.2.1),
        sourceJ_zero_value K order setup a runtime native keys
          (baseCoefficients.extend growth baseNative.operations.cached.handles.closed baseNative.operations.handles.jclocks baseNative.operations.handles.ellclock) n within x hx,
        tail.2.2.2 n within x hx]
      rfl

theorem finRange_sum {n : ℕ} (f : Fin n → ℂ) : ((List.finRange n).map f).sum=∑ i,f i := by
  rw [←List.ofFn_eq_map,List.sum_ofFn]

theorem native_getD_value (K : ℕ) (state : RawArena) (ids : List ℕ) (values : List ℂ)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state) (n : ℕ) (x : Phase)
    (same : ids.map (fun id=>nativePolynomial K state id x)=values) :
    nativePolynomial K state (ids.getD n 0) x=values.getD n 0 := by
  have zero : nativePolynomial K state 0 x=0 := by rw [native_zero K state closed initialized];rfl
  have equality:=congrArg (fun values : List ℂ=>values.getD n 0) same
  rw [←zero,List.getD_map] at equality
  simpa only [zero] using equality

abbrev kernelAffine (depth order : ℕ) (equation : Option (Fin 4)) (n : Fin (depth+1)) : PreparationVacuumCanonicalMoyal.Symbol :=
  (smooth_program_const% "affine") depth (sourceEngine order) equation n

def affineSums (depth : ℕ) (rows : List RawSeries) : RuntimeAction (List ℕ) :=
  runtimeSequence ((List.range (depth+1)).map (fun n=>runArena (rawAdd (rows.map (fun row=>seriesZeroId row n)))))

theorem affineSums_values (K depth : ℕ) (rows : List RawSeries) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (valid : ∀ row,row∈rows → SeriesHandles runtime.arena row) :
    let result:=affineSums depth rows runtime
    CachedNative K result.2 ∧ ListHandles result.2.arena result.1 ∧
      ∀ x,x∈poleDomain → result.1.map (fun id=>nativePolynomial K result.2.arena id x)=
        (List.range (depth+1)).map (fun n=>(rows.map (fun row=>nativePolynomial K runtime.arena (seriesZeroId row n) x)).sum) := by
  apply runtimeSequence_scalar_values K runtime runtime (List.range (depth+1)) _ _ (RawExtends.refl _) cached
    (fun _ _ _=>rawAdd_extends _ _)
  intro n member current growth paid
  have output:=runAdd_cached (rows.map (fun row=>seriesZeroId row n)) current paid
  have handles : ListHandles runtime.arena (rows.map (fun row=>seriesZeroId row n)) := by
    intro id member
    obtain ⟨row,present,rfl⟩:=List.mem_map.mp member
    exact seriesZeroId_bound _ _ n cached.handles.initialized (valid row present)
  refine ⟨output.1,output.2,?_⟩
  intro x hx
  rw [show nativePolynomial K (runArena (rawAdd (rows.map (fun row=>seriesZeroId row n))) current).2.arena
      (runArena (rawAdd (rows.map (fun row=>seriesZeroId row n))) current).1 x=_ from
    rawAdd_native K _ current.arena paid.handles.closed (list_extend growth handles) x hx]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro row present
  exact congrFun (nativePolynomial_prefix K growth cached.handles.closed _
    (seriesZeroId_bound _ _ n cached.handles.initialized (valid row present))) x

theorem originalAffine_none_value (K order : ℕ) (setup : RawSetup) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (keys : JCacheUnique runtime)
    (coefficients : SetupCoefficients K order runtime.arena setup) (n : Fin (setup.depth+1)) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalAffine setup none runtime).2.arena ((originalAffine setup none runtime).1.getD n.val 0) x=
      (kernelAffine setup.depth order none n x : ℂ) := by
  let sources:=affineSources setup (List.finRange 4) runtime
  have sourcePaid:=affineSources_values K order setup runtime (List.finRange 4) runtime native coefficients (RawExtends.refl _) native keys
  have sums:=affineSums_values K setup.depth sources.1 sources.2 sourcePaid.1.operations.cached sourcePaid.2.2.1
  change nativePolynomial K (affineSums setup.depth sources.1 sources.2).2.arena
    ((affineSums setup.depth sources.1 sources.2).1.getD n.val 0) x=_
  rw [native_getD_value K _ _ _ sums.1.handles.closed sums.1.handles.initialized n.val x (sums.2.2 x hx),
    List.getD_eq_getElem _ _ (by simpa using n.isLt),List.getElem_map,List.getElem_range,
    sourcePaid.2.2.2 n.val (by omega) x hx,finRange_sum]
  change (∑ a : Fin 4,(kernelAffineTerm setup.depth order a n.val x : ℂ))=
    (((∑ a : Fin 4,kernelAffineTerm setup.depth order a n.val) x : ℝ) : ℂ)
  simp only [Finset.sum_apply,Complex.ofReal_sum]

 theorem negativeCoefficient_value (x : Phase) : coefficientValue (polynomialCoefficient (-1)) x = -1 := by
  rw [polynomialCoefficient_source]
  simp [polynomialSymbol]

def negativeRows (rows : RawSeries) : RuntimeAction (List ℕ) :=
  runtimeSequence (rows.map (fun row=>runArena (rawScale (polynomialCoefficient (-1)) (angularLookup angleZero row))))

theorem negativeRows_values (K : ℕ) (rows : RawSeries) (runtime : RawRuntime) (cached : CachedNative K runtime)
    (valid : SeriesHandles runtime.arena rows) :
    let result:=negativeRows rows runtime
    CachedNative K result.2 ∧ ListHandles result.2.arena result.1 ∧
      ∀ x,x∈poleDomain → result.1.map (fun id=>nativePolynomial K result.2.arena id x)=
        rows.map (fun row=> -nativePolynomial K runtime.arena (angularLookup angleZero row) x) := by
  apply runtimeSequence_scalar_values K runtime runtime rows _ _ (RawExtends.refl _) cached
    (fun _ _ _=>rawScale_extends _ _ _)
  intro row member current growth paid
  have output:=runScale_cached (polynomialCoefficient (-1)) (angularLookup angleZero row) current paid
  have handle:=angularLookup_bound runtime.arena cached.handles.initialized row (valid row member) angleZero
  refine ⟨output.1,output.2,?_⟩
  intro x hx
  rw [show nativePolynomial K (runArena (rawScale (polynomialCoefficient (-1)) (angularLookup angleZero row)) current).2.arena
      (runArena (rawScale (polynomialCoefficient (-1)) (angularLookup angleZero row)) current).1 x=_ from
    rawScale_native K _ _ current.arena paid.handles.closed (handle_extend growth handle) x hx,
    negativeCoefficient_value,nativePolynomial_prefix K growth cached.handles.closed _ handle]
  simp

theorem originalAffine_some_value (K order : ℕ) (setup : RawSetup) (axis : Fin 4) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (n : Fin (setup.depth+1)) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalAffine setup (some axis) runtime).2.arena ((originalAffine setup (some axis) runtime).1.getD n.val 0) x=
      (kernelAffine setup.depth order (some axis) n x : ℂ) := by
  let source:=runtimeSource setup.depth (Fin.castAdd 9 axis) runtime
  have sourcePaid:=sourceInput_full_native K setup (some (Fin.castAdd 9 axis)) runtime native
  have negative:=negativeRows_values K source.1 source.2 sourcePaid.1.operations.cached sourcePaid.2
  change nativePolynomial K (negativeRows source.1 source.2).2.arena ((negativeRows source.1 source.2).1.getD n.val 0) x=_
  rw [native_getD_value K _ _ _ negative.1.handles.closed negative.1.handles.initialized n.val x (negative.2.2 x hx)]
  have zero : -nativePolynomial K source.2.arena (angularLookup angleZero []) x=0 := by
    change -nativePolynomial K source.2.arena 0 x=0
    rw [native_zero K source.2.arena sourcePaid.1.operations.cached.handles.closed sourcePaid.1.operations.cached.handles.initialized]
    simp
  rw [←zero,List.getD_map]
  have unique : UniqueAngles (source.1.getD n.val []) := (originalSource_unique setup.depth (Fin.castAdd 9 axis) runtime.arena).getD n.val
  rw [←angularValue_lookup K source.2.arena sourcePaid.1.operations.cached.handles.closed sourcePaid.1.operations.cached.handles.initialized
    (source.1.getD n.val []) unique angleZero x]
  have value:=sourceInput_coefficients K setup (some (Fin.castAdd 9 axis)) runtime native.operations.cached n.val (by omega) 0 hx
  change angularValue K source.2.arena (source.1.getD n.val []) angleZero x=_ at value
  rw [value]
  change -(↑(MvPolynomial.coeff 0 ((kernelSourceSeries (Fin.castAdd 9 axis)).getD n.val 0) x) : ℂ)=↑(-MvPolynomial.coeff 0 ((kernelSourceSeries (Fin.castAdd 9 axis)).getD n.val 0) x)
  simp

theorem originalAffine_kernel_value (K order : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (keys : JCacheUnique runtime)
    (coefficients : SetupCoefficients K order runtime.arena setup) (n : Fin (setup.depth+1)) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalAffine setup equation runtime).2.arena ((originalAffine setup equation runtime).1.getD n.val 0) x=
      (kernelAffine setup.depth order equation n x : ℂ) := by
  cases equation with
  | none=>exact originalAffine_none_value K order setup runtime native keys coefficients n x hx
  | some a=>exact originalAffine_some_value K order setup a runtime native n x hx

def ArrayValues (K : ℕ) (state : RawArena) (ids : List ℕ) (depth : ℕ) (value : Fin (depth+1) → PreparationVacuumCanonicalMoyal.Symbol) : Prop :=
  ∀ n x,x∈poleDomain → nativePolynomial K state (ids.getD n.val 0) x=(value n x : ℂ)

theorem ArrayValues.extend {K depth : ℕ} {old new : RawRuntime} {ids : List ℕ} {value : Fin (depth+1) → PreparationVacuumCanonicalMoyal.Symbol}
    (same : ArrayValues K old.arena ids depth value) (growth : RawExtends old.arena new.arena)
    (closed : RuntimeHandles old) (valid : ListHandles old.arena ids) : ArrayValues K new.arena ids depth value := by
  intro n x hx
  rw [nativePolynomial_prefix K growth closed.closed _ (list_getD_handle closed valid n.val)]
  exact same n x hx

def temporalInputs (setup : RawSetup) (equation : Option (Fin 4)) (entries : List (Fin 4 × Fin 4 × Option (Fin 13))) : RuntimeAction (List (List ℕ)) :=
  runtimeSequence (entries.map (fun entry=>sourceApplyT setup entry.1 entry.2.1 equation entry.2.2))

theorem sourceApplyT_grows (setup : RawSetup) (a b : Fin 4) (equation : Option (Fin 4)) (slot : Option (Fin 13)) (runtime : RawRuntime) :
    RawExtends runtime.arena (sourceApplyT setup a b equation slot runtime).2.arena :=
  (sourceInput_grows setup slot runtime).trans (originalApplyT_grows setup a b _ equation _)

theorem sourceApplyT_properties (K : ℕ) (setup : RawSetup) (a b : Fin 4) (equation : Option (Fin 4)) (slot : Option (Fin 13)) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) :
    FullSetupNative K setup (sourceApplyT setup a b equation slot runtime).2 ∧
      ListHandles (sourceApplyT setup a b equation slot runtime).2.arena (sourceApplyT setup a b equation slot runtime).1 := by
  have source:=sourceInput_full_native K setup slot runtime native
  exact ⟨originalApplyT_full_native K setup a b _ equation _ source.1 source.2,
    (originalApplyT_cached K setup a b _ equation _ source.1.operations.cached source.1.operations.handles source.2).2⟩

theorem temporalInputs_grows (setup : RawSetup) (equation : Option (Fin 4)) (entries : List (Fin 4 × Fin 4 × Option (Fin 13))) (runtime : RawRuntime) :
    RawExtends runtime.arena (temporalInputs setup equation entries runtime).2.arena := by
  apply runtimeSequence_grows
  intro action member current
  obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
  exact sourceApplyT_grows setup entry.1 entry.2.1 equation entry.2.2 current

theorem temporalInputs_values (K order : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) (base : RawRuntime)
    (entries : List (Fin 4 × Fin 4 × Option (Fin 13))) (runtime : RawRuntime)
    (baseNative : FullSetupNative K setup base) (baseCoefficients : SetupCoefficients K order base.arena setup)
    (growth : RawExtends base.arena runtime.arena) (native : FullSetupNative K setup runtime) :
    let result:=temporalInputs setup equation entries runtime
    FullSetupNative K setup result.2 ∧ (∀ row,row∈result.1 → ListHandles result.2.arena row) ∧
      ∀ n : Fin (setup.depth+1),∀ x,x∈poleDomain →
        result.1.map (fun row=>nativePolynomial K result.2.arena (row.getD n.val 0) x)=
          entries.map (fun entry=>(kernelApplyT setup.depth order entry.1 entry.2.1 equation (kernelInput entry.2.2) n x : ℂ)) := by
  induction entries generalizing runtime with
  | nil=>exact ⟨native,fun _ h=>False.elim (List.not_mem_nil h),fun _ _ _=>rfl⟩
  | cons entry entries ih=>
    let first:=sourceApplyT setup entry.1 entry.2.1 equation entry.2.2 runtime
    have one:=sourceApplyT_properties K setup entry.1 entry.2.1 equation entry.2.2 runtime native
    have oneGrow:=sourceApplyT_grows setup entry.1 entry.2.1 equation entry.2.2 runtime
    have tail:=ih first.2 (growth.trans oneGrow) one.1
    have tailGrow:=temporalInputs_grows setup equation entries first.2
    refine ⟨tail.1,?_,?_⟩
    · intro row member
      rcases List.mem_cons.mp member with equal|old
      · subst row;exact list_extend tailGrow one.2
      · exact tail.2.1 row old
    · intro n x hx
      change nativePolynomial K (temporalInputs setup equation entries first.2).2.arena (first.1.getD n.val 0) x::
        ((temporalInputs setup equation entries first.2).1.map (fun row=>nativePolynomial K (temporalInputs setup equation entries first.2).2.arena (row.getD n.val 0) x))=_
      rw [nativePolynomial_prefix K tailGrow one.1.operations.cached.handles.closed _
        (list_getD_handle one.1.operations.cached.handles one.2 n.val),
        sourceApplyT_kernel_value K order setup entry.1 entry.2.1 equation entry.2.2 runtime native
          (baseCoefficients.extend growth baseNative.operations.cached.handles.closed baseNative.operations.handles.jclocks baseNative.operations.handles.ellclock) n x hx,
        tail.2.2 n x hx]
      rfl

def numericScaleRows (n : ℕ) (terms : List (ℚ × List ℕ)) : RuntimeAction (List ℕ) :=
  runtimeSequence (terms.map (fun row=>runArena (rawScale (polynomialCoefficient (MvPolynomial.C row.1)) (row.2.getD n 0))))

theorem numericScaleRows_values (K n : ℕ) (terms : List (ℚ × List ℕ)) (runtime : RawRuntime) (cached : CachedNative K runtime)
    (valid : ∀ term,term∈terms → ListHandles runtime.arena term.2) :
    let result:=numericScaleRows n terms runtime
    CachedNative K result.2 ∧ ListHandles result.2.arena result.1 ∧
      ∀ x,x∈poleDomain → result.1.map (fun id=>nativePolynomial K result.2.arena id x)=
        terms.map (fun term=>(term.1 : ℂ)*nativePolynomial K runtime.arena (term.2.getD n 0) x) := by
  apply runtimeSequence_scalar_values K runtime runtime terms _ _ (RawExtends.refl _) cached
    (fun _ _ _=>rawScale_extends _ _ _)
  intro term member current growth paid
  have output:=runScale_cached (polynomialCoefficient (MvPolynomial.C term.1)) (term.2.getD n 0) current paid
  have handle:=list_getD_handle cached.handles (valid term member) n
  refine ⟨output.1,output.2,?_⟩
  intro x hx
  rw [show nativePolynomial K (runArena (rawScale (polynomialCoefficient (MvPolynomial.C term.1)) (term.2.getD n 0)) current).2.arena
      (runArena (rawScale (polynomialCoefficient (MvPolynomial.C term.1)) (term.2.getD n 0)) current).1 x=_ from
    rawScale_native K _ _ current.arena paid.handles.closed (handle_extend growth handle) x hx,
    rationalCoefficient_value,nativePolynomial_prefix K growth cached.handles.closed _ handle]
  simp

def numericSumStep (head : List ℕ) (terms : List (ℚ × List ℕ)) (n : ℕ) : RuntimeAction ℕ := fun current=>
  let scaled:=numericScaleRows n terms current
  runArena (rawAdd ((head.getD n 0)::scaled.1)) scaled.2

theorem numericScaleRows_grows (n : ℕ) (terms : List (ℚ × List ℕ)) (runtime : RawRuntime) :
    RawExtends runtime.arena (numericScaleRows n terms runtime).2.arena := by
  apply runtimeSequence_grows
  intro action member current
  obtain ⟨term,_,rfl⟩:=List.mem_map.mp member
  exact rawScale_extends _ _ _

theorem numericSumStep_grows (head : List ℕ) (terms : List (ℚ × List ℕ)) (n : ℕ) (runtime : RawRuntime) :
    RawExtends runtime.arena (numericSumStep head terms n runtime).2.arena :=
  (numericScaleRows_grows n terms runtime).trans (rawAdd_extends _ _)

theorem numericSumStep_value (K : ℕ) (head : List ℕ) (terms : List (ℚ × List ℕ)) (n : ℕ) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (headValid : ListHandles runtime.arena head)
    (valid : ∀ term,term∈terms → ListHandles runtime.arena term.2) :
    CachedNative K (numericSumStep head terms n runtime).2 ∧ Handle (numericSumStep head terms n runtime).2.arena (numericSumStep head terms n runtime).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (numericSumStep head terms n runtime).2.arena (numericSumStep head terms n runtime).1 x=
        nativePolynomial K runtime.arena (head.getD n 0) x+(terms.map (fun term=>(term.1 : ℂ)*nativePolynomial K runtime.arena (term.2.getD n 0) x)).sum := by
  let scaled:=numericScaleRows n terms runtime
  have scalePaid:=numericScaleRows_values K n terms runtime cached valid
  have growth:=numericScaleRows_grows n terms runtime
  have headHandle:=list_getD_handle cached.handles headValid n
  have out:=runAdd_cached ((head.getD n 0)::scaled.1) scaled.2 scalePaid.1
  refine ⟨out.1,out.2,?_⟩
  intro x hx
  rw [show nativePolynomial K (numericSumStep head terms n runtime).2.arena (numericSumStep head terms n runtime).1 x=_ from
    rawAdd_native K _ scaled.2.arena scalePaid.1.handles.closed (by
      intro id member
      rcases List.mem_cons.mp member with equal|old
      · subst id;exact handle_extend growth headHandle
      · exact scalePaid.2.1 id old) x hx]
  rw [List.map_cons,List.sum_cons,nativePolynomial_prefix K growth cached.handles.closed _ headHandle,scalePaid.2.2 x hx]

def numericSeriesSum (depth : ℕ) (head : List ℕ) (terms : List (ℚ × List ℕ)) : RuntimeAction (List ℕ) :=
  runtimeSequence ((List.range (depth+1)).map (numericSumStep head terms))

theorem numericSeriesSum_value (K depth : ℕ) (head : List ℕ) (terms : List (ℚ × List ℕ)) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (headValid : ListHandles runtime.arena head)
    (valid : ∀ term,term∈terms → ListHandles runtime.arena term.2) (n : Fin (depth+1)) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (numericSeriesSum depth head terms runtime).2.arena ((numericSeriesSum depth head terms runtime).1.getD n.val 0) x=
      nativePolynomial K runtime.arena (head.getD n.val 0) x+
        (terms.map (fun term=>(term.1 : ℂ)*nativePolynomial K runtime.arena (term.2.getD n.val 0) x)).sum := by
  have result:=runtimeSequence_scalar_values K runtime runtime (List.range (depth+1)) (numericSumStep head terms)
    (fun n x=>nativePolynomial K runtime.arena (head.getD n 0) x+(terms.map (fun term=>(term.1 : ℂ)*nativePolynomial K runtime.arena (term.2.getD n 0) x)).sum)
    (RawExtends.refl _) cached (fun _ _=>numericSumStep_grows head terms _) (by
      intro index _ current growth paid
      have one:=numericSumStep_value K head terms index current paid (list_extend growth headValid)
        (fun term member=>list_extend growth (valid term member))
      refine ⟨one.1,one.2.1,?_⟩
      intro y hy
      rw [one.2.2 y hy,nativePolynomial_prefix K growth cached.handles.closed _ (list_getD_handle cached.handles headValid index)]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro term member
      rw [nativePolynomial_prefix K growth cached.handles.closed _ (list_getD_handle cached.handles (valid term member) index)])
  unfold numericSeriesSum
  rw [native_getD_value K _ _ _ result.1.handles.closed result.1.handles.initialized n.val x (result.2.2 x hx),
    List.getD_eq_getElem _ _ (by simpa using n.isLt),List.getElem_map,List.getElem_range]

def diagonalEntries : List (Fin 4 × Fin 4 × Option (Fin 13)) :=
  (List.finRange 3).map (fun i=>(Fin.succ i,Fin.succ i,some ⟨4+i.val,by omega⟩))
def crossEntries : List (Fin 4 × Fin 4 × Option (Fin 13)) := [(1,2,some 7),(1,3,some 8),(2,3,some 9)]
def timeEntries : List (Fin 4 × Fin 4 × Option (Fin 13)) :=
  (List.finRange 3).map (fun i=>(0,Fin.succ i,some ⟨10+i.val,by omega⟩))

def forceProgram (setup : RawSetup) (equation : Option (Fin 4)) : RuntimeAction (List ℕ) := fun runtime=>
  let affine:=originalAffine setup equation runtime
  let first:=sourceApplyT setup 0 0 equation none affine.2
  let diagonal:=temporalInputs setup equation diagonalEntries first.2
  let cross:=temporalInputs setup equation crossEntries diagonal.2
  let time:=temporalInputs setup equation timeEntries cross.2
  numericSeriesSum setup.depth affine.1
    ([(1/2,first.1)]++diagonal.1.map (fun row=>(-1/2,row))++cross.1.map (fun row=>(-1,row))++time.1.map (fun row=>(-1,row))) time.2

theorem originalForceOrEnergy_program (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime) :
    originalForceOrEnergy setup equation runtime=forceProgram setup equation runtime := rfl

theorem native_rows_prefix (K : ℕ) (old new : RawRuntime) (rows : List (List ℕ)) (n : ℕ) (x : Phase)
    (growth : RawExtends old.arena new.arena) (closed : RuntimeHandles old)
    (valid : ∀ row,row∈rows → ListHandles old.arena row) :
    rows.map (fun row=>nativePolynomial K new.arena (row.getD n 0) x)=rows.map (fun row=>nativePolynomial K old.arena (row.getD n 0) x) := by
  apply List.map_congr_left
  intro row member
  exact congrFun (nativePolynomial_prefix K growth closed.closed _ (list_getD_handle closed (valid row member) n)) x

theorem weighted_rows_value (K : ℕ) (state : RawArena) (rows : List (List ℕ)) (n : ℕ) (x : Phase) (q : ℚ) (values : List ℂ)
    (same : rows.map (fun row=>nativePolynomial K state (row.getD n 0) x)=values) :
    ((rows.map (fun row=>(q,row))).map (fun term=>(term.1 : ℂ)*nativePolynomial K state (term.2.getD n 0) x)).sum=
      (values.map (fun value=>(q : ℂ)*value)).sum := by
  rw [←same]
  simp only [List.map_map]
  rfl

theorem originalForceOrEnergy_kernel_value (K order : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (keys : JCacheUnique runtime)
    (coefficients : SetupCoefficients K order runtime.arena setup) (n : Fin (setup.depth+1)) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalForceOrEnergy setup equation runtime).2.arena ((originalForceOrEnergy setup equation runtime).1.getD n.val 0) x=
      (forceOrEnergy setup.depth (sourceEngine order) equation n x : ℂ) := by
  let affine:=originalAffine setup equation runtime
  let first:=sourceApplyT setup 0 0 equation none affine.2
  let diagonal:=temporalInputs setup equation diagonalEntries first.2
  let cross:=temporalInputs setup equation crossEntries diagonal.2
  let time:=temporalInputs setup equation timeEntries cross.2
  have na:=originalAffine_full_native K setup equation runtime native
  have va:=(originalAffine_cached K setup equation runtime native.operations.cached native.operations.handles).2
  have ga:=originalAffine_grows setup equation runtime
  have nf:=sourceApplyT_properties K setup 0 0 equation none affine.2 na
  have gf:=sourceApplyT_grows setup 0 0 equation none affine.2
  have nd:=temporalInputs_values K order setup equation runtime diagonalEntries first.2 native coefficients (ga.trans gf) nf.1
  have gd:=temporalInputs_grows setup equation diagonalEntries first.2
  have nc:=temporalInputs_values K order setup equation runtime crossEntries diagonal.2 native coefficients ((ga.trans gf).trans gd) nd.1
  have gc:=temporalInputs_grows setup equation crossEntries diagonal.2
  have nt:=temporalInputs_values K order setup equation runtime timeEntries cross.2 native coefficients (((ga.trans gf).trans gd).trans gc) nc.1
  have gt:=temporalInputs_grows setup equation timeEntries cross.2
  have affineValue : nativePolynomial K time.2.arena (affine.1.getD n.val 0) x=(kernelAffine setup.depth order equation n x : ℂ) := by
    rw [nativePolynomial_prefix K (((gf.trans gd).trans gc).trans gt) na.operations.cached.handles.closed _ (list_getD_handle na.operations.cached.handles va n.val)]
    exact originalAffine_kernel_value K order setup equation runtime native keys coefficients n x hx
  have firstValue : nativePolynomial K time.2.arena (first.1.getD n.val 0) x=(kernelApplyT setup.depth order 0 0 equation (kernelInput none) n x : ℂ) := by
    rw [nativePolynomial_prefix K ((gd.trans gc).trans gt) nf.1.operations.cached.handles.closed _ (list_getD_handle nf.1.operations.cached.handles nf.2 n.val)]
    exact sourceApplyT_kernel_value K order setup 0 0 equation none affine.2 na
      (coefficients.extend ga native.operations.cached.handles.closed native.operations.handles.jclocks native.operations.handles.ellclock) n x hx
  have diagonalValue : diagonal.1.map (fun row=>nativePolynomial K time.2.arena (row.getD n.val 0) x)=
      diagonalEntries.map (fun entry=>(kernelApplyT setup.depth order entry.1 entry.2.1 equation (kernelInput entry.2.2) n x : ℂ)) := by
    rw [native_rows_prefix K diagonal.2 time.2 diagonal.1 n.val x (gc.trans gt) nd.1.operations.cached.handles nd.2.1]
    exact nd.2.2 n x hx
  have crossValue : cross.1.map (fun row=>nativePolynomial K time.2.arena (row.getD n.val 0) x)=
      crossEntries.map (fun entry=>(kernelApplyT setup.depth order entry.1 entry.2.1 equation (kernelInput entry.2.2) n x : ℂ)) := by
    rw [native_rows_prefix K cross.2 time.2 cross.1 n.val x gt nc.1.operations.cached.handles nc.2.1]
    exact nc.2.2 n x hx
  rw [originalForceOrEnergy_program]
  change nativePolynomial K (numericSeriesSum setup.depth affine.1
    ([(1/2,first.1)]++diagonal.1.map (fun row=>(-1/2,row))++cross.1.map (fun row=>(-1,row))++time.1.map (fun row=>(-1,row))) time.2).2.arena
      ((numericSeriesSum setup.depth affine.1
    ([(1/2,first.1)]++diagonal.1.map (fun row=>(-1/2,row))++cross.1.map (fun row=>(-1,row))++time.1.map (fun row=>(-1,row))) time.2).1.getD n.val 0) x=_
  rw [numericSeriesSum_value K setup.depth _ _ time.2 nt.1.operations.cached
    (list_extend (((gf.trans gd).trans gc).trans gt) va) (by
      intro term member
      simp only [List.mem_append,List.mem_singleton] at member
      rcases member with ((equal|diagonalMember)|crossMember)|timeMember
      · subst term;exact list_extend ((gd.trans gc).trans gt) nf.2
      · obtain ⟨row,present,rfl⟩:=List.mem_map.mp diagonalMember
        exact list_extend (gc.trans gt) (nd.2.1 row present)
      · obtain ⟨row,present,rfl⟩:=List.mem_map.mp crossMember
        exact list_extend gt (nc.2.1 row present)
      · obtain ⟨row,present,rfl⟩:=List.mem_map.mp timeMember
        exact nt.2.1 row present) n x hx]
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [affineValue,firstValue,weighted_rows_value K time.2.arena diagonal.1 n.val x (-1/2) _ diagonalValue,
    weighted_rows_value K time.2.arena cross.1 n.val x (-1) _ crossValue,
    weighted_rows_value K time.2.arena time.1 n.val x (-1) _ (nt.2.2 n x hx)]
  simp only [diagonalEntries,crossEntries,timeEntries,List.map_map,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,finRange_sum]
  simp only [forceOrEnergy,Pi.sub_apply,Pi.add_apply,Finset.sum_apply,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sum]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  have cf : (smooth_program_const% "crossFirst") = ![(0 : Fin 3),0,1] := rfl
  have cs : (smooth_program_const% "crossSecond") = ![(1 : Fin 3),2,2] := rfl
  have ci : (smooth_program_const% "crossSlot") = ![(7 : Fin 13),8,9] := rfl
  rw [cf,cs,ci]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ]
  simp only [Function.comp_apply,kernelApplyT,kernelAffine,kernelInput,kernelSourceSeries,kernelTraceSeries]
  simp only [show Fin.succ (0 : Fin 3) = (1 : Fin 4) from rfl,
    show Fin.succ (1 : Fin 3) = (2 : Fin 4) from rfl,show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl]
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,Rat.cast_div,Rat.cast_neg,Rat.cast_one]
  ring

theorem actual_engine_force_value (k : ℕ) (equation : Option (Fin 4))
    (n : Fin ((engineNextSetup k (originalEngine k)).depth+1)) (x : Phase) (hx : x∈poleDomain) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    nativePolynomial (k+1) (originalForceOrEnergy setup equation runtime).2.arena ((originalForceOrEnergy setup equation runtime).1.getD n.val 0) x=
      (forceOrEnergy setup.depth (sourceEngine (k+1)) equation n x : ℂ) :=
  originalForceOrEnergy_kernel_value (k+1) (k+1) _ equation _ (originalEngine_full_native (k+1) k)
    (originalEngine_keys (k+1)) (originalEngine_setup_coefficients (k+1) k (by omega)) n x hx

theorem actual_engine_force_all_jets (k : ℕ) (equation : Option (Fin 4))
    (n : Fin ((engineNextSetup k (originalEngine k)).depth+1)) (m : ℕ) (x : Phase) (hx : x∈poleDomain) (directions : Fin m → Phase) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    let result:=originalForceOrEnergy setup equation runtime
    iteratedFDeriv ℝ m (nativePolynomial (k+1) result.2.arena (result.1.getD n.val 0)) x directions=
      iteratedFDeriv ℝ m (fun y=>(forceOrEnergy setup.depth (sourceEngine (k+1)) equation n y : ℂ)) x directions := by
  have same : nativePolynomial (k+1) (originalForceOrEnergy (engineNextSetup k (originalEngine k)) equation (originalEngine (k+1)).runtime).2.arena
      ((originalForceOrEnergy (engineNextSetup k (originalEngine k)) equation (originalEngine (k+1)).runtime).1.getD n.val 0)=ᶠ[𝓝 x]
      (fun y=>(forceOrEnergy (engineNextSetup k (originalEngine k)).depth (sourceEngine (k+1)) equation n y : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact actual_engine_force_value k equation n y hy
  exact congrArg (fun D=>D directions) (same.iteratedFDeriv ℝ m).eq_of_nhds

theorem SetupCoefficients.restrict {K order : ℕ} {old next : RawArena} {setup : RawSetup}
    (values : SetupCoefficients K order next setup) (growth : RawExtends old next) (closed : RawMoyalClosed old)
    (jclocks : ∀ a,SeriesHandles old (setup.jclocks a)) (ellclock : SeriesHandles old setup.ellclock) :
    SetupCoefficients K order old setup := by
  constructor
  · intro a n within
    have same:=values.jordan a n within
    rw [readAngular_prefix K growth closed _ (series_getD (jclocks a) n)] at same
    exact same
  · intro n within
    have same:=values.ell n within
    rw [readAngular_prefix K growth closed _ (series_getD ellclock n)] at same
    exact same

def engineCheckedRun (k : ℕ) : List ℕ × List Bool × RawRuntime :=
  let residuals:=originalResidualRun k
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstalledRun k
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  originalChecks after.1 (k+1) residualIds installed.2.1 after.2

theorem engineCheckedRun_native (K k : ℕ) :
    FullSetupNative K (engineNextSetup k (originalEngine k)) (engineCheckedRun k).2.2 := by
  let engine:=originalEngine k
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))
  let residuals:=runtimeSequence actions before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  have hb:=runtimeSetup_cached (k+1) engine.clocks engine.runtime (originalEngine_cached K k) (originalEngine_handles k).clocks
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  have hr:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    before.2 before.2 actions (RawExtends.refl _) hb.1 grows (by
      intro action member current extension currentValid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalForceOrEnergy_cached K before.1 (some a) current currentValid (hb.2.extend extension))
  have clockGrow : RawExtends engine.runtime.arena residuals.2.arena :=
    (runtimeSetup_grows _ _ _).trans (runtimeSequence_grows actions grows before.2)
  have hi:=originalInstall_cached K k residualIds engine.clocks residuals.2 hr.1 (clocks_extend clockGrow (originalEngine_handles k).clocks)
  have ha:=runtimeSetup_full_native K (k+1) installed.1 installed.2.2.2 hi.1 hi.2.1
  exact originalChecks_full_native K after.1 (k+1) residualIds installed.2.1 after.2 ha

theorem engineCheckedRun_keys (k : ℕ) : JCacheUnique (engineCheckedRun k).2.2 := by
  let installed:=originalInstalledRun k
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  exact originalChecks_keys after.1 (k+1) _ installed.2.1 after.2 (runtimeSetup_keys _ _ _)

theorem engineCheckedRun_to_final (k : ℕ) : RawExtends (engineCheckedRun k).2.2.arena (originalEngine (k+1)).runtime.arena :=
  originalForceOrEnergy_grows (engineNextSetup k (originalEngine k)) none (engineCheckedRun k).2.2

theorem engineCheckedRun_coefficients (K k : ℕ) (bound : k < K) :
    SetupCoefficients K (k+1) (engineCheckedRun k).2.2.arena (engineNextSetup k (originalEngine k)) := by
  have native:=engineCheckedRun_native K k
  exact (originalEngine_setup_coefficients K k bound).restrict (engineCheckedRun_to_final k) native.operations.cached.handles.closed
    native.operations.handles.jclocks native.operations.handles.ellclock

theorem engineNextSetup_depth (k : ℕ) : (engineNextSetup k (originalEngine k)).depth=k+1 := rfl

theorem originalStageRecord_energy_id (k : ℕ) :
    (originalStageRecord k).energy=
      (originalForceOrEnergy (engineNextSetup k (originalEngine k)) none (engineCheckedRun k).2.2).1.getD (k+1) 0 := by
  unfold originalStageRecord
  change (((originalEngine k).stages++[_])[k]'(by simp only [List.length_append,List.length_singleton,originalEngine_stage_count];omega)).energy=_
  rw [List.getElem_append_right (by rw [originalEngine_stage_count])]
  simp only [originalEngine_stage_count,Nat.sub_self,List.getElem_cons_zero]
  rfl

theorem originalFiveNative_energy (k : ℕ) (x : Phase) (hx : x∈poleDomain) :
    originalFiveNative k (Fin.last 4) x=(sourceEngineEnergy (k+1) x : ℂ) := by
  unfold originalFiveNative
  rw [originalFive_energy,originalStageRecord_energy_id]
  exact originalForceOrEnergy_kernel_value (k+1) (k+1) (engineNextSetup k (originalEngine k)) none (engineCheckedRun k).2.2
    (engineCheckedRun_native (k+1) k) (engineCheckedRun_keys k) (engineCheckedRun_coefficients (k+1) k (by omega))
    ⟨k+1,by rw [engineNextSetup_depth];omega⟩ x hx

theorem originalFiveNative_energy_all_jets (k m : ℕ) (x : Phase) (hx : x∈poleDomain) (directions : Fin m → Phase) :
    iteratedFDeriv ℝ m (originalFiveNative k (Fin.last 4)) x directions=
      iteratedFDeriv ℝ m (fun y=>(sourceEngineEnergy (k+1) y : ℂ)) x directions := by
  have same : originalFiveNative k (Fin.last 4)=ᶠ[𝓝 x] (fun y=>(sourceEngineEnergy (k+1) y : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact originalFiveNative_energy k y hy
  exact congrArg (fun D=>D directions) (same.iteratedFDeriv ℝ m).eq_of_nhds

def forceInputs (setup : RawSetup) (axes : List (Fin 4)) : RuntimeAction (List (List ℕ)) :=
  runtimeSequence (axes.map (fun a=>originalForceOrEnergy setup (some a)))

theorem forceInputs_grows (setup : RawSetup) (axes : List (Fin 4)) (runtime : RawRuntime) :
    RawExtends runtime.arena (forceInputs setup axes runtime).2.arena := by
  apply runtimeSequence_grows
  intro action member current
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
  exact originalForceOrEnergy_grows setup (some a) current

theorem forceInputs_values (K order : ℕ) (setup : RawSetup) (base : RawRuntime) (axes : List (Fin 4)) (runtime : RawRuntime)
    (baseNative : FullSetupNative K setup base) (baseCoefficients : SetupCoefficients K order base.arena setup)
    (growth : RawExtends base.arena runtime.arena) (native : FullSetupNative K setup runtime) (keys : JCacheUnique runtime) :
    let result:=forceInputs setup axes runtime
    FullSetupNative K setup result.2 ∧ JCacheUnique result.2 ∧ (∀ row,row∈result.1 → ListHandles result.2.arena row) ∧
      ∀ n : Fin (setup.depth+1),∀ x,x∈poleDomain →
        result.1.map (fun row=>nativePolynomial K result.2.arena (row.getD n.val 0) x)=
          axes.map (fun a=>(forceOrEnergy setup.depth (sourceEngine order) (some a) n x : ℂ)) := by
  induction axes generalizing runtime with
  | nil=>exact ⟨native,keys,fun _ h=>False.elim (List.not_mem_nil h),fun _ _ _=>rfl⟩
  | cons a axes ih=>
    let first:=originalForceOrEnergy setup (some a) runtime
    have one:=originalForceOrEnergy_full_native K setup (some a) runtime native
    have oneValid:=(originalForceOrEnergy_cached K setup (some a) runtime native.operations.cached native.operations.handles).2
    have oneKeys:=originalForceOrEnergy_keys setup (some a) runtime keys
    have oneGrow:=originalForceOrEnergy_grows setup (some a) runtime
    have tail:=ih first.2 (growth.trans oneGrow) one oneKeys
    have tailGrow:=forceInputs_grows setup axes first.2
    refine ⟨tail.1,tail.2.1,?_,?_⟩
    · intro row member
      rcases List.mem_cons.mp member with equal|old
      · subst row;exact list_extend tailGrow oneValid
      · exact tail.2.2.1 row old
    · intro n x hx
      change nativePolynomial K (forceInputs setup axes first.2).2.arena (first.1.getD n.val 0) x::
        ((forceInputs setup axes first.2).1.map (fun row=>nativePolynomial K (forceInputs setup axes first.2).2.arena (row.getD n.val 0) x))=_
      rw [nativePolynomial_prefix K tailGrow one.operations.cached.handles.closed _ (list_getD_handle one.operations.cached.handles oneValid n.val),
        originalForceOrEnergy_kernel_value K order setup (some a) runtime native keys
          (baseCoefficients.extend growth baseNative.operations.cached.handles.closed baseNative.operations.handles.jclocks baseNative.operations.handles.ellclock) n x hx,
        tail.2.2.2 n x hx]
      rfl

def residualHandles (k : ℕ) : List ℕ := (originalResidualRun k).1.map (fun row=>row.getD (k+1) 0)

theorem actual_residual_values (K k : ℕ) (bound : k ≤ K) (x : Phase) (hx : x∈poleDomain) :
    (residualHandles k).map (fun id=>nativePolynomial K (originalResidualRun k).2.arena id x)=
      (List.finRange 4).map (fun a=>(forceOrEnergy (k+1) (sourceEngine k) (some a) (Fin.last (k+1)) x : ℂ)) := by
  let before:=actualSetup k (k+1)
  have native:=runtimeSetup_full_native K (k+1) (originalEngine k).clocks (originalEngine k).runtime
    (originalEngine_cached K k) (originalEngine_handles k).clocks
  have generated:=forceInputs_values K k before.1 before.2 (List.finRange 4) before.2 native
    (actual_reset_setup_coefficients K k (k+1) bound) (RawExtends.refl _) native (runtimeSetup_keys _ _ _)
  have value:=generated.2.2.2 (Fin.last (k+1)) x hx
  change ((originalResidualRun k).1.map (fun row=>nativePolynomial K (originalResidualRun k).2.arena (row.getD (k+1) 0) x))=_ at value
  unfold residualHandles
  rw [List.map_map]
  exact value

theorem actual_residual_cached (K k : ℕ) : CachedNative K (originalResidualRun k).2 := by
  let before:=actualSetup k (k+1)
  have native:=runtimeSetup_full_native K (k+1) (originalEngine k).clocks (originalEngine k).runtime
    (originalEngine_cached K k) (originalEngine_handles k).clocks
  exact (runtimeSequence_full_native K before.1 _ before.2 native (by
    intro action member current paid
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_full_native K before.1 (some a) current paid)).operations.cached

theorem actual_residual_handles (k : ℕ) : ListHandles (originalResidualRun k).2.arena (residualHandles k) := by
  intro id member
  obtain ⟨row,present,rfl⟩:=List.mem_map.mp member
  exact list_getD_handle (originalResidualRun_handles k).1 ((originalResidualRun_handles k).2 row present) (k+1)

def correctionRun (k : ℕ) (residualIds : List ℕ) (a : Fin 4) : RuntimeAction ℕ := fun runtime=>
  let atom:=runArena (rawAtom (.clock k a) false) runtime
  let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
    (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))) atom.2
  runArena (rawAdd scaled.1) scaled.2

def correctionRead (K : ℕ) (state : RawArena) (residualIds : List ℕ) (a : Fin 4) (x : Phase) : ℂ :=
  ∑ b : Fin 4,(coefficientValue (correctionCoefficient a b) x : ℂ)*nativePolynomial K state (residualIds.getD b.val 0) x

theorem correctionRun_grows (k : ℕ) (residualIds : List ℕ) (a : Fin 4) (runtime : RawRuntime) :
    RawExtends runtime.arena (correctionRun k residualIds a runtime).2.arena := by
  apply (rawAtom_extends (.clock k a) false runtime.arena).trans
  apply RawExtends.trans ?_ (rawAdd_extends _ _)
  exact runtimeSequence_grows _ (by
    intro action member current
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_extends _ _ _) (runArena (rawAtom (.clock k a) false) runtime).2

theorem correctionRun_value (K k : ℕ) (residualIds : List ℕ) (a : Fin 4) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (valid : ListHandles runtime.arena residualIds) :
    CachedNative K (correctionRun k residualIds a runtime).2 ∧ Handle (correctionRun k residualIds a runtime).2.arena (correctionRun k residualIds a runtime).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (correctionRun k residualIds a runtime).2.arena (correctionRun k residualIds a runtime).1 x=
        correctionRead K runtime.arena residualIds a x := by
  let atom:=runArena (rawAtom (.clock k a) false) runtime
  let actions:=(List.finRange 4).map (fun b=>runArena (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))
  let scaled:=runtimeSequence actions atom.2
  have atomPaid:=runAtom_cached (.clock k a) false runtime cached (by intro id member;cases member)
  have scaledPaid:=runtimeSequence_scalar_values K runtime atom.2 (List.finRange 4)
    (fun b=>runArena (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))
    (fun b x=>(coefficientValue (correctionCoefficient a b) x : ℂ)*nativePolynomial K runtime.arena (residualIds.getD b.val 0) x)
    (rawAtom_extends _ _ _) atomPaid.1 (fun _ _ _=>rawScale_extends _ _ _) (by
      intro b _ current growth paid
      have out:=runScale_cached (correctionCoefficient a b) (residualIds.getD b.val 0) current paid
      have handle:=list_getD_handle cached.handles valid b.val
      refine ⟨out.1,out.2,?_⟩
      intro x hx
      rw [show nativePolynomial K (runArena (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)) current).2.arena
          (runArena (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)) current).1 x=_ from
        rawScale_native K _ _ current.arena paid.handles.closed (handle_extend growth handle) x hx,
        nativePolynomial_prefix K growth cached.handles.closed _ handle])
  have out:=runAdd_cached scaled.1 scaled.2 scaledPaid.1
  refine ⟨out.1,out.2,?_⟩
  intro x hx
  rw [show nativePolynomial K (correctionRun k residualIds a runtime).2.arena (correctionRun k residualIds a runtime).1 x=_ from
    rawAdd_native K _ scaled.2.arena scaledPaid.1.handles.closed scaledPaid.2.1 x hx,scaledPaid.2.2 x hx,finRange_sum]
  rfl

theorem correctionRead_prefix (K : ℕ) (base current : RawRuntime) (ids : List ℕ) (a : Fin 4) (x : Phase)
    (growth : RawExtends base.arena current.arena) (closed : RuntimeHandles base) (valid : ListHandles base.arena ids) :
    correctionRead K current.arena ids a x=correctionRead K base.arena ids a x := by
  unfold correctionRead
  apply Finset.sum_congr rfl
  intro b _
  rw [nativePolynomial_prefix K growth closed.closed _ (list_getD_handle closed valid b.val)]

theorem installFold_definition_values (K k : ℕ) (base : RawRuntime) (residualIds : List ℕ) (axes : List (Fin 4))
    (out : RawClocks × List ℕ × List ℕ × RawRuntime) (done : List (Fin 4))
    (baseCached : CachedNative K base) (residualValid : ListHandles base.arena residualIds)
    (growth : RawExtends base.arena out.2.2.2.arena) (cached : CachedNative K out.2.2.2)
    (valid : ListHandles out.2.2.2.arena out.2.2.1)
    (native : ∀ x,x∈poleDomain → out.2.2.1.map (fun id=>nativePolynomial K out.2.2.2.arena id x)=done.map (fun a=>correctionRead K base.arena residualIds a x)) :
    let result:=axes.foldl (installStep k residualIds) out
    CachedNative K result.2.2.2 ∧ ListHandles result.2.2.2.arena result.2.2.1 ∧
      ∀ x,x∈poleDomain → result.2.2.1.map (fun id=>nativePolynomial K result.2.2.2.arena id x)=
        (done++axes).map (fun a=>correctionRead K base.arena residualIds a x) := by
  induction axes generalizing out done with
  | nil=>simpa only [List.foldl_nil,List.append_nil] using And.intro cached (And.intro valid native)
  | cons a axes ih=>
    let next:=installStep k residualIds out a
    have one:=correctionRun_value K k residualIds a out.2.2.2 cached (list_extend growth residualValid)
    have oneGrow:=correctionRun_grows k residualIds a out.2.2.2
    have nextValid : ListHandles next.2.2.2.arena next.2.2.1 :=
      list_append_handle (list_extend oneGrow valid) _ one.2.1
    have nextNative : ∀ x,x∈poleDomain → next.2.2.1.map (fun id=>nativePolynomial K next.2.2.2.arena id x)=
        (done++[a]).map (fun axis=>correctionRead K base.arena residualIds axis x) := by
      intro x hx
      change (out.2.2.1++[(correctionRun k residualIds a out.2.2.2).1]).map
        (fun id=>nativePolynomial K (correctionRun k residualIds a out.2.2.2).2.arena id x)=_
      rw [List.map_append,List.map_append,List.map_singleton,List.map_singleton,one.2.2 x hx,
        correctionRead_prefix K base out.2.2.2 residualIds a x growth baseCached.handles residualValid]
      congr 1
      calc
        _=out.2.2.1.map (fun id=>nativePolynomial K out.2.2.2.arena id x) := by
          apply List.map_congr_left
          intro id member
          exact congrFun (nativePolynomial_prefix K oneGrow cached.handles.closed id (valid id member)) x
        _=done.map (fun a=>correctionRead K base.arena residualIds a x) :=native x hx
    have rest:=ih next (done++[a]) (growth.trans oneGrow) one.1 nextValid nextNative
    simpa only [List.foldl_cons,List.append_assoc,List.singleton_append] using rest

theorem originalInstall_definition_values (K k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (valid : ListHandles runtime.arena residualIds) :
    let result:=originalInstall k residualIds clocks runtime
    CachedNative K result.2.2.2 ∧ ListHandles result.2.2.2.arena result.2.2.1 ∧
      ∀ x,x∈poleDomain → result.2.2.1.map (fun id=>nativePolynomial K result.2.2.2.arena id x)=
        (List.finRange 4).map (fun a=>correctionRead K runtime.arena residualIds a x) := by
  have generated:=installFold_definition_values K k runtime residualIds (List.finRange 4) (clocks,[],[],runtime) [] cached valid
    (RawExtends.refl _) cached (fun _ h=>False.elim (List.not_mem_nil h)) (fun _ _=>rfl)
  simpa only [originalInstall_as_fold,List.nil_append] using generated

theorem actual_installed_definition_values (k : ℕ) :
    CachedNative (k+1) (originalInstalledRun k).2.2.2 ∧ ListHandles (originalInstalledRun k).2.2.2.arena (originalInstalledRun k).2.2.1 ∧
      ∀ x,x∈poleDomain → (originalInstalledRun k).2.2.1.map (fun id=>nativePolynomial (k+1) (originalInstalledRun k).2.2.2.arena id x)=
        (List.finRange 4).map (fun a=>correctionRead (k+1) (originalResidualRun k).2.arena (residualHandles k) a x) :=
  originalInstall_definition_values (k+1) k (residualHandles k) (originalEngine k).clocks (originalResidualRun k).2
    (actual_residual_cached (k+1) k) (actual_residual_handles k)

theorem actual_residual_value (K k : ℕ) (bound : k ≤ K) (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalResidualRun k).2.arena ((residualHandles k).getD a.val 0) x=
      (forceOrEnergy (k+1) (sourceEngine k) (some a) (Fin.last (k+1)) x : ℂ) := by
  have cached:=actual_residual_cached K k
  rw [native_getD_value K _ _ _ cached.handles.closed cached.handles.initialized a.val x (actual_residual_values K k bound x hx)]
  rw [←List.ofFn_eq_map,List.getD_eq_getElem _ _ (by rw [List.length_ofFn];exact a.isLt),List.getElem_ofFn]

theorem originalInstalled_definition_value (k : ℕ) (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial (k+1) (originalInstalledRun k).2.2.2.arena ((originalInstalledRun k).2.2.1.getD a.val 0) x=
      (sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ) := by
  have generated:=actual_installed_definition_values k
  rw [native_getD_value (k+1) _ _ _ generated.1.handles.closed generated.1.handles.initialized a.val x (generated.2.2 x hx)]
  rw [←List.ofFn_eq_map,List.getD_eq_getElem _ _ (by rw [List.length_ofFn];exact a.isLt),List.getElem_ofFn,
    sourceEngine_generated_normalized k a x hx]
  unfold correctionRead
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [actual_residual_value (k+1) k (by omega) b x hx]

theorem originalInstalled_to_final (k : ℕ) : RawExtends (originalInstalledRun k).2.2.2.arena (originalEngine (k+1)).runtime.arena := by
  let installed:=originalInstalledRun k
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  exact ((runtimeSetup_grows (k+1) installed.1 installed.2.2.2).trans
    (originalChecks_grows after.1 (k+1) (residualHandles k) installed.2.1 after.2)).trans (engineCheckedRun_to_final k)

theorem originalStageRecord_definition_ids (k : ℕ) : (originalStageRecord k).clockDefinitions=(originalInstalledRun k).2.2.1 := by
  unfold originalStageRecord
  change (((originalEngine k).stages++[_])[k]'(by simp only [List.length_append,List.length_singleton,originalEngine_stage_count];omega)).clockDefinitions=_
  rw [List.getElem_append_right (by rw [originalEngine_stage_count])]
  simp only [originalEngine_stage_count,Nat.sub_self,List.getElem_cons_zero]
  rfl

theorem originalFiveNative_clock (k : ℕ) (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    originalFiveNative k a.castSucc x=(sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ) := by
  have generated:=actual_installed_definition_values k
  unfold originalFiveNative
  rw [originalFive_clock_definition,originalStageRecord_definition_ids,
    nativePolynomial_prefix (k+1) (originalInstalled_to_final k) generated.1.handles.closed _
      (list_getD_handle generated.1.handles generated.2.1 a.val)]
  exact originalInstalled_definition_value k a x hx

theorem originalFiveNative_actual (k : ℕ) (i : Fin 5) (x : Phase) (hx : x∈poleDomain) :
    originalFiveNative k i x=(PreparationVacuumLiteralFeed.actualFiveSymbols (k+1) i x : ℂ) := by
  induction i using Fin.lastCases with
  | last=>simpa only [PreparationVacuumLiteralFeed.actualFiveSymbols,Fin.lastCases_last] using originalFiveNative_energy k x hx
  | cast a=>simpa only [PreparationVacuumLiteralFeed.actualFiveSymbols,Fin.lastCases_castSucc] using originalFiveNative_clock k a x hx

theorem originalFiveNative_actual_all_jets (k m : ℕ) (i : Fin 5) (x : Phase) (hx : x∈poleDomain) (directions : Fin m → Phase) :
    iteratedFDeriv ℝ m (originalFiveNative k i) x directions=
      iteratedFDeriv ℝ m (fun y=>(PreparationVacuumLiteralFeed.actualFiveSymbols (k+1) i y : ℂ)) x directions := by
  have same : originalFiveNative k i=ᶠ[𝓝 x] (fun y=>(PreparationVacuumLiteralFeed.actualFiveSymbols (k+1) i y : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact originalFiveNative_actual k i y hy
  exact congrArg (fun D=>D directions) (same.iteratedFDeriv ℝ m).eq_of_nhds

end LowEnergy.PreparationVacuumKernelValues
