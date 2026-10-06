import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationSetupAngularValues

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSetupValues
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumNativeMemo
open PreparationVacuumDAGSemantic PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open PreparationVacuumMoyalNormalization PreparationVacuumArenaBudget PreparationVacuumArenaRows
open PreparationVacuumClockSymbol
open scoped BigOperators Topology

abbrev AngularField := AngularExponent → Phase → ℂ

def complexJordan (r : ℕ) (f g : Phase → ℂ) : Phase → ℂ := fun x=>
  (1/2 : ℂ)*(complexMoyal r f g x+complexMoyal r g f x)

def convolution (r : ℕ) (f g : AngularField) (u : AngularExponent) : Phase → ℂ := fun x=>
  ∑ pair∈Finset.HasAntidiagonal.antidiagonal u,complexJordan r (f pair.1) (g pair.2) x

def readAngular (K : ℕ) (state : RawArena) (rows : RawAngular) : AngularField :=
  fun u=>angularValue K state rows (fun j=>u j)

def singletonField (u : AngularExponent) (f : Phase → ℂ) : AngularField := by
  classical
  exact fun v=>if u=v then f else 0

def SmoothAngular (f : AngularField) : Prop := ∀ u,SmoothComplex (f u)

theorem readAngular_smooth (K : ℕ) (state : RawArena) (rows : RawAngular) : SmoothAngular (readAngular K state rows) :=
  fun _=>angularValue_smooth K state rows _

theorem singletonField_smooth (u : AngularExponent) (f : Phase → ℂ) (smooth : SmoothComplex f) :
    SmoothAngular (singletonField u f) := by
  classical
  intro v
  unfold singletonField
  split_ifs
  · exact smooth
  · exact contDiffOn_const

theorem readAngular_nil (K : ℕ) (state : RawArena) : readAngular K state []=0 := rfl

theorem readAngular_cons (K : ℕ) (state : RawArena) (row : RawAngle × ℕ) (rows : RawAngular) :
    readAngular K state (row::rows)=singletonField (angleExponent row.1) (nativePolynomial K state row.2)+readAngular K state rows := by
  classical
  funext u x
  rw [show readAngular K state (row::rows) u x=angularValue K state (row::rows) (fun j=>u j) x from rfl,angularValue_cons]
  change (if row.1=(fun j=>u j) then _ else 0)+_=(singletonField (angleExponent row.1) (nativePolynomial K state row.2) u) x+_
  have same : row.1=(fun j=>u j) ↔ angleExponent row.1=u := by
    constructor
    · intro h;ext j;exact congrFun h j
    · intro h;funext j;exact congrArg (fun a : AngularExponent=>a j) h
  simp only [singletonField,same]
  split_ifs <;> rfl

theorem complexJordan_zero_left (r : ℕ) (f : Phase → ℂ) : complexJordan r 0 f=0 := by
  funext x
  change (1/2 : ℂ)*(complexMoyal r (fun _=>0) f x+complexMoyal r f (fun _=>0) x)=0
  rw [moyal_zero_left,moyal_zero_right,add_zero,mul_zero]

theorem complexJordan_zero_right (r : ℕ) (f : Phase → ℂ) : complexJordan r f 0=0 := by
  funext x
  change (1/2 : ℂ)*(complexMoyal r f (fun _=>0) x+complexMoyal r (fun _=>0) f x)=0
  rw [moyal_zero_left,moyal_zero_right,add_zero,mul_zero]

theorem complexJordan_add_left (r : ℕ) (f g h : Phase → ℂ)
    (hf : SmoothComplex f) (hg : SmoothComplex g) (hh : SmoothComplex h) (x : Phase) (hx : x∈poleDomain) :
    complexJordan r (f+g) h x=complexJordan r f h x+complexJordan r g h x := by
  simp only [complexJordan]
  change (1/2 : ℂ)*(complexMoyal r (fun y=>f y+g y) h x+complexMoyal r h (fun y=>f y+g y) x)=_
  rw [moyal_add_left r f g h hf hg hh x hx,moyal_add_right r h f g hh hf hg x hx]
  ring

theorem complexJordan_add_right (r : ℕ) (f g h : Phase → ℂ)
    (hf : SmoothComplex f) (hg : SmoothComplex g) (hh : SmoothComplex h) (x : Phase) (hx : x∈poleDomain) :
    complexJordan r f (g+h) x=complexJordan r f g x+complexJordan r f h x := by
  simp only [complexJordan]
  change (1/2 : ℂ)*(complexMoyal r f (fun y=>g y+h y) x+complexMoyal r (fun y=>g y+h y) f x)=_
  rw [moyal_add_right r f g h hf hg hh x hx,moyal_add_left r g h f hg hh hf x hx]
  ring

theorem convolution_add_left (r : ℕ) (f g h : AngularField)
    (hf : SmoothAngular f) (hg : SmoothAngular g) (hh : SmoothAngular h) (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) :
    convolution r (f+g) h u x=convolution r f h u x+convolution r g h u x := by
  simp only [convolution,Pi.add_apply]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  exact complexJordan_add_left r _ _ _ (hf _) (hg _) (hh _) x hx

theorem convolution_add_right (r : ℕ) (f g h : AngularField)
    (hf : SmoothAngular f) (hg : SmoothAngular g) (hh : SmoothAngular h) (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) :
    convolution r f (g+h) u x=convolution r f g u x+convolution r f h u x := by
  simp only [convolution,Pi.add_apply]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  exact complexJordan_add_right r _ _ _ (hf _) (hg _) (hh _) x hx

theorem convolution_zero_left (r : ℕ) (f : AngularField) (u : AngularExponent) : convolution r 0 f u=0 := by
  funext x
  simp only [convolution,Pi.zero_apply,complexJordan_zero_left,Finset.sum_const_zero]

theorem convolution_zero_right (r : ℕ) (f : AngularField) (u : AngularExponent) : convolution r f 0 u=0 := by
  funext x
  simp only [convolution,Pi.zero_apply,complexJordan_zero_right,Finset.sum_const_zero]

theorem convolution_singletons (r : ℕ) (a b u : AngularExponent) (f g : Phase → ℂ) (x : Phase) :
    convolution r (singletonField a f) (singletonField b g) u x=
      if a+b=u then complexJordan r f g x else 0 := by
  classical
  unfold convolution
  have term (pair : AngularExponent × AngularExponent) :
      complexJordan r (singletonField a f pair.1) (singletonField b g pair.2) x=
        if pair=(a,b) then complexJordan r f g x else 0 := by
    unfold singletonField
    by_cases ha : a=pair.1 <;> by_cases hb : b=pair.2
    · simp [ha,hb]
    · simp [ha,hb,complexJordan_zero_right,Prod.ext_iff,eq_comm]
    · simp [ha,hb,complexJordan_zero_left,Prod.ext_iff,eq_comm]
    · simp [ha,hb,complexJordan_zero_left,Prod.ext_iff,eq_comm]
  simp only [term,Finset.sum_ite_eq',Finset.HasAntidiagonal.mem_antidiagonal]

theorem convolution_row_right (K r : ℕ) (state : RawArena) (a : RawAngle × ℕ) (right : RawAngular)
    (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) :
    convolution r (singletonField (angleExponent a.1) (nativePolynomial K state a.2)) (readAngular K state right) u x=
      (right.map (fun b=>if angleExponent a.1+angleExponent b.1=u then jordanValue K r state a.2 b.2 x else 0)).sum := by
  classical
  induction right with
  | nil=>rw [readAngular_nil,convolution_zero_right];rfl
  | cons b bs ih=>
    rw [readAngular_cons,convolution_add_right r _ _ _
      (singletonField_smooth _ _ (nativePolynomial_smooth K state a.2))
      (singletonField_smooth _ _ (nativePolynomial_smooth K state b.2))
      (readAngular_smooth K state bs) u x hx,convolution_singletons,ih]
    rfl

theorem convolution_rows (K r : ℕ) (state : RawArena) (left right : RawAngular)
    (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) :
    convolution r (readAngular K state left) (readAngular K state right) u x=
      (left.map (fun a=>(right.map (fun b=>if angleExponent a.1+angleExponent b.1=u then jordanValue K r state a.2 b.2 x else 0)).sum)).sum := by
  classical
  induction left with
  | nil=>rw [readAngular_nil,convolution_zero_left];rfl
  | cons a as ih=>
    rw [readAngular_cons,convolution_add_left r _ _ _
      (singletonField_smooth _ _ (nativePolynomial_smooth K state a.2))
      (readAngular_smooth K state as) (readAngular_smooth K state right) u x hx,
      convolution_row_right K r state a right u x hx,ih]
    rfl

theorem runtimeWeighted_convolution (K r : ℕ) (left right : RawAngular) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (hl : AngularHandles runtime.arena left) (hr : AngularHandles runtime.arena right)
    (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) :
    readAngular K (runtimeWeighted r left right runtime).2.arena (runtimeWeighted r left right runtime).1 u x=
      convolution r (readAngular K runtime.arena left) (readAngular K runtime.arena right) u x := by
  classical
  rw [readAngular,(runtimeWeighted_native K r left right runtime cached hl hr).2 _ x hx,
    convolution_rows K r runtime.arena left right u x hx]
  have delta (a b : RawAngle) : a+b=(fun j=>u j) ↔ angleExponent a+angleExponent b=u := by
    constructor
    · intro h;ext j;exact congrFun h j
    · intro h;funext j;exact congrArg (fun a : AngularExponent=>a j) h
  simp only [List.map_flatMap,List.map_map,Function.comp_def]
  clear cached hl hr
  induction left with
  | nil=>rfl
  | cons a rest ih=>
    simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro b _
    simp only [delta]

theorem weighted_coefficient_antidiagonal (r : ℕ) (P Q : AngularPolynomial) (u : AngularExponent) :
    MvPolynomial.coeff u (weighted r P Q)=
      ∑ pair∈Finset.HasAntidiagonal.antidiagonal u,scalarJordan r (MvPolynomial.coeff pair.1 P) (MvPolynomial.coeff pair.2 Q) := by
  classical
  let pairs:=(P.support ×ˢ Q.support).filter (fun pair=>pair.1+pair.2=u)
  have finite : MvPolynomial.coeff u (weighted r P Q)=
      ∑ pair∈pairs,scalarJordan r (MvPolynomial.coeff pair.1 P) (MvPolynomial.coeff pair.2 Q) := by
    simp only [weighted,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,pairs,Finset.sum_filter,Finset.sum_product]
  rw [finite]
  apply Finset.sum_subset
  · intro pair member
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Finset.mem_filter.mp member).2
  · intro pair member outside
    have notBoth : ¬(pair.1∈P.support ∧ pair.2∈Q.support) := by
      intro both
      exact outside (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr both,Finset.HasAntidiagonal.mem_antidiagonal.mp member⟩)
    by_cases first : pair.1∈P.support
    · have second : pair.2∉Q.support := fun h=>notBoth ⟨first,h⟩
      rw [MvPolynomial.notMem_support_iff.mp second,scalarJordan_zero_right]
    · rw [MvPolynomial.notMem_support_iff.mp first,scalarJordan_zero_left]

def realCoefficients (P : AngularPolynomial) : AngularField := fun u x=>(MvPolynomial.coeff u P x : ℂ)

theorem complexJordan_real (r : ℕ) (f g : PreparationVacuumCanonicalMoyal.Symbol) (x : Phase) :
    complexJordan r (fun y=>(f y : ℂ)) (fun y=>(g y : ℂ)) x=(scalarJordan r f g x : ℂ) := by
  rw [scalarJordan_native]
  simp only [complexJordan,complexMoyal_real,jordan]
  ring

theorem convolution_weighted (r : ℕ) (P Q : AngularPolynomial) (u : AngularExponent) (x : Phase) :
    convolution r (realCoefficients P) (realCoefficients Q) u x=realCoefficients (weighted r P Q) u x := by
  rw [realCoefficients,weighted_coefficient_antidiagonal]
  simp only [convolution,Finset.sum_apply,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro pair _
  exact complexJordan_real r _ _ x

def AngularAgrees (f g : AngularField) : Prop := ∀ u,Set.EqOn (f u) (g u) poleDomain

theorem complexJordan_germ (r : ℕ) (f f' g g' : Phase → ℂ) (x : Phase)
    (left : f=ᶠ[𝓝 x]f') (right : g=ᶠ[𝓝 x]g') :
    complexJordan r f g x=complexJordan r f' g' x := by
  unfold complexJordan
  rw [moyal_germ r f f' g g' x left right,moyal_germ r g g' f f' x right left]

theorem convolution_congr (r : ℕ) (f f' g g' : AngularField)
    (left : AngularAgrees f f') (right : AngularAgrees g g') :
    AngularAgrees (convolution r f g) (convolution r f' g') := by
  intro u x hx
  unfold convolution
  apply Finset.sum_congr rfl
  intro pair _
  apply complexJordan_germ
  · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact left pair.1 hy
  · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact right pair.2 hy

theorem runtimeWeighted_source (K r : ℕ) (left right : RawAngular) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (hl : AngularHandles runtime.arena left) (hr : AngularHandles runtime.arena right)
    (P Q : AngularPolynomial)
    (leftSource : AngularAgrees (readAngular K runtime.arena left) (realCoefficients P))
    (rightSource : AngularAgrees (readAngular K runtime.arena right) (realCoefficients Q)) :
    AngularAgrees (readAngular K (runtimeWeighted r left right runtime).2.arena (runtimeWeighted r left right runtime).1)
      (realCoefficients (weighted r P Q)) := by
  intro u x hx
  rw [runtimeWeighted_convolution K r left right runtime cached hl hr u x hx,
    convolution_congr r _ _ _ _ leftSource rightSource u hx,convolution_weighted]

theorem actual_weighted_convolution (order r : ℕ)
    (left right : List (RawAngle × Fin (originalEngine order).runtime.arena.polynomials.length)) :
    let runtime:=(originalEngine order).runtime
    let ls:=actualAngular order left
    let rs:=actualAngular order right
    AngularAgrees (readAngular (order+1) (runtimeWeighted r ls rs runtime).2.arena (runtimeWeighted r ls rs runtime).1)
      (convolution r (readAngular (order+1) runtime.arena ls) (readAngular (order+1) runtime.arena rs)) := by
  dsimp only
  intro u x hx
  exact runtimeWeighted_convolution (order+1) r _ _ _ (originalEngine_cached (order+1) order)
    (actualAngular_handles order left) (actualAngular_handles order right) u x hx

end LowEnergy.PreparationVacuumSetupValues
