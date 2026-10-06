import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineAverageBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineBudget
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationVacuumEngineSmooth
open PreparationVacuumMoyalBudget PreparationVacuumClockSymbol
open scoped BigOperators ContDiff
variable {x : SourcePhase}

structure SymbolEstimate (f : RealSymbol) (x : SourcePhase) where
  upper : JetMajorant
  bound : SymbolBound f upper x

structure PolynomialEstimate (P : AngularPolynomial) (x : SourcePhase) where
  upper : PolynomialMajorant
  bound : PolynomialBound P upper x

abbrev SeriesEstimate (X : List AngularPolynomial) (x : SourcePhase) :=
  ∀ n : ℕ,PolynomialEstimate (X.getD n 0) x

abbrev ClockEstimate {k : ℕ} (clock : ClockAt k) (x : SourcePhase) :=
  ∀ a i,SymbolEstimate ((smooth_program_const% "clockAt") clock a i) x

def symbolZero (x : SourcePhase) : SymbolEstimate 0 x := ⟨fun _ => 0,symbolBound_zero x⟩

def symbolConstant (c : ℝ) (x : SourcePhase) : SymbolEstimate (fun _ => c) x where
  upper m := if m=0 then |c| else 0
  bound := by
    intro m w
    cases m with
    | zero => simp [jet]
    | succ m => simp [jet,iteratedFDeriv_succ_const]

def symbolScale (c : ℝ) {f : RealSymbol} (sf : SmoothSymbol f) (x : SourcePhase) (hx : x∈poleDomain)
    (bf : SymbolEstimate f x) : SymbolEstimate (fun y => c*f y) x :=
  ⟨fun m => |c| *bf.upper m,symbolBound_scale c sf x hx bf.bound⟩

def symbolAdd {f g : RealSymbol} (sf : SmoothSymbol f) (sg : SmoothSymbol g)
    (x : SourcePhase) (hx : x∈poleDomain) (bf : SymbolEstimate f x) (bg : SymbolEstimate g x) :
    SymbolEstimate (f+g) x := ⟨fun m => bf.upper m+bg.upper m,symbolBound_add sf sg x hx bf.bound bg.bound⟩

def symbolSum {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → RealSymbol) (sf : ∀ i∈s,SmoothSymbol (f i))
    (x : SourcePhase) (hx : x∈poleDomain) (bf : ∀ i∈s,SymbolEstimate (f i) x) : SymbolEstimate (∑ i∈s,f i) x where
  upper m := ∑ i∈s,if hi : i∈s then (bf i hi).upper m else 0
  bound := by
    intro m w
    have representation : (∑ i∈s,f i)=(fun y => ∑ i∈s,f i y) := by funext y; simp only [Finset.sum_apply]
    rw [representation,jet_sum poleDomain_open s f sf m w x hx]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    simpa only [dif_pos hi] using (bf i hi).bound m w

def symbolNeg {f : RealSymbol} (sf : SmoothSymbol f) (x : SourcePhase) (hx : x∈poleDomain)
    (bf : SymbolEstimate f x) : SymbolEstimate (-f) x where
  upper := bf.upper
  bound := by
    intro m w
    have same : -f=(fun y => (-1 : ℝ)*f y) := by funext y; simp
    rw [same,jet_scale (-1) f sf m w x hx,abs_mul]
    simpa only [abs_neg,abs_one,one_mul] using bf.bound m w

def symbolSub {f g : RealSymbol} (sf : SmoothSymbol f) (sg : SmoothSymbol g)
    (x : SourcePhase) (hx : x∈poleDomain) (bf : SymbolEstimate f x) (bg : SymbolEstimate g x) :
    SymbolEstimate (f-g) x := by
  have result := symbolAdd sf (smoothSymbol_neg sg) x hx bf (symbolNeg sg x hx bg)
  simpa only [sub_eq_add_neg] using result

def symbolProduct {f g : RealSymbol} (sf : SmoothSymbol f) (sg : SmoothSymbol g)
    (x : SourcePhase) (hx : x∈poleDomain) (bf : SymbolEstimate f x) (bg : SymbolEstimate g x) :
    SymbolEstimate (f*g) x where
  upper m := convolution m 0 bf.upper bg.upper
  bound := by
    intro m w
    have result := scalarJordan_canonical_budget poleDomain_open 0 m f g sf sg w x hx bf.upper bg.upper
      (fun n => symbolBound_nonnegative f bf.upper x bf.bound n)
      (fun n _ v => bf.bound n v) (fun n _ v => bg.bound n v)
    simpa only [scalarJordan_zero,moyalScale,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one,one_mul] using result

def polynomialZero (x : SourcePhase) : PolynomialEstimate 0 x := ⟨fun _ _ => 0,polynomialBound_zero x⟩

def polynomialMonomial (u : AngularExponent) {f : RealSymbol} (bf : SymbolEstimate f x) :
    PolynomialEstimate (MvPolynomial.monomial u f) x where
  upper v m := if u=v then bf.upper m else 0
  bound := by
    intro v
    by_cases same : u=v
    · subst v
      simpa only [MvPolynomial.coeff_monomial,ite_true] using bf.bound
    · simpa only [MvPolynomial.coeff_monomial,if_neg same] using symbolBound_zero x

def polynomialConstant {f : RealSymbol} (bf : SymbolEstimate f x) : PolynomialEstimate (MvPolynomial.C f) x :=
  polynomialMonomial 0 bf

def polynomialAdd {P Q : AngularPolynomial} (sp : SmoothPolynomial P) (sq : SmoothPolynomial Q)
    (x : SourcePhase) (hx : x∈poleDomain) (bp : PolynomialEstimate P x) (bq : PolynomialEstimate Q x) :
    PolynomialEstimate (P+Q) x := ⟨fun u m => bp.upper u m+bq.upper u m,polynomialBound_add sp sq x hx bp.bound bq.bound⟩

def polynomialNeg {P : AngularPolynomial} (sp : SmoothPolynomial P)
    (x : SourcePhase) (hx : x∈poleDomain) (bp : PolynomialEstimate P x) : PolynomialEstimate (-P) x where
  upper := bp.upper
  bound := by
    intro u
    have negative := (symbolNeg (sp u) x hx ⟨bp.upper u,bp.bound u⟩).bound
    simpa only [MvPolynomial.coeff_neg,symbolNeg] using negative

def polynomialSub {P Q : AngularPolynomial} (sp : SmoothPolynomial P) (sq : SmoothPolynomial Q)
    (x : SourcePhase) (hx : x∈poleDomain) (bp : PolynomialEstimate P x) (bq : PolynomialEstimate Q x) :
    PolynomialEstimate (P-Q) x := by
  have sn : SmoothPolynomial (-Q) := by simpa only [zero_sub] using smoothPolynomial_sub smoothPolynomial_zero sq
  have result := polynomialAdd sp sn x hx bp (polynomialNeg sq x hx bq)
  simpa only [sub_eq_add_neg] using result

def polynomialSum {ι : Type} [DecidableEq ι] (s : Finset ι) (P : ι → AngularPolynomial) (sp : ∀ i∈s,SmoothPolynomial (P i))
    (x : SourcePhase) (hx : x∈poleDomain) (bp : ∀ i∈s,PolynomialEstimate (P i) x) :
    PolynomialEstimate (∑ i∈s,P i) x where
  upper u m := ∑ i∈s,if hi : i∈s then (bp i hi).upper u m else 0
  bound := by
    intro u
    simpa only [MvPolynomial.coeff_sum,symbolSum] using
      (symbolSum s (fun i => MvPolynomial.coeff u (P i)) (fun i hi => sp i hi u) x hx
        (fun i hi => ⟨(bp i hi).upper u,(bp i hi).bound u⟩)).bound

def polynomialWeighted (r : ℕ) {P Q : AngularPolynomial} (sp : SmoothPolynomial P) (sq : SmoothPolynomial Q)
    (x : SourcePhase) (hx : x∈poleDomain) (bp : PolynomialEstimate P x) (bq : PolynomialEstimate Q x) :
    PolynomialEstimate (weighted r P Q) x :=
  ⟨weightedMajorant r P Q bp.upper bq.upper,weighted_budget r P Q bp.upper bq.upper sp sq x hx bp.bound bq.bound⟩

def polynomialProduct {P Q : AngularPolynomial} (sp : SmoothPolynomial P) (sq : SmoothPolynomial Q)
    (x : SourcePhase) (hx : x∈poleDomain) (bp : PolynomialEstimate P x) (bq : PolynomialEstimate Q x) :
    PolynomialEstimate (P*Q) x := by
  have result := polynomialWeighted 0 sp sq x hx bp bq
  simpa only [weighted_zero] using result

def polynomialAverage {P : AngularPolynomial} (sp : SmoothPolynomial P)
    (x : SourcePhase) (hx : x∈poleDomain) (bp : PolynomialEstimate P x) : SymbolEstimate (average P) x :=
  ⟨averageMajorant P bp.upper,average_budget P bp.upper sp x hx bp.bound⟩

def seriesNil (x : SourcePhase) : SeriesEstimate [] x := fun _ => polynomialZero x

def seriesAppendOne {X : List AngularPolynomial} {P : AngularPolynomial}
    (bx : SeriesEstimate X x) (bp : PolynomialEstimate P x) : SeriesEstimate (X++[P]) x := by
  intro n
  by_cases low : n<X.length
  · rw [List.getD_append _ _ _ _ low]
    exact bx n
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases same : n=X.length
    · subst n
      simpa only [Nat.sub_self,List.getD_cons_zero] using bp
    · rw [List.getD_eq_default _ _ (by simp only [List.length_cons,List.length_nil]; omega)]
      exact polynomialZero x

def clockPolynomialEstimate {k : ℕ} {clock : ClockAt k} (bc : ClockEstimate clock x) (a : Fin 4) (i : ℕ) :
    PolynomialEstimate ((smooth_program_const% "clockPolynomial") clock a i) x := polynomialConstant (bc a i)

def ellEstimate {k : ℕ} {clock : ClockAt k} (sc : SmoothClock clock) (x : SourcePhase) (hx : x∈poleDomain)
    (bc : ClockEstimate clock x) (i : ℕ) : PolynomialEstimate ((smooth_program_const% "ellPolynomial") clock i) x :=
  polynomialAdd (clockPolynomial_smooth sc 0 i)
    (smoothPolynomial_sum _ _ (fun a _ => smoothPolynomial_mul (smoothPolynomial_X a) (clockPolynomial_smooth sc _ i))) x hx
    (clockPolynomialEstimate bc 0 i)
    (polynomialSum Finset.univ _ (fun a _ => smoothPolynomial_mul (smoothPolynomial_X a) (clockPolynomial_smooth sc _ i)) x hx
      (fun a _ => polynomialProduct (smoothPolynomial_X a) (clockPolynomial_smooth sc _ i) x hx
        (polynomialMonomial _ (symbolConstant 1 x)) (clockPolynomialEstimate bc _ i)))

def sourceJEstimate {k : ℕ} (depth : ℕ) {clock : ClockAt k} (sc : SmoothClock clock)
    (x : SourcePhase) (hx : x∈poleDomain) (bc : ClockEstimate clock x)
    {X : List AngularPolynomial} (sx : SmoothSeries X) (bx : SeriesEstimate X x) :
    ∀ a,SeriesEstimate ((smooth_program_const% "js") depth clock a X) x := by
  intro a n
  by_cases hn : n<depth+1
  · change PolynomialEstimate ((List.ofFn (fun m : Fin (depth+1) =>
      ∑ i∈Finset.range (m.val+1),∑ j∈Finset.range (m.val+1-i),weighted (m.val-i-j)
        ((smooth_program_const% "clockPolynomial") clock a i) (X.getD j 0))).getD n 0) x
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hn,dif_pos,Option.getD_some]
    apply polynomialSum
    · intro i _
      apply smoothPolynomial_sum
      intro j _
      exact smoothPolynomial_weighted _ (clockPolynomial_smooth sc a i) (smoothSeries_getD sx j)
    · exact hx
    · intro i _
      apply polynomialSum
      · intro j _
        exact smoothPolynomial_weighted _ (clockPolynomial_smooth sc a i) (smoothSeries_getD sx j)
      · exact hx
      · intro j _
        exact polynomialWeighted _ (clockPolynomial_smooth sc a i) (smoothSeries_getD sx j) x hx
          (clockPolynomialEstimate bc a i) (bx j)
  · rw [List.getD_eq_default _ _ (by change (List.ofFn _).length≤n; simp only [List.length_ofFn]; omega)]
    exact polynomialZero x


private theorem sourceRBody_smooth {k : ℕ} {clock : ClockAt k} (sc : SmoothClock clock)
    {X answers : List AngularPolynomial} (sx : SmoothSeries X) (sa : SmoothSeries answers) (n : ℕ) :
    SmoothPolynomial (X.getD n 0-∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1-i),
      if i=0 ∧ n-i-j=0 then 0 else weighted (n-i-j)
        ((smooth_program_const% "ellPolynomial") clock i) (answers.getD j 0)) := by
  apply smoothPolynomial_sub (smoothSeries_getD sx n)
  apply smoothPolynomial_sum
  intro i _
  apply smoothPolynomial_sum
  intro j _
  split_ifs
  · exact smoothPolynomial_zero
  · exact smoothPolynomial_weighted _ (ellPolynomial_smooth sc i) (smoothSeries_getD sa j)

def sourceRNextEstimate {k : ℕ} {clock : ClockAt k} (sc : SmoothClock clock)
    (x : SourcePhase) (hx : x∈poleDomain) (bc : ClockEstimate clock x)
    (inverse : SymbolEstimate (fun y => (sourceClock y)⁻¹) x)
    {X answers : List AngularPolynomial} (sx : SmoothSeries X) (sa : SmoothSeries answers)
    (bx : SeriesEstimate X x) (ba : SeriesEstimate answers x) (n : ℕ) :
    PolynomialEstimate ((smooth_program_const% "resolventNext") clock X answers n) x := by
  change PolynomialEstimate (MvPolynomial.C (fun y => (sourceClock y)⁻¹)*
    (X.getD n 0-∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1-i),
      if i=0 ∧ n-i-j=0 then 0 else weighted (n-i-j)
        ((smooth_program_const% "ellPolynomial") clock i) (answers.getD j 0))) x
  apply polynomialProduct (smoothPolynomial_constant sourceClock_inverse_smooth) (sourceRBody_smooth sc sx sa n) x hx
    (polynomialConstant inverse)
  apply polynomialSub (smoothSeries_getD sx n)
  · apply smoothPolynomial_sum
    intro i _
    apply smoothPolynomial_sum
    intro j _
    split_ifs
    · exact smoothPolynomial_zero
    · exact smoothPolynomial_weighted _ (ellPolynomial_smooth sc i) (smoothSeries_getD sa j)
  · exact hx
  · exact bx n
  · apply polynomialSum
    · intro i _
      apply smoothPolynomial_sum
      intro j _
      split_ifs
      · exact smoothPolynomial_zero
      · exact smoothPolynomial_weighted _ (ellPolynomial_smooth sc i) (smoothSeries_getD sa j)
    · exact hx
    · intro i _
      apply polynomialSum
      · intro j _
        split_ifs
        · exact smoothPolynomial_zero
        · exact smoothPolynomial_weighted _ (ellPolynomial_smooth sc i) (smoothSeries_getD sa j)
      · exact hx
      · intro j _
        split_ifs
        · exact polynomialZero x
        · exact polynomialWeighted _ (ellPolynomial_smooth sc i) (smoothSeries_getD sa j) x hx
            (ellEstimate sc x hx bc i) (ba j)

def sourceREstimate {k : ℕ} (depth : ℕ) {clock : ClockAt k} (sc : SmoothClock clock)
    (x : SourcePhase) (hx : x∈poleDomain) (bc : ClockEstimate clock x)
    (inverse : SymbolEstimate (fun y => (sourceClock y)⁻¹) x)
    {X : List AngularPolynomial} (sx : SmoothSeries X) (bx : SeriesEstimate X x) :
    SeriesEstimate ((smooth_program_const% "resolvent") depth clock X) x :=
  Nat.rec (motive:=fun n => SeriesEstimate ((smooth_program_const% "resolvent") n clock X) x)
    (by
      have equal : (smooth_program_const% "resolvent") 0 clock X=[]++[
          (smooth_program_const% "resolventNext") clock X [] 0] := rfl
      rw [equal]
      exact seriesAppendOne (seriesNil x) (sourceRNextEstimate sc x hx bc inverse sx smoothSeries_nil bx (seriesNil x) 0))
    (fun n previous => by
      have equal := (filtration_const% "R_succ") n clock X
      change (smooth_program_const% "resolvent") (n+1) clock X=
        (smooth_program_const% "resolvent") n clock X++[(smooth_program_const% "resolventNext")
          clock X ((smooth_program_const% "resolvent") n clock X) (n+1)] at equal
      rw [equal]
      exact seriesAppendOne previous (sourceRNextEstimate sc x hx bc inverse sx (sourceR_program_smooth n sc sx)
        bx previous (n+1))) depth

def sourceActEstimate {k : ℕ} (depth : ℕ) {clock : ClockAt k} (sc : SmoothClock clock)
    (x : SourcePhase) (hx : x∈poleDomain) (bc : ClockEstimate clock x)
    (inverse : SymbolEstimate (fun y => (sourceClock y)⁻¹) x) (token : Token)
    {X : List AngularPolynomial} (sx : SmoothSeries X) (bx : SeriesEstimate X x) :
    SeriesEstimate ((smooth_program_const% "act") depth clock token X) x := by
  cases token with
  | inverse => exact sourceREstimate depth sc x hx bc inverse sx bx
  | jordan a => exact sourceJEstimate depth sc x hx bc sx bx a

def sourceWordEstimate {k : ℕ} (depth : ℕ) {clock : ClockAt k} (sc : SmoothClock clock)
    (x : SourcePhase) (hx : x∈poleDomain) (bc : ClockEstimate clock x)
    (inverse : SymbolEstimate (fun y => (sourceClock y)⁻¹) x)
    (tokens : List Token) {X : List AngularPolynomial} (sx : SmoothSeries X) (bx : SeriesEstimate X x) :
    SeriesEstimate ((smooth_program_const% "word") depth clock tokens X) x :=
  List.rec (motive:=fun terms => SeriesEstimate ((smooth_program_const% "word") depth clock terms X) x)
    bx (fun token terms previous => sourceActEstimate depth sc x hx bc inverse token
      (sourceWord_program_smooth depth sc terms sx) previous) tokens


def sourceTableEstimate {k : ℕ} (depth : ℕ) {clock : ClockAt k} (sc : SmoothClock clock)
    (x : SourcePhase) (hx : x∈poleDomain) (bc : ClockEstimate clock x)
    (inverse : SymbolEstimate (fun y => (sourceClock y)⁻¹) x)
    (a b : Fin 4) (equation : Option (Fin 4)) {X : List AngularPolynomial}
    (sx : SmoothSeries X) (bx : SeriesEstimate X x) (n : Fin (depth+1)) :
    SymbolEstimate ((smooth_program_const% "applyT") depth clock a b equation X n) x := by
  let termPolynomial : TableTerm → AngularPolynomial := fun term =>
    MvPolynomial.C (fun _ => term.coefficient)*(MvPolynomial.monomial term.exponent 1*
      ((smooth_program_const% "word") depth clock term.tokens X).getD n.val 0)
  have termSmooth (term : TableTerm) : SmoothPolynomial (termPolynomial term) :=
    smoothPolynomial_mul (smoothPolynomial_constant (smoothSymbol_const term.coefficient))
      (smoothPolynomial_mul (smoothPolynomial_monomial _ (smoothSymbol_const 1))
        (smoothSeries_getD (sourceWord_program_smooth depth sc term.tokens sx) n.val))
  let termEstimate (term : TableTerm) : PolynomialEstimate (termPolynomial term) x :=
    polynomialProduct (smoothPolynomial_constant (smoothSymbol_const term.coefficient))
      (smoothPolynomial_mul (smoothPolynomial_monomial _ (smoothSymbol_const 1))
        (smoothSeries_getD (sourceWord_program_smooth depth sc term.tokens sx) n.val)) x hx
      (polynomialConstant (symbolConstant term.coefficient x))
      (polynomialProduct (smoothPolynomial_monomial _ (smoothSymbol_const 1))
        (smoothSeries_getD (sourceWord_program_smooth depth sc term.tokens sx) n.val) x hx
        (polynomialMonomial _ (symbolConstant 1 x))
        (sourceWordEstimate depth sc x hx bc inverse term.tokens sx bx n.val))
  let fold : ∀ terms : List TableTerm,∀ initial : AngularPolynomial,SmoothPolynomial initial →
      PolynomialEstimate initial x → PolynomialEstimate (terms.foldl (fun out term => out+termPolynomial term) initial) x :=
    List.rec (motive:=fun terms => ∀ initial : AngularPolynomial,SmoothPolynomial initial →
      PolynomialEstimate initial x → PolynomialEstimate (terms.foldl (fun out term => out+termPolynomial term) initial) x)
      (fun _ _ estimate => estimate)
      (fun term _ previous initial smooth estimate =>
        previous (initial+termPolynomial term) (smoothPolynomial_add smooth (termSmooth term))
          (polynomialAdd smooth (termSmooth term) x hx estimate (termEstimate term)))
  let smoothFold : ∀ terms : List TableTerm,∀ initial : AngularPolynomial,SmoothPolynomial initial →
      SmoothPolynomial (terms.foldl (fun out term => out+termPolynomial term) initial) :=
    List.rec (motive:=fun terms => ∀ initial : AngularPolynomial,SmoothPolynomial initial →
      SmoothPolynomial (terms.foldl (fun out term => out+termPolynomial term) initial))
      (fun _ smooth => smooth)
      (fun term _ previous initial smooth => previous (initial+termPolynomial term)
        (smoothPolynomial_add smooth (termSmooth term)))
  exact polynomialAverage (smoothFold ((smooth_program_const% "table") a b equation) 0 smoothPolynomial_zero) x hx
    (fold ((smooth_program_const% "table") a b equation) 0 smoothPolynomial_zero (polynomialZero x))

end LowEnergy.PreparationVacuumEngineBudget
