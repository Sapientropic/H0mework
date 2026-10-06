import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineCanonicalRadial
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineSmoothProgram

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineHomogeneity
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineSource PreparationVacuumEngineSmooth
open PreparationVacuumEngineIdentities PreparationVacuumEngineResponse PreparationVacuumClockSymbol
open PreparationVacuumClockJacobian
open scoped BigOperators ContDiff

theorem radialLaw_zero (d : ℤ) : RadialLaw d (0 : PreparationVacuumCanonicalMoyal.Symbol) := by
  intro r hr x hx
  simp

theorem radialLaw_constant (c : ℝ) : RadialLaw 0 (fun _ => c) := by
  intro r hr x hx
  simp

theorem radialLaw_add {d : ℤ} {f g : PreparationVacuumCanonicalMoyal.Symbol}
    (hf : RadialLaw d f) (hg : RadialLaw d g) : RadialLaw d (f+g) := by
  intro r hr x hx
  simp only [Pi.add_apply,hf r hr x hx,hg r hr x hx,mul_add]

theorem radialLaw_sub {d : ℤ} {f g : PreparationVacuumCanonicalMoyal.Symbol}
    (hf : RadialLaw d f) (hg : RadialLaw d g) : RadialLaw d (f-g) := by
  intro r hr x hx
  simp only [Pi.sub_apply,hf r hr x hx,hg r hr x hx,mul_sub]

theorem radialLaw_mul {d e : ℤ} {f g : PreparationVacuumCanonicalMoyal.Symbol}
    (hf : RadialLaw d f) (hg : RadialLaw e g) : RadialLaw (d+e) (f*g) := by
  intro r hr x hx
  simp only [Pi.mul_apply,hf r hr x hx,hg r hr x hx,zpow_add₀ hr]
  ring

theorem radialLaw_sum {ι : Type*} (d : ℤ) (s : Finset ι) (F : ι → PreparationVacuumCanonicalMoyal.Symbol)
    (h : ∀ i∈s,RadialLaw d (F i)) : RadialLaw d (∑ i∈s,F i) := by
  intro r hr x hx
  simp only [Finset.sum_apply,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi r hr x hx)

def PolynomialLaw (d : ℤ) (P : AngularPolynomial) : Prop :=
  ∀ u : AngularExponent,RadialLaw d (MvPolynomial.coeff u P)

theorem polynomialLaw_zero (d : ℤ) : PolynomialLaw d 0 := by
  intro u
  simpa only [MvPolynomial.coeff_zero] using radialLaw_zero d

theorem polynomialLaw_monomial {d : ℤ} (u : AngularExponent)
    {f : PreparationVacuumCanonicalMoyal.Symbol} (hf : RadialLaw d f) :
    PolynomialLaw d (MvPolynomial.monomial u f) := by
  intro v
  by_cases same : u=v
  · subst v
    simpa only [MvPolynomial.coeff_monomial,ite_true] using hf
  · simpa only [MvPolynomial.coeff_monomial,if_neg same] using radialLaw_zero d

theorem polynomialLaw_C {d : ℤ} {f : PreparationVacuumCanonicalMoyal.Symbol} (hf : RadialLaw d f) :
    PolynomialLaw d (MvPolynomial.C f) := polynomialLaw_monomial 0 hf

theorem polynomialLaw_X (a : Fin 3) : PolynomialLaw 0 (MvPolynomial.X a : AngularPolynomial) :=
  polynomialLaw_monomial _ (radialLaw_constant 1)

theorem polynomialLaw_add {d : ℤ} {P Q : AngularPolynomial} (hp : PolynomialLaw d P) (hq : PolynomialLaw d Q) :
    PolynomialLaw d (P+Q) := by
  intro u
  simpa only [MvPolynomial.coeff_add] using radialLaw_add (hp u) (hq u)

theorem polynomialLaw_sub {d : ℤ} {P Q : AngularPolynomial} (hp : PolynomialLaw d P) (hq : PolynomialLaw d Q) :
    PolynomialLaw d (P-Q) := by
  intro u
  simpa only [MvPolynomial.coeff_sub] using radialLaw_sub (hp u) (hq u)

theorem polynomialLaw_sum {ι : Type*} (d : ℤ) (s : Finset ι) (P : ι → AngularPolynomial)
    (h : ∀ i∈s,PolynomialLaw d (P i)) : PolynomialLaw d (∑ i∈s,P i) := by
  intro u
  simpa only [MvPolynomial.coeff_sum] using radialLaw_sum d s (fun i => MvPolynomial.coeff u (P i))
    (fun i hi => h i hi u)

theorem polynomialLaw_weighted {dp dq : ℤ} {P Q : AngularPolynomial} (r : ℕ)
    (hp : PolynomialLaw dp P) (hq : PolynomialLaw dq Q) (sp : SmoothPolynomial P) (sq : SmoothPolynomial Q) :
    PolynomialLaw (dp+dq-r) (weighted r P Q) := by
  unfold weighted
  apply polynomialLaw_sum
  intro u _
  apply polynomialLaw_sum
  intro v _
  apply polynomialLaw_monomial
  exact scalarJordan_radial dp dq r _ _
    (fun x hx => (sp u x hx).contDiffAt (poleDomain_open.mem_nhds hx))
    (fun x hx => (sq v x hx).contDiffAt (poleDomain_open.mem_nhds hx)) (hp u) (hq v)

theorem polynomialLaw_mul {dp dq : ℤ} {P Q : AngularPolynomial}
    (hp : PolynomialLaw dp P) (hq : PolynomialLaw dq Q) (sp : SmoothPolynomial P) (sq : SmoothPolynomial Q) :
    PolynomialLaw (dp+dq) (P*Q) := by
  simpa only [Nat.cast_zero,sub_zero,weighted_zero] using polynomialLaw_weighted 0 hp hq sp sq

theorem polynomialLaw_average {d : ℤ} {P : AngularPolynomial} (hp : PolynomialLaw d P) : RadialLaw d (average P) := by
  unfold average
  apply radialLaw_sum
  intro u _
  change RadialLaw d ((fun _ => angularMoment u)*MvPolynomial.coeff u P)
  simpa only [zero_add] using radialLaw_mul (radialLaw_constant (angularMoment u)) (hp u)

def ClockLaw {k : ℕ} (clock : ClockAt k) : Prop :=
  ∀ (a : Fin 4) (i : ℕ),RadialLaw (-(i : ℤ)) ((smooth_program_const% "clockAt") clock a i)

def SeriesLaw (d : ℤ) (X : List AngularPolynomial) : Prop :=
  ∀ i : ℕ,PolynomialLaw (d-(i : ℤ)) (X.getD i 0)

theorem seriesLaw_nil (d : ℤ) : SeriesLaw d [] := by
  intro i
  simpa only [List.getD_nil] using polynomialLaw_zero (d-i)

theorem seriesLaw_append_one {d : ℤ} {X : List AngularPolynomial} {P : AngularPolynomial}
    (hx : SeriesLaw d X) (hp : PolynomialLaw (d-(X.length : ℤ)) P) : SeriesLaw d (X++[P]) := by
  intro i
  by_cases low : i<X.length
  · rw [List.getD_append _ _ _ _ low]
    exact hx i
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases same : i=X.length
    · subst i
      simpa only [Nat.sub_self,List.getD_cons_zero] using hp
    · rw [List.getD_eq_default _ _ (by simp only [List.length_cons,List.length_nil]; omega)]
      exact polynomialLaw_zero _

theorem clockPolynomial_radial {k : ℕ} {clock : ClockAt k} (hc : ClockLaw clock) (a : Fin 4) (i : ℕ) :
    PolynomialLaw (-(i : ℤ)) ((smooth_program_const% "clockPolynomial") clock a i) := polynomialLaw_C (hc a i)

theorem ellPolynomial_radial {k : ℕ} {clock : ClockAt k} (hc : ClockLaw clock) (sc : SmoothClock clock) (i : ℕ) :
    PolynomialLaw (-(i : ℤ)) ((smooth_program_const% "ellPolynomial") clock i) := by
  change PolynomialLaw _ ((smooth_program_const% "clockPolynomial") clock 0 i+
    ∑ a : Fin 3,MvPolynomial.X a*(smooth_program_const% "clockPolynomial") clock (Fin.succ a) i)
  apply polynomialLaw_add (clockPolynomial_radial hc 0 i)
  apply polynomialLaw_sum
  intro a _
  simpa only [zero_add] using polynomialLaw_mul (polynomialLaw_X a) (clockPolynomial_radial hc _ i)
    (smoothPolynomial_X a) (clockPolynomial_smooth sc _ i)

theorem sourceClock_inverse_radial : RadialLaw 0 (fun x => (sourceClock x)⁻¹) := by
  intro r hr x hx
  change (actualC (radial r x))⁻¹=r^(0 : ℤ)*(actualC x)⁻¹
  rw [actualC_radial r hr]
  simp

theorem sourceJ_radial {k : ℕ} {d : ℤ} (depth : ℕ) {clock : ClockAt k} (hc : ClockLaw clock)
    (sc : SmoothClock clock) (a : Fin 4) {X : List AngularPolynomial} (hx : SeriesLaw d X) (sx : SmoothSeries X) :
    SeriesLaw d ((smooth_program_const% "js") depth clock a X) := by
  intro n
  by_cases hn : n<depth+1
  · change PolynomialLaw _ ((List.ofFn (fun m : Fin (depth+1) =>
      ∑ i∈Finset.range (m.val+1),∑ j∈Finset.range (m.val+1-i),weighted (m.val-i-j)
        ((smooth_program_const% "clockPolynomial") clock a i) (X.getD j 0))).getD n 0)
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hn,dif_pos,Option.getD_some]
    apply polynomialLaw_sum
    intro i hi
    apply polynomialLaw_sum
    intro j hj
    have equality : -(i : ℤ)+(d-j)-((n-i-j : ℕ) : ℤ)=d-n := by
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hj
      omega
    rw [←equality]
    exact polynomialLaw_weighted _ (clockPolynomial_radial hc a i) (hx j)
      (clockPolynomial_smooth sc a i) (smoothSeries_getD sx j)
  · rw [List.getD_eq_default _ _ (by change (List.ofFn _).length≤n; simp only [List.length_ofFn]; omega)]
    exact polynomialLaw_zero _

theorem sourceR_next_radial {k : ℕ} {d : ℤ} {clock : ClockAt k} (hc : ClockLaw clock) (sc : SmoothClock clock)
    {X answers : List AngularPolynomial} (hx : SeriesLaw d X) (sx : SmoothSeries X)
    (ha : SeriesLaw d answers) (sa : SmoothSeries answers) (n : ℕ) :
    PolynomialLaw (d-n) ((smooth_program_const% "resolventNext") clock X answers n) := by
  change PolynomialLaw _ (MvPolynomial.C (fun x => (sourceClock x)⁻¹)*
    (X.getD n 0-∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1-i),
      if i=0 ∧ n-i-j=0 then 0 else weighted (n-i-j)
        ((smooth_program_const% "ellPolynomial") clock i) (answers.getD j 0)))
  rw [←zero_add (d-(n : ℤ))]
  apply polynomialLaw_mul (dp:=0) (dq:=d-n) (polynomialLaw_C sourceClock_inverse_radial)
  · apply polynomialLaw_sub (hx n)
    apply polynomialLaw_sum
    intro i hi
    apply polynomialLaw_sum
    intro j hj
    split_ifs
    · exact polynomialLaw_zero _
    · have equality : -(i : ℤ)+(d-j)-((n-i-j : ℕ) : ℤ)=d-n := by
        have := Finset.mem_range.mp hi
        have := Finset.mem_range.mp hj
        omega
      rw [←equality]
      exact polynomialLaw_weighted _ (ellPolynomial_radial hc sc i) (ha j)
        (ellPolynomial_smooth sc i) (smoothSeries_getD sa j)
  · exact smoothPolynomial_constant sourceClock_inverse_smooth
  · apply smoothPolynomial_sub (smoothSeries_getD sx n)
    apply smoothPolynomial_sum
    intro i _
    apply smoothPolynomial_sum
    intro j _
    split_ifs
    · exact smoothPolynomial_zero
    · exact smoothPolynomial_weighted _ (ellPolynomial_smooth sc i) (smoothSeries_getD sa j)

end LowEnergy.PreparationVacuumEngineHomogeneity
