import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgramRadial
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineSmoothActual

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineHomogeneity
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineSource PreparationVacuumEngineSmooth
open PreparationVacuumEngineIdentities PreparationVacuumEngineResponse PreparationVacuumClockSymbol
open PreparationVacuumClockJacobian PreparationVacuumLowerLeaves PreparationVacuumEnergyTail
open PreparationActualFactor PreparationVacuumWeyl
open scoped BigOperators ContDiff

theorem sourceR_radial {k : ℕ} {d : ℤ} (depth : ℕ) {clock : ClockAt k}
    (hc : ClockLaw clock) (sc : SmoothClock clock) {X : List AngularPolynomial}
    (hx : SeriesLaw d X) (sx : SmoothSeries X) :
    SeriesLaw d ((smooth_program_const% "resolvent") depth clock X) := by
  induction depth with
  | zero =>
    have output : (smooth_program_const% "resolvent") 0 clock X=
      []++[(smooth_program_const% "resolventNext") clock X [] 0] := rfl
    rw [output]
    exact seriesLaw_append_one (seriesLaw_nil d)
      (sourceR_next_radial hc sc hx sx (seriesLaw_nil d) smoothSeries_nil 0)
  | succ n ih =>
    have output := (filtration_const% "R_succ") n clock X
    change (smooth_program_const% "resolvent") (n+1) clock X=
      (smooth_program_const% "resolvent") n clock X++[(smooth_program_const% "resolventNext")
        clock X ((smooth_program_const% "resolvent") n clock X) (n+1)] at output
    rw [output]
    apply seriesLaw_append_one ih
    rw [source_resolvent_length]
    exact sourceR_next_radial hc sc hx sx ih (sourceR_program_smooth n sc sx) (n+1)

theorem sourceAct_radial {k : ℕ} {d : ℤ} (depth : ℕ) {clock : ClockAt k}
    (hc : ClockLaw clock) (sc : SmoothClock clock) (token : Token) {X : List AngularPolynomial}
    (hx : SeriesLaw d X) (sx : SmoothSeries X) :
    SeriesLaw d ((smooth_program_const% "act") depth clock token X) := by
  cases token with
  | inverse => exact sourceR_radial depth hc sc hx sx
  | jordan a => exact sourceJ_radial depth hc sc a hx sx

theorem sourceWord_radial {k : ℕ} {d : ℤ} (depth : ℕ) {clock : ClockAt k}
    (hc : ClockLaw clock) (sc : SmoothClock clock) (tokens : List Token) {X : List AngularPolynomial}
    (hx : SeriesLaw d X) (sx : SmoothSeries X) :
    SeriesLaw d ((smooth_program_const% "word") depth clock tokens X) := by
  induction tokens with
  | nil => exact hx
  | cons token tokens ih => exact sourceAct_radial depth hc sc token ih (sourceWord_program_smooth depth sc tokens sx)

theorem sourceTable_radial {k : ℕ} {d : ℤ} (depth : ℕ) {clock : ClockAt k}
    (hc : ClockLaw clock) (sc : SmoothClock clock) (a b : Fin 4) (equation : Option (Fin 4))
    {X : List AngularPolynomial} (hx : SeriesLaw d X) (sx : SmoothSeries X) (n : Fin (depth+1)) :
    RadialLaw (d-n.val) ((smooth_program_const% "applyT") depth clock a b equation X n) := by
  have fold (terms : List TableTerm) (initial : AngularPolynomial)
      (hi : PolynomialLaw (d-n.val) initial) (si : SmoothPolynomial initial) :
      PolynomialLaw (d-n.val) (terms.foldl (fun out term => out+MvPolynomial.C (fun _ => term.coefficient)*
        (MvPolynomial.monomial term.exponent 1*
          ((smooth_program_const% "word") depth clock term.tokens X).getD n.val 0)) initial) := by
    induction terms generalizing initial with
    | nil => exact hi
    | cons term terms ih =>
      rw [List.foldl_cons]
      apply ih
      · apply polynomialLaw_add hi
        rw [←zero_add (d-(n.val : ℤ))]
        apply polynomialLaw_mul (polynomialLaw_C (radialLaw_constant term.coefficient))
        · rw [←zero_add (d-(n.val : ℤ))]
          exact polynomialLaw_mul (polynomialLaw_monomial _ (radialLaw_constant 1))
            (sourceWord_radial depth hc sc term.tokens hx sx n.val)
            (smoothPolynomial_monomial _ (smoothSymbol_const 1))
            (smoothSeries_getD (sourceWord_program_smooth depth sc term.tokens sx) n.val)
        · exact smoothPolynomial_constant (smoothSymbol_const term.coefficient)
        · exact smoothPolynomial_mul (smoothPolynomial_monomial _ (smoothSymbol_const 1))
            (smoothSeries_getD (sourceWord_program_smooth depth sc term.tokens sx) n.val)
      · exact smoothPolynomial_add si (smoothPolynomial_mul
          (smoothPolynomial_constant (smoothSymbol_const term.coefficient))
          (smoothPolynomial_mul (smoothPolynomial_monomial _ (smoothSymbol_const 1))
            (smoothSeries_getD (sourceWord_program_smooth depth sc term.tokens sx) n.val)))
  exact polynomialLaw_average (fold ((smooth_program_const% "table") a b equation) 0
    (polynomialLaw_zero _) smoothPolynomial_zero)

theorem engineSource_radial (n : ℕ) (slot : Fin 13) : RadialLaw (2-(n : ℤ)) (engineSource n slot) := by
  intro r hr x hx
  have native : (PreparationActualFactor.nativePhase (radial r x)).2=r • (PreparationActualFactor.nativePhase x).2 :=
    PreparationActualFactor.nativeCovectorLinear.map_smul r x.2
  have position : (PreparationActualFactor.nativePhase (radial r x)).1=(PreparationActualFactor.nativePhase x).1 := rfl
  cases n with
  | zero =>
    fin_cases slot <;> simp only [engineSource,originalEnginePrincipalLeaves]
    all_goals simp
    all_goals simp only [position,native,T_smul,S_smul,C_smul _ _ r hr]
    all_goals ring
  | succ n =>
    cases n with
    | zero =>
      change originalFirstLeaves (PreparationActualFactor.nativePhase (radial r x)).1
        (PreparationActualFactor.nativePhase (radial r x)).2 (Fin.castSucc slot)=
        r^(1 : ℤ)*originalFirstLeaves (PreparationActualFactor.nativePhase x).1
          (PreparationActualFactor.nativePhase x).2 (Fin.castSucc slot)
      rw [position,native,zpow_one]
      have linear := congrArg (fun v : Fin 14 → ℝ => v (Fin.castSucc slot))
        ((originalFirstLinear (PreparationActualFactor.nativePhase x).1).map_smul r (PreparationActualFactor.nativePhase x).2)
      change originalFirstLeaves (PreparationActualFactor.nativePhase x).1
        (r • (PreparationActualFactor.nativePhase x).2) (Fin.castSucc slot)=
        r*originalFirstLeaves (PreparationActualFactor.nativePhase x).1
          (PreparationActualFactor.nativePhase x).2 (Fin.castSucc slot) at linear
      exact linear
    | succ n =>
      cases n with
      | zero =>
        rw [engineSource_zero]
        change originalZeroLeaves (PreparationActualFactor.nativePhase (radial r x)).1 (Fin.castSucc slot)=
          r^(0 : ℤ)*originalZeroLeaves (PreparationActualFactor.nativePhase x).1 (Fin.castSucc slot)
        simp only [position,zpow_zero,one_mul]
      | succ n => simp [engineSource]

theorem engineTrace_radial (n : ℕ) : RadialLaw (2-(n : ℤ)) (engineTrace n) := by
  exact radialLaw_add (radialLaw_add (engineSource_radial n 4) (engineSource_radial n 5)) (engineSource_radial n 6)

private theorem threeSeries_radial (d : ℤ) (f : ℕ → PreparationVacuumCanonicalMoyal.Symbol)
    (hf : ∀ n : ℕ,RadialLaw (d-n) (f n)) :
    SeriesLaw d [MvPolynomial.C (f 0),MvPolynomial.C (f 1),MvPolynomial.C (f 2)] := by
  intro n
  cases n with
  | zero => exact polynomialLaw_C (hf 0)
  | succ n =>
    cases n with
    | zero => exact polynomialLaw_C (hf 1)
    | succ n =>
      cases n with
      | zero => exact polynomialLaw_C (hf 2)
      | succ n => exact polynomialLaw_zero _

theorem sourceSeries_radial (slot : Fin 13) : SeriesLaw 2 ((smooth_program_const% "sourceSeries") slot) :=
  threeSeries_radial 2 (fun n => engineSource n slot) (fun n => engineSource_radial n slot)

theorem traceSeries_radial : SeriesLaw 2 (smooth_program_const% "traceSeries") :=
  threeSeries_radial 2 engineTrace engineTrace_radial

theorem sourceAffine_radial {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : ClockLaw clock) (sc : SmoothClock clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) :
    RadialLaw (2-n.val) ((smooth_program_const% "affine") depth clock equation n) := by
  cases equation with
  | none =>
    apply radialLaw_sum
    intro a _
    exact sourceJ_radial depth hc sc a (sourceSeries_radial _) (sourceSeries_smooth _) n.val 0
  | some a =>
    change RadialLaw _ (-MvPolynomial.coeff 0 ((smooth_program_const% "sourceSeries") (Fin.castAdd 9 a) |>.getD n.val 0))
    intro r hr x hx
    simp only [Pi.neg_apply,sourceSeries_radial _ n.val 0 r hr x hx]
    ring

theorem forceOrEnergy_radial {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : ClockLaw clock) (sc : SmoothClock clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) : RadialLaw (2-n.val) (forceOrEnergy depth clock equation n) := by
  unfold forceOrEnergy
  apply radialLaw_sub
  · apply radialLaw_sub
    · apply radialLaw_sub
      · apply radialLaw_add (sourceAffine_radial depth hc sc equation n)
        change RadialLaw _ ((fun _ => (1/2 : ℝ))*(smooth_program_const% "applyT") depth clock 0 0 equation (smooth_program_const% "traceSeries") n)
        simpa only [zero_add] using radialLaw_mul (radialLaw_constant (1/2))
          (sourceTable_radial depth hc sc 0 0 equation traceSeries_radial traceSeries_smooth n)
      · apply radialLaw_sum
        intro i _
        change RadialLaw _ ((fun _ => (1/2 : ℝ))*(smooth_program_const% "applyT") depth clock (Fin.succ i) (Fin.succ i) equation
          ((smooth_program_const% "sourceSeries") ⟨4+i.val,by omega⟩) n)
        simpa only [zero_add] using radialLaw_mul (radialLaw_constant (1/2))
          (sourceTable_radial depth hc sc (Fin.succ i) (Fin.succ i) equation
            (sourceSeries_radial _) (sourceSeries_smooth _) n)
    · apply radialLaw_sum
      intro i _
      exact sourceTable_radial depth hc sc _ _ equation (sourceSeries_radial _) (sourceSeries_smooth _) n
  · apply radialLaw_sum
    intro i _
    exact sourceTable_radial depth hc sc _ _ equation (sourceSeries_radial _) (sourceSeries_smooth _) n


theorem sourceClock_radial : RadialLaw 0 sourceClock := by
  intro r hr x hx
  change actualC (radial r x)=r^(0 : ℤ)*actualC x
  rw [actualC_radial r hr]
  simp

theorem engineInverse_radial (a b : Fin 4) :
    RadialLaw (-2) (fun x => (principalForceJacobian x)⁻¹ a b) := by
  intro r hr x hx
  have shifted := radial_admitted r hr x hx
  have scaled : (principalForceJacobian (radial r x))⁻¹=(r^2)⁻¹ • (principalForceJacobian x)⁻¹ := by
    rw [sourceInverse_native _ shifted.1 shifted.2,sourceInverse_native _ hx.1 hx.2,
      sourceInverse_radial r hr x hx]
  have entry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M a b) scaled
  simpa only [Matrix.smul_apply,smul_eq_mul,zpow_neg,zpow_ofNat] using entry

theorem radialLaw_neg {d : ℤ} {f : PreparationVacuumCanonicalMoyal.Symbol} (hf : RadialLaw d f) :
    RadialLaw d (-f) := by
  intro r hr x hx
  simp only [Pi.neg_apply,hf r hr x hx,mul_neg]

private theorem clockLaw_of_entries {k : ℕ} (clock : ClockAt k)
    (entries : ∀ a (j : Fin (k+1)),RadialLaw (-(j.val : ℤ)) (clock a j)) : ClockLaw clock := by
  intro a i
  change RadialLaw (-(i : ℤ)) (if h : i<k+1 then clock a ⟨i,h⟩ else 0)
  split_ifs
  · exact entries _ _
  · exact radialLaw_zero _

theorem sourceEngine_entries_radial (k : ℕ) :
    ∀ a (j : Fin (k+1)),RadialLaw (-(j.val : ℤ)) (sourceEngine k a j) := by
  induction k with
  | zero =>
    intro a j
    have first : j=(0 : Fin 1) := by apply Fin.ext; have := j.isLt; omega
    rw [first,sourceEngine_initial]
    by_cases axis : a=0
    · simp only [if_pos axis,Fin.val_zero,Int.natCast_zero,neg_zero]
      exact sourceClock_radial
    · simp only [if_neg axis]
      exact radialLaw_zero _
  | succ k ih =>
    intro a j
    by_cases old : j.val<k+1
    · have same : j=Fin.castSucc ⟨j.val,old⟩ := Fin.ext rfl
      rw [same,sourceEngine_preserves]
      exact ih a ⟨j.val,old⟩
    · have same : j=Fin.last (k+1) := by apply Fin.ext; have := j.isLt; simp only [Fin.val_last]; omega
      rw [same]
      have generated : sourceEngine (k+1) a (Fin.last (k+1))=
          -(∑ b : Fin 4,(fun x => (principalForceJacobian x)⁻¹ a b)*
            forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1))) := by
        funext x
        exact sourceEngine_generated k a x
      rw [generated]
      apply radialLaw_neg
      apply radialLaw_sum
      intro b _
      have term := radialLaw_mul (engineInverse_radial a b)
        (forceOrEnergy_radial (k+1) (clockLaw_of_entries (sourceEngine k) ih)
          (sourceEngine_smooth k) (some b) (Fin.last (k+1)))
      convert term using 1
      simp only [Fin.val_last]
      omega

theorem sourceEngine_radial (k : ℕ) : ClockLaw (sourceEngine k) :=
  clockLaw_of_entries (sourceEngine k) (sourceEngine_entries_radial k)

theorem sourceEngineEnergy_radial (k : ℕ) : RadialLaw (2-(k : ℤ)) (sourceEngineEnergy k) := by
  exact forceOrEnergy_radial k (sourceEngine_radial k) (sourceEngine_smooth k) none (Fin.last k)

theorem sourceEngineForces_radial (k : ℕ) (a : Fin 4) : RadialLaw (2-(k : ℤ)) (sourceEngineForces k a) := by
  exact forceOrEnergy_radial k (sourceEngine_radial k) (sourceEngine_smooth k) (some a) (Fin.last k)

theorem sourceEngineEnergy_unitrestriction (k : ℕ)
    (z : CanonicalPreparationCutoff.FlatConfiguration) (p : CanonicalPreparationSquareCutoff.PhysicalMomentum)
    (admitted : (z,p)∈poleDomain) (nonzero : p≠0) :
    sourceEngineEnergy k (z,p)=‖p‖^(2-(k : ℤ))*
      sourceEngineEnergy k (z,WithLp.toLp 2 (CanonicalPreparationSquareCutoff.normalizedMomentum p)) := by
  have normNonzero : ‖p‖≠0 := norm_ne_zero_iff.mpr nonzero
  have normalized := radial_admitted (‖p‖⁻¹) (inv_ne_zero normNonzero) (z,p) admitted
  have read := sourceEngineEnergy_radial k ‖p‖ normNonzero (radial (‖p‖⁻¹) (z,p)) normalized
  have back : radial ‖p‖ (radial (‖p‖⁻¹) (z,p))=(z,p) := by
    simp [radial,smul_smul,mul_inv_cancel₀ normNonzero]
  rw [back] at read
  simpa only [radial,PreparationPhaseSource.normalized_native_vector] using read

end LowEnergy.PreparationVacuumEngineHomogeneity
