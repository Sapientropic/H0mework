import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineLeading

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineIdentities
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationActualFactor
open scoped BigOperators

open Lean Elab Tactic in
elab "unfold_force_table" : tactic => do
  let engineNS := Name.str (Name.str (Name.num `_private.H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  let ids := #["differentiateTerm","derivativeExponent"].map (fun suffix => mkIdent (Name.str engineNS suffix))
  evalTactic (← `(tactic| simp only [$[$ids:ident],*]))

private abbrev originalR := engine_const% "resolvent"
private abbrev originalJ := engine_const% "js"
private abbrev originalClockAt := engine_const% "clockAt"
private abbrev originalAct := engine_const% "act"

private theorem R_zero {k : ℕ} (clock : ClockAt k) (X : List AngularPolynomial) :
    originalR 0 clock X=[MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 0 0] := by
  change (engine_const% "resolvent") 0 clock X=_
  unfold_engine_helpers
  simp

private theorem J_zero {k : ℕ} (clock : ClockAt k) (a : Fin 4) (X : List AngularPolynomial) :
    originalJ 0 clock a X=[MvPolynomial.C (originalClockAt clock a 0)*X.getD 0 0] := by
  change (engine_const% "js") 0 clock a X=_
  unfold_engine_helpers
  simp
  rw [weighted_zero]

private theorem act_inverse_zero {k : ℕ} (clock : ClockAt k) (X : List AngularPolynomial) :
    originalAct 0 clock Token.inverse X=[MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 0 0] := by
  change originalR 0 clock X=_
  exact R_zero clock X

private theorem act_jordan_zero {k : ℕ} (clock : ClockAt k) (a : Fin 4) (X : List AngularPolynomial) :
    originalAct 0 clock (Token.jordan a) X=[MvPolynomial.C (originalClockAt clock a 0)*X.getD 0 0] := by
  change originalJ 0 clock a X=_
  exact J_zero clock a X

private theorem monomial_add (u : AngularExponent) (f g : Symbol) :
    MvPolynomial.monomial u (f+g)=MvPolynomial.monomial u f+MvPolynomial.monomial u g := map_add _ _ _

private theorem moment_single (i : Fin 3) : angularMoment (Finsupp.single i 1)=0 :=
  angularMoment_odd _ i (by simp)

theorem sourceEngineForces_zero (a : Fin 4) : sourceEngineForces 0 a=0 := by
  funext zp
  fin_cases a <;> unfold sourceEngineForces forceOrEnergy
  all_goals unfold_engine_helpers
  all_goals simp
  all_goals unfold_force_table
  all_goals simp
  all_goals simp [act_inverse_zero,act_jordan_zero]
  all_goals simp [originalClockAt]
  all_goals unfold_engine_helpers
  all_goals simp
  all_goals simp only [MvPolynomial.C_apply,MvPolynomial.monomial_mul,zero_add,add_zero,←monomial_add]
  all_goals simp only [average_monomial,angularMoment_zero,moment_single]
  all_goals have az : average 0 zp=0 := by simp [average]
  all_goals simp only [Pi.mul_apply,Pi.add_apply,az,zero_mul,mul_zero,zero_add,add_zero,sub_zero]
  all_goals try rw [engineTrace_principal]
  all_goals dsimp only [engineSource,sourceClock,sourceTrace,PreparationVacuumEnergyTail.originalEnginePrincipalLeaves]
  all_goals norm_num
  all_goals by_cases zero : C (nativePhase zp).1 (nativePhase zp).2=0
  all_goals first | (simp [zero]; done) | (field_simp [zero]; ring)

end LowEnergy.PreparationVacuumEngineIdentities
