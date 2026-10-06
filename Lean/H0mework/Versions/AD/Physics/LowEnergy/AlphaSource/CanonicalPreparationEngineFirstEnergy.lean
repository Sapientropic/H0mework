import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineNewestEnergy

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEnginePaidDepth
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities PreparationVacuumEngineResponse
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

private abbrev originalR := engine_const% "resolvent"
private abbrev originalJ := engine_const% "js"
private abbrev originalAct := engine_const% "act"

private theorem scalarJordan_one (f g : Symbol) : scalarJordan 1 f g=0 :=
  scalarJordan_odd 0 f g

private theorem weighted_one (P Q : AngularPolynomial) : weighted 1 P Q=0 := by
  unfold weighted
  simp only [scalarJordan_one,map_zero,Finset.sum_const_zero]

private theorem R_one (X : List AngularPolynomial) :
    originalR 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) X=
      [MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 0 0,
        MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 1 0] := by
  change (engine_const% "resolvent") 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) X=_
  unfold_engine_helpers
  simp [List.range_succ,Finset.sum_range_succ,weighted_one,weighted_zero]

private theorem J_one (a : Fin 4) (X : List AngularPolynomial) :
    originalJ 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) a X=
      [MvPolynomial.C (if a=0 then sourceClock else 0)*X.getD 0 0,
        MvPolynomial.C (if a=0 then sourceClock else 0)*X.getD 1 0] := by
  change (engine_const% "js") 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) a X=_
  unfold_engine_helpers
  simp [Finset.sum_range_succ,weighted_one,weighted_zero]

private theorem act_inverse_one (X : List AngularPolynomial) :
    originalAct 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) Token.inverse X=
      [MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 0 0,
        MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 1 0] := by
  exact R_one X

private theorem act_jordan_one (a : Fin 4) (X : List AngularPolynomial) :
    originalAct 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) (Token.jordan a) X=
      [MvPolynomial.C (if a=0 then sourceClock else 0)*X.getD 0 0,
        MvPolynomial.C (if a=0 then sourceClock else 0)*X.getD 1 0] := by
  exact J_one a X

theorem sourceEngineEnergy_one : sourceEngineEnergy 1=0 := by
  rw [sourceEngineEnergy_newestExcluded 0]
  funext zp
  unfold forceOrEnergy
  unfold_engine_helpers
  simp
  simp [act_inverse_one,act_jordan_one,Finset.sum_range_succ,weighted_one,weighted_zero]
  unfold_engine_helpers
  try simp
  have traceZero : engineTrace 1=(0 : Symbol) := engineTrace_first
  rw [traceZero]
  simp [engineSource,originalLeaf_first,PreparationVacuumLowerLeaves.originalFirstLeaves,average]

end LowEnergy.PreparationVacuumEnginePaidDepth
