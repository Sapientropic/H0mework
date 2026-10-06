import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram
import Lean.Elab.Tactic

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineIdentities
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationActualFactor
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators

open Lean Elab Tactic in
elab "unfold_engine_helpers" : tactic => do
  let engineNS := Name.str (Name.str (Name.num `_private.H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  let helpers := #["affine","applyT","table","energyTable","word","act","js","resolvent",
    "resolventNext","scale","clockPolynomial","clockAt","ellPolynomial","sourceSeries",
    "traceSeries","crossFirst","crossSecond","crossSlot"]
  let ids := helpers.map (fun suffix => mkIdent (Name.str engineNS suffix))
  evalTactic (← `(tactic| simp only [$[$ids:ident],*,sourceEngine,weighted_zero,
    average_constant,←MvPolynomial.C_mul,Fin.sum_univ_succ]))

open Lean Elab Term in
elab "engine_const%" name:str : term => do
  unless #["resolvent","js","clockAt","act"].contains name.getString do
    throwError "Not an Engine helper in this proof"
  let engineNS := Name.str (Name.str (Name.num `_private.H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  Lean.Meta.mkConstWithFreshMVarLevels (Name.str engineNS name.getString)

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

theorem sourceEngineEnergy_zero : sourceEngineEnergy 0=engineLeadingEnergy := by
  funext zp
  unfold sourceEngineEnergy forceOrEnergy
  unfold_engine_helpers
  simp
  simp [act_inverse_zero,act_jordan_zero,weighted_zero]
  simp [originalClockAt]
  unfold_engine_helpers
  simp
  simp only [←MvPolynomial.C_mul,←MvPolynomial.C_add]
  simp only [average_constant]
  unfold engineLeadingEnergy
  have az : average (0 : AngularPolynomial) zp=0 := by simp [average]
  simp only [Pi.mul_apply,Pi.add_apply,az,mul_zero,add_zero]
  by_cases zero : sourceClock zp=0
  · simp [zero]
  · field_simp
    ring

theorem sourceEngineLeading_b1_square (zp : PreparationVacuumCanonicalMoyal.Phase) :
    sourceTheta zp.1 (normalizedMomentum zp.2)*
      sourceChi (2*‖zp.2‖)*sourceEngineEnergy 0 zp=
        b1 zp^2 := by
  rw [sourceEngineEnergy_zero]
  exact engineLeadingLocalizedEnergy_b1_square zp

end LowEnergy.PreparationVacuumEngineIdentities
