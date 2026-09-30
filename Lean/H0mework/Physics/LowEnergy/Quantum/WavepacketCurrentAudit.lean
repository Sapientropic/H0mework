import H0mework.Physics.LowEnergy.Quantum.WavepacketCurrent
import H0mework.Physics.LowEnergy.Quantum.WavepacketAudit
import H0mework.Physics.LowEnergy.Quantum.ScalarCCR

/-! Independent real-momentum current and polynomial-CCR consumers.
The polynomial unit below is an algebraic test vector, not a chosen vacuum. -/
set_option autoImplicit false
namespace SourceWavepacketCurrentAudit
open SourceWavepacketInteraction SourceWavepacketCurrent SourceWavepacketAudit
open scoped BigOperators
noncomputable section

abbrev Poly := SourceScalarCCR.BosonSpace (Fin 1)
abbrev PolynomialWave := Wave ℝ (Fin 2) Poly 2

def Q : Module.End ℂ Poly := SourceScalarCCR.position 0
def P : Module.End ℂ Poly := SourceScalarCCR.momentum 0

theorem actual_same_line_with_arbitrary_bosons
    (U V : Module.End ℂ Poly) (t u : ℝ) (line : Fin 2) :
    lineAction (fun p : ℝ => p-1) (scalarKernel (sourceMatrix t) U) line *
      lineAction (fun p : ℝ => p+2) (scalarKernel (sourceMatrix u) V) line = 0 := by
  exact same_line_zero target _ _ _ _
    (scalarKernel_support target (sourceMatrix t) U (source_matrix_grade t))
    (scalarKernel_support target (sourceMatrix u) V (source_matrix_grade u)) line

theorem actual_distinct_matter_lines_commute (t u : ℝ) :
    Commute (lineAction (fun p : ℝ => p-1)
      (scalarKernel (sourceMatrix t) (1 : Module.End ℂ Poly)) (0 : Fin 2))
      (lineAction (fun p : ℝ => p+2)
        (scalarKernel (sourceMatrix u) (1 : Module.End ℂ Poly)) (1 : Fin 2)) := by
  exact distinct_lines_commute _ _ _ _ _ _ (by decide)

theorem actual_currents_commute (t u : ℝ) :
    Commute (current (B := Poly) (N := 2) (fun p : ℝ => p-1) (sourceMatrix t))
      (current (fun p : ℝ => p+2) (sourceMatrix u)) := by
  exact currents_commute target _ _ _ _ (source_matrix_grade t) (source_matrix_grade u)

theorem actual_two_currents_survive :
    (current (N := 2) (fun p : ℝ => p-1) (sourceMatrix 0)
      (current (fun p : ℝ => p-1) (sourceMatrix 0) sameInternalWave))
        ![(2,1),(0,1)] = 12 := by
  norm_num [current, interaction, lineAction, scalarKernel, sourceMatrix,
    sameInternalWave, Fin.sum_univ_two, Function.update_apply]

theorem actual_polynomial_CCR : Q * P - P * Q = Complex.I • 1 := by
  simpa [Q, P] using SourceScalarCCR.position_momentum (0 : Fin 1) 0

theorem actual_wave_CCR :
    onBoson (M := ℝ) (I := Fin 2) (N := 2) Q * onBoson P -
      onBoson P * onBoson Q = Complex.I • 1 := by
  exact onBoson_CCR Q P Complex.I actual_polynomial_CCR

theorem actual_boson_current_factor (t : ℝ) :
    onBoson Q * current (N := 2) (fun p : ℝ => p-1) (sourceMatrix t) =
      interaction (fun p : ℝ => p-1) (scalarKernel (sourceMatrix t) Q) := by
  exact boson_current_factor Q _ _

theorem actual_boson_commutes_current (t : ℝ) :
    Commute (onBoson (M := ℝ) (I := Fin 2) (N := 2) P)
      (current (fun p : ℝ => p-1) (sourceMatrix t)) := by
  exact boson_commutes_current P _ _

def polynomialWave : PolynomialWave := fun x => sameInternalWave x • (1 : Poly)
def qLine : Module.End ℂ PolynomialWave :=
  lineAction (fun p : ℝ => p-1) (scalarKernel (sourceMatrix 0) Q) 0
def pLine : Module.End ℂ PolynomialWave :=
  lineAction (fun p : ℝ => p-1) (scalarKernel (sourceMatrix 0) P) 1

theorem noncommuting_boson_line_value :
    ((qLine * pLine - pLine * qLine) polynomialWave) ![(2,1),(0,1)] =
      (6*Complex.I) • (1 : Poly) := by
  norm_num [qLine, pLine, Module.End.mul_apply, LinearMap.sub_apply,
    lineAction, scalarKernel, polynomialWave, sameInternalWave, sourceMatrix,
    Fin.sum_univ_two, Function.update_apply, Q, P,
    SourceScalarCCR.position, SourceScalarCCR.momentum, smul_smul]
  ring

theorem general_boson_lines_do_not_commute : ¬ Commute qLine pLine := by
  intro commute
  have zero_operator : qLine * pLine - pLine * qLine = 0 := sub_eq_zero.mpr commute.eq
  have value := congrArg (fun A : Module.End ℂ PolynomialWave =>
    (A polynomialWave) ![(2,1),(0,1)]) zero_operator
  rw [noncommuting_boson_line_value] at value
  have nonzero : (6*Complex.I) • (1 : Poly) ≠ 0 :=
    smul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) one_ne_zero
  change (6*Complex.I) • (1 : Poly) = 0 at value
  exact nonzero value

#print axioms SourceWavepacketCurrent.same_line_zero
#print axioms SourceWavepacketCurrent.distinct_lines_commute
#print axioms SourceWavepacketCurrent.currents_commute
#print axioms SourceWavepacketCurrent.boson_commutes_current
#print axioms SourceWavepacketCurrent.boson_current_factor
#print axioms SourceWavepacketCurrent.onBoson_CCR
#print axioms actual_same_line_with_arbitrary_bosons
#print axioms actual_distinct_matter_lines_commute
#print axioms actual_currents_commute
#print axioms actual_two_currents_survive
#print axioms actual_polynomial_CCR
#print axioms actual_wave_CCR
#print axioms actual_boson_current_factor
#print axioms actual_boson_commutes_current
#print axioms noncommuting_boson_line_value
#print axioms general_boson_lines_do_not_commute

end
end SourceWavepacketCurrentAudit
