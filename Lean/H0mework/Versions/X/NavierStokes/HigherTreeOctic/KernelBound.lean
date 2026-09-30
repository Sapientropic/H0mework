import H0mework.Versions.X.NavierStokes.HigherTreeOctic.GramDualWork
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatEvaluation
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatCoefficient
import H0mework.Versions.X.NavierStokes.HigherTreeSeptic.Alignment

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedTreeHeatTopology NativeUnheatedTreeHeatEvaluation
open NativeUnheatedSexticLatticePower
open NativeUnheatedTreeTime
noncomputable section

theorem mass_at_le_one (wave : IntegerWavevector) : 1 ≤ mass wave := by
  unfold mass
  linarith [integerWaveNormSq_nonneg wave]

theorem symbol_upper (nu : Viscosity) (first last : IntegerWavevector) :
    symbol nu first last ≤ 2 * factor nu := by
  have root : mass (first+last)^(1/2 : ℝ) ≤ mass (first+last) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_self_iff.mpr (Or.inr (mass_at_le_one _))
  have sumPositive : 0 < mass first+mass last :=
    add_pos (mass_positive first) (mass_positive last)
  have triangle := NativeUnheatedTreeHeatKernel.mass_add first last
  have paid := mul_le_mul_of_nonneg_left triangle (factor_positive nu).le
  unfold symbol
  apply (div_le_iff₀ sumPositive).mpr
  nlinarith [mul_le_mul_of_nonneg_left root (factor_positive nu).le]

theorem coefficient_upper (nu : Viscosity) (tree : Tree) (wave : IntegerWavevector)
    (index : NativeUnheatedTreeHeatEvaluation.Index tree) :
    NativeUnheatedTreeHeatCoefficient.coefficient nu tree wave index ≤
      (2 * factor nu)^(NativeUnheatedTreeHeatTopology.nodes tree) := by
  induction tree generalizing wave with
  | leaf => simp [NativeUnheatedTreeHeatCoefficient.coefficient, NativeUnheatedTreeHeatTopology.nodes]
  | fork left right leftBound rightBound =>
      change symbol nu index.1 (wave-index.1) *
        NativeUnheatedTreeHeatCoefficient.coefficient nu left index.1 index.2.1 *
        NativeUnheatedTreeHeatCoefficient.coefficient nu right (wave-index.1) index.2.2 ≤
        (2*factor nu)^(NativeUnheatedTreeHeatTopology.nodes left+NativeUnheatedTreeHeatTopology.nodes right+1)
      calc
        _ ≤ (2*factor nu) * (2*factor nu)^(NativeUnheatedTreeHeatTopology.nodes left) *
            (2*factor nu)^(NativeUnheatedTreeHeatTopology.nodes right) := by
              gcongr
              all_goals first
                | exact symbol_upper nu index.1 (wave-index.1)
                | exact leftBound index.1 index.2.1
                | exact rightBound (wave-index.1) index.2.2
                | exact NativeUnheatedTreeHeatCoefficient.coefficient_nonnegative nu left index.1 index.2.1
                | exact NativeUnheatedTreeHeatCoefficient.coefficient_nonnegative nu right (wave-index.1) index.2.2
                | positivity [factor_positive nu]
        _ = _ := by simp only [pow_add, pow_one]; ring

theorem rootCoefficient_upper (nu : Viscosity) (tree : Tree) (wave : IntegerWavevector)
    (index : NativeUnheatedTreeHeatEvaluation.Index tree) :
    NativeUnheatedTreeHeatCoefficient.rootCoefficient nu tree wave index ≤
      (2*Real.pi)⁻¹ * (2*factor nu)^(NativeUnheatedTreeHeatTopology.nodes tree) := by
  have rootLe : mass wave^(-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (mass_at_le_one wave) (by norm_num)
  have coefficient0 := NativeUnheatedTreeHeatCoefficient.coefficient_nonnegative nu tree wave index
  have first := mul_le_mul_of_nonneg_right rootLe coefficient0
  have second := mul_le_mul_of_nonneg_left first (by positivity : 0 ≤ (2*Real.pi)⁻¹)
  unfold NativeUnheatedTreeHeatCoefficient.rootCoefficient
  calc
    _ ≤ (2*Real.pi)⁻¹ * NativeUnheatedTreeHeatCoefficient.coefficient nu tree wave index := by
      nlinarith [second]
    _ ≤ _ := mul_le_mul_of_nonneg_left (coefficient_upper nu tree wave index) (by positivity)

theorem selected_decay_le_sumRate {nu : Viscosity} {n : ℕ}
    (slots : Fin (n+1) → Slot) (selected : Fin (n+1)) :
    NativeUnheatedStressPairEvolution.decay nu (slots selected).1 0 ≤ sumRate nu slots := by
  have lower := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (n+1))))
    (fun other _ => NativeUnheatedTriadKernel.multiplier_nonnegative (slots other).1)
    (Finset.mem_univ selected)
  unfold NativeUnheatedStressPairEvolution.decay sumRate
  have zero : integerWaveViscousMultiplier (0 : IntegerWavevector) = 0 := by
    simp [integerWaveViscousMultiplier, integerWaveNormSq]
  rw [zero, add_zero]
  exact mul_le_mul_of_nonneg_left lower nu.coeff_pos.le

theorem normalized_pressure_upper {nu : Viscosity} {n : ℕ}
    (slots : Fin (n+1) → Slot) (selected : Fin (n+1))
    (p q response : Coordinate) :
    ‖(sumRate nu slots)⁻¹ •
      NativeUnheatedTriadChannels.pressure (slots selected).1 p q response‖ ≤
      NativeUnheatedTreeLocalHeat.cap nu * (2*Real.pi) := by
  have paid := NativeUnheatedTreeLocalHeat.pressure_rate_bound nu (sumRate nu slots)
    (slots selected).1 0 p q response (selected_decay_le_sumRate slots selected)
  simp only [add_zero] at paid
  have root : mass (slots selected).1^(1/2 : ℝ) ≤ mass (slots selected).1 := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_self_iff.mpr (Or.inr (mass_at_le_one _))
  have positive : 0 < mass (slots selected).1 + mass (0 : IntegerWavevector) :=
    add_pos (mass_positive _) (mass_positive _)
  apply paid.trans
  apply (div_le_iff₀ positive).mpr
  have cap0 : 0 ≤ NativeUnheatedTreeLocalHeat.cap nu * (2*Real.pi) := by
    positivity [NativeUnheatedTreeLocalHeat.cap_positive nu]
  nlinarith [mul_le_mul_of_nonneg_left root cap0, mass_positive (0 : IntegerWavevector)]

variable {nu : Viscosity}
variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (i j response outside l m p q r s u v : Coordinate)

def oldCap : ℝ :=
  (2*Real.pi)⁻¹ * (2*factor nu)^
    (NativeUnheatedTreeHeatTopology.nodes
      (NativeUnheatedSepticAlignment.septic nu slot leaf position newest i j response outside l m p q r s u v).tree)

theorem oldCap_eq :
    oldCap (nu := nu) slot leaf position newest i j response outside l m p q r s u v =
      (2*Real.pi)⁻¹ * (2*factor nu)^6 := by
  let paid := NativeUnheatedSepticAlignment.septic nu slot leaf position newest i j response outside l m p q r s u v
  have count : NativeUnheatedTreeHeatTopology.leaves paid.tree = 7 := by
    simpa only [Nat.reduceAdd] using paid.count
  have nodesEq : NativeUnheatedTreeHeatTopology.nodes paid.tree = 6 := by
    have relation := NativeUnheatedTreeHeatTopology.leaves_nodes paid.tree
    omega
  change (2*Real.pi)⁻¹ * (2*factor nu)^(NativeUnheatedTreeHeatTopology.nodes paid.tree) = _
  rw [nodesEq]

theorem old_base_upper (wave : IntegerWavevector) (index : NativeUnheatedSepticSevenRows.Index) :
    ‖NativeUnheatedOcticEightRows.base slot leaf position newest wave i j response outside l m p q r s u v nu index‖ ≤
      oldCap (nu := nu) slot leaf position newest i j response outside l m p q r s u v := by
  let paid := NativeUnheatedSepticAlignment.septic nu slot leaf position newest i j response outside l m p q r s u v
  exact (paid.coefficient_bound wave index).trans
    (rootCoefficient_upper nu paid.tree wave (paid.indices wave index))

theorem oldCap_nonnegative :
    0 ≤ oldCap (nu := nu) slot leaf position newest i j response outside l m p q r s u v := by
  unfold oldCap
  positivity [factor_positive nu]

theorem constant_upper (selected : Fin 7) (a b : Coordinate)
    (test : Test) (entry : Address) :
    ‖constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖ ≤
      ‖test entry.1‖ * oldCap (nu := nu) slot leaf position newest i j response outside l m p q r s u v *
        (NativeUnheatedTreeLocalHeat.cap nu * (2*Real.pi)) := by
  have identity : constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry =
      star (test entry.1) *
        (NativeUnheatedOcticEightRows.base slot leaf position newest entry.1 i j response outside l m p q r s u v nu entry.2.1 *
          ((sumRate nu (nodes slot leaf position newest i j outside l m p q r s u v entry))⁻¹ •
            NativeUnheatedTriadChannels.pressure
              ((nodes slot leaf position newest i j outside l m p q r s u v entry) selected).1 a b
              ((nodes slot leaf position newest i j outside l m p q r s u v entry) selected).2)) := by
    simp only [constant, NativeUnheatedTreeLeaf.kernel, NativeUnheatedTreeNormalForm.normalizer,
      NativeUnheatedOcticEightRows.base, NativeUnheatedOcticEightRows.parent, nodes,
      Complex.real_smul]
    ring
  rw [identity, norm_mul, norm_mul, norm_star]
  have first := old_base_upper (nu := nu) slot leaf position newest i j response outside l m p q r s u v entry.1 entry.2.1
  have second := normalized_pressure_upper (nu := nu)
    (nodes slot leaf position newest i j outside l m p q r s u v entry) selected a b
    ((nodes slot leaf position newest i j outside l m p q r s u v entry) selected).2
  have compared := mul_le_mul first second (norm_nonneg _)
    (oldCap_nonnegative (nu := nu) slot leaf position newest i j response outside l m p q r s u v)
  exact (mul_le_mul_of_nonneg_left compared (norm_nonneg _)).trans_eq (by ring)

theorem basis_upper (selected : Fin 7) (a b : Coordinate)
    (test : Test) (entry : Address) :
    ‖basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖ ≤
      ‖test entry.1‖ * oldCap (nu := nu) slot leaf position newest i j response outside l m p q r s u v *
        (NativeUnheatedTreeLocalHeat.cap nu * (2*Real.pi)) := by
  rw [basis, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_smul]
  have pulse := NativeUnheatedOcticGramDualPulse.pulse_norm (nu := nu)
    (rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected entry)
    (rest_nonnegative slot leaf position newest i j outside l m p q r s u v selected entry)
    (other slot leaf position newest i j outside l m p q r s u v selected entry)
  calc
    _ ≤ ‖constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖ * 1 :=
      mul_le_mul_of_nonneg_left pulse (norm_nonneg _)
    _ = ‖constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖ := by ring
    _ ≤ _ := constant_upper (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
