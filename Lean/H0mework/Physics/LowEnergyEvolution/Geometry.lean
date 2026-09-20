import H0mework.Physics.LowEnergyEvolution.Cartan

/-! Coframe jets of the same generated curve, including the dynamically
determined lapse derivative, generate the Levi--Civita part of the connection. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCoframeFirstJet
open StageNineGlobalIntegratedAction PointwiseLorentzianCoframeJet
open StageNineLorentzConnectionVariation
open StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineCartanAffineConnectionActualization Stage9C.Reduction
open StageNineFormNativeP286GaugeYangMillsReadout
open Stage9C.Dynamics.Homogeneous
noncomputable section

def clockRate (x : State) : ℝ := fderiv ℝ clock x (generator x)

theorem Solution.clock_derivative {initial : State} (flow : Solution initial)
    (time : ℝ) (inside : time ∈ Set.Ioo (-flow.radius) flow.radius) :
    HasDerivAt (fun t => clock (flow.curve t)) (clockRate (flow.curve time)) time :=
  ((clock_contDiffAt _ (flow.admissible time inside)).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt time (flow.evolves time inside)

def diagonalJet (n a nd d : ℝ) : PointwiseLorentzianCoframeJet where
  coframe := diagonalCoframe n a
  derivative := fun mu row col => if mu = 0 then diagonalCoframe nd d row col else 0

def boostConnection (velocity : ℝ) : PointwiseLorentzSpinConnection :=
  fun mu row col => if mu = 0 then 0
    else if (row = 0 ∧ col = mu) ∨ (row = mu ∧ col = 0) then velocity else 0

set_option maxHeartbeats 1600000 in
theorem diagonalJet_connection (n a nd d : ℝ) (hn : n ≠ 0) (ha : a ≠ 0) :
    (diagonalJet n a nd d).lorentzSpinConnection = boostConnection (d/n) := by
  funext mu row col
  unfold lorentzSpinConnection lorentzSpinConnectionMatrix coordinateConnectionMatrix
    affineConnectionMatrix leviCivitaConnection leviCivitaConnectionVector
    loweredLeviCivitaVector loweredLeviCivitaConnection metric coframeDerivativeMatrix
  simp only [diagonalJet, diagonalCoframe_inv n a hn ha, diagonalCoframe_metric_inverse n a hn ha]
  fin_cases mu <;> fin_cases row <;> fin_cases col <;>
    simp [metricDerivative, diagonalCoframe, boostConnection, minkowskiInternalSign,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hn, ha] <;> field_simp [hn, ha] <;> ring

theorem diagonalCoframe_apply (n a : ℝ) (row col : LorentzianIndex) :
    diagonalCoframe n a row col = if row = col then (if row = 0 then n else a) else 0 := by
  fin_cases row <;> fin_cases col <;> simp [diagonalCoframe]

theorem time_fderiv_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (profile : ℝ → V) (velocity : V) (point : BasePoint)
    (derivative : HasDerivAt profile velocity (point 0)) (mu : LorentzianIndex) :
    fderiv ℝ (fun p : BasePoint => profile (p 0)) point (coordinateDirection mu) =
      if mu = 0 then velocity else 0 := by
  have d := derivative.hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun p : BasePoint => profile (p 0)) _ point at d
  rw [d.fderiv]
  change (coordinateDirection mu) 0 • velocity = _
  by_cases temporal : mu = 0
  · simp [temporal, coordinateDirection]
  · simp [temporal, coordinateDirection, Ne.symm temporal]

theorem Solution.coframe_jet {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    holonomicCoframeFirstJetAt flow.configuration.coframe point =
      diagonalJet (clock (flow.pointState point)) (flow.pointState point 0)
        (clockRate (flow.pointState point)) (clock (flow.pointState point) * flow.pointState point 1) := by
  apply coframeJet_eq_of_fields_eq
  · exact flow.coframe point
  · have dn := time_fderiv_apply _ _ point (flow.clock_derivative (point 0) inside)
    have da := time_fderiv_apply _ _ point (flow.coordinate_derivative (point 0) inside 0)
    have frame : flow.configuration.coframe = fun p =>
        diagonalCoframe (clock (flow.pointState p)) (flow.pointState p 0) := funext flow.coframe
    funext mu row col
    change fderiv ℝ (fun p => flow.configuration.coframe p row col) point (coordinateDirection mu) =
      if mu = 0 then diagonalCoframe (clockRate (flow.pointState point))
        (clock (flow.pointState point) * flow.pointState point 1) row col else 0
    rw [frame]
    simp only [diagonalCoframe_apply]
    by_cases same : row = col
    · simp only [if_pos same]
      by_cases zeroRow : row = 0
      · simp only [if_pos zeroRow]
        exact dn mu
      · simp only [if_neg zeroRow]
        exact da mu
    · simp only [if_neg same]
      simp

set_option maxHeartbeats 1000000 in
theorem Solution.connection_generated {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    flow.configuration.gravityConnection point =
      boostConnection (flow.pointState point 1) +
        homogeneousConnection (contorsion (flow.pointState point)) := by
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  have lapseNonzero := ne_of_gt (clock_positive _ admissible)
  change (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource
      (formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource flow.raw)).gravityConnection point = _
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated]
  change diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource flow.configuration point = _
  unfold diracDualFormNativeActionCartanConnectionAt cartanAffineSpinConnection
  rw [flow.coframe_jet point inside, flow.contorsion_generated point inside,
    diagonalJet_connection _ _ _ _ lapseNonzero (ne_of_gt admissible.1)]
  simp only [mul_div_cancel_left₀ _ lapseNonzero, homogeneousConnection]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
