import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPoleRead

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticPole
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil PreparationVacuumFieldPerturbation
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedStaticResponse ActualEMAction
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
attribute [local irreducible] staticInputNormalizer staticQuantumCorrection staticResponsePencil
  dressedStaticPolarization dressedStaticPoleOrder dressedStaticPoleRegular dressedStaticPoleLeading emOriginalJacobi

private theorem power_normalization (c q : ℂ) (m : ℕ) (positive : 0 < m) :
    c^(2*m-1)*(c*q)=c^(2*m)*q := by
  have exponent : 2*m-1+1=2*m := by omega
  rw [←mul_assoc,←pow_succ,exponent]

/-- The original one-time input normalization reduces the source pole bound by one. -/
theorem dressed_quantum_correction_pole_regularized (event : DressedEvent) (lambda : ℂ)
    (positive : 0<lambda.re) (i j : Fin 289) :
    lambda^(2*dressedStaticPoleOrder event-1)*staticQuantumCorrection event 0 lambda i j=
      dressedStaticPoleRegular event lambda i j := by
  have correction : staticQuantumCorrection event 0 lambda i j=lambda*dressedStaticPolarization event 0 lambda i j := by
    unfold staticQuantumCorrection
    simp only [Matrix.smul_apply,smul_eq_mul,static_input_normalizer_generated lambda positive]
  have normalize:=power_normalization lambda (dressedStaticPolarization event 0 lambda i j)
    (dressedStaticPoleOrder event) (dressed_static_pole_order_positive event)
  exact (congrArg (fun z : ℂ=>lambda^(2*dressedStaticPoleOrder event-1)*z) correction).trans
    (normalize.trans (dressed_static_polarization_regularized event lambda positive i j))

theorem dressed_quantum_correction_pole_limit (event : DressedEvent) (i j : Fin 289) :
    Tendsto (fun sigma : ℝ=>(sigma:ℂ)^(2*dressedStaticPoleOrder event-1)*
      staticQuantumCorrection event 0 (sigma:ℂ) i j) (nhdsWithin 0 (Ioi (0:ℝ)))
      (𝓝 (dressedStaticPoleLeading event i j)) := by
  have embedding : Tendsto (fun sigma : ℝ=>(sigma:ℂ)) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have regular:=((continuous_apply j).continuousAt.tendsto.comp
    ((continuous_apply i).continuousAt.tendsto.comp
      (dressed_static_pole_regular_continuous event).tendsto)).comp embedding
  have origin : dressedStaticPoleRegular event 0 i j=dressedStaticPoleLeading event i j :=
    congrFun (congrFun (dressed_static_pole_regular_origin event) i) j
  rw [origin] at regular
  apply Tendsto.congr' _ regular
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  exact (dressed_quantum_correction_pole_regularized event (sigma:ℂ) positive i j).symm

private theorem response_pole_algebra (c K Q : ℂ) (n : ℕ) :
    c^n*(K-Q)=c^n*K-c^n*Q := mul_sub _ _ _

/-- The complete static action-minus-quantum response consumes the same generated observed coefficient. -/
theorem dressed_static_response_pole_limit (event : DressedEvent) (i j : Fin 289) :
    Tendsto (fun sigma : ℝ=>(sigma:ℂ)^(2*dressedStaticPoleOrder event-1)*
      staticResponsePencil event 0 (fun _ : Fin 4=>(0:ℂ)) (sigma:ℂ) i j) (nhdsWithin 0 (Ioi (0:ℝ)))
      (𝓝 (-dressedStaticPoleLeading event i j)) := by
  have orderPositive : 0<2*dressedStaticPoleOrder event-1 := by
    have source:=dressed_static_pole_order_positive event
    omega
  have embedding : Tendsto (fun sigma : ℝ=>(sigma:ℂ)) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have power : Tendsto (fun sigma : ℝ=>(sigma:ℂ)^(2*dressedStaticPoleOrder event-1))
      (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℂ)) := by
    simpa only [zero_pow (ne_of_gt orderPositive)] using! embedding.pow (2*dressedStaticPoleOrder event-1)
  have classical : Tendsto (fun sigma : ℝ=>(sigma:ℂ)^(2*dressedStaticPoleOrder event-1)*
      emOriginalJacobi (fun _ : Fin 4=>(0:ℂ)) i j) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℂ)) := by
    simpa only [zero_mul] using! power.mul_const (emOriginalJacobi (fun _ : Fin 4=>(0:ℂ)) i j)
  have quantum:=dressed_quantum_correction_pole_limit event i j
  have combined:=classical.sub quantum
  have same : (fun sigma : ℝ=>(sigma:ℂ)^(2*dressedStaticPoleOrder event-1)*
      staticResponsePencil event 0 (fun _ : Fin 4=>(0:ℂ)) (sigma:ℂ) i j)=
      (fun sigma : ℝ=>(sigma:ℂ)^(2*dressedStaticPoleOrder event-1)*emOriginalJacobi (fun _ : Fin 4=>(0:ℂ)) i j-
        (sigma:ℂ)^(2*dressedStaticPoleOrder event-1)*staticQuantumCorrection event 0 (sigma:ℂ) i j) := by
    funext sigma
    unfold staticResponsePencil
    exact response_pole_algebra (sigma:ℂ) (emOriginalJacobi (fun _ : Fin 4=>(0:ℂ)) i j)
      (staticQuantumCorrection event 0 (sigma:ℂ) i j) (2*dressedStaticPoleOrder event-1)
  rw [same]
  simpa only [zero_sub] using! combined

end LowEnergy.GaussComposite.ActualDressedStaticPole
