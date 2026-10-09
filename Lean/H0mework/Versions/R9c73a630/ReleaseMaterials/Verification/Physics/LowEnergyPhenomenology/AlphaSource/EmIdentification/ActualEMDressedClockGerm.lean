import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSchur
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeClockFlux

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedClockGerm
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumCausalPoleResponse
open PreparationVacuumCurrentSignalOperator ActualDressedFullCoulomb ActualDressedNoether
open ActualDressedSignal ActualDressedPencil ActualDressedClockMoment ActualDressedPhysicalClock
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open Filter Set
open scoped BigOperators Matrix Topology
attribute [local irreducible] originalChange originalInverse originalReadback originalJacobi
  dressedWindowPolarization anchorEvent sourceGreen

private abbrev matrixNorm (m n : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin n) ℂ) := by
  unfold Matrix
  infer_instance

attribute [local instance] matrixNorm

private abbrev matrixSpace (m n : ℕ) : NormedSpace ℂ (Matrix (Fin m) (Fin n) ℂ) := by
  unfold Matrix
  infer_instance

attribute [local instance] matrixSpace

private theorem entries_analytic {m n : ℕ} (A : ℂ→Matrix (Fin m) (Fin n) ℂ) (z : ℂ)
    (entries : ∀i j,AnalyticAt ℂ (fun w=>A w i j) z) : AnalyticAt ℂ A z :=
  AnalyticAt.pi (fun i=>AnalyticAt.pi (fun j=>entries i j))

private theorem determinant_analytic {n : ℕ} (A : ℂ→Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (entries : ∀i j,AnalyticAt ℂ (fun w=>A w i j) z) : AnalyticAt ℂ (fun w=>(A w).det) z := by
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro sigma _
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_fun_prod _ (fun i _=>entries _ i)

private theorem inverse_entry_analytic {n : ℕ} (A : ℂ→Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (entries : ∀i j,AnalyticAt ℂ (fun w=>A w i j) z) (regular : IsUnit (A z).det)
    (i j : Fin n) : AnalyticAt ℂ (fun w=>(A w)⁻¹ i j) z := by
  have cofactor : AnalyticAt ℂ (fun w=>(A w).adjugate i j) z := by
    simp only [Matrix.adjugate_apply]
    apply determinant_analytic
    intro k l
    by_cases same : k=j
    · subst k
      simpa only [Matrix.updateRow_self] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ=>((Pi.single i (1:ℂ) : Fin n→ℂ) l)) z)
    · simpa only [Matrix.updateRow_ne same] using entries k l
  simp only [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv']
  exact ((determinant_analytic A z entries).inv (isUnit_iff_ne_zero.mp regular)).mul cofactor

private theorem product_entry_analytic {m n k : ℕ} (A : ℂ→Matrix (Fin m) (Fin n) ℂ)
    (B : ℂ→Matrix (Fin n) (Fin k) ℂ) (z : ℂ)
    (ha : ∀i j,AnalyticAt ℂ (fun w=>A w i j) z) (hb : ∀i j,AnalyticAt ℂ (fun w=>B w i j) z)
    (i : Fin m) (j : Fin k) : AnalyticAt ℂ (fun w=>(A w*B w) i j) z := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ (fun l _=>(ha i l).mul (hb l j))

private theorem source_matrix_analytic (terms : List SourceTerm) (p : ℂ→Fin 4→ℂ) (z : ℂ)
    (coordinates : ∀i,AnalyticAt ℂ (fun w=>p w i) z) (i j : Fin 289) :
    AnalyticAt ℂ (fun w=>sourceMatrix terms (p w) i j) z := by
  induction terms with
  | nil=>exact analyticAt_const
  | cons a rest ih=>
    have term : AnalyticAt ℂ (fun w=>a.matrix (p w) i j) z := by
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value
        exact analyticAt_const.mul (((((coordinates 0).pow _).mul ((coordinates 1).pow _)).mul
          ((coordinates 2).pow _)).mul ((coordinates 3).pow _))
      · exact analyticAt_const
    exact term.add ih

private theorem clock_coordinate (z : ℂ) (i : Fin 4) : AnalyticAt ℂ (fun w=>sourceInputClock w i) z := by
  by_cases zero : i=0
  · subst i
    have same : (fun w : ℂ=>sourceInputClock w 0)=(id : ℂ→ℂ) := by funext w; simp only [sourceInputClock,Pi.single_eq_same,id_eq]
    rw [same]
    exact analyticAt_id
  · simpa only [sourceInputClock,Pi.single_eq_of_ne zero] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ=>(0:ℂ)) z)

private theorem clock_anchor : sourceInputClock 3=anchorInput := by
  unfold sourceInputClock anchorInput
  funext i
  fin_cases i <;> rfl

private theorem extended_entry (z : ℂ) (i j : Fin 289) :
    AnalyticAt ℂ (fun w=>extendedKernel (sourceInputClock w) i j) z :=
  (source_matrix_analytic activeTerms sourceInputClock z (clock_coordinate z) i j).add analyticAt_const

/-- The same full original Green, with its original clock dependence retained. -/
def clockGreen (z : ℂ) : Matrix (Fin 289) (Fin 289) ℂ := originalGreenExpression (sourceInputClock z)

theorem clock_green_actual (z : ℂ) (regular : sourceInputClock z∈regularSource) :
    clockGreen z=sourceGreen ⟨sourceInputClock z,regular⟩ := by
  unfold clockGreen
  exact originalGreenExpression_actual ⟨sourceInputClock z,regular⟩

private theorem green_entry (z : ℂ) (regular : sourceInputClock z∈regularSource) (i j : Fin 289) :
    AnalyticAt ℂ (fun w=>clockGreen w i j) z := by
  have changeEntry : ∀i j,AnalyticAt ℂ (fun w=>originalChange (sourceInputClock w) i j) z :=
    by simpa only [originalChange] using source_matrix_analytic originalChangeTerms sourceInputClock z (clock_coordinate z)
  have readEntry : ∀i j,AnalyticAt ℂ (fun w=>originalReadback (sourceInputClock w) i j) z := by
    intro r s
    simpa only [originalReadback,originalChange,Matrix.transpose_apply] using
      source_matrix_analytic originalChangeTerms (fun w=>-sourceInputClock w) z
        (fun k=>(clock_coordinate z k).neg) s r
  have contactEntry : ∀i j,AnalyticAt ℂ (fun w=>contactInverse (sourceInputClock w) i j) z :=
    source_matrix_analytic contactInverseTerms sourceInputClock z (clock_coordinate z)
  have inverseEntry:=inverse_entry_analytic (fun w=>extendedKernel (sourceInputClock w)) z (extended_entry z) regular
  have activeEntry : ∀i j,AnalyticAt ℂ (fun w=>(activeProjection*(extendedKernel (sourceInputClock w))⁻¹) i j) z :=
    product_entry_analytic (fun _=>activeProjection) _ z (fun _ _=>analyticAt_const) inverseEntry
  unfold clockGreen originalGreenExpression
  exact product_entry_analytic _ _ z
    (product_entry_analytic _ _ z changeEntry (fun r s=>(contactEntry r s).add (activeEntry r s))) readEntry i j

private theorem polarization_entry (event : DressedEvent) (T : ℝ) (z : ℂ) (i j : Fin 289) :
    AnalyticAt ℂ (fun w=>dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock w) w T i j) z := by
  apply Differentiable.analyticAt
  intro w
  with_reducible_and_instances
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp
      (dressed_coincident_clock_jet_generated (anchorEvent event) 0 w T) i) j).differentiableAt

/-- Every factor, including the original Green and two quantum clocks, varies at this source occurrence. -/
def clockFeedback (event : DressedEvent) (T : ℝ) (z : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  1-(T:ℂ)⁻¹ • (clockGreen z*dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock z) z T)

private theorem feedback_entry (event : DressedEvent) (T : ℝ) (z : ℂ)
    (regular : sourceInputClock z∈regularSource) (i j : Fin 289) :
    AnalyticAt ℂ (fun w=>clockFeedback event T w i j) z := by
  exact analyticAt_const.sub (analyticAt_const.mul
    (product_entry_analytic _ _ z (green_entry z regular) (polarization_entry event T z) i j))

private theorem feedback_anchor (event : DressedEvent) (T : ℝ) : clockFeedback event T 3=anchorFeedback event T := by
  have green : clockGreen 3=sourceGreen generatedRegularPoint := by
    rw [clockGreen,clock_anchor]
    exact originalGreenExpression_actual generatedRegularPoint
  rw [clockFeedback,green,clock_anchor]
  rfl

/-- A positive-real clock neighborhood is generated from the paid actual source anchor. -/
theorem clock_regular_neighborhood (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    ∃radius : ℝ,0 < radius ∧ ∀z : ℂ,‖z-3‖<radius→
      0 < z.re ∧ sourceInputClock z∈regularSource ∧ IsUnit (clockFeedback event T z) := by
  have regular : sourceInputClock 3∈regularSource := by rw [clock_anchor]; exact generatedRegularPoint.property
  have unit : IsUnit (clockFeedback event T 3) := by rw [feedback_anchor]; exact anchor_feedback_unit event T positive small
  have originalNonzero : (extendedKernel (sourceInputClock 3)).det≠0:=isUnit_iff_ne_zero.mp regular
  have feedbackNonzero : (clockFeedback event T 3).det≠0:=isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp unit)
  have originalEvent : ∀ᶠz in 𝓝 (3:ℂ),(extendedKernel (sourceInputClock z)).det≠0 :=
    (determinant_analytic _ _ (extended_entry 3)).continuousAt.eventually_ne originalNonzero
  have feedbackEvent : ∀ᶠz in 𝓝 (3:ℂ),(clockFeedback event T z).det≠0 :=
    (determinant_analytic _ _ (feedback_entry event T 3 regular)).continuousAt.eventually_ne feedbackNonzero
  have positiveEvent : ∀ᶠz in 𝓝 (3:ℂ),0 < z.re :=
    (Complex.continuous_re.continuousAt).eventually (Ioi_mem_nhds (by norm_num : (0:ℝ)<(3:ℂ).re))
  have all : ∀ᶠz in 𝓝 (3:ℂ),0 < z.re ∧ sourceInputClock z∈regularSource ∧ IsUnit (clockFeedback event T z) := by
    filter_upwards [positiveEvent,originalEvent,feedbackEvent] with z hz hK hF
    exact ⟨hz,isUnit_iff_ne_zero.mpr hK,(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hF)⟩
  obtain ⟨radius,pos,bound⟩:=Metric.eventually_nhds_iff.mp all
  exact ⟨radius,pos,fun z hz=>bound (by simpa only [dist_eq_norm] using hz)⟩

def clockResolvent (event : DressedEvent) (T : ℝ) (z : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  (clockFeedback event T z)⁻¹

theorem clock_resolvent_generated (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    ∀ᶠz in 𝓝 (3:ℂ),clockFeedback event T z*clockResolvent event T z=1 ∧
      clockResolvent event T z*clockFeedback event T z=1 := by
  obtain ⟨radius,pos,domain⟩:=clock_regular_neighborhood event T positive small
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨radius,pos,?_⟩
  intro z close
  have unit:=(domain z (by simpa only [dist_eq_norm] using close)).2.2
  have determinant:=(Matrix.isUnit_iff_isUnit_det _).mp unit
  exact ⟨Matrix.mul_nonsing_inv _ determinant,Matrix.nonsing_inv_mul _ determinant⟩


private theorem matrix_product_derivative {m n k : ℕ}
    (A : ℂ→Matrix (Fin m) (Fin n) ℂ) (B : ℂ→Matrix (Fin n) (Fin k) ℂ)
    (dA : Matrix (Fin m) (Fin n) ℂ) (dB : Matrix (Fin n) (Fin k) ℂ) (z : ℂ)
    (ha : HasDerivAt A dA z) (hb : HasDerivAt B dB z) :
    HasDerivAt (fun w=>A w*B w) (dA*B z+A z*dB) z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have entries (l : Fin n) : HasDerivAt (fun w=>A w i l*B w l j)
      (dA i l*B z l j+A z i l*dB l j) z := by
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp ha i) l).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hb l) j)
  simpa only [Matrix.mul_apply,Matrix.add_apply,Finset.sum_add_distrib] using
    (HasDerivAt.fun_sum (u:=Finset.univ) (fun l _=>entries l))

private theorem matrix_inverse_derivative {n : ℕ} (A : ℂ→Matrix (Fin n) (Fin n) ℂ)
    (dA : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (entries : ∀i j,AnalyticAt ℂ (fun w=>A w i j) z) (ha : HasDerivAt A dA z)
    (unit : IsUnit (A z).det) :
    HasDerivAt (fun w=>(A w)⁻¹) (-((A z)⁻¹*dA*(A z)⁻¹)) z := by
  have inverse := (entries_analytic _ z (inverse_entry_analytic A z entries unit)).differentiableAt.hasDerivAt
  have product:=matrix_product_derivative A (fun w=>(A w)⁻¹) dA _ z ha inverse
  have nearby : ∀ᶠw in 𝓝 z,(A w).det≠0 :=
    (determinant_analytic A z entries).continuousAt.eventually_ne (isUnit_iff_ne_zero.mp unit)
  have identity : (fun w=>A w*(A w)⁻¹)=ᶠ[𝓝 z] fun _=>1 := by
    filter_upwards [nearby] with w regular
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr regular)
  have zero := (hasDerivAt_const z (1:Matrix (Fin n) (Fin n) ℂ)).congr_of_eventuallyEq identity
  have balance:=product.unique zero
  have answer : deriv (fun w=>(A w)⁻¹) z= -((A z)⁻¹*dA*(A z)⁻¹) := by
    have eqn:=congrArg (fun M : Matrix (Fin n) (Fin n) ℂ=>(A z)⁻¹*M) balance
    rw [mul_add,←mul_assoc (A z)⁻¹ (A z),Matrix.nonsing_inv_mul _ unit,one_mul,mul_zero] at eqn
    rw [←mul_assoc] at eqn
    exact eq_neg_of_add_eq_zero_right eqn
  exact inverse.congr_deriv answer

/-- The original Green's own clock derivative, including all moving source projectors. -/
def clockGreenJet (z : ℂ) : Matrix (Fin 289) (Fin 289) ℂ := deriv clockGreen z

def clockFeedbackJet (event : DressedEvent) (T : ℝ) (z : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  -((T:ℂ)⁻¹ • (clockGreenJet z*dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock z) z T+
    clockGreen z*dressedCoincidentClockJet (anchorEvent event) 0 z T))

private theorem feedback_derivative (event : DressedEvent) (T : ℝ) (z : ℂ)
    (regular : sourceInputClock z∈regularSource) :
    HasDerivAt (clockFeedback event T) (clockFeedbackJet event T z) z := by
  have green : HasDerivAt clockGreen (clockGreenJet z) z :=
    (entries_analytic clockGreen z (green_entry z regular)).differentiableAt.hasDerivAt
  have quantum:=dressed_coincident_clock_jet_generated (anchorEvent event) 0 z T
  have product:=matrix_product_derivative clockGreen
    (fun w=>dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock w) w T) _ _ z green quantum
  simpa only [clockFeedback,clockFeedbackJet,zero_sub,Pi.sub_def,Pi.smul_def] using!
    (hasDerivAt_const z (1:Matrix (Fin 289) (Fin 289) ℂ)).sub (product.const_smul (T:ℂ)⁻¹)

/-- The source-generated coupled resolvent differentiates with the full original Green and quantum memory jets. -/
theorem clock_resolvent_derivative (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    ∀ᶠz in 𝓝 (3:ℂ),HasDerivAt (clockResolvent event T)
      (-(clockResolvent event T z*clockFeedbackJet event T z*clockResolvent event T z)) z := by
  obtain ⟨radius,pos,domain⟩:=clock_regular_neighborhood event T positive small
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨radius,pos,?_⟩
  intro z close
  obtain ⟨_,regular,unit⟩:=domain z (by simpa only [dist_eq_norm] using close)
  exact matrix_inverse_derivative (clockFeedback event T) _ z (feedback_entry event T z regular)
    (feedback_derivative event T z regular) ((Matrix.isUnit_iff_isUnit_det _).mp unit)

private theorem null_entry (z : ℂ) (i j : Fin 289) :
    AnalyticAt ℂ (fun w=>sourceNull (sourceInputClock w) i j) z := by
  have changeEntry : ∀i j,AnalyticAt ℂ (fun w=>originalChange (sourceInputClock w) i j) z := by
    simpa only [originalChange] using source_matrix_analytic originalChangeTerms sourceInputClock z (clock_coordinate z)
  have inverseEntry : ∀i j,AnalyticAt ℂ (fun w=>originalInverse (sourceInputClock w) i j) z := by
    simpa only [originalInverse] using source_matrix_analytic originalInverseTerms sourceInputClock z (clock_coordinate z)
  unfold sourceNull
  exact product_entry_analytic (fun w=>originalChange (sourceInputClock w)*nullProjection)
    (fun w=>originalInverse (sourceInputClock w)) z
    (product_entry_analytic (fun w=>originalChange (sourceInputClock w)) (fun _=>nullProjection)
      z changeEntry (fun _ _=>analyticAt_const)) inverseEntry i j

def clockNullJet (z : ℂ) : Matrix (Fin 289) (Fin 289) ℂ := deriv (fun w=>sourceNull (sourceInputClock w)) z

private theorem momentum_zero (z : ℂ) :
    fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial 0) z=sourceInputClock z := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · simp only [fullMomentum,Fin.cases_succ,sourceInputClock,Pi.single_eq_of_ne (Fin.succ_ne_zero j),
      PreparationVacuumPhysicalFeedback.physicalSpatial,Pi.zero_apply,Complex.ofReal_zero,mul_zero]

private theorem feedback_full_pencil (event : DressedEvent) (T : ℝ) (nonzero : T≠0) (z : ℂ)
    (regular : sourceInputClock z∈regularSource) :
    clockFeedback event T z=(T:ℂ)⁻¹ • (clockGreen z*dressedSynchronizedPencil (anchorEvent event) 0 z T)+
      sourceNull (sourceInputClock z) := by
  have original:=PreparationPhysicalVoltageCompleteReturn.sourceGreen_original_left ⟨sourceInputClock z,regular⟩
  have tn : (T:ℂ)≠0:=by exact_mod_cast nonzero
  rw [clockFeedback,dressed_synchronized_pencil_original_action,ActualEMAction.em_jacobi_source,momentum_zero,
    mul_sub,Matrix.mul_smul,smul_sub,smul_smul,inv_mul_cancel₀ tn,one_smul,clock_green_actual z regular,original]
  unfold sourceNull
  abel

/-- The derivative of the same full pencil retains the derivative of its original null/initial projector. -/
theorem clock_feedback_full_flux (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    ∀ᶠz in 𝓝 (3:ℂ),clockFeedbackJet event T z=
      (T:ℂ)⁻¹ • (clockGreenJet z*dressedSynchronizedPencil (anchorEvent event) 0 z T+
        clockGreen z*dressedNativeClockFlux (anchorEvent event) 0 z T)+clockNullJet z := by
  obtain ⟨radius,pos,domain⟩:=clock_regular_neighborhood event T positive small
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨radius,pos,?_⟩
  intro z close
  have regular:=(domain z (by simpa only [dist_eq_norm] using close)).2.1
  have green : HasDerivAt clockGreen (clockGreenJet z) z :=
    (entries_analytic clockGreen z (green_entry z regular)).differentiableAt.hasDerivAt
  have nullDerivative : HasDerivAt (fun w=>sourceNull (sourceInputClock w)) (clockNullJet z) z :=
    (entries_analytic _ z (null_entry z)).differentiableAt.hasDerivAt
  have product:=matrix_product_derivative clockGreen (fun w=>dressedSynchronizedPencil (anchorEvent event) 0 w T)
    _ _ z green (dressed_native_clock_flux_generated (anchorEvent event) 0 z T)
  have returned := (product.const_smul (T:ℂ)⁻¹).add nullDerivative
  have legal : ∀ᶠw in 𝓝 z,sourceInputClock w∈regularSource := by
    have localDet:=(determinant_analytic _ z (extended_entry z)).continuousAt.eventually_ne
      (isUnit_iff_ne_zero.mp regular)
    filter_upwards [localDet] with w hw
    exact isUnit_iff_ne_zero.mpr hw
  have same : clockFeedback event T=ᶠ[𝓝 z] fun w=>
      (T:ℂ)⁻¹ • (clockGreen w*dressedSynchronizedPencil (anchorEvent event) 0 w T)+sourceNull (sourceInputClock w) := by
    filter_upwards [legal] with w hw
    exact feedback_full_pencil event T positive.ne' w hw
  exact (feedback_derivative event T z regular).unique (returned.congr_of_eventuallyEq same)

end LowEnergy.GaussComposite.ActualEMDressedClockGerm
