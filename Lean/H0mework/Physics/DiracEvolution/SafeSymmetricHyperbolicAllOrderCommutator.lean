import H0mework.Physics.DiracEvolution.SafeSymmetricHyperbolicAllOrderCoefficients

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCommutator

open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCoefficients
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator
open ProofFreeRicherAnholonomicSource

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-- Spatial derivatives indexed by one finite word.  The recursion is the
single carrier used for every commutation order. -/
def fixedSpatialWordDerivative
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier) :
    BasePoint → MatterCoordinateCarrier :=
  match word with
  | [] => field
  | direction :: tail => fun point =>
      fieldDirectionalDerivative (fixedSpatialWordDerivative tail field)
        point direction.succ

theorem fixedSpatialWordDerivative_contDiff_infty
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (fixedSpatialWordDerivative word field) := by
  induction word with
  | nil => simpa [fixedSpatialWordDerivative] using fieldSmooth
  | cons direction tail inductionHypothesis =>
      simp only [fixedSpatialWordDerivative]
      unfold fieldDirectionalDerivative
      exact
        (inductionHypothesis.fderiv_right (m := ∞) (by simp)).clm_apply
          contDiff_const

@[simp] theorem fixedSpatialWordDerivative_zero
    (word : List (Fin 3))
    (point : BasePoint) :
    fixedSpatialWordDerivative word
        (0 : BasePoint → MatterCoordinateCarrier) point = 0 := by
  induction word generalizing point with
  | nil => rfl
  | cons direction tail inductionHypothesis =>
      simp only [fixedSpatialWordDerivative, fieldDirectionalDerivative]
      rw [show fixedSpatialWordDerivative tail
          (0 : BasePoint → MatterCoordinateCarrier) = 0 by
        funext candidate
        exact inductionHypothesis candidate]
      simp

private theorem directionalDerivativeField_contDiff_infty
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun point => fieldDirectionalDerivative field point direction) := by
  unfold fieldDirectionalDerivative
  exact (fieldSmooth.fderiv_right (m := ∞) (by simp)).clm_apply
    contDiff_const

private theorem principalCoefficientDirectionalDerivative_contDiff_infty
    (direction commutedDirection : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      fieldDirectionalDerivative
        (fixedEvolutionPrincipalCoordinateCLM direction) point
        commutedDirection) := by
  unfold fieldDirectionalDerivative
  exact
    ((fixedEvolutionPrincipalCoordinateCLM_contDiff_infty direction
      ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem lowerCoefficientDirectionalDerivative_contDiff_infty
    (commutedDirection : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      fieldDirectionalDerivative fixedMatterLowerCoefficient point
        commutedDirection) := by
  unfold fieldDirectionalDerivative
  exact
    (fixedMatterLowerCoefficient_contDiff_infty.fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const

theorem fixedMatterFirstOrderOperator_contDiff_infty
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞
      (matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field) := by
  unfold matterCoordinateFirstOrderOperator
  have principalRegular : ContDiff ℝ ∞ (fun point =>
      ∑ direction : LorentzianIndex,
        fixedEvolutionPrincipalCoordinateCLM direction point
          (fieldDirectionalDerivative field point direction)) :=
    ContDiff.sum fun direction _ =>
      (fixedEvolutionPrincipalCoordinateCLM_contDiff_infty direction
        ).clm_apply
          (directionalDerivativeField_contDiff_infty field fieldSmooth
            direction)
  exact principalRegular.add
    (fixedMatterLowerCoefficient_contDiff_infty.clm_apply fieldSmooth)

/-- The coefficient-only forcing exposed by one spatial commutation. -/
def fixedMatterFirstCommutatorForcing
    (field : BasePoint → MatterCoordinateCarrier)
    (commutedDirection : LorentzianIndex)
    (point : BasePoint) : MatterCoordinateCarrier :=
  (∑ direction : LorentzianIndex,
    (fieldDirectionalDerivative
        (fixedEvolutionPrincipalCoordinateCLM direction) point
        commutedDirection)
      (fieldDirectionalDerivative field point direction)) +
  (fieldDirectionalDerivative fixedMatterLowerCoefficient point
      commutedDirection) (field point)

theorem fixedMatterFirstCommutatorForcing_contDiff_infty
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field)
    (commutedDirection : LorentzianIndex) :
    ContDiff ℝ ∞
      (fixedMatterFirstCommutatorForcing field commutedDirection) := by
  unfold fixedMatterFirstCommutatorForcing
  have principalRegular : ContDiff ℝ ∞ (fun point =>
      ∑ direction : LorentzianIndex,
        (fieldDirectionalDerivative
            (fixedEvolutionPrincipalCoordinateCLM direction) point
            commutedDirection)
          (fieldDirectionalDerivative field point direction)) :=
    ContDiff.sum fun direction _ =>
      (principalCoefficientDirectionalDerivative_contDiff_infty
        direction commutedDirection).clm_apply
          (directionalDerivativeField_contDiff_infty field fieldSmooth
            direction)
  exact principalRegular.add
    ((lowerCoefficientDirectionalDerivative_contDiff_infty
      commutedDirection).clm_apply fieldSmooth)

/-- Recursive lower-order forcing for a complete spatial derivative word. -/
def fixedMatterAllOrderCommutedForcing
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier) :
    BasePoint → MatterCoordinateCarrier :=
  match word with
  | [] => 0
  | direction :: tail => fun point =>
      fieldDirectionalDerivative
          (fixedMatterAllOrderCommutedForcing tail field)
          point direction.succ +
        fixedMatterFirstCommutatorForcing
          (fixedSpatialWordDerivative tail field) direction.succ point

theorem fixedMatterAllOrderCommutedForcing_contDiff_infty
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (fixedMatterAllOrderCommutedForcing word field) := by
  induction word with
  | nil =>
      simp only [fixedMatterAllOrderCommutedForcing]
      exact (contDiff_const : ContDiff ℝ ∞
        (fun _ : BasePoint => (0 : MatterCoordinateCarrier)))
  | cons direction tail inductionHypothesis =>
      simp only [fixedMatterAllOrderCommutedForcing]
      exact
        (directionalDerivativeField_contDiff_infty
          (fixedMatterAllOrderCommutedForcing tail field)
          inductionHypothesis direction.succ).add
        (fixedMatterFirstCommutatorForcing_contDiff_infty
          (fixedSpatialWordDerivative tail field)
          (fixedSpatialWordDerivative_contDiff_infty tail field fieldSmooth)
          direction.succ)

theorem fixedMatterAllOrderCommutedActionLaw
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field)
    (point : BasePoint) :
    fixedSpatialWordDerivative word
        (matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          field) point =
      matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          (fixedSpatialWordDerivative word field) point +
        fixedMatterAllOrderCommutedForcing word field point := by
  induction word generalizing point with
  | nil => simp [fixedSpatialWordDerivative, fixedMatterAllOrderCommutedForcing]
  | cons direction tail inductionHypothesis =>
      have tailLaw :
          fixedSpatialWordDerivative tail
              (matterCoordinateFirstOrderOperator
                fixedEvolutionPrincipalCoordinateCLM
                fixedMatterLowerCoefficient field) =
            fun candidate =>
              matterCoordinateFirstOrderOperator
                  fixedEvolutionPrincipalCoordinateCLM
                  fixedMatterLowerCoefficient
                  (fixedSpatialWordDerivative tail field) candidate +
                fixedMatterAllOrderCommutedForcing tail field candidate := by
        funext candidate
        exact inductionHypothesis candidate
      rw [show fixedSpatialWordDerivative (direction :: tail)
          (matterCoordinateFirstOrderOperator
            fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
            field) point =
          fieldDirectionalDerivative
            (fixedSpatialWordDerivative tail
              (matterCoordinateFirstOrderOperator
                fixedEvolutionPrincipalCoordinateCLM
                fixedMatterLowerCoefficient field))
            point direction.succ by rfl,
        tailLaw]
      unfold fieldDirectionalDerivative
      rw [fderiv_fun_add
        ((fixedMatterFirstOrderOperator_contDiff_infty
          (fixedSpatialWordDerivative tail field)
          (fixedSpatialWordDerivative_contDiff_infty tail field fieldSmooth)
          ).differentiable (by simp)).differentiableAt
        ((fixedMatterAllOrderCommutedForcing_contDiff_infty
          tail field fieldSmooth).differentiable (by simp)).differentiableAt]
      simp only [add_apply]
      rw [show fderiv ℝ
          (matterCoordinateFirstOrderOperator
            fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
            (fixedSpatialWordDerivative tail field)) point
            (coordinateDirection direction.succ) =
          matterCoordinateFirstOrderOperator
              fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
              (fixedSpatialWordDerivative (direction :: tail) field) point +
            fixedMatterFirstCommutatorForcing
              (fixedSpatialWordDerivative tail field) direction.succ point by
        simpa only [fixedSpatialWordDerivative,
          fixedMatterFirstCommutatorForcing, fieldDirectionalDerivative,
          add_assoc]
          using fixedMatterFirstOrderOperator_directionalDerivative
            (fixedSpatialWordDerivative tail field)
            ((fixedSpatialWordDerivative_contDiff_infty tail field fieldSmooth
              ).of_le (show ((2 : ℕ∞) : ℕ∞ω) ≤
                ((⊤ : ℕ∞) : ℕ∞ω) from
                  WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
            point direction.succ]
      simp only [fixedMatterAllOrderCommutedForcing,
        fieldDirectionalDerivative]
      abel

/-- Every spatial word of an exact mother-action solution satisfies the same
principal equation with the recursively generated coefficient forcing. -/
theorem fixedMatterAllOrderCommutedActionLaw_of_actionZero
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field)
    (actionZero : ∀ point,
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point = 0)
    (point : BasePoint) :
    matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        (fixedSpatialWordDerivative word field) point =
      -fixedMatterAllOrderCommutedForcing word field point := by
  have law := fixedMatterAllOrderCommutedActionLaw
    word field fieldSmooth point
  have actionEq :
      matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          field = 0 := by
    funext candidate
    exact actionZero candidate
  rw [actionEq] at law
  rw [fixedSpatialWordDerivative_zero word point] at law
  exact eq_neg_of_add_eq_zero_left law.symm

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCommutator
