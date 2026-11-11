import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceData
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceProgram
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusSourceData
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceData
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Source.PowerWave

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKForcedInverseSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open OriginalKSourceResolventReconstruction OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalWholeDebtRPowerWaveDilationSource

abbrev Value := OriginalKJointMobiusSourceCalculation.Value
abbrev Var (_ : Unit) := Fin 2 × Fin 16
abbrev Base := OriginalKJointMobiusSourceCalculation.Base
abbrev Half := OriginalKJointMobiusSourceCalculation.Half
abbrev E := Expr Value Var ()
abbrev coordinate := OriginalKJointMobiusSourceCalculation.coordinate
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Hq" => BurnolQuarterIntervalL2
local notation "q" => (1/4 : ℝ)

def atCoordinate (c : BurnolCompletedMellinCoordinate) (side : Fin 2) : BurnolCompletedMellinCoordinate :=
  ![c,barC c] side
def opposite (side : Fin 2) : Fin 2 := ![1,0] side
abbrev sourceCoupling (c : BurnolCompletedMellinCoordinate) : ℂ := (damping c : ℂ)*returnRatio c

def sourceEnvironment (c : BurnolCompletedMellinCoordinate) (originalPa originalUnit : BurnolL2) :
    Env Value Var := fun _ address =>
  let side := address.1
  let d := atCoordinate c side
  ![BandFullStockEuler.regularSource d,
    burnolQuarterZeroExtension (PsiDrive.psiU : Hq),
    burnolQuarterZeroExtension (PsiDrive.psiV : Hq),
    burnolQuarterZeroExtension (TwoPieceFourierAction.eta q : Hq),
    burnolQuarterZeroExtension (TwoPieceFourierAction.eta junctionPoint : Hq),
    burnolQuarterZeroExtension (sourceFirst d : Hq),
    burnolQuarterZeroExtension (sourceSecond d : Hq),
    profileIntegral (barC d) (-junctionShift),fourierProfileIntegral (barC d) (-junctionShift),
    profileIntegral (barC d) junctionShift,fourierProfileIntegral (barC d) junctionShift,
    (if side = 0 then originalPa else OriginalWholeDebtRJointMobiusSource.paWave d),
    (if side = 0 then originalUnit else burnolUnitTailResponse d 4),
    OriginalWholeDebtRAdjointContactSource.step junctionPoint,
    OriginalWholeDebtRAdjointContactSource.step q,generatedK d] address.2

def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input
def scale (scalar : ℂ) (input : E) : E := linear (scalar • ContinuousLinearMap.id ℂ BurnolL2) input
def sub (left right : E) : E := .add left (scale (-1) right)
def fourier (input : E) : E := linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap input
def wholeS : BurnolL2 →L[ℂ] BurnolL2 :=
  OriginalKBFiniteCalculation.wholeZeroMean.comp fourierL2.toContinuousLinearEquiv.toContinuousLinearMap
def diagonalCode (input : E) : E :=
  .add input (linear wholeS (linear OriginalKBFiniteCalculation.wholeBInverse (linear wholeS input)))
def crossCode (input : E) : E := linear wholeS (linear OriginalKBFiniteCalculation.wholeBInverse input)

def matrixRead (d : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  (innerSL ℂ (SingularCounting.centeredPower (barC d))).comp
    (Constructor.zeroMean.comp burnolQuarterRestriction)
def matrixAction (d : BurnolCompletedMellinCoordinate) : BurnolL2 →+ BurnolL2 →+ BurnolL2 where
  toFun := fun left => (matrixRead d left • ContinuousLinearMap.id ℂ BurnolL2).toLinearMap.toAddMonoidHom
  map_zero' := by ext right; simp
  map_add' := by intro left right; ext value; simp [add_smul]

def matrixCode (c : BurnolCompletedMellinCoordinate) (side : Fin 2) (input : E) : E :=
  .bilinear (matrixAction (barC (atCoordinate c side))) input
    (fourier (.var (opposite side,15)))

def contactPaymentCode (c : BurnolCompletedMellinCoordinate) (side : Fin 2) : E :=
  let d := atCoordinate c side
  sub (.add
    (sub (scale (sourceTrace d 0) (matrixCode c side (diagonalCode (.var (side,3)))))
      (scale (((junctionPoint/q : ℝ) : ℂ)*sourceJump d 0)
        (matrixCode c side (diagonalCode (.var (side,4))))))
    (scale (sourceTrace d 1) (matrixCode c side (crossCode (.var (side,3))))))
    (scale (((junctionPoint/q : ℝ) : ℂ)*sourceJump d 1)
      (matrixCode c side (crossCode (.var (side,4)))))

/-- The finite payment is executed from the two original Psi columns and all four contacts. -/
def gammaFieldCode (c : BurnolCompletedMellinCoordinate) (side : Fin 2) : E :=
  let d := atCoordinate c side
  let z := star (barC d).value
  let fk := fourier (.var (opposite side,15))
  .add
    (sub
      (scale 2 (sub (.add
        (scale (-Kernel.A d) (matrixCode c side (.var (side,2))))
        (scale (-Kernel.beta d) (matrixCode c side (.var (side,1)))))
        (contactPaymentCode c side)))
      (scale (2*(2*(q : ℂ)^z*sourceTrace d 1-
        2*(junctionPoint : ℂ)^z*sourceJump d 1)) fk))
    (scale (2*(sourceTrace d 1-((junctionPoint/q : ℝ) : ℂ)*sourceJump d 1)*
      (2*(q : ℂ)^z/z)) fk)

def contactBinding (side : Fin 2) :
    ∀ sort, OriginalKContactClosureSourceCalculation.Var sort → Expr Value Var sort :=
  fun _ index => ![.var (side,0),.var (side,13),.var (side,14)] index
def effectCode (c : BurnolCompletedMellinCoordinate) (side : Fin 2) : E :=
  (OriginalKContactClosureSourceCalculation.effectCode (atCoordinate c side)
    (barC (atCoordinate c side))).subst (contactBinding side)
def correctionRawCode (side : Fin 2) : E := .add (.var (side,5)) (fourier (.var (side,6)))
def correctionCode (c : BurnolCompletedMellinCoordinate) (side : Fin 2) : E :=
  .add (.var (side,11))
    (scale (OriginalWholeDebtRJointMobiusUnitSource.unitCoefficient (atCoordinate c side)) (.var (side,12)))
def pairedSourceCode (c : BurnolCompletedMellinCoordinate) (side : Fin 2) : E :=
  let d := atCoordinate c side
  scale (1/2) (.add
    (fourier (.add (scale (coupling1 d) (.var (side,7))) (scale (coupling0 d) (.var (side,8)))))
    (fourier (.add (scale (coupling1 d) (.var (side,9))) (scale (coupling0 d) (.var (side,10))))))

def forcingCode (c : BurnolCompletedMellinCoordinate) (side : Fin 2) : E :=
  let d := atCoordinate c side
  let r := sourceCoupling d
  sub (.add (.add (.add
    (sub (scale (r*(OriginalWholeDebtRJointMobiusSource.character d-
      OriginalWholeDebtRJointMobiusSource.character (barC d))) (fourier (.var (opposite side,15))))
      (scale r (fourier (correctionRawCode (opposite side)))))
    (scale (damping d : ℂ) (pairedSourceCode c side)))
    (scale (1/2) (.add (gammaFieldCode c side)
      (linear ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.starProjection)
        (effectCode c side)))))
    (scale r (fourier (correctionCode c (opposite side)))))
    (linear (sourceCayley (barC d)).adjoint (correctionCode c side))

def responseCode (c : BurnolCompletedMellinCoordinate) : E :=
  scale (((4*(sourceDamping c)^2*‖generatedK c‖^2*
    ‖hPowerPhysicalCorrection (barC c)‖^2 : ℝ) : ℂ)⁻¹)
    (.add (scale (sourceCoupling c) (fourier (forcingCode c 1)))
      (linear (sourceCayley (barC c)) (forcingCode c 0)))
def inputCode (c : BurnolCompletedMellinCoordinate) : E := fourier (responseCode c)
def code (c : BurnolCompletedMellinCoordinate) : E := linear (burnolDirectRightResolventCLM c) (inputCode c)

theorem operation_budget (c : BurnolCompletedMellinCoordinate) : 0 < remaining (code c) := by
  change 0 < remaining (inputCode c)+1
  omega

def reader (originalPa originalUnit : BurnolL2) (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1)) (half : Half observation)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()) :=
  { environment := sourceEnvironment (coordinate observation nontrivial half occurrence) originalPa originalUnit
    expression := code (coordinate observation nontrivial half occurrence) }

end OriginalKForcedInverseSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
