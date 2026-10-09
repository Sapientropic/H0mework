import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime.Consumers

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open Lean Elab Term Command Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

private def unitText : String := include_str "../../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/lalanine40k-si-work/source/packet.json"
private def unitArtifactSha256 : String := "7c6036f022f1918f92553fb238d251bbb7711951afe549b0d704a5e41fa11928"

private def declareUnit (name : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let fullName := (← getCurrNamespace) ++ name
  addDecl (.defnDecl { name := fullName, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · fullName)
  enableRealizationsForConst fullName

elab "generateRegisteredUnits" : command => liftTermElabM do
  unless Sha256.hex unitText == unitArtifactSha256 do throwError "Registered unit artifact changed"
  let packet ← parse unitText
  unless (← decode String (← field packet "schema")) == "lalanine40k-registered-engine-si-convention/v1" do
    throwError "Registered unit artifact schema"
  let source ← field packet "source"
  unless (← decode String (← field source "reentry_packet_sha256")) == Reentry.SourceParsing.sourceArtifactSha256 do
    throwError "SI units must use the registered Reentry occurrence"
  unless (← decode String (← field source "pyscf_version")) == "2.10.0" do
    throwError "SI units must preserve the registered engine convention"
  declareUnit `reentryIdentity (toExpr (← decode String (← field source "reentry_packet_sha256")))
  declareUnit `engineVersion (toExpr (← decode String (← field source "pyscf_version")))
  let raw ← field packet "raw_dyadic"
  for (name,key) in [(`lengthMeterQ,"BOHR_SI"),(`engineBohrAngstromQ,"BOHR"),(`massKilogramQ,"E_MASS"),
      (`hbarJouleSecondQ,"HBAR"),(`engineHartreeJouleQ,"HARTREE2J")] do
    declareUnit name (← rationalExpr (← field raw key))

generateRegisteredUnits

noncomputable section

def sourceRuntime := FiniteContinuation.Runtime.afterFirst
def sourceMaterial := FiniteContinuation.Runtime.readCurrent sourceRuntime

theorem source_identity : reentryIdentity=Reentry.SourceParsing.sourceArtifactSha256 := rfl

def lengthMeter : ℝ := lengthMeterQ
def massKilogram : ℝ := massKilogramQ
def hbarJouleSecond : ℝ := hbarJouleSecondQ
-- Coherent units derive from raw source constants; engine rounding remains explicit.
def energyJoule : ℝ := hbarJouleSecond^2/(massKilogram*lengthMeter^2)
def timeSecond : ℝ := hbarJouleSecond/energyJoule
def momentumSI : ℝ := hbarJouleSecond/lengthMeter
def engineEnergyResidual : ℝ := (engineHartreeJouleQ : ℝ)-energyJoule

theorem length_positive : 0 < lengthMeter := by norm_num [lengthMeter,lengthMeterQ,rationalRead]
theorem mass_positive : 0 < massKilogram := by norm_num [massKilogram,massKilogramQ,rationalRead]
theorem hbar_positive : 0 < hbarJouleSecond := by norm_num [hbarJouleSecond,hbarJouleSecondQ,rationalRead]
theorem energy_positive : 0 < energyJoule :=
  div_pos (sq_pos_of_pos hbar_positive) (mul_pos mass_positive (sq_pos_of_pos length_positive))
theorem time_positive : 0 < timeSecond := div_pos hbar_positive energy_positive
theorem momentum_positive : 0 < momentumSI := div_pos hbar_positive length_positive

theorem kinetic_units : momentumSI^2/massKilogram=energyJoule := by
  unfold momentumSI energyJoule
  field_simp

theorem phase_units : timeSecond*energyJoule=hbarJouleSecond := by
  exact div_mul_cancel₀ _ energy_positive.ne'

theorem velocity_units : lengthMeter/timeSecond=momentumSI/massKilogram := by
  unfold timeSecond energyJoule momentumSI
  field_simp [hbar_positive.ne',mass_positive.ne',length_positive.ne']

theorem engine_energy_account : (engineHartreeJouleQ : ℝ)=energyJoule+engineEnergyResidual := by
  unfold engineEnergyResidual
  ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
