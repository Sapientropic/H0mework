import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M5.SourceFirstCrossOccurrenceResidual

/-!
# M6 normalized authority observer fixture

This fixture does not introduce another occurrence carrier.  Its actual fibre
is exactly the M5 source-path index, whose two constructors already name the
two distinct source-generated occurrences.  The visible carrier is the image
subtype of their common independently presented classical normal form.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M6NormalizedAuthorityObserverFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Classical.Source Classical.Source.FreeStrategicSyntax
open Classical.Independent
open Classical.GeneratedTerminalExchange
open M5SourceFirstCrossOccurrenceFixture
open M5SourceFirstCrossOccurrenceResidual

/-- The actual carrier is the already existing M5 source-path carrier. -/
abbrev ActualPath := PathIndex

/-- The visible carrier is precisely the one normalized classical image, not a
caller-provided normalizer or representative selector. -/
abbrev NormalizedImage :=
  { image : FiniteStrategicGame // image = normalizedClassicalImage }

def commonImage : NormalizedImage :=
  ⟨normalizedClassicalImage, rfl⟩

/-- Both actual source paths forget to the same normalized image. -/
def normalizedForget (_path : ActualPath) : NormalizedImage :=
  commonImage

/-- A source path reads its authority only from the already fulfilled exact
terminal-authority consumer belonging to that path's source program. -/
def pathAuthorityK : ActualPath → ℚ
  | .left => terminalAuthorityK leftProgram leftTerminal
  | .right => terminalAuthorityK rightProgram rightTerminal

/-- Readout of the existing actual source occurrence selected by the M5 path. -/
def actualOccurrence : ActualPath →
    RootedAccountedUnfolding FreeClassicalAtom
  | .left => leftProgram.occurrence
  | .right => rightProgram.occurrence

theorem left_actualOccurrence :
    actualOccurrence leftPath = leftProgram.occurrence := rfl

theorem right_actualOccurrence :
    actualOccurrence rightPath = rightProgram.occurrence := rfl

theorem actualOccurrences_ne :
    actualOccurrence leftPath ≠ actualOccurrence rightPath :=
  source_occurrences_ne

theorem left_pathAuthorityK : pathAuthorityK leftPath = 1 :=
  left_terminalAuthorityK

theorem right_pathAuthorityK : pathAuthorityK rightPath = 0 :=
  right_terminalAuthorityK

theorem pathAuthorityK_ne :
    pathAuthorityK leftPath ≠ pathAuthorityK rightPath := by
  rw [left_pathAuthorityK, right_pathAuthorityK]
  decide

theorem left_exact_authority_consumer :
    TerminalAuthorityConsumerAt leftProgram leftTerminal :=
  leftAuthorityConsumer

theorem right_exact_authority_consumer :
    TerminalAuthorityConsumerAt rightProgram rightTerminal :=
  rightAuthorityConsumer

theorem normalizedForget_paths_equal :
    normalizedForget leftPath = normalizedForget rightPath := rfl

/-- Choosing the left actual path gives an honest object-level right section
of forgetting on the exact normalized-image carrier. -/
def leftSurrogateSection (_image : NormalizedImage) : ActualPath :=
  leftPath

theorem leftSurrogateSection_rightInverse :
    Function.RightInverse leftSurrogateSection normalizedForget := by
  intro image
  apply Subtype.ext
  exact image.property.symm

/-- The admissible vertical transport exchanges the two already generated
source paths while acting identically on their common visible image. -/
def verticalSwap : ActualPath → ActualPath
  | .left => .right
  | .right => .left

def verticalSwapEquiv : ActualPath ≃ ActualPath where
  toFun := verticalSwap
  invFun := verticalSwap
  left_inv path := by cases path <;> rfl
  right_inv path := by cases path <;> rfl

/-- The residual coordinate is transported honestly: it swaps the two exact
values emitted by the M5 authority consumers and fixes every other rational. -/
def residualSwapEquiv : ℚ ≃ ℚ :=
  Equiv.swap 1 0

theorem residualSwap_authority_commutes (path : ActualPath) :
    residualSwapEquiv (pathAuthorityK path) =
      pathAuthorityK (verticalSwapEquiv path) := by
  cases path with
  | left =>
      change residualSwapEquiv
        (terminalAuthorityK leftProgram leftTerminal) =
          terminalAuthorityK rightProgram rightTerminal
      rw [left_terminalAuthorityK, right_terminalAuthorityK]
      exact Equiv.swap_apply_left 1 0
  | right =>
      change residualSwapEquiv
        (terminalAuthorityK rightProgram rightTerminal) =
          terminalAuthorityK leftProgram leftTerminal
      rw [right_terminalAuthorityK, left_terminalAuthorityK]
      exact Equiv.swap_apply_right 1 0

theorem residualSwap_changes_authority (path : ActualPath) :
    residualSwapEquiv (pathAuthorityK path) ≠ pathAuthorityK path := by
  cases path with
  | left =>
      change residualSwapEquiv
        (terminalAuthorityK leftProgram leftTerminal) ≠
          terminalAuthorityK leftProgram leftTerminal
      rw [left_terminalAuthorityK]
      have swapped : residualSwapEquiv (1 : ℚ) = 0 :=
        Equiv.swap_apply_left 1 0
      rw [swapped]
      decide
  | right =>
      change residualSwapEquiv
        (terminalAuthorityK rightProgram rightTerminal) ≠
          terminalAuthorityK rightProgram rightTerminal
      rw [right_terminalAuthorityK]
      have swapped : residualSwapEquiv (0 : ℚ) = 1 :=
        Equiv.swap_apply_right 1 0
      rw [swapped]
      decide

def visibleIdentity : NormalizedImage → NormalizedImage := id

def visibleIdentityEquiv : NormalizedImage ≃ NormalizedImage :=
  Equiv.refl NormalizedImage

theorem verticalSwap_forget_commutes (path : ActualPath) :
    normalizedForget (verticalSwap path) =
      visibleIdentity (normalizedForget path) := rfl

theorem verticalSwap_has_no_fixed_path (path : ActualPath) :
    verticalSwap path ≠ path := by
  cases path <;> decide

theorem verticalSwap_changes_authority (path : ActualPath) :
    pathAuthorityK (verticalSwap path) ≠ pathAuthorityK path := by
  cases path with
  | left => exact pathAuthorityK_ne.symm
  | right => exact pathAuthorityK_ne

end
end M6NormalizedAuthorityObserverFixture
end Society
end ProcessGame
end SaturationMonoid
