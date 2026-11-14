import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.BufferedReplay

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.EarlierSourceSearch.Extracted

structure Case where
  name : String
  moves : List (Move 19)
  black : Nat
  white : Nat
  played : Nat
  peak : Nat
  whiteTurn : Bool
  maxima : List Nat

def cases : List Case := [
  {name := "birth", moves := [.play (1, 1), .play (18, 18), .play (1, 2), .play (18, 16), .play (1, 3), .play (18, 14), .play (1, 0), .play (0, 1), .play (2, 3), .play (18, 12), .play (2, 1), .play (18, 10), .play (3, 1), .play (18, 8), .play (3, 0), .play (18, 6)],
   black := 6457216, white := 2, played := 6457216, peak := 8,
   whiteTurn := false, maxima := [6457216]},
  {name := "hook", moves := [.play (1, 1), .play (18, 18), .play (1, 2), .play (18, 16), .play (1, 3), .play (18, 14), .play (1, 0), .play (0, 1), .play (2, 3), .play (18, 12), .play (2, 1), .play (18, 10), .play (3, 1), .play (18, 8), .play (3, 0)],
   black := 6457216, white := 2, played := 6457216, peak := 8,
   whiteTurn := true, maxima := [6457216]},
  {name := "capturing", moves := [.play (1, 1), .play (18, 18), .play (1, 2), .play (18, 16), .play (1, 3), .play (18, 14), .play (1, 0), .play (0, 1), .play (2, 3), .play (18, 12), .play (2, 1), .play (18, 10), .play (3, 1), .play (18, 8), .play (3, 0), .play (2, 2)],
   black := 6457216, white := 65538, played := 6457216, peak := 8,
   whiteTurn := false, maxima := [6457216]},
  {name := "miai", moves := [.play (1, 1), .play (18, 18), .play (1, 2), .play (18, 16), .play (1, 3), .play (18, 14), .play (1, 0), .play (0, 1), .play (2, 3), .play (18, 12), .play (2, 1), .play (18, 10), .play (3, 1), .play (2, 0), .play (1, 4), .play (0, 0), .play (0, 2), .play (18, 8), .play (0, 1)],
   black := 4362118, white := 16384, played := 4362118, peak := 10,
   whiteTurn := true, maxima := [4362118]},
  {name := "vital", moves := [.play (1, 1), .play (18, 18), .play (1, 2), .play (18, 16), .play (1, 3), .play (18, 14), .play (1, 0), .play (0, 1), .play (2, 3), .play (18, 12), .play (2, 1), .play (18, 10), .play (3, 1), .play (18, 8), .play (3, 0), .play (3, 2), .play (4, 1), .play (18, 6), .play (5, 1), .play (5, 0), .play (2, 4), .play (18, 4), .play (0, 2)],
   black := 69263067012, white := 34368126978, played := 69263067012, peak := 12,
   whiteTurn := true, maxima := [69263067012]},
  {name := "straight_four", moves := [.play (1, 1), .play (18, 18), .play (1, 2), .play (18, 16), .play (1, 3), .play (18, 14), .play (1, 0), .play (0, 1), .play (2, 3), .play (18, 12), .play (2, 1), .play (3, 1), .play (2, 4), .play (0, 0), .play (2, 5), .play (0, 3), .play (1, 4), .play (0, 2), .play (0, 4)],
   black := 954256, white := 4194304, played := 954256, peak := 10,
   whiteTurn := true, maxima := [954256]}]

end SaturationMonoid.ProcessGame.Go.CriticalKomi.EarlierSourceSearch.Extracted
