import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.MatchingHistoryWholeRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.Go.GoReadoutFactorizationRegression

/-! # M7 matching, history, and Go readout whole consumer -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M7ReadoutFactorizationWholeRegression

open M7MatchingHistoryWholeRegression
open M7GoReadoutFactorizationRegression

structure M7ReadoutFactorizationWholeCertificate : Prop where
  matchingHistory : MatchingHistoryWholeCertificate
  go : ∀ horizon : Nat, GoReadoutFactorizationCertificate horizon

theorem m7ReadoutFactorizationWholeDirectConsumer :
    M7ReadoutFactorizationWholeCertificate where
  matchingHistory := matchingHistoryWholeDirectConsumer
  go := goReadoutFactorizationDirectConsumer

end M7ReadoutFactorizationWholeRegression
end Society
end ProcessGame
end SaturationMonoid
