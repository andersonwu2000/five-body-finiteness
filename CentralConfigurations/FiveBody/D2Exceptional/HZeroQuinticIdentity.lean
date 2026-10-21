import CentralConfigurations.FiveBody.D2Exceptional.HZeroQuintic

namespace CentralConfigurations.FiveBody.D2.Exceptional

theorem normalized_quintic0 (h y : ℂ) (hh : h^2+3=0) :
    P0 h y = eulerQuintic ((h-1)/2) y (1) (1) := by
  dsimp [P0,eulerQuintic]
  linear_combination (h^3/32 + h^2*(-y/8 - 9/32) + h*(y^2/8 + y + 27/32) - y^3/4 - 5*y^2/8 - 17*y/8 - 27/32)*hh

theorem normalized_quintic1 (h y : ℂ) (hh : h^2+3=0) :
    P1 h y = eulerQuintic ((h-1)/2) y (1) (-1) := by
  dsimp [P1,eulerQuintic]
  linear_combination (h^3/32 + h^2*(-y/8 - 9/32) + h*(y^2/8 + y + 27/32) - y^3/4 - y^2/8 - 25*y/8 - 11/32)*hh

theorem normalized_quintic2 (h y : ℂ) (hh : h^2+3=0) :
    P2 h y = eulerQuintic ((h-1)/2) y (-1) (1) := by
  dsimp [P2,eulerQuintic]
  linear_combination (-h^3/32 + h^2*(y/8 + 9/32) + h*(-y^2/8 - y - 27/32) - y^3/4 + 9*y^2/8 + 21*y/8 + 11/32)*hh

theorem normalized_quintic3 (h y : ℂ) (hh : h^2+3=0) :
    P3 h y = eulerQuintic ((h-1)/2) y (-1) (-1) := by
  dsimp [P3,eulerQuintic]
  linear_combination (-h^3/32 + h^2*(y/8 + 9/32) + h*(-y^2/8 - y - 27/32) - y^3/4 + 13*y^2/8 + 13*y/8 + 27/32)*hh

end CentralConfigurations.FiveBody.D2.Exceptional
