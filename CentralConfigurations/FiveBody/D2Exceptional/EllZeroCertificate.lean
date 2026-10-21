import Mathlib.Tactic

namespace CentralConfigurations.FiveBody.D2.Exceptional
set_option maxHeartbeats 2000000

def GapP0 (a b c x : ℂ) : ℂ := -a*x^5 + 2*a*x^4 - a*x^3 + a*x^2 - 2*a*x + a - b*x^5 + 3*b*x^4 - 3*b*x^3 + 2*b*x^2 + 3*c*x^2 - 3*c*x + c
def GapQ0 (a b c x : ℂ) : ℂ := a*x^3 - 3*a*x^2 + 3*a*x - a + b*x^3 + 4*c*x^3 - 6*c*x^2 + 4*c*x - c
def RankK0 (x : ℂ) : ℂ := 2*x^2 - x + 1

theorem rank_identity0 (a b c x : ℂ) :
    (2*x^5 - 6*x^4 + 6*x^3 - 2*x^2)*RankK0 x*(a+b+c) = (-3*x^2 + 3*x - 1)*GapP0 a b c x+(x^4 - 2*x^3 + x^2 + 2*x - 1)*GapQ0 a b c x := by
  dsimp [RankK0,GapP0,GapQ0]
  ring

theorem Q_reduction0 (a b c x : ℂ) (hk : RankK0 x=0) :
    GapQ0 a b c x = a/4 - b/4 + c + x*(5*a/4 - b/4) := by
  dsimp [RankK0] at hk
  dsimp [GapQ0]
  linear_combination (-5*a/4 + b/4 - 2*c + x*(a/2 + b/2 + 2*c))*hk

def GapP1 (a b c x : ℂ) : ℂ := -a*x^5 + 2*a*x^4 - a*x^3 + a*x^2 - 2*a*x + a - b*x^5 + 3*b*x^4 - 3*b*x^3 - 2*c*x^3 + 3*c*x^2 - 3*c*x + c
def GapQ1 (a b c x : ℂ) : ℂ := a*x^3 - 3*a*x^2 + 3*a*x - a - b*x^3 - 2*c*x^4 + 4*c*x^3 - 6*c*x^2 + 4*c*x - c
def RankK1 (x : ℂ) : ℂ := x^2 - x + 2

theorem rank_identity1 (a b c x : ℂ) :
    (2*x^6 - 6*x^5 + 6*x^4 - 2*x^3)*RankK1 x*(a+b+c) = (-2*x^3 + 3*x^2 - 3*x + 1)*GapP1 a b c x+(-x^4 + 2*x^3 + x^2 - 2*x + 1)*GapQ1 a b c x := by
  dsimp [RankK1,GapP1,GapQ1]
  ring

theorem Q_reduction1 (a b c x : ℂ) (hk : RankK1 x=0) :
    GapQ1 a b c x = 3*a + 2*b - c + x*(-a + b) := by
  dsimp [RankK1] at hk
  dsimp [GapQ1]
  linear_combination (-2*a - b - 2*c*x^2 + x*(a - b + 2*c))*hk

def GapP2 (a b c x : ℂ) : ℂ := -a*x^5 + 2*a*x^4 - a*x^3 - a*x^2 + 2*a*x - a - b*x^5 + 3*b*x^4 - 3*b*x^3 + 2*b*x^2 + 2*c*x^3 - 3*c*x^2 + 3*c*x - c
def GapQ2 (a b c x : ℂ) : ℂ := -a*x^3 + 3*a*x^2 - 3*a*x + a + b*x^3 + 2*c*x^4 - 4*c*x^3 + 6*c*x^2 - 4*c*x + c
def RankK2 (x : ℂ) : ℂ := x^2 - x + 1

theorem rank_identity2 (a b c x : ℂ) :
    (2*x^4 - 4*x^3 + 2*x^2)*RankK2 x*(a+b+c) = (1 - 2*x)*GapP2 a b c x+(x^2 - x + 1)*GapQ2 a b c x := by
  dsimp [RankK2,GapP2,GapQ2]
  ring

theorem Q_reduction2 (a b c x : ℂ) (hk : RankK2 x=0) :
    GapQ2 a b c x = -a - b - c := by
  dsimp [RankK2] at hk
  dsimp [GapQ2]
  linear_combination (2*a + b + 2*c*x^2 + 2*c + x*(-a + b - 2*c))*hk

def GapP3 (a b c x : ℂ) : ℂ := -a*x^5 + 2*a*x^4 - a*x^3 - a*x^2 + 2*a*x - a - b*x^5 + 3*b*x^4 - 3*b*x^3 - 3*c*x^2 + 3*c*x - c
def GapQ3 (a b c x : ℂ) : ℂ := -a*x^3 + 3*a*x^2 - 3*a*x + a - b*x^3 - 4*c*x^3 + 6*c*x^2 - 4*c*x + c
def RankK3 (x : ℂ) : ℂ := 2*x^2 - 3*x + 2

theorem rank_identity3 (a b c x : ℂ) :
    (2*x^5 - 4*x^4 + 2*x^3)*RankK3 x*(a+b+c) = (-3*x^2 + 3*x - 1)*GapP3 a b c x+(-x^4 + 2*x^3 - x^2 + 2*x - 1)*GapQ3 a b c x := by
  dsimp [RankK3,GapP3,GapQ3]
  ring

theorem Q_reduction3 (a b c x : ℂ) (hk : RankK3 x=0) :
    GapQ3 a b c x = -a/2 + 3*b/2 + c + x*(a/4 - 5*b/4) := by
  dsimp [RankK3] at hk
  dsimp [GapQ3]
  linear_combination (3*a/4 - 3*b/4 + x*(-a/2 - b/2 - 2*c))*hk

end CentralConfigurations.FiveBody.D2.Exceptional
