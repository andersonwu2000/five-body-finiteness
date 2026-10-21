import CentralConfigurations.Enumeration.FiveBodyPairPart0
import CentralConfigurations.Enumeration.FiveBodyPairPart1
import CentralConfigurations.Enumeration.FiveBodyPairPart2
import CentralConfigurations.Enumeration.FiveBodyPairPart3
import CentralConfigurations.Enumeration.FiveBodyPairPart4

namespace CentralConfigurations.FiveBodyPairs

theorem all_rows_covered (a b : Fin 55)
    (hb : b.val ∈ (survivingRows[a.val]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair a b k).1 (inputPair a b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair a b k) := by
  by_cases h0 : a.val = 0
  · have ha : a = 0 := Fin.ext h0
    subst a
    exact row0_covered b hb k hc
  by_cases h1 : a.val = 1
  · have ha : a = 1 := Fin.ext h1
    subst a
    exact row1_covered b hb k hc
  by_cases h2 : a.val = 2
  · have ha : a = 2 := Fin.ext h2
    subst a
    exact row2_covered b hb k hc
  by_cases h3 : a.val = 3
  · have ha : a = 3 := Fin.ext h3
    subst a
    exact row3_covered b hb k hc
  by_cases h4 : a.val = 4
  · have ha : a = 4 := Fin.ext h4
    subst a
    exact row4_covered b hb k hc
  by_cases h5 : a.val = 5
  · have ha : a = 5 := Fin.ext h5
    subst a
    exact row5_covered b hb k hc
  by_cases h6 : a.val = 6
  · have ha : a = 6 := Fin.ext h6
    subst a
    exact row6_covered b hb k hc
  by_cases h7 : a.val = 7
  · have ha : a = 7 := Fin.ext h7
    subst a
    exact row7_covered b hb k hc
  by_cases h8 : a.val = 8
  · have ha : a = 8 := Fin.ext h8
    subst a
    exact row8_covered b hb k hc
  by_cases h9 : a.val = 9
  · have ha : a = 9 := Fin.ext h9
    subst a
    exact row9_covered b hb k hc
  by_cases h10 : a.val = 10
  · have ha : a = 10 := Fin.ext h10
    subst a
    exact row10_covered b hb k hc
  by_cases h11 : a.val = 11
  · have ha : a = 11 := Fin.ext h11
    subst a
    exact row11_covered b hb k hc
  by_cases h12 : a.val = 12
  · have ha : a = 12 := Fin.ext h12
    subst a
    exact row12_covered b hb k hc
  by_cases h13 : a.val = 13
  · have ha : a = 13 := Fin.ext h13
    subst a
    exact row13_covered b hb k hc
  by_cases h14 : a.val = 14
  · have ha : a = 14 := Fin.ext h14
    subst a
    exact row14_covered b hb k hc
  by_cases h15 : a.val = 15
  · have ha : a = 15 := Fin.ext h15
    subst a
    exact row15_covered b hb k hc
  by_cases h16 : a.val = 16
  · have ha : a = 16 := Fin.ext h16
    subst a
    exact row16_covered b hb k hc
  by_cases h17 : a.val = 17
  · have ha : a = 17 := Fin.ext h17
    subst a
    exact row17_covered b hb k hc
  by_cases h18 : a.val = 18
  · have ha : a = 18 := Fin.ext h18
    subst a
    exact row18_covered b hb k hc
  by_cases h19 : a.val = 19
  · have ha : a = 19 := Fin.ext h19
    subst a
    exact row19_covered b hb k hc
  by_cases h20 : a.val = 20
  · have ha : a = 20 := Fin.ext h20
    subst a
    exact row20_covered b hb k hc
  by_cases h21 : a.val = 21
  · have ha : a = 21 := Fin.ext h21
    subst a
    exact row21_covered b hb k hc
  by_cases h22 : a.val = 22
  · have ha : a = 22 := Fin.ext h22
    subst a
    exact row22_covered b hb k hc
  by_cases h23 : a.val = 23
  · have ha : a = 23 := Fin.ext h23
    subst a
    exact row23_covered b hb k hc
  by_cases h24 : a.val = 24
  · have ha : a = 24 := Fin.ext h24
    subst a
    exact row24_covered b hb k hc
  by_cases h25 : a.val = 25
  · have ha : a = 25 := Fin.ext h25
    subst a
    exact row25_covered b hb k hc
  by_cases h26 : a.val = 26
  · have ha : a = 26 := Fin.ext h26
    subst a
    exact row26_covered b hb k hc
  by_cases h27 : a.val = 27
  · have ha : a = 27 := Fin.ext h27
    subst a
    exact row27_covered b hb k hc
  by_cases h28 : a.val = 28
  · have ha : a = 28 := Fin.ext h28
    subst a
    exact row28_covered b hb k hc
  by_cases h29 : a.val = 29
  · have ha : a = 29 := Fin.ext h29
    subst a
    exact row29_covered b hb k hc
  by_cases h30 : a.val = 30
  · have ha : a = 30 := Fin.ext h30
    subst a
    exact row30_covered b hb k hc
  by_cases h31 : a.val = 31
  · have ha : a = 31 := Fin.ext h31
    subst a
    exact row31_covered b hb k hc
  by_cases h32 : a.val = 32
  · have ha : a = 32 := Fin.ext h32
    subst a
    exact row32_covered b hb k hc
  by_cases h33 : a.val = 33
  · have ha : a = 33 := Fin.ext h33
    subst a
    exact row33_covered b hb k hc
  by_cases h34 : a.val = 34
  · have ha : a = 34 := Fin.ext h34
    subst a
    exact row34_covered b hb k hc
  by_cases h35 : a.val = 35
  · have ha : a = 35 := Fin.ext h35
    subst a
    exact row35_covered b hb k hc
  by_cases h36 : a.val = 36
  · have ha : a = 36 := Fin.ext h36
    subst a
    exact row36_covered b hb k hc
  by_cases h37 : a.val = 37
  · have ha : a = 37 := Fin.ext h37
    subst a
    exact row37_covered b hb k hc
  by_cases h38 : a.val = 38
  · have ha : a = 38 := Fin.ext h38
    subst a
    exact row38_covered b hb k hc
  by_cases h39 : a.val = 39
  · have ha : a = 39 := Fin.ext h39
    subst a
    exact row39_covered b hb k hc
  by_cases h40 : a.val = 40
  · have ha : a = 40 := Fin.ext h40
    subst a
    exact row40_covered b hb k hc
  by_cases h41 : a.val = 41
  · have ha : a = 41 := Fin.ext h41
    subst a
    exact row41_covered b hb k hc
  by_cases h42 : a.val = 42
  · have ha : a = 42 := Fin.ext h42
    subst a
    exact row42_covered b hb k hc
  by_cases h43 : a.val = 43
  · have ha : a = 43 := Fin.ext h43
    subst a
    exact row43_covered b hb k hc
  by_cases h44 : a.val = 44
  · have ha : a = 44 := Fin.ext h44
    subst a
    exact row44_covered b hb k hc
  by_cases h45 : a.val = 45
  · have ha : a = 45 := Fin.ext h45
    subst a
    exact row45_covered b hb k hc
  by_cases h46 : a.val = 46
  · have ha : a = 46 := Fin.ext h46
    subst a
    exact row46_covered b hb k hc
  by_cases h47 : a.val = 47
  · have ha : a = 47 := Fin.ext h47
    subst a
    exact row47_covered b hb k hc
  by_cases h48 : a.val = 48
  · have ha : a = 48 := Fin.ext h48
    subst a
    exact row48_covered b hb k hc
  by_cases h49 : a.val = 49
  · have ha : a = 49 := Fin.ext h49
    subst a
    exact row49_covered b hb k hc
  by_cases h50 : a.val = 50
  · have ha : a = 50 := Fin.ext h50
    subst a
    exact row50_covered b hb k hc
  by_cases h51 : a.val = 51
  · have ha : a = 51 := Fin.ext h51
    subst a
    exact row51_covered b hb k hc
  by_cases h52 : a.val = 52
  · have ha : a = 52 := Fin.ext h52
    subst a
    exact row52_covered b hb k hc
  by_cases h53 : a.val = 53
  · have ha : a = 53 := Fin.ext h53
    subst a
    exact row53_covered b hb k hc
  have ha : a = 54 := Fin.ext (by omega)
  subst a
  exact row54_covered b hb k hc

end CentralConfigurations.FiveBodyPairs
