module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0330
public import BecknerOnofri.EntropyScalarCertificate.Bessel0331
public import BecknerOnofri.EntropyScalarCertificate.Bessel0332

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0132
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2112b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨0,by decide⟩
def lo2112b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨1,by decide⟩
def lo2112 : CheckedMoment :=
  CheckedMoment.ofBessel lo2112b1 lo2112b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2112b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨5,by decide⟩
def hi2112b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨6,by decide⟩
def hi2112 : CheckedMoment :=
  CheckedMoment.ofBessel hi2112b1 hi2112b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2112 : meanBracketCheck (4817/5000) lo2112 hi2112=true := by decide +kernel
def bracket2112 : MeanBracket := meanBracketOfMoments (4817/5000) lo2112 hi2112 accepted2112
def lo2113b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨10,by decide⟩
def lo2113b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨11,by decide⟩
def lo2113 : CheckedMoment :=
  CheckedMoment.ofBessel lo2113b1 lo2113b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2113b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨15,by decide⟩
def hi2113b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨16,by decide⟩
def hi2113 : CheckedMoment :=
  CheckedMoment.ofBessel hi2113b1 hi2113b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2113 : meanBracketCheck (1927/2000) lo2113 hi2113=true := by decide +kernel
def bracket2113 : MeanBracket := meanBracketOfMoments (1927/2000) lo2113 hi2113 accepted2113
def lo2114b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨20,by decide⟩
def lo2114b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨21,by decide⟩
def lo2114 : CheckedMoment :=
  CheckedMoment.ofBessel lo2114b1 lo2114b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2114b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨25,by decide⟩
def hi2114b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨26,by decide⟩
def hi2114 : CheckedMoment :=
  CheckedMoment.ofBessel hi2114b1 hi2114b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2114 : meanBracketCheck (2409/2500) lo2114 hi2114=true := by decide +kernel
def bracket2114 : MeanBracket := meanBracketOfMoments (2409/2500) lo2114 hi2114 accepted2114
def lo2115b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨30,by decide⟩
def lo2115b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨31,by decide⟩
def lo2115 : CheckedMoment :=
  CheckedMoment.ofBessel lo2115b1 lo2115b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2115b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨35,by decide⟩
def hi2115b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨36,by decide⟩
def hi2115 : CheckedMoment :=
  CheckedMoment.ofBessel hi2115b1 hi2115b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2115 : meanBracketCheck (9637/10000) lo2115 hi2115=true := by decide +kernel
def bracket2115 : MeanBracket := meanBracketOfMoments (9637/10000) lo2115 hi2115 accepted2115
def lo2116b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨40,by decide⟩
def lo2116b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨41,by decide⟩
def lo2116 : CheckedMoment :=
  CheckedMoment.ofBessel lo2116b1 lo2116b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2116b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨45,by decide⟩
def hi2116b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨46,by decide⟩
def hi2116 : CheckedMoment :=
  CheckedMoment.ofBessel hi2116b1 hi2116b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2116 : meanBracketCheck (4819/5000) lo2116 hi2116=true := by decide +kernel
def bracket2116 : MeanBracket := meanBracketOfMoments (4819/5000) lo2116 hi2116 accepted2116
def lo2117b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨50,by decide⟩
def lo2117b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨51,by decide⟩
def lo2117 : CheckedMoment :=
  CheckedMoment.ofBessel lo2117b1 lo2117b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2117b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨55,by decide⟩
def hi2117b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨56,by decide⟩
def hi2117 : CheckedMoment :=
  CheckedMoment.ofBessel hi2117b1 hi2117b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2117 : meanBracketCheck (9639/10000) lo2117 hi2117=true := by decide +kernel
def bracket2117 : MeanBracket := meanBracketOfMoments (9639/10000) lo2117 hi2117 accepted2117
def lo2118b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨60,by decide⟩
def lo2118b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨61,by decide⟩
def lo2118 : CheckedMoment :=
  CheckedMoment.ofBessel lo2118b1 lo2118b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2118b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨1,by decide⟩
def hi2118b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨2,by decide⟩
def hi2118 : CheckedMoment :=
  CheckedMoment.ofBessel hi2118b1 hi2118b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2118 : meanBracketCheck (241/250) lo2118 hi2118=true := by decide +kernel
def bracket2118 : MeanBracket := meanBracketOfMoments (241/250) lo2118 hi2118 accepted2118
def lo2119b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨6,by decide⟩
def lo2119b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨7,by decide⟩
def lo2119 : CheckedMoment :=
  CheckedMoment.ofBessel lo2119b1 lo2119b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2119b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨11,by decide⟩
def hi2119b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨12,by decide⟩
def hi2119 : CheckedMoment :=
  CheckedMoment.ofBessel hi2119b1 hi2119b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2119 : meanBracketCheck (9641/10000) lo2119 hi2119=true := by decide +kernel
def bracket2119 : MeanBracket := meanBracketOfMoments (9641/10000) lo2119 hi2119 accepted2119
def lo2120b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨16,by decide⟩
def lo2120b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨17,by decide⟩
def lo2120 : CheckedMoment :=
  CheckedMoment.ofBessel lo2120b1 lo2120b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2120b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨21,by decide⟩
def hi2120b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨22,by decide⟩
def hi2120 : CheckedMoment :=
  CheckedMoment.ofBessel hi2120b1 hi2120b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2120 : meanBracketCheck (4821/5000) lo2120 hi2120=true := by decide +kernel
def bracket2120 : MeanBracket := meanBracketOfMoments (4821/5000) lo2120 hi2120 accepted2120
def lo2121b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨26,by decide⟩
def lo2121b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨27,by decide⟩
def lo2121 : CheckedMoment :=
  CheckedMoment.ofBessel lo2121b1 lo2121b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2121b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨31,by decide⟩
def hi2121b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨32,by decide⟩
def hi2121 : CheckedMoment :=
  CheckedMoment.ofBessel hi2121b1 hi2121b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2121 : meanBracketCheck (9643/10000) lo2121 hi2121=true := by decide +kernel
def bracket2121 : MeanBracket := meanBracketOfMoments (9643/10000) lo2121 hi2121 accepted2121
def lo2122b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨36,by decide⟩
def lo2122b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨37,by decide⟩
def lo2122 : CheckedMoment :=
  CheckedMoment.ofBessel lo2122b1 lo2122b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2122b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨41,by decide⟩
def hi2122b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨42,by decide⟩
def hi2122 : CheckedMoment :=
  CheckedMoment.ofBessel hi2122b1 hi2122b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2122 : meanBracketCheck (2411/2500) lo2122 hi2122=true := by decide +kernel
def bracket2122 : MeanBracket := meanBracketOfMoments (2411/2500) lo2122 hi2122 accepted2122
def lo2123b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨46,by decide⟩
def lo2123b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨47,by decide⟩
def lo2123 : CheckedMoment :=
  CheckedMoment.ofBessel lo2123b1 lo2123b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2123b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨51,by decide⟩
def hi2123b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨52,by decide⟩
def hi2123 : CheckedMoment :=
  CheckedMoment.ofBessel hi2123b1 hi2123b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2123 : meanBracketCheck (1929/2000) lo2123 hi2123=true := by decide +kernel
def bracket2123 : MeanBracket := meanBracketOfMoments (1929/2000) lo2123 hi2123 accepted2123
def lo2124b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨56,by decide⟩
def lo2124b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨57,by decide⟩
def lo2124 : CheckedMoment :=
  CheckedMoment.ofBessel lo2124b1 lo2124b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2124b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨61,by decide⟩
def hi2124b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨62,by decide⟩
def hi2124 : CheckedMoment :=
  CheckedMoment.ofBessel hi2124b1 hi2124b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2124 : meanBracketCheck (4823/5000) lo2124 hi2124=true := by decide +kernel
def bracket2124 : MeanBracket := meanBracketOfMoments (4823/5000) lo2124 hi2124 accepted2124
def lo2125b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨2,by decide⟩
def lo2125b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨3,by decide⟩
def lo2125 : CheckedMoment :=
  CheckedMoment.ofBessel lo2125b1 lo2125b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2125b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨7,by decide⟩
def hi2125b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨8,by decide⟩
def hi2125 : CheckedMoment :=
  CheckedMoment.ofBessel hi2125b1 hi2125b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2125 : meanBracketCheck (9647/10000) lo2125 hi2125=true := by decide +kernel
def bracket2125 : MeanBracket := meanBracketOfMoments (9647/10000) lo2125 hi2125 accepted2125
def lo2126b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨12,by decide⟩
def lo2126b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨13,by decide⟩
def lo2126 : CheckedMoment :=
  CheckedMoment.ofBessel lo2126b1 lo2126b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2126b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨17,by decide⟩
def hi2126b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨18,by decide⟩
def hi2126 : CheckedMoment :=
  CheckedMoment.ofBessel hi2126b1 hi2126b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2126 : meanBracketCheck (603/625) lo2126 hi2126=true := by decide +kernel
def bracket2126 : MeanBracket := meanBracketOfMoments (603/625) lo2126 hi2126 accepted2126
def lo2127b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨22,by decide⟩
def lo2127b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨23,by decide⟩
def lo2127 : CheckedMoment :=
  CheckedMoment.ofBessel lo2127b1 lo2127b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2127b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨27,by decide⟩
def hi2127b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨28,by decide⟩
def hi2127 : CheckedMoment :=
  CheckedMoment.ofBessel hi2127b1 hi2127b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2127 : meanBracketCheck (9649/10000) lo2127 hi2127=true := by decide +kernel
def bracket2127 : MeanBracket := meanBracketOfMoments (9649/10000) lo2127 hi2127 accepted2127
#print axioms bracket2112
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0132
