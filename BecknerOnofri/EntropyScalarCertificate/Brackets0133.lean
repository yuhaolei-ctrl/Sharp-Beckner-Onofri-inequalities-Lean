import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0332
import BecknerOnofri.EntropyScalarCertificate.Bessel0333
import BecknerOnofri.EntropyScalarCertificate.Bessel0334
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0133
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2128b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨32,by decide⟩
def lo2128b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨33,by decide⟩
def lo2128 : CheckedMoment :=
  CheckedMoment.ofBessel lo2128b1 lo2128b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2128b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨37,by decide⟩
def hi2128b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨38,by decide⟩
def hi2128 : CheckedMoment :=
  CheckedMoment.ofBessel hi2128b1 hi2128b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2128 : meanBracketCheck (193/200) lo2128 hi2128=true := by decide +kernel
def bracket2128 : MeanBracket := meanBracketOfMoments (193/200) lo2128 hi2128 accepted2128
def lo2129b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨42,by decide⟩
def lo2129b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨43,by decide⟩
def lo2129 : CheckedMoment :=
  CheckedMoment.ofBessel lo2129b1 lo2129b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2129b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨47,by decide⟩
def hi2129b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨48,by decide⟩
def hi2129 : CheckedMoment :=
  CheckedMoment.ofBessel hi2129b1 hi2129b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2129 : meanBracketCheck (9651/10000) lo2129 hi2129=true := by decide +kernel
def bracket2129 : MeanBracket := meanBracketOfMoments (9651/10000) lo2129 hi2129 accepted2129
def lo2130b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨52,by decide⟩
def lo2130b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨53,by decide⟩
def lo2130 : CheckedMoment :=
  CheckedMoment.ofBessel lo2130b1 lo2130b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2130b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨57,by decide⟩
def hi2130b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨58,by decide⟩
def hi2130 : CheckedMoment :=
  CheckedMoment.ofBessel hi2130b1 hi2130b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2130 : meanBracketCheck (2413/2500) lo2130 hi2130=true := by decide +kernel
def bracket2130 : MeanBracket := meanBracketOfMoments (2413/2500) lo2130 hi2130 accepted2130
def lo2131b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨62,by decide⟩
def lo2131b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨63,by decide⟩
def lo2131 : CheckedMoment :=
  CheckedMoment.ofBessel lo2131b1 lo2131b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2131b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨3,by decide⟩
def hi2131b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨4,by decide⟩
def hi2131 : CheckedMoment :=
  CheckedMoment.ofBessel hi2131b1 hi2131b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2131 : meanBracketCheck (9653/10000) lo2131 hi2131=true := by decide +kernel
def bracket2131 : MeanBracket := meanBracketOfMoments (9653/10000) lo2131 hi2131 accepted2131
def lo2132b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨8,by decide⟩
def lo2132b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨9,by decide⟩
def lo2132 : CheckedMoment :=
  CheckedMoment.ofBessel lo2132b1 lo2132b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2132b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨13,by decide⟩
def hi2132b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨14,by decide⟩
def hi2132 : CheckedMoment :=
  CheckedMoment.ofBessel hi2132b1 hi2132b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2132 : meanBracketCheck (4827/5000) lo2132 hi2132=true := by decide +kernel
def bracket2132 : MeanBracket := meanBracketOfMoments (4827/5000) lo2132 hi2132 accepted2132
def lo2133b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨18,by decide⟩
def lo2133b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨19,by decide⟩
def lo2133 : CheckedMoment :=
  CheckedMoment.ofBessel lo2133b1 lo2133b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2133b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨23,by decide⟩
def hi2133b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨24,by decide⟩
def hi2133 : CheckedMoment :=
  CheckedMoment.ofBessel hi2133b1 hi2133b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2133 : meanBracketCheck (1931/2000) lo2133 hi2133=true := by decide +kernel
def bracket2133 : MeanBracket := meanBracketOfMoments (1931/2000) lo2133 hi2133 accepted2133
def lo2134b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨28,by decide⟩
def lo2134b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨29,by decide⟩
def lo2134 : CheckedMoment :=
  CheckedMoment.ofBessel lo2134b1 lo2134b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2134b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨33,by decide⟩
def hi2134b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨34,by decide⟩
def hi2134 : CheckedMoment :=
  CheckedMoment.ofBessel hi2134b1 hi2134b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2134 : meanBracketCheck (1207/1250) lo2134 hi2134=true := by decide +kernel
def bracket2134 : MeanBracket := meanBracketOfMoments (1207/1250) lo2134 hi2134 accepted2134
def lo2135b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨38,by decide⟩
def lo2135b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨39,by decide⟩
def lo2135 : CheckedMoment :=
  CheckedMoment.ofBessel lo2135b1 lo2135b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2135b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨43,by decide⟩
def hi2135b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨44,by decide⟩
def hi2135 : CheckedMoment :=
  CheckedMoment.ofBessel hi2135b1 hi2135b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2135 : meanBracketCheck (9657/10000) lo2135 hi2135=true := by decide +kernel
def bracket2135 : MeanBracket := meanBracketOfMoments (9657/10000) lo2135 hi2135 accepted2135
def lo2136b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨48,by decide⟩
def lo2136b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨49,by decide⟩
def lo2136 : CheckedMoment :=
  CheckedMoment.ofBessel lo2136b1 lo2136b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2136b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨53,by decide⟩
def hi2136b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨54,by decide⟩
def hi2136 : CheckedMoment :=
  CheckedMoment.ofBessel hi2136b1 hi2136b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2136 : meanBracketCheck (4829/5000) lo2136 hi2136=true := by decide +kernel
def bracket2136 : MeanBracket := meanBracketOfMoments (4829/5000) lo2136 hi2136 accepted2136
def lo2137b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨58,by decide⟩
def lo2137b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨59,by decide⟩
def lo2137 : CheckedMoment :=
  CheckedMoment.ofBessel lo2137b1 lo2137b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2137b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨63,by decide⟩
def hi2137b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨0,by decide⟩
def hi2137 : CheckedMoment :=
  CheckedMoment.ofBessel hi2137b1 hi2137b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2137 : meanBracketCheck (9659/10000) lo2137 hi2137=true := by decide +kernel
def bracket2137 : MeanBracket := meanBracketOfMoments (9659/10000) lo2137 hi2137 accepted2137
def lo2138b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨4,by decide⟩
def lo2138b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨5,by decide⟩
def lo2138 : CheckedMoment :=
  CheckedMoment.ofBessel lo2138b1 lo2138b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2138b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨9,by decide⟩
def hi2138b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨10,by decide⟩
def hi2138 : CheckedMoment :=
  CheckedMoment.ofBessel hi2138b1 hi2138b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2138 : meanBracketCheck (483/500) lo2138 hi2138=true := by decide +kernel
def bracket2138 : MeanBracket := meanBracketOfMoments (483/500) lo2138 hi2138 accepted2138
def lo2139b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨14,by decide⟩
def lo2139b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨15,by decide⟩
def lo2139 : CheckedMoment :=
  CheckedMoment.ofBessel lo2139b1 lo2139b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2139b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨19,by decide⟩
def hi2139b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨20,by decide⟩
def hi2139 : CheckedMoment :=
  CheckedMoment.ofBessel hi2139b1 hi2139b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2139 : meanBracketCheck (9661/10000) lo2139 hi2139=true := by decide +kernel
def bracket2139 : MeanBracket := meanBracketOfMoments (9661/10000) lo2139 hi2139 accepted2139
def lo2140b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨24,by decide⟩
def lo2140b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨25,by decide⟩
def lo2140 : CheckedMoment :=
  CheckedMoment.ofBessel lo2140b1 lo2140b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2140b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨29,by decide⟩
def hi2140b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨30,by decide⟩
def hi2140 : CheckedMoment :=
  CheckedMoment.ofBessel hi2140b1 hi2140b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2140 : meanBracketCheck (4831/5000) lo2140 hi2140=true := by decide +kernel
def bracket2140 : MeanBracket := meanBracketOfMoments (4831/5000) lo2140 hi2140 accepted2140
def lo2141b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨34,by decide⟩
def lo2141b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨35,by decide⟩
def lo2141 : CheckedMoment :=
  CheckedMoment.ofBessel lo2141b1 lo2141b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2141b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨39,by decide⟩
def hi2141b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨40,by decide⟩
def hi2141 : CheckedMoment :=
  CheckedMoment.ofBessel hi2141b1 hi2141b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2141 : meanBracketCheck (9663/10000) lo2141 hi2141=true := by decide +kernel
def bracket2141 : MeanBracket := meanBracketOfMoments (9663/10000) lo2141 hi2141 accepted2141
def lo2142b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨44,by decide⟩
def lo2142b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨45,by decide⟩
def lo2142 : CheckedMoment :=
  CheckedMoment.ofBessel lo2142b1 lo2142b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2142b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨49,by decide⟩
def hi2142b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨50,by decide⟩
def hi2142 : CheckedMoment :=
  CheckedMoment.ofBessel hi2142b1 hi2142b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2142 : meanBracketCheck (604/625) lo2142 hi2142=true := by decide +kernel
def bracket2142 : MeanBracket := meanBracketOfMoments (604/625) lo2142 hi2142 accepted2142
def lo2143b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨54,by decide⟩
def lo2143b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨55,by decide⟩
def lo2143 : CheckedMoment :=
  CheckedMoment.ofBessel lo2143b1 lo2143b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2143b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨59,by decide⟩
def hi2143b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0334.rows BesselBatch0334.accepted ⟨60,by decide⟩
def hi2143 : CheckedMoment :=
  CheckedMoment.ofBessel hi2143b1 hi2143b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2143 : meanBracketCheck (1933/2000) lo2143 hi2143=true := by decide +kernel
def bracket2143 : MeanBracket := meanBracketOfMoments (1933/2000) lo2143 hi2143 accepted2143
#print axioms bracket2128
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0133
