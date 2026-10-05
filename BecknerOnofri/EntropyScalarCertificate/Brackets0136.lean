import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0340
import BecknerOnofri.EntropyScalarCertificate.Bessel0341
import BecknerOnofri.EntropyScalarCertificate.Bessel0342
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0136
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2176b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨0,by decide⟩
def lo2176b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨1,by decide⟩
def lo2176 : CheckedMoment :=
  CheckedMoment.ofBessel lo2176b1 lo2176b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2176b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨5,by decide⟩
def hi2176b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨6,by decide⟩
def hi2176 : CheckedMoment :=
  CheckedMoment.ofBessel hi2176b1 hi2176b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2176 : meanBracketCheck (4849/5000) lo2176 hi2176=true := by decide +kernel
def bracket2176 : MeanBracket := meanBracketOfMoments (4849/5000) lo2176 hi2176 accepted2176
def lo2177b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨10,by decide⟩
def lo2177b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨11,by decide⟩
def lo2177 : CheckedMoment :=
  CheckedMoment.ofBessel lo2177b1 lo2177b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2177b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨15,by decide⟩
def hi2177b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨16,by decide⟩
def hi2177 : CheckedMoment :=
  CheckedMoment.ofBessel hi2177b1 hi2177b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2177 : meanBracketCheck (9699/10000) lo2177 hi2177=true := by decide +kernel
def bracket2177 : MeanBracket := meanBracketOfMoments (9699/10000) lo2177 hi2177 accepted2177
def lo2178b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨20,by decide⟩
def lo2178b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨21,by decide⟩
def lo2178 : CheckedMoment :=
  CheckedMoment.ofBessel lo2178b1 lo2178b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2178b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨25,by decide⟩
def hi2178b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨26,by decide⟩
def hi2178 : CheckedMoment :=
  CheckedMoment.ofBessel hi2178b1 hi2178b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2178 : meanBracketCheck (97/100) lo2178 hi2178=true := by decide +kernel
def bracket2178 : MeanBracket := meanBracketOfMoments (97/100) lo2178 hi2178 accepted2178
def lo2179b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨30,by decide⟩
def lo2179b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨31,by decide⟩
def lo2179 : CheckedMoment :=
  CheckedMoment.ofBessel lo2179b1 lo2179b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2179b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨35,by decide⟩
def hi2179b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨36,by decide⟩
def hi2179 : CheckedMoment :=
  CheckedMoment.ofBessel hi2179b1 hi2179b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2179 : meanBracketCheck (9701/10000) lo2179 hi2179=true := by decide +kernel
def bracket2179 : MeanBracket := meanBracketOfMoments (9701/10000) lo2179 hi2179 accepted2179
def lo2180b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨40,by decide⟩
def lo2180b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨41,by decide⟩
def lo2180 : CheckedMoment :=
  CheckedMoment.ofBessel lo2180b1 lo2180b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2180b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨45,by decide⟩
def hi2180b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨46,by decide⟩
def hi2180 : CheckedMoment :=
  CheckedMoment.ofBessel hi2180b1 hi2180b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2180 : meanBracketCheck (4851/5000) lo2180 hi2180=true := by decide +kernel
def bracket2180 : MeanBracket := meanBracketOfMoments (4851/5000) lo2180 hi2180 accepted2180
def lo2181b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨50,by decide⟩
def lo2181b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨51,by decide⟩
def lo2181 : CheckedMoment :=
  CheckedMoment.ofBessel lo2181b1 lo2181b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2181b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨55,by decide⟩
def hi2181b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨56,by decide⟩
def hi2181 : CheckedMoment :=
  CheckedMoment.ofBessel hi2181b1 hi2181b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2181 : meanBracketCheck (9703/10000) lo2181 hi2181=true := by decide +kernel
def bracket2181 : MeanBracket := meanBracketOfMoments (9703/10000) lo2181 hi2181 accepted2181
def lo2182b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨60,by decide⟩
def lo2182b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨61,by decide⟩
def lo2182 : CheckedMoment :=
  CheckedMoment.ofBessel lo2182b1 lo2182b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2182b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨1,by decide⟩
def hi2182b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨2,by decide⟩
def hi2182 : CheckedMoment :=
  CheckedMoment.ofBessel hi2182b1 hi2182b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2182 : meanBracketCheck (1213/1250) lo2182 hi2182=true := by decide +kernel
def bracket2182 : MeanBracket := meanBracketOfMoments (1213/1250) lo2182 hi2182 accepted2182
def lo2183b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨6,by decide⟩
def lo2183b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨7,by decide⟩
def lo2183 : CheckedMoment :=
  CheckedMoment.ofBessel lo2183b1 lo2183b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2183b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨11,by decide⟩
def hi2183b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨12,by decide⟩
def hi2183 : CheckedMoment :=
  CheckedMoment.ofBessel hi2183b1 hi2183b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2183 : meanBracketCheck (1941/2000) lo2183 hi2183=true := by decide +kernel
def bracket2183 : MeanBracket := meanBracketOfMoments (1941/2000) lo2183 hi2183 accepted2183
def lo2184b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨16,by decide⟩
def lo2184b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨17,by decide⟩
def lo2184 : CheckedMoment :=
  CheckedMoment.ofBessel lo2184b1 lo2184b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2184b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨21,by decide⟩
def hi2184b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨22,by decide⟩
def hi2184 : CheckedMoment :=
  CheckedMoment.ofBessel hi2184b1 hi2184b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2184 : meanBracketCheck (4853/5000) lo2184 hi2184=true := by decide +kernel
def bracket2184 : MeanBracket := meanBracketOfMoments (4853/5000) lo2184 hi2184 accepted2184
def lo2185b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨26,by decide⟩
def lo2185b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨27,by decide⟩
def lo2185 : CheckedMoment :=
  CheckedMoment.ofBessel lo2185b1 lo2185b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2185b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨31,by decide⟩
def hi2185b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨32,by decide⟩
def hi2185 : CheckedMoment :=
  CheckedMoment.ofBessel hi2185b1 hi2185b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2185 : meanBracketCheck (9707/10000) lo2185 hi2185=true := by decide +kernel
def bracket2185 : MeanBracket := meanBracketOfMoments (9707/10000) lo2185 hi2185 accepted2185
def lo2186b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨36,by decide⟩
def lo2186b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨37,by decide⟩
def lo2186 : CheckedMoment :=
  CheckedMoment.ofBessel lo2186b1 lo2186b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2186b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨41,by decide⟩
def hi2186b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨42,by decide⟩
def hi2186 : CheckedMoment :=
  CheckedMoment.ofBessel hi2186b1 hi2186b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2186 : meanBracketCheck (2427/2500) lo2186 hi2186=true := by decide +kernel
def bracket2186 : MeanBracket := meanBracketOfMoments (2427/2500) lo2186 hi2186 accepted2186
def lo2187b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨46,by decide⟩
def lo2187b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨47,by decide⟩
def lo2187 : CheckedMoment :=
  CheckedMoment.ofBessel lo2187b1 lo2187b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2187b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨51,by decide⟩
def hi2187b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨52,by decide⟩
def hi2187 : CheckedMoment :=
  CheckedMoment.ofBessel hi2187b1 hi2187b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2187 : meanBracketCheck (9709/10000) lo2187 hi2187=true := by decide +kernel
def bracket2187 : MeanBracket := meanBracketOfMoments (9709/10000) lo2187 hi2187 accepted2187
def lo2188b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨56,by decide⟩
def lo2188b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨57,by decide⟩
def lo2188 : CheckedMoment :=
  CheckedMoment.ofBessel lo2188b1 lo2188b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2188b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨61,by decide⟩
def hi2188b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨62,by decide⟩
def hi2188 : CheckedMoment :=
  CheckedMoment.ofBessel hi2188b1 hi2188b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2188 : meanBracketCheck (971/1000) lo2188 hi2188=true := by decide +kernel
def bracket2188 : MeanBracket := meanBracketOfMoments (971/1000) lo2188 hi2188 accepted2188
def lo2189b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨2,by decide⟩
def lo2189b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨3,by decide⟩
def lo2189 : CheckedMoment :=
  CheckedMoment.ofBessel lo2189b1 lo2189b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2189b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨7,by decide⟩
def hi2189b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨8,by decide⟩
def hi2189 : CheckedMoment :=
  CheckedMoment.ofBessel hi2189b1 hi2189b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2189 : meanBracketCheck (9711/10000) lo2189 hi2189=true := by decide +kernel
def bracket2189 : MeanBracket := meanBracketOfMoments (9711/10000) lo2189 hi2189 accepted2189
def lo2190b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨12,by decide⟩
def lo2190b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨13,by decide⟩
def lo2190 : CheckedMoment :=
  CheckedMoment.ofBessel lo2190b1 lo2190b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2190b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨17,by decide⟩
def hi2190b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨18,by decide⟩
def hi2190 : CheckedMoment :=
  CheckedMoment.ofBessel hi2190b1 hi2190b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2190 : meanBracketCheck (607/625) lo2190 hi2190=true := by decide +kernel
def bracket2190 : MeanBracket := meanBracketOfMoments (607/625) lo2190 hi2190 accepted2190
def lo2191b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨22,by decide⟩
def lo2191b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨23,by decide⟩
def lo2191 : CheckedMoment :=
  CheckedMoment.ofBessel lo2191b1 lo2191b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2191b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨27,by decide⟩
def hi2191b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨28,by decide⟩
def hi2191 : CheckedMoment :=
  CheckedMoment.ofBessel hi2191b1 hi2191b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2191 : meanBracketCheck (9713/10000) lo2191 hi2191=true := by decide +kernel
def bracket2191 : MeanBracket := meanBracketOfMoments (9713/10000) lo2191 hi2191 accepted2191
#print axioms bracket2176
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0136
