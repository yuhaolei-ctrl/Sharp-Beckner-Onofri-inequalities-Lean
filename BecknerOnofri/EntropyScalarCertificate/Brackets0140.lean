import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0350
import BecknerOnofri.EntropyScalarCertificate.Bessel0351
import BecknerOnofri.EntropyScalarCertificate.Bessel0352
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0140
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2240b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨0,by decide⟩
def lo2240b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨1,by decide⟩
def lo2240 : CheckedMoment :=
  CheckedMoment.ofBessel lo2240b1 lo2240b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2240b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨5,by decide⟩
def hi2240b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨6,by decide⟩
def hi2240 : CheckedMoment :=
  CheckedMoment.ofBessel hi2240b1 hi2240b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2240 : meanBracketCheck (4881/5000) lo2240 hi2240=true := by decide +kernel
def bracket2240 : MeanBracket := meanBracketOfMoments (4881/5000) lo2240 hi2240 accepted2240
def lo2241b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨10,by decide⟩
def lo2241b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨11,by decide⟩
def lo2241 : CheckedMoment :=
  CheckedMoment.ofBessel lo2241b1 lo2241b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2241b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨15,by decide⟩
def hi2241b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨16,by decide⟩
def hi2241 : CheckedMoment :=
  CheckedMoment.ofBessel hi2241b1 hi2241b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2241 : meanBracketCheck (9763/10000) lo2241 hi2241=true := by decide +kernel
def bracket2241 : MeanBracket := meanBracketOfMoments (9763/10000) lo2241 hi2241 accepted2241
def lo2242b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨20,by decide⟩
def lo2242b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨21,by decide⟩
def lo2242 : CheckedMoment :=
  CheckedMoment.ofBessel lo2242b1 lo2242b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2242b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨25,by decide⟩
def hi2242b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨26,by decide⟩
def hi2242 : CheckedMoment :=
  CheckedMoment.ofBessel hi2242b1 hi2242b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2242 : meanBracketCheck (2441/2500) lo2242 hi2242=true := by decide +kernel
def bracket2242 : MeanBracket := meanBracketOfMoments (2441/2500) lo2242 hi2242 accepted2242
def lo2243b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨30,by decide⟩
def lo2243b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨31,by decide⟩
def lo2243 : CheckedMoment :=
  CheckedMoment.ofBessel lo2243b1 lo2243b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2243b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨35,by decide⟩
def hi2243b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨36,by decide⟩
def hi2243 : CheckedMoment :=
  CheckedMoment.ofBessel hi2243b1 hi2243b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2243 : meanBracketCheck (1953/2000) lo2243 hi2243=true := by decide +kernel
def bracket2243 : MeanBracket := meanBracketOfMoments (1953/2000) lo2243 hi2243 accepted2243
def lo2244b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨40,by decide⟩
def lo2244b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨41,by decide⟩
def lo2244 : CheckedMoment :=
  CheckedMoment.ofBessel lo2244b1 lo2244b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2244b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨45,by decide⟩
def hi2244b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨46,by decide⟩
def hi2244 : CheckedMoment :=
  CheckedMoment.ofBessel hi2244b1 hi2244b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2244 : meanBracketCheck (4883/5000) lo2244 hi2244=true := by decide +kernel
def bracket2244 : MeanBracket := meanBracketOfMoments (4883/5000) lo2244 hi2244 accepted2244
def lo2245b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨50,by decide⟩
def lo2245b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨51,by decide⟩
def lo2245 : CheckedMoment :=
  CheckedMoment.ofBessel lo2245b1 lo2245b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2245b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨55,by decide⟩
def hi2245b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨56,by decide⟩
def hi2245 : CheckedMoment :=
  CheckedMoment.ofBessel hi2245b1 hi2245b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2245 : meanBracketCheck (9767/10000) lo2245 hi2245=true := by decide +kernel
def bracket2245 : MeanBracket := meanBracketOfMoments (9767/10000) lo2245 hi2245 accepted2245
def lo2246b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨60,by decide⟩
def lo2246b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨61,by decide⟩
def lo2246 : CheckedMoment :=
  CheckedMoment.ofBessel lo2246b1 lo2246b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2246b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨1,by decide⟩
def hi2246b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨2,by decide⟩
def hi2246 : CheckedMoment :=
  CheckedMoment.ofBessel hi2246b1 hi2246b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2246 : meanBracketCheck (1221/1250) lo2246 hi2246=true := by decide +kernel
def bracket2246 : MeanBracket := meanBracketOfMoments (1221/1250) lo2246 hi2246 accepted2246
def lo2247b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨6,by decide⟩
def lo2247b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨7,by decide⟩
def lo2247 : CheckedMoment :=
  CheckedMoment.ofBessel lo2247b1 lo2247b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2247b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨11,by decide⟩
def hi2247b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨12,by decide⟩
def hi2247 : CheckedMoment :=
  CheckedMoment.ofBessel hi2247b1 hi2247b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2247 : meanBracketCheck (9769/10000) lo2247 hi2247=true := by decide +kernel
def bracket2247 : MeanBracket := meanBracketOfMoments (9769/10000) lo2247 hi2247 accepted2247
def lo2248b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨16,by decide⟩
def lo2248b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨17,by decide⟩
def lo2248 : CheckedMoment :=
  CheckedMoment.ofBessel lo2248b1 lo2248b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2248b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨21,by decide⟩
def hi2248b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨22,by decide⟩
def hi2248 : CheckedMoment :=
  CheckedMoment.ofBessel hi2248b1 hi2248b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2248 : meanBracketCheck (977/1000) lo2248 hi2248=true := by decide +kernel
def bracket2248 : MeanBracket := meanBracketOfMoments (977/1000) lo2248 hi2248 accepted2248
def lo2249b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨26,by decide⟩
def lo2249b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨27,by decide⟩
def lo2249 : CheckedMoment :=
  CheckedMoment.ofBessel lo2249b1 lo2249b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2249b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨31,by decide⟩
def hi2249b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨32,by decide⟩
def hi2249 : CheckedMoment :=
  CheckedMoment.ofBessel hi2249b1 hi2249b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2249 : meanBracketCheck (9771/10000) lo2249 hi2249=true := by decide +kernel
def bracket2249 : MeanBracket := meanBracketOfMoments (9771/10000) lo2249 hi2249 accepted2249
def lo2250b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨36,by decide⟩
def lo2250b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨37,by decide⟩
def lo2250 : CheckedMoment :=
  CheckedMoment.ofBessel lo2250b1 lo2250b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2250b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨41,by decide⟩
def hi2250b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨42,by decide⟩
def hi2250 : CheckedMoment :=
  CheckedMoment.ofBessel hi2250b1 hi2250b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2250 : meanBracketCheck (2443/2500) lo2250 hi2250=true := by decide +kernel
def bracket2250 : MeanBracket := meanBracketOfMoments (2443/2500) lo2250 hi2250 accepted2250
def lo2251b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨46,by decide⟩
def lo2251b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨47,by decide⟩
def lo2251 : CheckedMoment :=
  CheckedMoment.ofBessel lo2251b1 lo2251b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2251b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨51,by decide⟩
def hi2251b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨52,by decide⟩
def hi2251 : CheckedMoment :=
  CheckedMoment.ofBessel hi2251b1 hi2251b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2251 : meanBracketCheck (9773/10000) lo2251 hi2251=true := by decide +kernel
def bracket2251 : MeanBracket := meanBracketOfMoments (9773/10000) lo2251 hi2251 accepted2251
def lo2252b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨56,by decide⟩
def lo2252b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨57,by decide⟩
def lo2252 : CheckedMoment :=
  CheckedMoment.ofBessel lo2252b1 lo2252b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2252b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨61,by decide⟩
def hi2252b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨62,by decide⟩
def hi2252 : CheckedMoment :=
  CheckedMoment.ofBessel hi2252b1 hi2252b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2252 : meanBracketCheck (4887/5000) lo2252 hi2252=true := by decide +kernel
def bracket2252 : MeanBracket := meanBracketOfMoments (4887/5000) lo2252 hi2252 accepted2252
def lo2253b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨2,by decide⟩
def lo2253b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨3,by decide⟩
def lo2253 : CheckedMoment :=
  CheckedMoment.ofBessel lo2253b1 lo2253b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2253b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨7,by decide⟩
def hi2253b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨8,by decide⟩
def hi2253 : CheckedMoment :=
  CheckedMoment.ofBessel hi2253b1 hi2253b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2253 : meanBracketCheck (391/400) lo2253 hi2253=true := by decide +kernel
def bracket2253 : MeanBracket := meanBracketOfMoments (391/400) lo2253 hi2253 accepted2253
def lo2254b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨12,by decide⟩
def lo2254b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨13,by decide⟩
def lo2254 : CheckedMoment :=
  CheckedMoment.ofBessel lo2254b1 lo2254b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2254b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨17,by decide⟩
def hi2254b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨18,by decide⟩
def hi2254 : CheckedMoment :=
  CheckedMoment.ofBessel hi2254b1 hi2254b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2254 : meanBracketCheck (611/625) lo2254 hi2254=true := by decide +kernel
def bracket2254 : MeanBracket := meanBracketOfMoments (611/625) lo2254 hi2254 accepted2254
def lo2255b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨22,by decide⟩
def lo2255b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨23,by decide⟩
def lo2255 : CheckedMoment :=
  CheckedMoment.ofBessel lo2255b1 lo2255b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2255b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨27,by decide⟩
def hi2255b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨28,by decide⟩
def hi2255 : CheckedMoment :=
  CheckedMoment.ofBessel hi2255b1 hi2255b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2255 : meanBracketCheck (9777/10000) lo2255 hi2255=true := by decide +kernel
def bracket2255 : MeanBracket := meanBracketOfMoments (9777/10000) lo2255 hi2255 accepted2255
#print axioms bracket2240
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0140
