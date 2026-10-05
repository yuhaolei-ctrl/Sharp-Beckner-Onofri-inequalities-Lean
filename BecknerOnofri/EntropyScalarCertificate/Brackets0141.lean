module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0352
public import BecknerOnofri.EntropyScalarCertificate.Bessel0353
public import BecknerOnofri.EntropyScalarCertificate.Bessel0354

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0141
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2256b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨32,by decide⟩
def lo2256b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨33,by decide⟩
def lo2256 : CheckedMoment :=
  CheckedMoment.ofBessel lo2256b1 lo2256b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2256b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨37,by decide⟩
def hi2256b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨38,by decide⟩
def hi2256 : CheckedMoment :=
  CheckedMoment.ofBessel hi2256b1 hi2256b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2256 : meanBracketCheck (4889/5000) lo2256 hi2256=true := by decide +kernel
def bracket2256 : MeanBracket := meanBracketOfMoments (4889/5000) lo2256 hi2256 accepted2256
def lo2257b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨42,by decide⟩
def lo2257b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨43,by decide⟩
def lo2257 : CheckedMoment :=
  CheckedMoment.ofBessel lo2257b1 lo2257b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2257b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨47,by decide⟩
def hi2257b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨48,by decide⟩
def hi2257 : CheckedMoment :=
  CheckedMoment.ofBessel hi2257b1 hi2257b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2257 : meanBracketCheck (9779/10000) lo2257 hi2257=true := by decide +kernel
def bracket2257 : MeanBracket := meanBracketOfMoments (9779/10000) lo2257 hi2257 accepted2257
def lo2258b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨52,by decide⟩
def lo2258b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨53,by decide⟩
def lo2258 : CheckedMoment :=
  CheckedMoment.ofBessel lo2258b1 lo2258b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2258b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨57,by decide⟩
def hi2258b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨58,by decide⟩
def hi2258 : CheckedMoment :=
  CheckedMoment.ofBessel hi2258b1 hi2258b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2258 : meanBracketCheck (489/500) lo2258 hi2258=true := by decide +kernel
def bracket2258 : MeanBracket := meanBracketOfMoments (489/500) lo2258 hi2258 accepted2258
def lo2259b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨62,by decide⟩
def lo2259b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨63,by decide⟩
def lo2259 : CheckedMoment :=
  CheckedMoment.ofBessel lo2259b1 lo2259b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2259b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨3,by decide⟩
def hi2259b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨4,by decide⟩
def hi2259 : CheckedMoment :=
  CheckedMoment.ofBessel hi2259b1 hi2259b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2259 : meanBracketCheck (9781/10000) lo2259 hi2259=true := by decide +kernel
def bracket2259 : MeanBracket := meanBracketOfMoments (9781/10000) lo2259 hi2259 accepted2259
def lo2260b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨8,by decide⟩
def lo2260b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨9,by decide⟩
def lo2260 : CheckedMoment :=
  CheckedMoment.ofBessel lo2260b1 lo2260b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2260b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨13,by decide⟩
def hi2260b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨14,by decide⟩
def hi2260 : CheckedMoment :=
  CheckedMoment.ofBessel hi2260b1 hi2260b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2260 : meanBracketCheck (4891/5000) lo2260 hi2260=true := by decide +kernel
def bracket2260 : MeanBracket := meanBracketOfMoments (4891/5000) lo2260 hi2260 accepted2260
def lo2261b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨18,by decide⟩
def lo2261b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨19,by decide⟩
def lo2261 : CheckedMoment :=
  CheckedMoment.ofBessel lo2261b1 lo2261b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2261b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨23,by decide⟩
def hi2261b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨24,by decide⟩
def hi2261 : CheckedMoment :=
  CheckedMoment.ofBessel hi2261b1 hi2261b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2261 : meanBracketCheck (9783/10000) lo2261 hi2261=true := by decide +kernel
def bracket2261 : MeanBracket := meanBracketOfMoments (9783/10000) lo2261 hi2261 accepted2261
def lo2262b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨28,by decide⟩
def lo2262b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨29,by decide⟩
def lo2262 : CheckedMoment :=
  CheckedMoment.ofBessel lo2262b1 lo2262b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2262b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨33,by decide⟩
def hi2262b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨34,by decide⟩
def hi2262 : CheckedMoment :=
  CheckedMoment.ofBessel hi2262b1 hi2262b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2262 : meanBracketCheck (1223/1250) lo2262 hi2262=true := by decide +kernel
def bracket2262 : MeanBracket := meanBracketOfMoments (1223/1250) lo2262 hi2262 accepted2262
def lo2263b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨38,by decide⟩
def lo2263b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨39,by decide⟩
def lo2263 : CheckedMoment :=
  CheckedMoment.ofBessel lo2263b1 lo2263b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2263b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨43,by decide⟩
def hi2263b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨44,by decide⟩
def hi2263 : CheckedMoment :=
  CheckedMoment.ofBessel hi2263b1 hi2263b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2263 : meanBracketCheck (1957/2000) lo2263 hi2263=true := by decide +kernel
def bracket2263 : MeanBracket := meanBracketOfMoments (1957/2000) lo2263 hi2263 accepted2263
def lo2264b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨48,by decide⟩
def lo2264b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨49,by decide⟩
def lo2264 : CheckedMoment :=
  CheckedMoment.ofBessel lo2264b1 lo2264b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2264b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨53,by decide⟩
def hi2264b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨54,by decide⟩
def hi2264 : CheckedMoment :=
  CheckedMoment.ofBessel hi2264b1 hi2264b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2264 : meanBracketCheck (4893/5000) lo2264 hi2264=true := by decide +kernel
def bracket2264 : MeanBracket := meanBracketOfMoments (4893/5000) lo2264 hi2264 accepted2264
def lo2265b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨58,by decide⟩
def lo2265b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨59,by decide⟩
def lo2265 : CheckedMoment :=
  CheckedMoment.ofBessel lo2265b1 lo2265b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2265b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨63,by decide⟩
def hi2265b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨0,by decide⟩
def hi2265 : CheckedMoment :=
  CheckedMoment.ofBessel hi2265b1 hi2265b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2265 : meanBracketCheck (9787/10000) lo2265 hi2265=true := by decide +kernel
def bracket2265 : MeanBracket := meanBracketOfMoments (9787/10000) lo2265 hi2265 accepted2265
def lo2266b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨4,by decide⟩
def lo2266b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨5,by decide⟩
def lo2266 : CheckedMoment :=
  CheckedMoment.ofBessel lo2266b1 lo2266b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2266b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨9,by decide⟩
def hi2266b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨10,by decide⟩
def hi2266 : CheckedMoment :=
  CheckedMoment.ofBessel hi2266b1 hi2266b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2266 : meanBracketCheck (2447/2500) lo2266 hi2266=true := by decide +kernel
def bracket2266 : MeanBracket := meanBracketOfMoments (2447/2500) lo2266 hi2266 accepted2266
def lo2267b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨14,by decide⟩
def lo2267b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨15,by decide⟩
def lo2267 : CheckedMoment :=
  CheckedMoment.ofBessel lo2267b1 lo2267b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2267b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨19,by decide⟩
def hi2267b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨20,by decide⟩
def hi2267 : CheckedMoment :=
  CheckedMoment.ofBessel hi2267b1 hi2267b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2267 : meanBracketCheck (9789/10000) lo2267 hi2267=true := by decide +kernel
def bracket2267 : MeanBracket := meanBracketOfMoments (9789/10000) lo2267 hi2267 accepted2267
def lo2268b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨24,by decide⟩
def lo2268b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨25,by decide⟩
def lo2268 : CheckedMoment :=
  CheckedMoment.ofBessel lo2268b1 lo2268b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2268b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨29,by decide⟩
def hi2268b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨30,by decide⟩
def hi2268 : CheckedMoment :=
  CheckedMoment.ofBessel hi2268b1 hi2268b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2268 : meanBracketCheck (979/1000) lo2268 hi2268=true := by decide +kernel
def bracket2268 : MeanBracket := meanBracketOfMoments (979/1000) lo2268 hi2268 accepted2268
def lo2269b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨34,by decide⟩
def lo2269b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨35,by decide⟩
def lo2269 : CheckedMoment :=
  CheckedMoment.ofBessel lo2269b1 lo2269b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2269b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨39,by decide⟩
def hi2269b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨40,by decide⟩
def hi2269 : CheckedMoment :=
  CheckedMoment.ofBessel hi2269b1 hi2269b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2269 : meanBracketCheck (9791/10000) lo2269 hi2269=true := by decide +kernel
def bracket2269 : MeanBracket := meanBracketOfMoments (9791/10000) lo2269 hi2269 accepted2269
def lo2270b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨44,by decide⟩
def lo2270b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨45,by decide⟩
def lo2270 : CheckedMoment :=
  CheckedMoment.ofBessel lo2270b1 lo2270b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2270b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨49,by decide⟩
def hi2270b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨50,by decide⟩
def hi2270 : CheckedMoment :=
  CheckedMoment.ofBessel hi2270b1 hi2270b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2270 : meanBracketCheck (612/625) lo2270 hi2270=true := by decide +kernel
def bracket2270 : MeanBracket := meanBracketOfMoments (612/625) lo2270 hi2270 accepted2270
def lo2271b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨54,by decide⟩
def lo2271b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨55,by decide⟩
def lo2271 : CheckedMoment :=
  CheckedMoment.ofBessel lo2271b1 lo2271b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2271b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨59,by decide⟩
def hi2271b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨60,by decide⟩
def hi2271 : CheckedMoment :=
  CheckedMoment.ofBessel hi2271b1 hi2271b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2271 : meanBracketCheck (9793/10000) lo2271 hi2271=true := by decide +kernel
def bracket2271 : MeanBracket := meanBracketOfMoments (9793/10000) lo2271 hi2271 accepted2271
#print axioms bracket2256
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0141
