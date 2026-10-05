import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0355
import BecknerOnofri.EntropyScalarCertificate.Bessel0356
import BecknerOnofri.EntropyScalarCertificate.Bessel0357
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0142
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2272b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨0,by decide⟩
def lo2272b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨1,by decide⟩
def lo2272 : CheckedMoment :=
  CheckedMoment.ofBessel lo2272b1 lo2272b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2272b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨5,by decide⟩
def hi2272b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨6,by decide⟩
def hi2272 : CheckedMoment :=
  CheckedMoment.ofBessel hi2272b1 hi2272b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2272 : meanBracketCheck (4897/5000) lo2272 hi2272=true := by decide +kernel
def bracket2272 : MeanBracket := meanBracketOfMoments (4897/5000) lo2272 hi2272 accepted2272
def lo2273b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨10,by decide⟩
def lo2273b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨11,by decide⟩
def lo2273 : CheckedMoment :=
  CheckedMoment.ofBessel lo2273b1 lo2273b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2273b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨15,by decide⟩
def hi2273b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨16,by decide⟩
def hi2273 : CheckedMoment :=
  CheckedMoment.ofBessel hi2273b1 hi2273b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2273 : meanBracketCheck (1959/2000) lo2273 hi2273=true := by decide +kernel
def bracket2273 : MeanBracket := meanBracketOfMoments (1959/2000) lo2273 hi2273 accepted2273
def lo2274b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨20,by decide⟩
def lo2274b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨21,by decide⟩
def lo2274 : CheckedMoment :=
  CheckedMoment.ofBessel lo2274b1 lo2274b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2274b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨25,by decide⟩
def hi2274b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨26,by decide⟩
def hi2274 : CheckedMoment :=
  CheckedMoment.ofBessel hi2274b1 hi2274b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2274 : meanBracketCheck (2449/2500) lo2274 hi2274=true := by decide +kernel
def bracket2274 : MeanBracket := meanBracketOfMoments (2449/2500) lo2274 hi2274 accepted2274
def lo2275b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨30,by decide⟩
def lo2275b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨31,by decide⟩
def lo2275 : CheckedMoment :=
  CheckedMoment.ofBessel lo2275b1 lo2275b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2275b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨35,by decide⟩
def hi2275b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨36,by decide⟩
def hi2275 : CheckedMoment :=
  CheckedMoment.ofBessel hi2275b1 hi2275b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2275 : meanBracketCheck (9797/10000) lo2275 hi2275=true := by decide +kernel
def bracket2275 : MeanBracket := meanBracketOfMoments (9797/10000) lo2275 hi2275 accepted2275
def lo2276b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨40,by decide⟩
def lo2276b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨41,by decide⟩
def lo2276 : CheckedMoment :=
  CheckedMoment.ofBessel lo2276b1 lo2276b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2276b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨45,by decide⟩
def hi2276b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨46,by decide⟩
def hi2276 : CheckedMoment :=
  CheckedMoment.ofBessel hi2276b1 hi2276b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2276 : meanBracketCheck (4899/5000) lo2276 hi2276=true := by decide +kernel
def bracket2276 : MeanBracket := meanBracketOfMoments (4899/5000) lo2276 hi2276 accepted2276
def lo2277b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨50,by decide⟩
def lo2277b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨51,by decide⟩
def lo2277 : CheckedMoment :=
  CheckedMoment.ofBessel lo2277b1 lo2277b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2277b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨55,by decide⟩
def hi2277b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨56,by decide⟩
def hi2277 : CheckedMoment :=
  CheckedMoment.ofBessel hi2277b1 hi2277b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2277 : meanBracketCheck (9799/10000) lo2277 hi2277=true := by decide +kernel
def bracket2277 : MeanBracket := meanBracketOfMoments (9799/10000) lo2277 hi2277 accepted2277
def lo2278b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨60,by decide⟩
def lo2278b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨61,by decide⟩
def lo2278 : CheckedMoment :=
  CheckedMoment.ofBessel lo2278b1 lo2278b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2278b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨1,by decide⟩
def hi2278b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨2,by decide⟩
def hi2278 : CheckedMoment :=
  CheckedMoment.ofBessel hi2278b1 hi2278b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2278 : meanBracketCheck (49/50) lo2278 hi2278=true := by decide +kernel
def bracket2278 : MeanBracket := meanBracketOfMoments (49/50) lo2278 hi2278 accepted2278
def lo2279b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨6,by decide⟩
def lo2279b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨7,by decide⟩
def lo2279 : CheckedMoment :=
  CheckedMoment.ofBessel lo2279b1 lo2279b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2279b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨11,by decide⟩
def hi2279b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨12,by decide⟩
def hi2279 : CheckedMoment :=
  CheckedMoment.ofBessel hi2279b1 hi2279b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2279 : meanBracketCheck (9801/10000) lo2279 hi2279=true := by decide +kernel
def bracket2279 : MeanBracket := meanBracketOfMoments (9801/10000) lo2279 hi2279 accepted2279
def lo2280b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨16,by decide⟩
def lo2280b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨17,by decide⟩
def lo2280 : CheckedMoment :=
  CheckedMoment.ofBessel lo2280b1 lo2280b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2280b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨21,by decide⟩
def hi2280b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨22,by decide⟩
def hi2280 : CheckedMoment :=
  CheckedMoment.ofBessel hi2280b1 hi2280b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2280 : meanBracketCheck (4901/5000) lo2280 hi2280=true := by decide +kernel
def bracket2280 : MeanBracket := meanBracketOfMoments (4901/5000) lo2280 hi2280 accepted2280
def lo2281b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨26,by decide⟩
def lo2281b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨27,by decide⟩
def lo2281 : CheckedMoment :=
  CheckedMoment.ofBessel lo2281b1 lo2281b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2281b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨31,by decide⟩
def hi2281b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨32,by decide⟩
def hi2281 : CheckedMoment :=
  CheckedMoment.ofBessel hi2281b1 hi2281b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2281 : meanBracketCheck (9803/10000) lo2281 hi2281=true := by decide +kernel
def bracket2281 : MeanBracket := meanBracketOfMoments (9803/10000) lo2281 hi2281 accepted2281
def lo2282b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨36,by decide⟩
def lo2282b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨37,by decide⟩
def lo2282 : CheckedMoment :=
  CheckedMoment.ofBessel lo2282b1 lo2282b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2282b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨41,by decide⟩
def hi2282b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨42,by decide⟩
def hi2282 : CheckedMoment :=
  CheckedMoment.ofBessel hi2282b1 hi2282b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2282 : meanBracketCheck (2451/2500) lo2282 hi2282=true := by decide +kernel
def bracket2282 : MeanBracket := meanBracketOfMoments (2451/2500) lo2282 hi2282 accepted2282
def lo2283b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨46,by decide⟩
def lo2283b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨47,by decide⟩
def lo2283 : CheckedMoment :=
  CheckedMoment.ofBessel lo2283b1 lo2283b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2283b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨51,by decide⟩
def hi2283b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨52,by decide⟩
def hi2283 : CheckedMoment :=
  CheckedMoment.ofBessel hi2283b1 hi2283b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2283 : meanBracketCheck (1961/2000) lo2283 hi2283=true := by decide +kernel
def bracket2283 : MeanBracket := meanBracketOfMoments (1961/2000) lo2283 hi2283 accepted2283
def lo2284b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨56,by decide⟩
def lo2284b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨57,by decide⟩
def lo2284 : CheckedMoment :=
  CheckedMoment.ofBessel lo2284b1 lo2284b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2284b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨61,by decide⟩
def hi2284b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨62,by decide⟩
def hi2284 : CheckedMoment :=
  CheckedMoment.ofBessel hi2284b1 hi2284b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2284 : meanBracketCheck (4903/5000) lo2284 hi2284=true := by decide +kernel
def bracket2284 : MeanBracket := meanBracketOfMoments (4903/5000) lo2284 hi2284 accepted2284
def lo2285b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨2,by decide⟩
def lo2285b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨3,by decide⟩
def lo2285 : CheckedMoment :=
  CheckedMoment.ofBessel lo2285b1 lo2285b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2285b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨7,by decide⟩
def hi2285b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨8,by decide⟩
def hi2285 : CheckedMoment :=
  CheckedMoment.ofBessel hi2285b1 hi2285b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2285 : meanBracketCheck (9807/10000) lo2285 hi2285=true := by decide +kernel
def bracket2285 : MeanBracket := meanBracketOfMoments (9807/10000) lo2285 hi2285 accepted2285
def lo2286b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨12,by decide⟩
def lo2286b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨13,by decide⟩
def lo2286 : CheckedMoment :=
  CheckedMoment.ofBessel lo2286b1 lo2286b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2286b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨17,by decide⟩
def hi2286b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨18,by decide⟩
def hi2286 : CheckedMoment :=
  CheckedMoment.ofBessel hi2286b1 hi2286b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2286 : meanBracketCheck (613/625) lo2286 hi2286=true := by decide +kernel
def bracket2286 : MeanBracket := meanBracketOfMoments (613/625) lo2286 hi2286 accepted2286
def lo2287b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨22,by decide⟩
def lo2287b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨23,by decide⟩
def lo2287 : CheckedMoment :=
  CheckedMoment.ofBessel lo2287b1 lo2287b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2287b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨27,by decide⟩
def hi2287b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨28,by decide⟩
def hi2287 : CheckedMoment :=
  CheckedMoment.ofBessel hi2287b1 hi2287b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2287 : meanBracketCheck (9809/10000) lo2287 hi2287=true := by decide +kernel
def bracket2287 : MeanBracket := meanBracketOfMoments (9809/10000) lo2287 hi2287 accepted2287
#print axioms bracket2272
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0142
