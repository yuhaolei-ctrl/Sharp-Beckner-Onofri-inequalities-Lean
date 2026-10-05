module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0357
public import BecknerOnofri.EntropyScalarCertificate.Bessel0358
public import BecknerOnofri.EntropyScalarCertificate.Bessel0359

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0143
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2288b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨32,by decide⟩
def lo2288b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨33,by decide⟩
def lo2288 : CheckedMoment :=
  CheckedMoment.ofBessel lo2288b1 lo2288b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2288b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨37,by decide⟩
def hi2288b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨38,by decide⟩
def hi2288 : CheckedMoment :=
  CheckedMoment.ofBessel hi2288b1 hi2288b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2288 : meanBracketCheck (981/1000) lo2288 hi2288=true := by decide +kernel
def bracket2288 : MeanBracket := meanBracketOfMoments (981/1000) lo2288 hi2288 accepted2288
def lo2289b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨42,by decide⟩
def lo2289b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨43,by decide⟩
def lo2289 : CheckedMoment :=
  CheckedMoment.ofBessel lo2289b1 lo2289b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2289b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨47,by decide⟩
def hi2289b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨48,by decide⟩
def hi2289 : CheckedMoment :=
  CheckedMoment.ofBessel hi2289b1 hi2289b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2289 : meanBracketCheck (9811/10000) lo2289 hi2289=true := by decide +kernel
def bracket2289 : MeanBracket := meanBracketOfMoments (9811/10000) lo2289 hi2289 accepted2289
def lo2290b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨52,by decide⟩
def lo2290b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨53,by decide⟩
def lo2290 : CheckedMoment :=
  CheckedMoment.ofBessel lo2290b1 lo2290b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2290b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨57,by decide⟩
def hi2290b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨58,by decide⟩
def hi2290 : CheckedMoment :=
  CheckedMoment.ofBessel hi2290b1 hi2290b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2290 : meanBracketCheck (2453/2500) lo2290 hi2290=true := by decide +kernel
def bracket2290 : MeanBracket := meanBracketOfMoments (2453/2500) lo2290 hi2290 accepted2290
def lo2291b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨62,by decide⟩
def lo2291b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨63,by decide⟩
def lo2291 : CheckedMoment :=
  CheckedMoment.ofBessel lo2291b1 lo2291b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2291b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨3,by decide⟩
def hi2291b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨4,by decide⟩
def hi2291 : CheckedMoment :=
  CheckedMoment.ofBessel hi2291b1 hi2291b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2291 : meanBracketCheck (9813/10000) lo2291 hi2291=true := by decide +kernel
def bracket2291 : MeanBracket := meanBracketOfMoments (9813/10000) lo2291 hi2291 accepted2291
def lo2292b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨8,by decide⟩
def lo2292b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨9,by decide⟩
def lo2292 : CheckedMoment :=
  CheckedMoment.ofBessel lo2292b1 lo2292b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2292b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨13,by decide⟩
def hi2292b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨14,by decide⟩
def hi2292 : CheckedMoment :=
  CheckedMoment.ofBessel hi2292b1 hi2292b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2292 : meanBracketCheck (4907/5000) lo2292 hi2292=true := by decide +kernel
def bracket2292 : MeanBracket := meanBracketOfMoments (4907/5000) lo2292 hi2292 accepted2292
def lo2293b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨18,by decide⟩
def lo2293b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨19,by decide⟩
def lo2293 : CheckedMoment :=
  CheckedMoment.ofBessel lo2293b1 lo2293b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2293b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨23,by decide⟩
def hi2293b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨24,by decide⟩
def hi2293 : CheckedMoment :=
  CheckedMoment.ofBessel hi2293b1 hi2293b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2293 : meanBracketCheck (1963/2000) lo2293 hi2293=true := by decide +kernel
def bracket2293 : MeanBracket := meanBracketOfMoments (1963/2000) lo2293 hi2293 accepted2293
def lo2294b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨28,by decide⟩
def lo2294b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨29,by decide⟩
def lo2294 : CheckedMoment :=
  CheckedMoment.ofBessel lo2294b1 lo2294b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2294b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨33,by decide⟩
def hi2294b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨34,by decide⟩
def hi2294 : CheckedMoment :=
  CheckedMoment.ofBessel hi2294b1 hi2294b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2294 : meanBracketCheck (1227/1250) lo2294 hi2294=true := by decide +kernel
def bracket2294 : MeanBracket := meanBracketOfMoments (1227/1250) lo2294 hi2294 accepted2294
def lo2295b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨38,by decide⟩
def lo2295b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨39,by decide⟩
def lo2295 : CheckedMoment :=
  CheckedMoment.ofBessel lo2295b1 lo2295b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2295b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨43,by decide⟩
def hi2295b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨44,by decide⟩
def hi2295 : CheckedMoment :=
  CheckedMoment.ofBessel hi2295b1 hi2295b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2295 : meanBracketCheck (9817/10000) lo2295 hi2295=true := by decide +kernel
def bracket2295 : MeanBracket := meanBracketOfMoments (9817/10000) lo2295 hi2295 accepted2295
def lo2296b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨48,by decide⟩
def lo2296b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨49,by decide⟩
def lo2296 : CheckedMoment :=
  CheckedMoment.ofBessel lo2296b1 lo2296b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2296b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨53,by decide⟩
def hi2296b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨54,by decide⟩
def hi2296 : CheckedMoment :=
  CheckedMoment.ofBessel hi2296b1 hi2296b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2296 : meanBracketCheck (4909/5000) lo2296 hi2296=true := by decide +kernel
def bracket2296 : MeanBracket := meanBracketOfMoments (4909/5000) lo2296 hi2296 accepted2296
def lo2297b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨58,by decide⟩
def lo2297b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨59,by decide⟩
def lo2297 : CheckedMoment :=
  CheckedMoment.ofBessel lo2297b1 lo2297b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2297b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨63,by decide⟩
def hi2297b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨0,by decide⟩
def hi2297 : CheckedMoment :=
  CheckedMoment.ofBessel hi2297b1 hi2297b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2297 : meanBracketCheck (9819/10000) lo2297 hi2297=true := by decide +kernel
def bracket2297 : MeanBracket := meanBracketOfMoments (9819/10000) lo2297 hi2297 accepted2297
def lo2298b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨4,by decide⟩
def lo2298b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨5,by decide⟩
def lo2298 : CheckedMoment :=
  CheckedMoment.ofBessel lo2298b1 lo2298b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2298b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨9,by decide⟩
def hi2298b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨10,by decide⟩
def hi2298 : CheckedMoment :=
  CheckedMoment.ofBessel hi2298b1 hi2298b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2298 : meanBracketCheck (491/500) lo2298 hi2298=true := by decide +kernel
def bracket2298 : MeanBracket := meanBracketOfMoments (491/500) lo2298 hi2298 accepted2298
def lo2299b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨14,by decide⟩
def lo2299b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨15,by decide⟩
def lo2299 : CheckedMoment :=
  CheckedMoment.ofBessel lo2299b1 lo2299b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2299b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨19,by decide⟩
def hi2299b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨20,by decide⟩
def hi2299 : CheckedMoment :=
  CheckedMoment.ofBessel hi2299b1 hi2299b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2299 : meanBracketCheck (9821/10000) lo2299 hi2299=true := by decide +kernel
def bracket2299 : MeanBracket := meanBracketOfMoments (9821/10000) lo2299 hi2299 accepted2299
def lo2300b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨24,by decide⟩
def lo2300b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨25,by decide⟩
def lo2300 : CheckedMoment :=
  CheckedMoment.ofBessel lo2300b1 lo2300b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2300b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨29,by decide⟩
def hi2300b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨30,by decide⟩
def hi2300 : CheckedMoment :=
  CheckedMoment.ofBessel hi2300b1 hi2300b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2300 : meanBracketCheck (4911/5000) lo2300 hi2300=true := by decide +kernel
def bracket2300 : MeanBracket := meanBracketOfMoments (4911/5000) lo2300 hi2300 accepted2300
def lo2301b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨34,by decide⟩
def lo2301b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨35,by decide⟩
def lo2301 : CheckedMoment :=
  CheckedMoment.ofBessel lo2301b1 lo2301b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2301b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨39,by decide⟩
def hi2301b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨40,by decide⟩
def hi2301 : CheckedMoment :=
  CheckedMoment.ofBessel hi2301b1 hi2301b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2301 : meanBracketCheck (9823/10000) lo2301 hi2301=true := by decide +kernel
def bracket2301 : MeanBracket := meanBracketOfMoments (9823/10000) lo2301 hi2301 accepted2301
def lo2302b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨44,by decide⟩
def lo2302b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨45,by decide⟩
def lo2302 : CheckedMoment :=
  CheckedMoment.ofBessel lo2302b1 lo2302b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2302b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨49,by decide⟩
def hi2302b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨50,by decide⟩
def hi2302 : CheckedMoment :=
  CheckedMoment.ofBessel hi2302b1 hi2302b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2302 : meanBracketCheck (614/625) lo2302 hi2302=true := by decide +kernel
def bracket2302 : MeanBracket := meanBracketOfMoments (614/625) lo2302 hi2302 accepted2302
def lo2303b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨54,by decide⟩
def lo2303b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨55,by decide⟩
def lo2303 : CheckedMoment :=
  CheckedMoment.ofBessel lo2303b1 lo2303b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2303b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨59,by decide⟩
def hi2303b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨60,by decide⟩
def hi2303 : CheckedMoment :=
  CheckedMoment.ofBessel hi2303b1 hi2303b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2303 : meanBracketCheck (393/400) lo2303 hi2303=true := by decide +kernel
def bracket2303 : MeanBracket := meanBracketOfMoments (393/400) lo2303 hi2303 accepted2303
#print axioms bracket2288
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0143
