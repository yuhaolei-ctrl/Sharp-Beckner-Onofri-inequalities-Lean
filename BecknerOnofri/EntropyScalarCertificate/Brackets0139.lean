module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0347
public import BecknerOnofri.EntropyScalarCertificate.Bessel0348
public import BecknerOnofri.EntropyScalarCertificate.Bessel0349

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0139
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2224b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨32,by decide⟩
def lo2224b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨33,by decide⟩
def lo2224 : CheckedMoment :=
  CheckedMoment.ofBessel lo2224b1 lo2224b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2224b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨37,by decide⟩
def hi2224b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨38,by decide⟩
def hi2224 : CheckedMoment :=
  CheckedMoment.ofBessel hi2224b1 hi2224b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2224 : meanBracketCheck (4873/5000) lo2224 hi2224=true := by decide +kernel
def bracket2224 : MeanBracket := meanBracketOfMoments (4873/5000) lo2224 hi2224 accepted2224
def lo2225b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨42,by decide⟩
def lo2225b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨43,by decide⟩
def lo2225 : CheckedMoment :=
  CheckedMoment.ofBessel lo2225b1 lo2225b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2225b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨47,by decide⟩
def hi2225b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨48,by decide⟩
def hi2225 : CheckedMoment :=
  CheckedMoment.ofBessel hi2225b1 hi2225b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2225 : meanBracketCheck (9747/10000) lo2225 hi2225=true := by decide +kernel
def bracket2225 : MeanBracket := meanBracketOfMoments (9747/10000) lo2225 hi2225 accepted2225
def lo2226b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨52,by decide⟩
def lo2226b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨53,by decide⟩
def lo2226 : CheckedMoment :=
  CheckedMoment.ofBessel lo2226b1 lo2226b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2226b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨57,by decide⟩
def hi2226b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨58,by decide⟩
def hi2226 : CheckedMoment :=
  CheckedMoment.ofBessel hi2226b1 hi2226b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2226 : meanBracketCheck (2437/2500) lo2226 hi2226=true := by decide +kernel
def bracket2226 : MeanBracket := meanBracketOfMoments (2437/2500) lo2226 hi2226 accepted2226
def lo2227b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨62,by decide⟩
def lo2227b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨63,by decide⟩
def lo2227 : CheckedMoment :=
  CheckedMoment.ofBessel lo2227b1 lo2227b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2227b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨3,by decide⟩
def hi2227b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨4,by decide⟩
def hi2227 : CheckedMoment :=
  CheckedMoment.ofBessel hi2227b1 hi2227b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2227 : meanBracketCheck (9749/10000) lo2227 hi2227=true := by decide +kernel
def bracket2227 : MeanBracket := meanBracketOfMoments (9749/10000) lo2227 hi2227 accepted2227
def lo2228b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨8,by decide⟩
def lo2228b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨9,by decide⟩
def lo2228 : CheckedMoment :=
  CheckedMoment.ofBessel lo2228b1 lo2228b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2228b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨13,by decide⟩
def hi2228b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨14,by decide⟩
def hi2228 : CheckedMoment :=
  CheckedMoment.ofBessel hi2228b1 hi2228b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2228 : meanBracketCheck (39/40) lo2228 hi2228=true := by decide +kernel
def bracket2228 : MeanBracket := meanBracketOfMoments (39/40) lo2228 hi2228 accepted2228
def lo2229b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨18,by decide⟩
def lo2229b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨19,by decide⟩
def lo2229 : CheckedMoment :=
  CheckedMoment.ofBessel lo2229b1 lo2229b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2229b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨23,by decide⟩
def hi2229b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨24,by decide⟩
def hi2229 : CheckedMoment :=
  CheckedMoment.ofBessel hi2229b1 hi2229b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2229 : meanBracketCheck (9751/10000) lo2229 hi2229=true := by decide +kernel
def bracket2229 : MeanBracket := meanBracketOfMoments (9751/10000) lo2229 hi2229 accepted2229
def lo2230b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨28,by decide⟩
def lo2230b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨29,by decide⟩
def lo2230 : CheckedMoment :=
  CheckedMoment.ofBessel lo2230b1 lo2230b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2230b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨33,by decide⟩
def hi2230b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨34,by decide⟩
def hi2230 : CheckedMoment :=
  CheckedMoment.ofBessel hi2230b1 hi2230b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2230 : meanBracketCheck (1219/1250) lo2230 hi2230=true := by decide +kernel
def bracket2230 : MeanBracket := meanBracketOfMoments (1219/1250) lo2230 hi2230 accepted2230
def lo2231b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨38,by decide⟩
def lo2231b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨39,by decide⟩
def lo2231 : CheckedMoment :=
  CheckedMoment.ofBessel lo2231b1 lo2231b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2231b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨43,by decide⟩
def hi2231b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨44,by decide⟩
def hi2231 : CheckedMoment :=
  CheckedMoment.ofBessel hi2231b1 hi2231b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2231 : meanBracketCheck (9753/10000) lo2231 hi2231=true := by decide +kernel
def bracket2231 : MeanBracket := meanBracketOfMoments (9753/10000) lo2231 hi2231 accepted2231
def lo2232b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨48,by decide⟩
def lo2232b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨49,by decide⟩
def lo2232 : CheckedMoment :=
  CheckedMoment.ofBessel lo2232b1 lo2232b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2232b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨53,by decide⟩
def hi2232b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨54,by decide⟩
def hi2232 : CheckedMoment :=
  CheckedMoment.ofBessel hi2232b1 hi2232b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2232 : meanBracketCheck (4877/5000) lo2232 hi2232=true := by decide +kernel
def bracket2232 : MeanBracket := meanBracketOfMoments (4877/5000) lo2232 hi2232 accepted2232
def lo2233b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨58,by decide⟩
def lo2233b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨59,by decide⟩
def lo2233 : CheckedMoment :=
  CheckedMoment.ofBessel lo2233b1 lo2233b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2233b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨63,by decide⟩
def hi2233b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨0,by decide⟩
def hi2233 : CheckedMoment :=
  CheckedMoment.ofBessel hi2233b1 hi2233b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2233 : meanBracketCheck (1951/2000) lo2233 hi2233=true := by decide +kernel
def bracket2233 : MeanBracket := meanBracketOfMoments (1951/2000) lo2233 hi2233 accepted2233
def lo2234b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨4,by decide⟩
def lo2234b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨5,by decide⟩
def lo2234 : CheckedMoment :=
  CheckedMoment.ofBessel lo2234b1 lo2234b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2234b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨9,by decide⟩
def hi2234b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨10,by decide⟩
def hi2234 : CheckedMoment :=
  CheckedMoment.ofBessel hi2234b1 hi2234b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2234 : meanBracketCheck (2439/2500) lo2234 hi2234=true := by decide +kernel
def bracket2234 : MeanBracket := meanBracketOfMoments (2439/2500) lo2234 hi2234 accepted2234
def lo2235b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨14,by decide⟩
def lo2235b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨15,by decide⟩
def lo2235 : CheckedMoment :=
  CheckedMoment.ofBessel lo2235b1 lo2235b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2235b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨19,by decide⟩
def hi2235b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨20,by decide⟩
def hi2235 : CheckedMoment :=
  CheckedMoment.ofBessel hi2235b1 hi2235b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2235 : meanBracketCheck (9757/10000) lo2235 hi2235=true := by decide +kernel
def bracket2235 : MeanBracket := meanBracketOfMoments (9757/10000) lo2235 hi2235 accepted2235
def lo2236b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨24,by decide⟩
def lo2236b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨25,by decide⟩
def lo2236 : CheckedMoment :=
  CheckedMoment.ofBessel lo2236b1 lo2236b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2236b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨29,by decide⟩
def hi2236b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨30,by decide⟩
def hi2236 : CheckedMoment :=
  CheckedMoment.ofBessel hi2236b1 hi2236b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2236 : meanBracketCheck (4879/5000) lo2236 hi2236=true := by decide +kernel
def bracket2236 : MeanBracket := meanBracketOfMoments (4879/5000) lo2236 hi2236 accepted2236
def lo2237b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨34,by decide⟩
def lo2237b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨35,by decide⟩
def lo2237 : CheckedMoment :=
  CheckedMoment.ofBessel lo2237b1 lo2237b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2237b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨39,by decide⟩
def hi2237b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨40,by decide⟩
def hi2237 : CheckedMoment :=
  CheckedMoment.ofBessel hi2237b1 hi2237b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2237 : meanBracketCheck (9759/10000) lo2237 hi2237=true := by decide +kernel
def bracket2237 : MeanBracket := meanBracketOfMoments (9759/10000) lo2237 hi2237 accepted2237
def lo2238b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨44,by decide⟩
def lo2238b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨45,by decide⟩
def lo2238 : CheckedMoment :=
  CheckedMoment.ofBessel lo2238b1 lo2238b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2238b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨49,by decide⟩
def hi2238b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨50,by decide⟩
def hi2238 : CheckedMoment :=
  CheckedMoment.ofBessel hi2238b1 hi2238b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2238 : meanBracketCheck (122/125) lo2238 hi2238=true := by decide +kernel
def bracket2238 : MeanBracket := meanBracketOfMoments (122/125) lo2238 hi2238 accepted2238
def lo2239b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨54,by decide⟩
def lo2239b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨55,by decide⟩
def lo2239 : CheckedMoment :=
  CheckedMoment.ofBessel lo2239b1 lo2239b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2239b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨59,by decide⟩
def hi2239b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0349.rows BesselBatch0349.accepted ⟨60,by decide⟩
def hi2239 : CheckedMoment :=
  CheckedMoment.ofBessel hi2239b1 hi2239b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2239 : meanBracketCheck (9761/10000) lo2239 hi2239=true := by decide +kernel
def bracket2239 : MeanBracket := meanBracketOfMoments (9761/10000) lo2239 hi2239 accepted2239
#print axioms bracket2224
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0139
