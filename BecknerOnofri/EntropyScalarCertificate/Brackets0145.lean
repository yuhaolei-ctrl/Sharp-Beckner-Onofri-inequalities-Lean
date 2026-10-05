import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0362
import BecknerOnofri.EntropyScalarCertificate.Bessel0363
import BecknerOnofri.EntropyScalarCertificate.Bessel0364
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0145
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2320b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨32,by decide⟩
def lo2320b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨33,by decide⟩
def lo2320 : CheckedMoment :=
  CheckedMoment.ofBessel lo2320b1 lo2320b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2320b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨37,by decide⟩
def hi2320b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨38,by decide⟩
def hi2320 : CheckedMoment :=
  CheckedMoment.ofBessel hi2320b1 hi2320b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2320 : meanBracketCheck (4921/5000) lo2320 hi2320=true := by decide +kernel
def bracket2320 : MeanBracket := meanBracketOfMoments (4921/5000) lo2320 hi2320 accepted2320
def lo2321b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨42,by decide⟩
def lo2321b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨43,by decide⟩
def lo2321 : CheckedMoment :=
  CheckedMoment.ofBessel lo2321b1 lo2321b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2321b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨47,by decide⟩
def hi2321b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨48,by decide⟩
def hi2321 : CheckedMoment :=
  CheckedMoment.ofBessel hi2321b1 hi2321b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2321 : meanBracketCheck (9843/10000) lo2321 hi2321=true := by decide +kernel
def bracket2321 : MeanBracket := meanBracketOfMoments (9843/10000) lo2321 hi2321 accepted2321
def lo2322b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨52,by decide⟩
def lo2322b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨53,by decide⟩
def lo2322 : CheckedMoment :=
  CheckedMoment.ofBessel lo2322b1 lo2322b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2322b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨57,by decide⟩
def hi2322b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨58,by decide⟩
def hi2322 : CheckedMoment :=
  CheckedMoment.ofBessel hi2322b1 hi2322b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2322 : meanBracketCheck (2461/2500) lo2322 hi2322=true := by decide +kernel
def bracket2322 : MeanBracket := meanBracketOfMoments (2461/2500) lo2322 hi2322 accepted2322
def lo2323b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨62,by decide⟩
def lo2323b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨63,by decide⟩
def lo2323 : CheckedMoment :=
  CheckedMoment.ofBessel lo2323b1 lo2323b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2323b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨3,by decide⟩
def hi2323b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨4,by decide⟩
def hi2323 : CheckedMoment :=
  CheckedMoment.ofBessel hi2323b1 hi2323b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2323 : meanBracketCheck (1969/2000) lo2323 hi2323=true := by decide +kernel
def bracket2323 : MeanBracket := meanBracketOfMoments (1969/2000) lo2323 hi2323 accepted2323
def lo2324b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨8,by decide⟩
def lo2324b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨9,by decide⟩
def lo2324 : CheckedMoment :=
  CheckedMoment.ofBessel lo2324b1 lo2324b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2324b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨13,by decide⟩
def hi2324b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨14,by decide⟩
def hi2324 : CheckedMoment :=
  CheckedMoment.ofBessel hi2324b1 hi2324b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2324 : meanBracketCheck (4923/5000) lo2324 hi2324=true := by decide +kernel
def bracket2324 : MeanBracket := meanBracketOfMoments (4923/5000) lo2324 hi2324 accepted2324
def lo2325b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨18,by decide⟩
def lo2325b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨19,by decide⟩
def lo2325 : CheckedMoment :=
  CheckedMoment.ofBessel lo2325b1 lo2325b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2325b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨23,by decide⟩
def hi2325b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨24,by decide⟩
def hi2325 : CheckedMoment :=
  CheckedMoment.ofBessel hi2325b1 hi2325b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2325 : meanBracketCheck (9847/10000) lo2325 hi2325=true := by decide +kernel
def bracket2325 : MeanBracket := meanBracketOfMoments (9847/10000) lo2325 hi2325 accepted2325
def lo2326b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨28,by decide⟩
def lo2326b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨29,by decide⟩
def lo2326 : CheckedMoment :=
  CheckedMoment.ofBessel lo2326b1 lo2326b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2326b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨33,by decide⟩
def hi2326b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨34,by decide⟩
def hi2326 : CheckedMoment :=
  CheckedMoment.ofBessel hi2326b1 hi2326b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2326 : meanBracketCheck (1231/1250) lo2326 hi2326=true := by decide +kernel
def bracket2326 : MeanBracket := meanBracketOfMoments (1231/1250) lo2326 hi2326 accepted2326
def lo2327b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨38,by decide⟩
def lo2327b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨39,by decide⟩
def lo2327 : CheckedMoment :=
  CheckedMoment.ofBessel lo2327b1 lo2327b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2327b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨43,by decide⟩
def hi2327b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨44,by decide⟩
def hi2327 : CheckedMoment :=
  CheckedMoment.ofBessel hi2327b1 hi2327b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2327 : meanBracketCheck (9849/10000) lo2327 hi2327=true := by decide +kernel
def bracket2327 : MeanBracket := meanBracketOfMoments (9849/10000) lo2327 hi2327 accepted2327
def lo2328b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨48,by decide⟩
def lo2328b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨49,by decide⟩
def lo2328 : CheckedMoment :=
  CheckedMoment.ofBessel lo2328b1 lo2328b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2328b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨53,by decide⟩
def hi2328b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨54,by decide⟩
def hi2328 : CheckedMoment :=
  CheckedMoment.ofBessel hi2328b1 hi2328b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2328 : meanBracketCheck (197/200) lo2328 hi2328=true := by decide +kernel
def bracket2328 : MeanBracket := meanBracketOfMoments (197/200) lo2328 hi2328 accepted2328
def lo2329b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨58,by decide⟩
def lo2329b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨59,by decide⟩
def lo2329 : CheckedMoment :=
  CheckedMoment.ofBessel lo2329b1 lo2329b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2329b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨63,by decide⟩
def hi2329b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨0,by decide⟩
def hi2329 : CheckedMoment :=
  CheckedMoment.ofBessel hi2329b1 hi2329b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2329 : meanBracketCheck (9851/10000) lo2329 hi2329=true := by decide +kernel
def bracket2329 : MeanBracket := meanBracketOfMoments (9851/10000) lo2329 hi2329 accepted2329
def lo2330b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨4,by decide⟩
def lo2330b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨5,by decide⟩
def lo2330 : CheckedMoment :=
  CheckedMoment.ofBessel lo2330b1 lo2330b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2330b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨9,by decide⟩
def hi2330b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨10,by decide⟩
def hi2330 : CheckedMoment :=
  CheckedMoment.ofBessel hi2330b1 hi2330b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2330 : meanBracketCheck (2463/2500) lo2330 hi2330=true := by decide +kernel
def bracket2330 : MeanBracket := meanBracketOfMoments (2463/2500) lo2330 hi2330 accepted2330
def lo2331b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨14,by decide⟩
def lo2331b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨15,by decide⟩
def lo2331 : CheckedMoment :=
  CheckedMoment.ofBessel lo2331b1 lo2331b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2331b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨19,by decide⟩
def hi2331b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨20,by decide⟩
def hi2331 : CheckedMoment :=
  CheckedMoment.ofBessel hi2331b1 hi2331b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2331 : meanBracketCheck (9853/10000) lo2331 hi2331=true := by decide +kernel
def bracket2331 : MeanBracket := meanBracketOfMoments (9853/10000) lo2331 hi2331 accepted2331
def lo2332b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨24,by decide⟩
def lo2332b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨25,by decide⟩
def lo2332 : CheckedMoment :=
  CheckedMoment.ofBessel lo2332b1 lo2332b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2332b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨29,by decide⟩
def hi2332b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨30,by decide⟩
def hi2332 : CheckedMoment :=
  CheckedMoment.ofBessel hi2332b1 hi2332b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2332 : meanBracketCheck (4927/5000) lo2332 hi2332=true := by decide +kernel
def bracket2332 : MeanBracket := meanBracketOfMoments (4927/5000) lo2332 hi2332 accepted2332
def lo2333b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨34,by decide⟩
def lo2333b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨35,by decide⟩
def lo2333 : CheckedMoment :=
  CheckedMoment.ofBessel lo2333b1 lo2333b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2333b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨39,by decide⟩
def hi2333b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨40,by decide⟩
def hi2333 : CheckedMoment :=
  CheckedMoment.ofBessel hi2333b1 hi2333b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2333 : meanBracketCheck (1971/2000) lo2333 hi2333=true := by decide +kernel
def bracket2333 : MeanBracket := meanBracketOfMoments (1971/2000) lo2333 hi2333 accepted2333
def lo2334b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨44,by decide⟩
def lo2334b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨45,by decide⟩
def lo2334 : CheckedMoment :=
  CheckedMoment.ofBessel lo2334b1 lo2334b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2334b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨49,by decide⟩
def hi2334b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨50,by decide⟩
def hi2334 : CheckedMoment :=
  CheckedMoment.ofBessel hi2334b1 hi2334b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2334 : meanBracketCheck (616/625) lo2334 hi2334=true := by decide +kernel
def bracket2334 : MeanBracket := meanBracketOfMoments (616/625) lo2334 hi2334 accepted2334
def lo2335b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨54,by decide⟩
def lo2335b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨55,by decide⟩
def lo2335 : CheckedMoment :=
  CheckedMoment.ofBessel lo2335b1 lo2335b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2335b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨59,by decide⟩
def hi2335b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨60,by decide⟩
def hi2335 : CheckedMoment :=
  CheckedMoment.ofBessel hi2335b1 hi2335b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2335 : meanBracketCheck (9857/10000) lo2335 hi2335=true := by decide +kernel
def bracket2335 : MeanBracket := meanBracketOfMoments (9857/10000) lo2335 hi2335 accepted2335
#print axioms bracket2320
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0145
