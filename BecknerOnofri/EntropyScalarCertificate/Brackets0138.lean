module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0345
public import BecknerOnofri.EntropyScalarCertificate.Bessel0346
public import BecknerOnofri.EntropyScalarCertificate.Bessel0347

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0138
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2208b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨0,by decide⟩
def lo2208b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨1,by decide⟩
def lo2208 : CheckedMoment :=
  CheckedMoment.ofBessel lo2208b1 lo2208b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2208b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨5,by decide⟩
def hi2208b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨6,by decide⟩
def hi2208 : CheckedMoment :=
  CheckedMoment.ofBessel hi2208b1 hi2208b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2208 : meanBracketCheck (973/1000) lo2208 hi2208=true := by decide +kernel
def bracket2208 : MeanBracket := meanBracketOfMoments (973/1000) lo2208 hi2208 accepted2208
def lo2209b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨10,by decide⟩
def lo2209b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨11,by decide⟩
def lo2209 : CheckedMoment :=
  CheckedMoment.ofBessel lo2209b1 lo2209b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2209b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨15,by decide⟩
def hi2209b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨16,by decide⟩
def hi2209 : CheckedMoment :=
  CheckedMoment.ofBessel hi2209b1 hi2209b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2209 : meanBracketCheck (9731/10000) lo2209 hi2209=true := by decide +kernel
def bracket2209 : MeanBracket := meanBracketOfMoments (9731/10000) lo2209 hi2209 accepted2209
def lo2210b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨20,by decide⟩
def lo2210b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨21,by decide⟩
def lo2210 : CheckedMoment :=
  CheckedMoment.ofBessel lo2210b1 lo2210b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2210b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨25,by decide⟩
def hi2210b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨26,by decide⟩
def hi2210 : CheckedMoment :=
  CheckedMoment.ofBessel hi2210b1 hi2210b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2210 : meanBracketCheck (2433/2500) lo2210 hi2210=true := by decide +kernel
def bracket2210 : MeanBracket := meanBracketOfMoments (2433/2500) lo2210 hi2210 accepted2210
def lo2211b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨30,by decide⟩
def lo2211b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨31,by decide⟩
def lo2211 : CheckedMoment :=
  CheckedMoment.ofBessel lo2211b1 lo2211b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2211b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨35,by decide⟩
def hi2211b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨36,by decide⟩
def hi2211 : CheckedMoment :=
  CheckedMoment.ofBessel hi2211b1 hi2211b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2211 : meanBracketCheck (9733/10000) lo2211 hi2211=true := by decide +kernel
def bracket2211 : MeanBracket := meanBracketOfMoments (9733/10000) lo2211 hi2211 accepted2211
def lo2212b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨40,by decide⟩
def lo2212b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨41,by decide⟩
def lo2212 : CheckedMoment :=
  CheckedMoment.ofBessel lo2212b1 lo2212b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2212b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨45,by decide⟩
def hi2212b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨46,by decide⟩
def hi2212 : CheckedMoment :=
  CheckedMoment.ofBessel hi2212b1 hi2212b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2212 : meanBracketCheck (4867/5000) lo2212 hi2212=true := by decide +kernel
def bracket2212 : MeanBracket := meanBracketOfMoments (4867/5000) lo2212 hi2212 accepted2212
def lo2213b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨50,by decide⟩
def lo2213b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨51,by decide⟩
def lo2213 : CheckedMoment :=
  CheckedMoment.ofBessel lo2213b1 lo2213b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2213b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨55,by decide⟩
def hi2213b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨56,by decide⟩
def hi2213 : CheckedMoment :=
  CheckedMoment.ofBessel hi2213b1 hi2213b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2213 : meanBracketCheck (1947/2000) lo2213 hi2213=true := by decide +kernel
def bracket2213 : MeanBracket := meanBracketOfMoments (1947/2000) lo2213 hi2213 accepted2213
def lo2214b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨60,by decide⟩
def lo2214b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨61,by decide⟩
def lo2214 : CheckedMoment :=
  CheckedMoment.ofBessel lo2214b1 lo2214b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2214b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨1,by decide⟩
def hi2214b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨2,by decide⟩
def hi2214 : CheckedMoment :=
  CheckedMoment.ofBessel hi2214b1 hi2214b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2214 : meanBracketCheck (1217/1250) lo2214 hi2214=true := by decide +kernel
def bracket2214 : MeanBracket := meanBracketOfMoments (1217/1250) lo2214 hi2214 accepted2214
def lo2215b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨6,by decide⟩
def lo2215b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨7,by decide⟩
def lo2215 : CheckedMoment :=
  CheckedMoment.ofBessel lo2215b1 lo2215b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2215b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨11,by decide⟩
def hi2215b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨12,by decide⟩
def hi2215 : CheckedMoment :=
  CheckedMoment.ofBessel hi2215b1 hi2215b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2215 : meanBracketCheck (9737/10000) lo2215 hi2215=true := by decide +kernel
def bracket2215 : MeanBracket := meanBracketOfMoments (9737/10000) lo2215 hi2215 accepted2215
def lo2216b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨16,by decide⟩
def lo2216b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨17,by decide⟩
def lo2216 : CheckedMoment :=
  CheckedMoment.ofBessel lo2216b1 lo2216b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2216b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨21,by decide⟩
def hi2216b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨22,by decide⟩
def hi2216 : CheckedMoment :=
  CheckedMoment.ofBessel hi2216b1 hi2216b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2216 : meanBracketCheck (4869/5000) lo2216 hi2216=true := by decide +kernel
def bracket2216 : MeanBracket := meanBracketOfMoments (4869/5000) lo2216 hi2216 accepted2216
def lo2217b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨26,by decide⟩
def lo2217b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨27,by decide⟩
def lo2217 : CheckedMoment :=
  CheckedMoment.ofBessel lo2217b1 lo2217b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2217b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨31,by decide⟩
def hi2217b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨32,by decide⟩
def hi2217 : CheckedMoment :=
  CheckedMoment.ofBessel hi2217b1 hi2217b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2217 : meanBracketCheck (9739/10000) lo2217 hi2217=true := by decide +kernel
def bracket2217 : MeanBracket := meanBracketOfMoments (9739/10000) lo2217 hi2217 accepted2217
def lo2218b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨36,by decide⟩
def lo2218b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨37,by decide⟩
def lo2218 : CheckedMoment :=
  CheckedMoment.ofBessel lo2218b1 lo2218b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2218b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨41,by decide⟩
def hi2218b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨42,by decide⟩
def hi2218 : CheckedMoment :=
  CheckedMoment.ofBessel hi2218b1 hi2218b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2218 : meanBracketCheck (487/500) lo2218 hi2218=true := by decide +kernel
def bracket2218 : MeanBracket := meanBracketOfMoments (487/500) lo2218 hi2218 accepted2218
def lo2219b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨46,by decide⟩
def lo2219b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨47,by decide⟩
def lo2219 : CheckedMoment :=
  CheckedMoment.ofBessel lo2219b1 lo2219b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2219b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨51,by decide⟩
def hi2219b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨52,by decide⟩
def hi2219 : CheckedMoment :=
  CheckedMoment.ofBessel hi2219b1 hi2219b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2219 : meanBracketCheck (9741/10000) lo2219 hi2219=true := by decide +kernel
def bracket2219 : MeanBracket := meanBracketOfMoments (9741/10000) lo2219 hi2219 accepted2219
def lo2220b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨56,by decide⟩
def lo2220b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨57,by decide⟩
def lo2220 : CheckedMoment :=
  CheckedMoment.ofBessel lo2220b1 lo2220b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2220b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨61,by decide⟩
def hi2220b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨62,by decide⟩
def hi2220 : CheckedMoment :=
  CheckedMoment.ofBessel hi2220b1 hi2220b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2220 : meanBracketCheck (4871/5000) lo2220 hi2220=true := by decide +kernel
def bracket2220 : MeanBracket := meanBracketOfMoments (4871/5000) lo2220 hi2220 accepted2220
def lo2221b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨2,by decide⟩
def lo2221b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨3,by decide⟩
def lo2221 : CheckedMoment :=
  CheckedMoment.ofBessel lo2221b1 lo2221b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2221b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨7,by decide⟩
def hi2221b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨8,by decide⟩
def hi2221 : CheckedMoment :=
  CheckedMoment.ofBessel hi2221b1 hi2221b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2221 : meanBracketCheck (9743/10000) lo2221 hi2221=true := by decide +kernel
def bracket2221 : MeanBracket := meanBracketOfMoments (9743/10000) lo2221 hi2221 accepted2221
def lo2222b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨12,by decide⟩
def lo2222b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨13,by decide⟩
def lo2222 : CheckedMoment :=
  CheckedMoment.ofBessel lo2222b1 lo2222b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2222b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨17,by decide⟩
def hi2222b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨18,by decide⟩
def hi2222 : CheckedMoment :=
  CheckedMoment.ofBessel hi2222b1 hi2222b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2222 : meanBracketCheck (609/625) lo2222 hi2222=true := by decide +kernel
def bracket2222 : MeanBracket := meanBracketOfMoments (609/625) lo2222 hi2222 accepted2222
def lo2223b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨22,by decide⟩
def lo2223b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨23,by decide⟩
def lo2223 : CheckedMoment :=
  CheckedMoment.ofBessel lo2223b1 lo2223b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2223b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨27,by decide⟩
def hi2223b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨28,by decide⟩
def hi2223 : CheckedMoment :=
  CheckedMoment.ofBessel hi2223b1 hi2223b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2223 : meanBracketCheck (1949/2000) lo2223 hi2223=true := by decide +kernel
def bracket2223 : MeanBracket := meanBracketOfMoments (1949/2000) lo2223 hi2223 accepted2223
#print axioms bracket2208
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0138
