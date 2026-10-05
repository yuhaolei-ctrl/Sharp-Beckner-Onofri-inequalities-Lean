module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0337
public import BecknerOnofri.EntropyScalarCertificate.Bessel0338
public import BecknerOnofri.EntropyScalarCertificate.Bessel0339

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0135
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2160b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨32,by decide⟩
def lo2160b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨33,by decide⟩
def lo2160 : CheckedMoment :=
  CheckedMoment.ofBessel lo2160b1 lo2160b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2160b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨37,by decide⟩
def hi2160b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨38,by decide⟩
def hi2160 : CheckedMoment :=
  CheckedMoment.ofBessel hi2160b1 hi2160b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2160 : meanBracketCheck (4841/5000) lo2160 hi2160=true := by decide +kernel
def bracket2160 : MeanBracket := meanBracketOfMoments (4841/5000) lo2160 hi2160 accepted2160
def lo2161b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨42,by decide⟩
def lo2161b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨43,by decide⟩
def lo2161 : CheckedMoment :=
  CheckedMoment.ofBessel lo2161b1 lo2161b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2161b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨47,by decide⟩
def hi2161b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨48,by decide⟩
def hi2161 : CheckedMoment :=
  CheckedMoment.ofBessel hi2161b1 hi2161b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2161 : meanBracketCheck (9683/10000) lo2161 hi2161=true := by decide +kernel
def bracket2161 : MeanBracket := meanBracketOfMoments (9683/10000) lo2161 hi2161 accepted2161
def lo2162b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨52,by decide⟩
def lo2162b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨53,by decide⟩
def lo2162 : CheckedMoment :=
  CheckedMoment.ofBessel lo2162b1 lo2162b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2162b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨57,by decide⟩
def hi2162b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨58,by decide⟩
def hi2162 : CheckedMoment :=
  CheckedMoment.ofBessel hi2162b1 hi2162b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2162 : meanBracketCheck (2421/2500) lo2162 hi2162=true := by decide +kernel
def bracket2162 : MeanBracket := meanBracketOfMoments (2421/2500) lo2162 hi2162 accepted2162
def lo2163b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨62,by decide⟩
def lo2163b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨63,by decide⟩
def lo2163 : CheckedMoment :=
  CheckedMoment.ofBessel lo2163b1 lo2163b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2163b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨3,by decide⟩
def hi2163b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨4,by decide⟩
def hi2163 : CheckedMoment :=
  CheckedMoment.ofBessel hi2163b1 hi2163b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2163 : meanBracketCheck (1937/2000) lo2163 hi2163=true := by decide +kernel
def bracket2163 : MeanBracket := meanBracketOfMoments (1937/2000) lo2163 hi2163 accepted2163
def lo2164b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨8,by decide⟩
def lo2164b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨9,by decide⟩
def lo2164 : CheckedMoment :=
  CheckedMoment.ofBessel lo2164b1 lo2164b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2164b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨13,by decide⟩
def hi2164b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨14,by decide⟩
def hi2164 : CheckedMoment :=
  CheckedMoment.ofBessel hi2164b1 hi2164b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2164 : meanBracketCheck (4843/5000) lo2164 hi2164=true := by decide +kernel
def bracket2164 : MeanBracket := meanBracketOfMoments (4843/5000) lo2164 hi2164 accepted2164
def lo2165b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨18,by decide⟩
def lo2165b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨19,by decide⟩
def lo2165 : CheckedMoment :=
  CheckedMoment.ofBessel lo2165b1 lo2165b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2165b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨23,by decide⟩
def hi2165b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨24,by decide⟩
def hi2165 : CheckedMoment :=
  CheckedMoment.ofBessel hi2165b1 hi2165b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2165 : meanBracketCheck (9687/10000) lo2165 hi2165=true := by decide +kernel
def bracket2165 : MeanBracket := meanBracketOfMoments (9687/10000) lo2165 hi2165 accepted2165
def lo2166b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨28,by decide⟩
def lo2166b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨29,by decide⟩
def lo2166 : CheckedMoment :=
  CheckedMoment.ofBessel lo2166b1 lo2166b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2166b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨33,by decide⟩
def hi2166b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨34,by decide⟩
def hi2166 : CheckedMoment :=
  CheckedMoment.ofBessel hi2166b1 hi2166b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2166 : meanBracketCheck (1211/1250) lo2166 hi2166=true := by decide +kernel
def bracket2166 : MeanBracket := meanBracketOfMoments (1211/1250) lo2166 hi2166 accepted2166
def lo2167b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨38,by decide⟩
def lo2167b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨39,by decide⟩
def lo2167 : CheckedMoment :=
  CheckedMoment.ofBessel lo2167b1 lo2167b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2167b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨43,by decide⟩
def hi2167b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨44,by decide⟩
def hi2167 : CheckedMoment :=
  CheckedMoment.ofBessel hi2167b1 hi2167b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2167 : meanBracketCheck (9689/10000) lo2167 hi2167=true := by decide +kernel
def bracket2167 : MeanBracket := meanBracketOfMoments (9689/10000) lo2167 hi2167 accepted2167
def lo2168b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨48,by decide⟩
def lo2168b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨49,by decide⟩
def lo2168 : CheckedMoment :=
  CheckedMoment.ofBessel lo2168b1 lo2168b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2168b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨53,by decide⟩
def hi2168b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨54,by decide⟩
def hi2168 : CheckedMoment :=
  CheckedMoment.ofBessel hi2168b1 hi2168b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2168 : meanBracketCheck (969/1000) lo2168 hi2168=true := by decide +kernel
def bracket2168 : MeanBracket := meanBracketOfMoments (969/1000) lo2168 hi2168 accepted2168
def lo2169b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨58,by decide⟩
def lo2169b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨59,by decide⟩
def lo2169 : CheckedMoment :=
  CheckedMoment.ofBessel lo2169b1 lo2169b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2169b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨63,by decide⟩
def hi2169b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨0,by decide⟩
def hi2169 : CheckedMoment :=
  CheckedMoment.ofBessel hi2169b1 hi2169b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2169 : meanBracketCheck (9691/10000) lo2169 hi2169=true := by decide +kernel
def bracket2169 : MeanBracket := meanBracketOfMoments (9691/10000) lo2169 hi2169 accepted2169
def lo2170b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨4,by decide⟩
def lo2170b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨5,by decide⟩
def lo2170 : CheckedMoment :=
  CheckedMoment.ofBessel lo2170b1 lo2170b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2170b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨9,by decide⟩
def hi2170b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨10,by decide⟩
def hi2170 : CheckedMoment :=
  CheckedMoment.ofBessel hi2170b1 hi2170b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2170 : meanBracketCheck (2423/2500) lo2170 hi2170=true := by decide +kernel
def bracket2170 : MeanBracket := meanBracketOfMoments (2423/2500) lo2170 hi2170 accepted2170
def lo2171b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨14,by decide⟩
def lo2171b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨15,by decide⟩
def lo2171 : CheckedMoment :=
  CheckedMoment.ofBessel lo2171b1 lo2171b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2171b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨19,by decide⟩
def hi2171b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨20,by decide⟩
def hi2171 : CheckedMoment :=
  CheckedMoment.ofBessel hi2171b1 hi2171b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2171 : meanBracketCheck (9693/10000) lo2171 hi2171=true := by decide +kernel
def bracket2171 : MeanBracket := meanBracketOfMoments (9693/10000) lo2171 hi2171 accepted2171
def lo2172b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨24,by decide⟩
def lo2172b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨25,by decide⟩
def lo2172 : CheckedMoment :=
  CheckedMoment.ofBessel lo2172b1 lo2172b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2172b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨29,by decide⟩
def hi2172b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨30,by decide⟩
def hi2172 : CheckedMoment :=
  CheckedMoment.ofBessel hi2172b1 hi2172b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2172 : meanBracketCheck (4847/5000) lo2172 hi2172=true := by decide +kernel
def bracket2172 : MeanBracket := meanBracketOfMoments (4847/5000) lo2172 hi2172 accepted2172
def lo2173b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨34,by decide⟩
def lo2173b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨35,by decide⟩
def lo2173 : CheckedMoment :=
  CheckedMoment.ofBessel lo2173b1 lo2173b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2173b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨39,by decide⟩
def hi2173b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨40,by decide⟩
def hi2173 : CheckedMoment :=
  CheckedMoment.ofBessel hi2173b1 hi2173b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2173 : meanBracketCheck (1939/2000) lo2173 hi2173=true := by decide +kernel
def bracket2173 : MeanBracket := meanBracketOfMoments (1939/2000) lo2173 hi2173 accepted2173
def lo2174b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨44,by decide⟩
def lo2174b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨45,by decide⟩
def lo2174 : CheckedMoment :=
  CheckedMoment.ofBessel lo2174b1 lo2174b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2174b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨49,by decide⟩
def hi2174b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨50,by decide⟩
def hi2174 : CheckedMoment :=
  CheckedMoment.ofBessel hi2174b1 hi2174b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2174 : meanBracketCheck (606/625) lo2174 hi2174=true := by decide +kernel
def bracket2174 : MeanBracket := meanBracketOfMoments (606/625) lo2174 hi2174 accepted2174
def lo2175b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨54,by decide⟩
def lo2175b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨55,by decide⟩
def lo2175 : CheckedMoment :=
  CheckedMoment.ofBessel lo2175b1 lo2175b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2175b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨59,by decide⟩
def hi2175b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨60,by decide⟩
def hi2175 : CheckedMoment :=
  CheckedMoment.ofBessel hi2175b1 hi2175b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2175 : meanBracketCheck (9697/10000) lo2175 hi2175=true := by decide +kernel
def bracket2175 : MeanBracket := meanBracketOfMoments (9697/10000) lo2175 hi2175 accepted2175
#print axioms bracket2160
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0135
