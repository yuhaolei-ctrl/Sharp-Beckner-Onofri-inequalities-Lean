module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0342
public import BecknerOnofri.EntropyScalarCertificate.Bessel0343
public import BecknerOnofri.EntropyScalarCertificate.Bessel0344

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0137
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2192b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨32,by decide⟩
def lo2192b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨33,by decide⟩
def lo2192 : CheckedMoment :=
  CheckedMoment.ofBessel lo2192b1 lo2192b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2192b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨37,by decide⟩
def hi2192b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨38,by decide⟩
def hi2192 : CheckedMoment :=
  CheckedMoment.ofBessel hi2192b1 hi2192b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2192 : meanBracketCheck (4857/5000) lo2192 hi2192=true := by decide +kernel
def bracket2192 : MeanBracket := meanBracketOfMoments (4857/5000) lo2192 hi2192 accepted2192
def lo2193b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨42,by decide⟩
def lo2193b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨43,by decide⟩
def lo2193 : CheckedMoment :=
  CheckedMoment.ofBessel lo2193b1 lo2193b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2193b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨47,by decide⟩
def hi2193b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨48,by decide⟩
def hi2193 : CheckedMoment :=
  CheckedMoment.ofBessel hi2193b1 hi2193b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2193 : meanBracketCheck (1943/2000) lo2193 hi2193=true := by decide +kernel
def bracket2193 : MeanBracket := meanBracketOfMoments (1943/2000) lo2193 hi2193 accepted2193
def lo2194b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨52,by decide⟩
def lo2194b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨53,by decide⟩
def lo2194 : CheckedMoment :=
  CheckedMoment.ofBessel lo2194b1 lo2194b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2194b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨57,by decide⟩
def hi2194b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨58,by decide⟩
def hi2194 : CheckedMoment :=
  CheckedMoment.ofBessel hi2194b1 hi2194b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2194 : meanBracketCheck (2429/2500) lo2194 hi2194=true := by decide +kernel
def bracket2194 : MeanBracket := meanBracketOfMoments (2429/2500) lo2194 hi2194 accepted2194
def lo2195b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨62,by decide⟩
def lo2195b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨63,by decide⟩
def lo2195 : CheckedMoment :=
  CheckedMoment.ofBessel lo2195b1 lo2195b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2195b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨3,by decide⟩
def hi2195b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨4,by decide⟩
def hi2195 : CheckedMoment :=
  CheckedMoment.ofBessel hi2195b1 hi2195b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2195 : meanBracketCheck (9717/10000) lo2195 hi2195=true := by decide +kernel
def bracket2195 : MeanBracket := meanBracketOfMoments (9717/10000) lo2195 hi2195 accepted2195
def lo2196b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨8,by decide⟩
def lo2196b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨9,by decide⟩
def lo2196 : CheckedMoment :=
  CheckedMoment.ofBessel lo2196b1 lo2196b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2196b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨13,by decide⟩
def hi2196b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨14,by decide⟩
def hi2196 : CheckedMoment :=
  CheckedMoment.ofBessel hi2196b1 hi2196b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2196 : meanBracketCheck (4859/5000) lo2196 hi2196=true := by decide +kernel
def bracket2196 : MeanBracket := meanBracketOfMoments (4859/5000) lo2196 hi2196 accepted2196
def lo2197b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨18,by decide⟩
def lo2197b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨19,by decide⟩
def lo2197 : CheckedMoment :=
  CheckedMoment.ofBessel lo2197b1 lo2197b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2197b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨23,by decide⟩
def hi2197b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨24,by decide⟩
def hi2197 : CheckedMoment :=
  CheckedMoment.ofBessel hi2197b1 hi2197b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2197 : meanBracketCheck (9719/10000) lo2197 hi2197=true := by decide +kernel
def bracket2197 : MeanBracket := meanBracketOfMoments (9719/10000) lo2197 hi2197 accepted2197
def lo2198b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨28,by decide⟩
def lo2198b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨29,by decide⟩
def lo2198 : CheckedMoment :=
  CheckedMoment.ofBessel lo2198b1 lo2198b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2198b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨33,by decide⟩
def hi2198b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨34,by decide⟩
def hi2198 : CheckedMoment :=
  CheckedMoment.ofBessel hi2198b1 hi2198b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2198 : meanBracketCheck (243/250) lo2198 hi2198=true := by decide +kernel
def bracket2198 : MeanBracket := meanBracketOfMoments (243/250) lo2198 hi2198 accepted2198
def lo2199b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨38,by decide⟩
def lo2199b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨39,by decide⟩
def lo2199 : CheckedMoment :=
  CheckedMoment.ofBessel lo2199b1 lo2199b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2199b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨43,by decide⟩
def hi2199b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨44,by decide⟩
def hi2199 : CheckedMoment :=
  CheckedMoment.ofBessel hi2199b1 hi2199b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2199 : meanBracketCheck (9721/10000) lo2199 hi2199=true := by decide +kernel
def bracket2199 : MeanBracket := meanBracketOfMoments (9721/10000) lo2199 hi2199 accepted2199
def lo2200b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨48,by decide⟩
def lo2200b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨49,by decide⟩
def lo2200 : CheckedMoment :=
  CheckedMoment.ofBessel lo2200b1 lo2200b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2200b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨53,by decide⟩
def hi2200b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨54,by decide⟩
def hi2200 : CheckedMoment :=
  CheckedMoment.ofBessel hi2200b1 hi2200b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2200 : meanBracketCheck (4861/5000) lo2200 hi2200=true := by decide +kernel
def bracket2200 : MeanBracket := meanBracketOfMoments (4861/5000) lo2200 hi2200 accepted2200
def lo2201b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨58,by decide⟩
def lo2201b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨59,by decide⟩
def lo2201 : CheckedMoment :=
  CheckedMoment.ofBessel lo2201b1 lo2201b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2201b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨63,by decide⟩
def hi2201b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨0,by decide⟩
def hi2201 : CheckedMoment :=
  CheckedMoment.ofBessel hi2201b1 hi2201b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2201 : meanBracketCheck (9723/10000) lo2201 hi2201=true := by decide +kernel
def bracket2201 : MeanBracket := meanBracketOfMoments (9723/10000) lo2201 hi2201 accepted2201
def lo2202b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨4,by decide⟩
def lo2202b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨5,by decide⟩
def lo2202 : CheckedMoment :=
  CheckedMoment.ofBessel lo2202b1 lo2202b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2202b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨9,by decide⟩
def hi2202b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨10,by decide⟩
def hi2202 : CheckedMoment :=
  CheckedMoment.ofBessel hi2202b1 hi2202b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2202 : meanBracketCheck (2431/2500) lo2202 hi2202=true := by decide +kernel
def bracket2202 : MeanBracket := meanBracketOfMoments (2431/2500) lo2202 hi2202 accepted2202
def lo2203b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨14,by decide⟩
def lo2203b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨15,by decide⟩
def lo2203 : CheckedMoment :=
  CheckedMoment.ofBessel lo2203b1 lo2203b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2203b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨19,by decide⟩
def hi2203b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨20,by decide⟩
def hi2203 : CheckedMoment :=
  CheckedMoment.ofBessel hi2203b1 hi2203b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2203 : meanBracketCheck (389/400) lo2203 hi2203=true := by decide +kernel
def bracket2203 : MeanBracket := meanBracketOfMoments (389/400) lo2203 hi2203 accepted2203
def lo2204b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨24,by decide⟩
def lo2204b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨25,by decide⟩
def lo2204 : CheckedMoment :=
  CheckedMoment.ofBessel lo2204b1 lo2204b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2204b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨29,by decide⟩
def hi2204b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨30,by decide⟩
def hi2204 : CheckedMoment :=
  CheckedMoment.ofBessel hi2204b1 hi2204b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2204 : meanBracketCheck (4863/5000) lo2204 hi2204=true := by decide +kernel
def bracket2204 : MeanBracket := meanBracketOfMoments (4863/5000) lo2204 hi2204 accepted2204
def lo2205b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨34,by decide⟩
def lo2205b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨35,by decide⟩
def lo2205 : CheckedMoment :=
  CheckedMoment.ofBessel lo2205b1 lo2205b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2205b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨39,by decide⟩
def hi2205b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨40,by decide⟩
def hi2205 : CheckedMoment :=
  CheckedMoment.ofBessel hi2205b1 hi2205b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2205 : meanBracketCheck (9727/10000) lo2205 hi2205=true := by decide +kernel
def bracket2205 : MeanBracket := meanBracketOfMoments (9727/10000) lo2205 hi2205 accepted2205
def lo2206b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨44,by decide⟩
def lo2206b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨45,by decide⟩
def lo2206 : CheckedMoment :=
  CheckedMoment.ofBessel lo2206b1 lo2206b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2206b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨49,by decide⟩
def hi2206b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨50,by decide⟩
def hi2206 : CheckedMoment :=
  CheckedMoment.ofBessel hi2206b1 hi2206b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2206 : meanBracketCheck (608/625) lo2206 hi2206=true := by decide +kernel
def bracket2206 : MeanBracket := meanBracketOfMoments (608/625) lo2206 hi2206 accepted2206
def lo2207b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨54,by decide⟩
def lo2207b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨55,by decide⟩
def lo2207 : CheckedMoment :=
  CheckedMoment.ofBessel lo2207b1 lo2207b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2207b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨59,by decide⟩
def hi2207b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0344.rows BesselBatch0344.accepted ⟨60,by decide⟩
def hi2207 : CheckedMoment :=
  CheckedMoment.ofBessel hi2207b1 hi2207b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2207 : meanBracketCheck (9729/10000) lo2207 hi2207=true := by decide +kernel
def bracket2207 : MeanBracket := meanBracketOfMoments (9729/10000) lo2207 hi2207 accepted2207
#print axioms bracket2192
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0137
