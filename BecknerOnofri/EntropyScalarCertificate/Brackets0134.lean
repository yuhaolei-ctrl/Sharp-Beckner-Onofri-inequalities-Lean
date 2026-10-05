module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0335
public import BecknerOnofri.EntropyScalarCertificate.Bessel0336
public import BecknerOnofri.EntropyScalarCertificate.Bessel0337

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0134
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2144b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨0,by decide⟩
def lo2144b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨1,by decide⟩
def lo2144 : CheckedMoment :=
  CheckedMoment.ofBessel lo2144b1 lo2144b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2144b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨5,by decide⟩
def hi2144b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨6,by decide⟩
def hi2144 : CheckedMoment :=
  CheckedMoment.ofBessel hi2144b1 hi2144b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2144 : meanBracketCheck (4833/5000) lo2144 hi2144=true := by decide +kernel
def bracket2144 : MeanBracket := meanBracketOfMoments (4833/5000) lo2144 hi2144 accepted2144
def lo2145b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨10,by decide⟩
def lo2145b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨11,by decide⟩
def lo2145 : CheckedMoment :=
  CheckedMoment.ofBessel lo2145b1 lo2145b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2145b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨15,by decide⟩
def hi2145b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨16,by decide⟩
def hi2145 : CheckedMoment :=
  CheckedMoment.ofBessel hi2145b1 hi2145b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2145 : meanBracketCheck (9667/10000) lo2145 hi2145=true := by decide +kernel
def bracket2145 : MeanBracket := meanBracketOfMoments (9667/10000) lo2145 hi2145 accepted2145
def lo2146b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨20,by decide⟩
def lo2146b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨21,by decide⟩
def lo2146 : CheckedMoment :=
  CheckedMoment.ofBessel lo2146b1 lo2146b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2146b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨25,by decide⟩
def hi2146b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨26,by decide⟩
def hi2146 : CheckedMoment :=
  CheckedMoment.ofBessel hi2146b1 hi2146b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2146 : meanBracketCheck (2417/2500) lo2146 hi2146=true := by decide +kernel
def bracket2146 : MeanBracket := meanBracketOfMoments (2417/2500) lo2146 hi2146 accepted2146
def lo2147b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨30,by decide⟩
def lo2147b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨31,by decide⟩
def lo2147 : CheckedMoment :=
  CheckedMoment.ofBessel lo2147b1 lo2147b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2147b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨35,by decide⟩
def hi2147b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨36,by decide⟩
def hi2147 : CheckedMoment :=
  CheckedMoment.ofBessel hi2147b1 hi2147b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2147 : meanBracketCheck (9669/10000) lo2147 hi2147=true := by decide +kernel
def bracket2147 : MeanBracket := meanBracketOfMoments (9669/10000) lo2147 hi2147 accepted2147
def lo2148b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨40,by decide⟩
def lo2148b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨41,by decide⟩
def lo2148 : CheckedMoment :=
  CheckedMoment.ofBessel lo2148b1 lo2148b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2148b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨45,by decide⟩
def hi2148b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨46,by decide⟩
def hi2148 : CheckedMoment :=
  CheckedMoment.ofBessel hi2148b1 hi2148b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2148 : meanBracketCheck (967/1000) lo2148 hi2148=true := by decide +kernel
def bracket2148 : MeanBracket := meanBracketOfMoments (967/1000) lo2148 hi2148 accepted2148
def lo2149b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨50,by decide⟩
def lo2149b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨51,by decide⟩
def lo2149 : CheckedMoment :=
  CheckedMoment.ofBessel lo2149b1 lo2149b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2149b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨55,by decide⟩
def hi2149b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨56,by decide⟩
def hi2149 : CheckedMoment :=
  CheckedMoment.ofBessel hi2149b1 hi2149b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2149 : meanBracketCheck (9671/10000) lo2149 hi2149=true := by decide +kernel
def bracket2149 : MeanBracket := meanBracketOfMoments (9671/10000) lo2149 hi2149 accepted2149
def lo2150b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨60,by decide⟩
def lo2150b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨61,by decide⟩
def lo2150 : CheckedMoment :=
  CheckedMoment.ofBessel lo2150b1 lo2150b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2150b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨1,by decide⟩
def hi2150b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨2,by decide⟩
def hi2150 : CheckedMoment :=
  CheckedMoment.ofBessel hi2150b1 hi2150b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2150 : meanBracketCheck (1209/1250) lo2150 hi2150=true := by decide +kernel
def bracket2150 : MeanBracket := meanBracketOfMoments (1209/1250) lo2150 hi2150 accepted2150
def lo2151b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨6,by decide⟩
def lo2151b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨7,by decide⟩
def lo2151 : CheckedMoment :=
  CheckedMoment.ofBessel lo2151b1 lo2151b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2151b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨11,by decide⟩
def hi2151b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨12,by decide⟩
def hi2151 : CheckedMoment :=
  CheckedMoment.ofBessel hi2151b1 hi2151b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2151 : meanBracketCheck (9673/10000) lo2151 hi2151=true := by decide +kernel
def bracket2151 : MeanBracket := meanBracketOfMoments (9673/10000) lo2151 hi2151 accepted2151
def lo2152b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨16,by decide⟩
def lo2152b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨17,by decide⟩
def lo2152 : CheckedMoment :=
  CheckedMoment.ofBessel lo2152b1 lo2152b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2152b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨21,by decide⟩
def hi2152b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨22,by decide⟩
def hi2152 : CheckedMoment :=
  CheckedMoment.ofBessel hi2152b1 hi2152b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2152 : meanBracketCheck (4837/5000) lo2152 hi2152=true := by decide +kernel
def bracket2152 : MeanBracket := meanBracketOfMoments (4837/5000) lo2152 hi2152 accepted2152
def lo2153b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨26,by decide⟩
def lo2153b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨27,by decide⟩
def lo2153 : CheckedMoment :=
  CheckedMoment.ofBessel lo2153b1 lo2153b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2153b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨31,by decide⟩
def hi2153b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨32,by decide⟩
def hi2153 : CheckedMoment :=
  CheckedMoment.ofBessel hi2153b1 hi2153b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2153 : meanBracketCheck (387/400) lo2153 hi2153=true := by decide +kernel
def bracket2153 : MeanBracket := meanBracketOfMoments (387/400) lo2153 hi2153 accepted2153
def lo2154b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨36,by decide⟩
def lo2154b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨37,by decide⟩
def lo2154 : CheckedMoment :=
  CheckedMoment.ofBessel lo2154b1 lo2154b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2154b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨41,by decide⟩
def hi2154b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨42,by decide⟩
def hi2154 : CheckedMoment :=
  CheckedMoment.ofBessel hi2154b1 hi2154b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2154 : meanBracketCheck (2419/2500) lo2154 hi2154=true := by decide +kernel
def bracket2154 : MeanBracket := meanBracketOfMoments (2419/2500) lo2154 hi2154 accepted2154
def lo2155b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨46,by decide⟩
def lo2155b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨47,by decide⟩
def lo2155 : CheckedMoment :=
  CheckedMoment.ofBessel lo2155b1 lo2155b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2155b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨51,by decide⟩
def hi2155b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨52,by decide⟩
def hi2155 : CheckedMoment :=
  CheckedMoment.ofBessel hi2155b1 hi2155b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2155 : meanBracketCheck (9677/10000) lo2155 hi2155=true := by decide +kernel
def bracket2155 : MeanBracket := meanBracketOfMoments (9677/10000) lo2155 hi2155 accepted2155
def lo2156b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨56,by decide⟩
def lo2156b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨57,by decide⟩
def lo2156 : CheckedMoment :=
  CheckedMoment.ofBessel lo2156b1 lo2156b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2156b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨61,by decide⟩
def hi2156b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨62,by decide⟩
def hi2156 : CheckedMoment :=
  CheckedMoment.ofBessel hi2156b1 hi2156b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2156 : meanBracketCheck (4839/5000) lo2156 hi2156=true := by decide +kernel
def bracket2156 : MeanBracket := meanBracketOfMoments (4839/5000) lo2156 hi2156 accepted2156
def lo2157b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨2,by decide⟩
def lo2157b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨3,by decide⟩
def lo2157 : CheckedMoment :=
  CheckedMoment.ofBessel lo2157b1 lo2157b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2157b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨7,by decide⟩
def hi2157b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨8,by decide⟩
def hi2157 : CheckedMoment :=
  CheckedMoment.ofBessel hi2157b1 hi2157b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2157 : meanBracketCheck (9679/10000) lo2157 hi2157=true := by decide +kernel
def bracket2157 : MeanBracket := meanBracketOfMoments (9679/10000) lo2157 hi2157 accepted2157
def lo2158b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨12,by decide⟩
def lo2158b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨13,by decide⟩
def lo2158 : CheckedMoment :=
  CheckedMoment.ofBessel lo2158b1 lo2158b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2158b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨17,by decide⟩
def hi2158b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨18,by decide⟩
def hi2158 : CheckedMoment :=
  CheckedMoment.ofBessel hi2158b1 hi2158b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2158 : meanBracketCheck (121/125) lo2158 hi2158=true := by decide +kernel
def bracket2158 : MeanBracket := meanBracketOfMoments (121/125) lo2158 hi2158 accepted2158
def lo2159b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨22,by decide⟩
def lo2159b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨23,by decide⟩
def lo2159 : CheckedMoment :=
  CheckedMoment.ofBessel lo2159b1 lo2159b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2159b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨27,by decide⟩
def hi2159b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨28,by decide⟩
def hi2159 : CheckedMoment :=
  CheckedMoment.ofBessel hi2159b1 hi2159b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2159 : meanBracketCheck (9681/10000) lo2159 hi2159=true := by decide +kernel
def bracket2159 : MeanBracket := meanBracketOfMoments (9681/10000) lo2159 hi2159 accepted2159
#print axioms bracket2144
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0134
