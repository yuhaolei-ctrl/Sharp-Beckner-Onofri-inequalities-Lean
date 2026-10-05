module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0037
public import BecknerOnofri.EntropyScalarCertificate.Bessel0038
public import BecknerOnofri.EntropyScalarCertificate.Bessel0039

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0015
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0240b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨32,by decide⟩
def lo0240b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨33,by decide⟩
def lo0240 : CheckedMoment :=
  CheckedMoment.ofBessel lo0240b1 lo0240b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0240b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨37,by decide⟩
def hi0240b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨38,by decide⟩
def hi0240 : CheckedMoment :=
  CheckedMoment.ofBessel hi0240b1 hi0240b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0240 : meanBracketCheck (209/2000) lo0240 hi0240=true := by decide +kernel
def bracket0240 : MeanBracket := meanBracketOfMoments (209/2000) lo0240 hi0240 accepted0240
def lo0241b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨42,by decide⟩
def lo0241b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨43,by decide⟩
def lo0241 : CheckedMoment :=
  CheckedMoment.ofBessel lo0241b1 lo0241b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0241b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨47,by decide⟩
def hi0241b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨48,by decide⟩
def hi0241 : CheckedMoment :=
  CheckedMoment.ofBessel hi0241b1 hi0241b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0241 : meanBracketCheck (1047/10000) lo0241 hi0241=true := by decide +kernel
def bracket0241 : MeanBracket := meanBracketOfMoments (1047/10000) lo0241 hi0241 accepted0241
def lo0242b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨52,by decide⟩
def lo0242b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨53,by decide⟩
def lo0242 : CheckedMoment :=
  CheckedMoment.ofBessel lo0242b1 lo0242b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0242b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨57,by decide⟩
def hi0242b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨58,by decide⟩
def hi0242 : CheckedMoment :=
  CheckedMoment.ofBessel hi0242b1 hi0242b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0242 : meanBracketCheck (1049/10000) lo0242 hi0242=true := by decide +kernel
def bracket0242 : MeanBracket := meanBracketOfMoments (1049/10000) lo0242 hi0242 accepted0242
def lo0243b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨62,by decide⟩
def lo0243b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨63,by decide⟩
def lo0243 : CheckedMoment :=
  CheckedMoment.ofBessel lo0243b1 lo0243b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0243b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨3,by decide⟩
def hi0243b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨4,by decide⟩
def hi0243 : CheckedMoment :=
  CheckedMoment.ofBessel hi0243b1 hi0243b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0243 : meanBracketCheck (1051/10000) lo0243 hi0243=true := by decide +kernel
def bracket0243 : MeanBracket := meanBracketOfMoments (1051/10000) lo0243 hi0243 accepted0243
def lo0244b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨8,by decide⟩
def lo0244b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨9,by decide⟩
def lo0244 : CheckedMoment :=
  CheckedMoment.ofBessel lo0244b1 lo0244b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0244b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨13,by decide⟩
def hi0244b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨14,by decide⟩
def hi0244 : CheckedMoment :=
  CheckedMoment.ofBessel hi0244b1 hi0244b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0244 : meanBracketCheck (1053/10000) lo0244 hi0244=true := by decide +kernel
def bracket0244 : MeanBracket := meanBracketOfMoments (1053/10000) lo0244 hi0244 accepted0244
def lo0245b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨18,by decide⟩
def lo0245b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨19,by decide⟩
def lo0245 : CheckedMoment :=
  CheckedMoment.ofBessel lo0245b1 lo0245b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0245b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨23,by decide⟩
def hi0245b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨24,by decide⟩
def hi0245 : CheckedMoment :=
  CheckedMoment.ofBessel hi0245b1 hi0245b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0245 : meanBracketCheck (211/2000) lo0245 hi0245=true := by decide +kernel
def bracket0245 : MeanBracket := meanBracketOfMoments (211/2000) lo0245 hi0245 accepted0245
def lo0246b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨28,by decide⟩
def lo0246b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨29,by decide⟩
def lo0246 : CheckedMoment :=
  CheckedMoment.ofBessel lo0246b1 lo0246b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0246b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨33,by decide⟩
def hi0246b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨34,by decide⟩
def hi0246 : CheckedMoment :=
  CheckedMoment.ofBessel hi0246b1 hi0246b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0246 : meanBracketCheck (1057/10000) lo0246 hi0246=true := by decide +kernel
def bracket0246 : MeanBracket := meanBracketOfMoments (1057/10000) lo0246 hi0246 accepted0246
def lo0247b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨38,by decide⟩
def lo0247b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨39,by decide⟩
def lo0247 : CheckedMoment :=
  CheckedMoment.ofBessel lo0247b1 lo0247b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0247b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨43,by decide⟩
def hi0247b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨44,by decide⟩
def hi0247 : CheckedMoment :=
  CheckedMoment.ofBessel hi0247b1 hi0247b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0247 : meanBracketCheck (1059/10000) lo0247 hi0247=true := by decide +kernel
def bracket0247 : MeanBracket := meanBracketOfMoments (1059/10000) lo0247 hi0247 accepted0247
def lo0248b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨48,by decide⟩
def lo0248b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨49,by decide⟩
def lo0248 : CheckedMoment :=
  CheckedMoment.ofBessel lo0248b1 lo0248b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0248b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨53,by decide⟩
def hi0248b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨54,by decide⟩
def hi0248 : CheckedMoment :=
  CheckedMoment.ofBessel hi0248b1 hi0248b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0248 : meanBracketCheck (1061/10000) lo0248 hi0248=true := by decide +kernel
def bracket0248 : MeanBracket := meanBracketOfMoments (1061/10000) lo0248 hi0248 accepted0248
def lo0249b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨58,by decide⟩
def lo0249b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨59,by decide⟩
def lo0249 : CheckedMoment :=
  CheckedMoment.ofBessel lo0249b1 lo0249b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0249b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨63,by decide⟩
def hi0249b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨0,by decide⟩
def hi0249 : CheckedMoment :=
  CheckedMoment.ofBessel hi0249b1 hi0249b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0249 : meanBracketCheck (1063/10000) lo0249 hi0249=true := by decide +kernel
def bracket0249 : MeanBracket := meanBracketOfMoments (1063/10000) lo0249 hi0249 accepted0249
def lo0250b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨4,by decide⟩
def lo0250b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨5,by decide⟩
def lo0250 : CheckedMoment :=
  CheckedMoment.ofBessel lo0250b1 lo0250b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0250b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨9,by decide⟩
def hi0250b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨10,by decide⟩
def hi0250 : CheckedMoment :=
  CheckedMoment.ofBessel hi0250b1 hi0250b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0250 : meanBracketCheck (213/2000) lo0250 hi0250=true := by decide +kernel
def bracket0250 : MeanBracket := meanBracketOfMoments (213/2000) lo0250 hi0250 accepted0250
def lo0251b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨14,by decide⟩
def lo0251b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨15,by decide⟩
def lo0251 : CheckedMoment :=
  CheckedMoment.ofBessel lo0251b1 lo0251b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0251b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨19,by decide⟩
def hi0251b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨20,by decide⟩
def hi0251 : CheckedMoment :=
  CheckedMoment.ofBessel hi0251b1 hi0251b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0251 : meanBracketCheck (1067/10000) lo0251 hi0251=true := by decide +kernel
def bracket0251 : MeanBracket := meanBracketOfMoments (1067/10000) lo0251 hi0251 accepted0251
def lo0252b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨24,by decide⟩
def lo0252b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨25,by decide⟩
def lo0252 : CheckedMoment :=
  CheckedMoment.ofBessel lo0252b1 lo0252b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0252b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨29,by decide⟩
def hi0252b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨30,by decide⟩
def hi0252 : CheckedMoment :=
  CheckedMoment.ofBessel hi0252b1 hi0252b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0252 : meanBracketCheck (1069/10000) lo0252 hi0252=true := by decide +kernel
def bracket0252 : MeanBracket := meanBracketOfMoments (1069/10000) lo0252 hi0252 accepted0252
def lo0253b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨34,by decide⟩
def lo0253b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨35,by decide⟩
def lo0253 : CheckedMoment :=
  CheckedMoment.ofBessel lo0253b1 lo0253b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0253b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨39,by decide⟩
def hi0253b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨40,by decide⟩
def hi0253 : CheckedMoment :=
  CheckedMoment.ofBessel hi0253b1 hi0253b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0253 : meanBracketCheck (1071/10000) lo0253 hi0253=true := by decide +kernel
def bracket0253 : MeanBracket := meanBracketOfMoments (1071/10000) lo0253 hi0253 accepted0253
def lo0254b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨44,by decide⟩
def lo0254b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨45,by decide⟩
def lo0254 : CheckedMoment :=
  CheckedMoment.ofBessel lo0254b1 lo0254b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0254b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨49,by decide⟩
def hi0254b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨50,by decide⟩
def hi0254 : CheckedMoment :=
  CheckedMoment.ofBessel hi0254b1 hi0254b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0254 : meanBracketCheck (1073/10000) lo0254 hi0254=true := by decide +kernel
def bracket0254 : MeanBracket := meanBracketOfMoments (1073/10000) lo0254 hi0254 accepted0254
def lo0255b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨54,by decide⟩
def lo0255b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨55,by decide⟩
def lo0255 : CheckedMoment :=
  CheckedMoment.ofBessel lo0255b1 lo0255b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0255b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨59,by decide⟩
def hi0255b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨60,by decide⟩
def hi0255 : CheckedMoment :=
  CheckedMoment.ofBessel hi0255b1 hi0255b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0255 : meanBracketCheck (43/400) lo0255 hi0255=true := by decide +kernel
def bracket0255 : MeanBracket := meanBracketOfMoments (43/400) lo0255 hi0255 accepted0255
#print axioms bracket0240
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0015
