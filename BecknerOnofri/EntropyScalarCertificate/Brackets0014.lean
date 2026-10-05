module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0035
public import BecknerOnofri.EntropyScalarCertificate.Bessel0036
public import BecknerOnofri.EntropyScalarCertificate.Bessel0037

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0014
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0224b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨0,by decide⟩
def lo0224b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨1,by decide⟩
def lo0224 : CheckedMoment :=
  CheckedMoment.ofBessel lo0224b1 lo0224b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0224b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨5,by decide⟩
def hi0224b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨6,by decide⟩
def hi0224 : CheckedMoment :=
  CheckedMoment.ofBessel hi0224b1 hi0224b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0224 : meanBracketCheck (1013/10000) lo0224 hi0224=true := by decide +kernel
def bracket0224 : MeanBracket := meanBracketOfMoments (1013/10000) lo0224 hi0224 accepted0224
def lo0225b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨10,by decide⟩
def lo0225b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨11,by decide⟩
def lo0225 : CheckedMoment :=
  CheckedMoment.ofBessel lo0225b1 lo0225b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0225b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨15,by decide⟩
def hi0225b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨16,by decide⟩
def hi0225 : CheckedMoment :=
  CheckedMoment.ofBessel hi0225b1 hi0225b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0225 : meanBracketCheck (203/2000) lo0225 hi0225=true := by decide +kernel
def bracket0225 : MeanBracket := meanBracketOfMoments (203/2000) lo0225 hi0225 accepted0225
def lo0226b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨20,by decide⟩
def lo0226b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨21,by decide⟩
def lo0226 : CheckedMoment :=
  CheckedMoment.ofBessel lo0226b1 lo0226b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0226b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨25,by decide⟩
def hi0226b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨26,by decide⟩
def hi0226 : CheckedMoment :=
  CheckedMoment.ofBessel hi0226b1 hi0226b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0226 : meanBracketCheck (1017/10000) lo0226 hi0226=true := by decide +kernel
def bracket0226 : MeanBracket := meanBracketOfMoments (1017/10000) lo0226 hi0226 accepted0226
def lo0227b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨30,by decide⟩
def lo0227b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨31,by decide⟩
def lo0227 : CheckedMoment :=
  CheckedMoment.ofBessel lo0227b1 lo0227b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0227b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨35,by decide⟩
def hi0227b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨36,by decide⟩
def hi0227 : CheckedMoment :=
  CheckedMoment.ofBessel hi0227b1 hi0227b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0227 : meanBracketCheck (1019/10000) lo0227 hi0227=true := by decide +kernel
def bracket0227 : MeanBracket := meanBracketOfMoments (1019/10000) lo0227 hi0227 accepted0227
def lo0228b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨40,by decide⟩
def lo0228b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨41,by decide⟩
def lo0228 : CheckedMoment :=
  CheckedMoment.ofBessel lo0228b1 lo0228b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0228b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨45,by decide⟩
def hi0228b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨46,by decide⟩
def hi0228 : CheckedMoment :=
  CheckedMoment.ofBessel hi0228b1 hi0228b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0228 : meanBracketCheck (1021/10000) lo0228 hi0228=true := by decide +kernel
def bracket0228 : MeanBracket := meanBracketOfMoments (1021/10000) lo0228 hi0228 accepted0228
def lo0229b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨50,by decide⟩
def lo0229b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨51,by decide⟩
def lo0229 : CheckedMoment :=
  CheckedMoment.ofBessel lo0229b1 lo0229b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0229b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨55,by decide⟩
def hi0229b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨56,by decide⟩
def hi0229 : CheckedMoment :=
  CheckedMoment.ofBessel hi0229b1 hi0229b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0229 : meanBracketCheck (1023/10000) lo0229 hi0229=true := by decide +kernel
def bracket0229 : MeanBracket := meanBracketOfMoments (1023/10000) lo0229 hi0229 accepted0229
def lo0230b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨60,by decide⟩
def lo0230b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨61,by decide⟩
def lo0230 : CheckedMoment :=
  CheckedMoment.ofBessel lo0230b1 lo0230b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0230b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨1,by decide⟩
def hi0230b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨2,by decide⟩
def hi0230 : CheckedMoment :=
  CheckedMoment.ofBessel hi0230b1 hi0230b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0230 : meanBracketCheck (41/400) lo0230 hi0230=true := by decide +kernel
def bracket0230 : MeanBracket := meanBracketOfMoments (41/400) lo0230 hi0230 accepted0230
def lo0231b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨6,by decide⟩
def lo0231b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨7,by decide⟩
def lo0231 : CheckedMoment :=
  CheckedMoment.ofBessel lo0231b1 lo0231b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0231b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨11,by decide⟩
def hi0231b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨12,by decide⟩
def hi0231 : CheckedMoment :=
  CheckedMoment.ofBessel hi0231b1 hi0231b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0231 : meanBracketCheck (1027/10000) lo0231 hi0231=true := by decide +kernel
def bracket0231 : MeanBracket := meanBracketOfMoments (1027/10000) lo0231 hi0231 accepted0231
def lo0232b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨16,by decide⟩
def lo0232b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨17,by decide⟩
def lo0232 : CheckedMoment :=
  CheckedMoment.ofBessel lo0232b1 lo0232b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0232b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨21,by decide⟩
def hi0232b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨22,by decide⟩
def hi0232 : CheckedMoment :=
  CheckedMoment.ofBessel hi0232b1 hi0232b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0232 : meanBracketCheck (1029/10000) lo0232 hi0232=true := by decide +kernel
def bracket0232 : MeanBracket := meanBracketOfMoments (1029/10000) lo0232 hi0232 accepted0232
def lo0233b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨26,by decide⟩
def lo0233b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨27,by decide⟩
def lo0233 : CheckedMoment :=
  CheckedMoment.ofBessel lo0233b1 lo0233b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0233b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨31,by decide⟩
def hi0233b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨32,by decide⟩
def hi0233 : CheckedMoment :=
  CheckedMoment.ofBessel hi0233b1 hi0233b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0233 : meanBracketCheck (1031/10000) lo0233 hi0233=true := by decide +kernel
def bracket0233 : MeanBracket := meanBracketOfMoments (1031/10000) lo0233 hi0233 accepted0233
def lo0234b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨36,by decide⟩
def lo0234b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨37,by decide⟩
def lo0234 : CheckedMoment :=
  CheckedMoment.ofBessel lo0234b1 lo0234b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0234b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨41,by decide⟩
def hi0234b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨42,by decide⟩
def hi0234 : CheckedMoment :=
  CheckedMoment.ofBessel hi0234b1 hi0234b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0234 : meanBracketCheck (1033/10000) lo0234 hi0234=true := by decide +kernel
def bracket0234 : MeanBracket := meanBracketOfMoments (1033/10000) lo0234 hi0234 accepted0234
def lo0235b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨46,by decide⟩
def lo0235b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨47,by decide⟩
def lo0235 : CheckedMoment :=
  CheckedMoment.ofBessel lo0235b1 lo0235b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0235b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨51,by decide⟩
def hi0235b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨52,by decide⟩
def hi0235 : CheckedMoment :=
  CheckedMoment.ofBessel hi0235b1 hi0235b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0235 : meanBracketCheck (207/2000) lo0235 hi0235=true := by decide +kernel
def bracket0235 : MeanBracket := meanBracketOfMoments (207/2000) lo0235 hi0235 accepted0235
def lo0236b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨56,by decide⟩
def lo0236b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨57,by decide⟩
def lo0236 : CheckedMoment :=
  CheckedMoment.ofBessel lo0236b1 lo0236b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0236b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨61,by decide⟩
def hi0236b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨62,by decide⟩
def hi0236 : CheckedMoment :=
  CheckedMoment.ofBessel hi0236b1 hi0236b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0236 : meanBracketCheck (1037/10000) lo0236 hi0236=true := by decide +kernel
def bracket0236 : MeanBracket := meanBracketOfMoments (1037/10000) lo0236 hi0236 accepted0236
def lo0237b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨2,by decide⟩
def lo0237b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨3,by decide⟩
def lo0237 : CheckedMoment :=
  CheckedMoment.ofBessel lo0237b1 lo0237b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0237b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨7,by decide⟩
def hi0237b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨8,by decide⟩
def hi0237 : CheckedMoment :=
  CheckedMoment.ofBessel hi0237b1 hi0237b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0237 : meanBracketCheck (1039/10000) lo0237 hi0237=true := by decide +kernel
def bracket0237 : MeanBracket := meanBracketOfMoments (1039/10000) lo0237 hi0237 accepted0237
def lo0238b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨12,by decide⟩
def lo0238b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨13,by decide⟩
def lo0238 : CheckedMoment :=
  CheckedMoment.ofBessel lo0238b1 lo0238b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0238b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨17,by decide⟩
def hi0238b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨18,by decide⟩
def hi0238 : CheckedMoment :=
  CheckedMoment.ofBessel hi0238b1 hi0238b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0238 : meanBracketCheck (1041/10000) lo0238 hi0238=true := by decide +kernel
def bracket0238 : MeanBracket := meanBracketOfMoments (1041/10000) lo0238 hi0238 accepted0238
def lo0239b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨22,by decide⟩
def lo0239b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨23,by decide⟩
def lo0239 : CheckedMoment :=
  CheckedMoment.ofBessel lo0239b1 lo0239b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0239b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨27,by decide⟩
def hi0239b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨28,by decide⟩
def hi0239 : CheckedMoment :=
  CheckedMoment.ofBessel hi0239b1 hi0239b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0239 : meanBracketCheck (1043/10000) lo0239 hi0239=true := by decide +kernel
def bracket0239 : MeanBracket := meanBracketOfMoments (1043/10000) lo0239 hi0239 accepted0239
#print axioms bracket0224
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0014
