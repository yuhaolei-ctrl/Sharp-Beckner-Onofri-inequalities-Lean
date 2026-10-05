module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0045
public import BecknerOnofri.EntropyScalarCertificate.Bessel0046
public import BecknerOnofri.EntropyScalarCertificate.Bessel0047

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0018
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0288b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨0,by decide⟩
def lo0288b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨1,by decide⟩
def lo0288 : CheckedMoment :=
  CheckedMoment.ofBessel lo0288b1 lo0288b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0288b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨5,by decide⟩
def hi0288b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨6,by decide⟩
def hi0288 : CheckedMoment :=
  CheckedMoment.ofBessel hi0288b1 hi0288b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0288 : meanBracketCheck (1141/10000) lo0288 hi0288=true := by decide +kernel
def bracket0288 : MeanBracket := meanBracketOfMoments (1141/10000) lo0288 hi0288 accepted0288
def lo0289b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨10,by decide⟩
def lo0289b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨11,by decide⟩
def lo0289 : CheckedMoment :=
  CheckedMoment.ofBessel lo0289b1 lo0289b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0289b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨15,by decide⟩
def hi0289b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨16,by decide⟩
def hi0289 : CheckedMoment :=
  CheckedMoment.ofBessel hi0289b1 hi0289b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0289 : meanBracketCheck (1143/10000) lo0289 hi0289=true := by decide +kernel
def bracket0289 : MeanBracket := meanBracketOfMoments (1143/10000) lo0289 hi0289 accepted0289
def lo0290b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨20,by decide⟩
def lo0290b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨21,by decide⟩
def lo0290 : CheckedMoment :=
  CheckedMoment.ofBessel lo0290b1 lo0290b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0290b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨25,by decide⟩
def hi0290b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨26,by decide⟩
def hi0290 : CheckedMoment :=
  CheckedMoment.ofBessel hi0290b1 hi0290b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0290 : meanBracketCheck (229/2000) lo0290 hi0290=true := by decide +kernel
def bracket0290 : MeanBracket := meanBracketOfMoments (229/2000) lo0290 hi0290 accepted0290
def lo0291b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨30,by decide⟩
def lo0291b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨31,by decide⟩
def lo0291 : CheckedMoment :=
  CheckedMoment.ofBessel lo0291b1 lo0291b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0291b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨35,by decide⟩
def hi0291b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨36,by decide⟩
def hi0291 : CheckedMoment :=
  CheckedMoment.ofBessel hi0291b1 hi0291b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0291 : meanBracketCheck (1147/10000) lo0291 hi0291=true := by decide +kernel
def bracket0291 : MeanBracket := meanBracketOfMoments (1147/10000) lo0291 hi0291 accepted0291
def lo0292b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨40,by decide⟩
def lo0292b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨41,by decide⟩
def lo0292 : CheckedMoment :=
  CheckedMoment.ofBessel lo0292b1 lo0292b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0292b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨45,by decide⟩
def hi0292b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨46,by decide⟩
def hi0292 : CheckedMoment :=
  CheckedMoment.ofBessel hi0292b1 hi0292b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0292 : meanBracketCheck (1149/10000) lo0292 hi0292=true := by decide +kernel
def bracket0292 : MeanBracket := meanBracketOfMoments (1149/10000) lo0292 hi0292 accepted0292
def lo0293b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨50,by decide⟩
def lo0293b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨51,by decide⟩
def lo0293 : CheckedMoment :=
  CheckedMoment.ofBessel lo0293b1 lo0293b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0293b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨55,by decide⟩
def hi0293b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨56,by decide⟩
def hi0293 : CheckedMoment :=
  CheckedMoment.ofBessel hi0293b1 hi0293b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0293 : meanBracketCheck (1151/10000) lo0293 hi0293=true := by decide +kernel
def bracket0293 : MeanBracket := meanBracketOfMoments (1151/10000) lo0293 hi0293 accepted0293
def lo0294b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨60,by decide⟩
def lo0294b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨61,by decide⟩
def lo0294 : CheckedMoment :=
  CheckedMoment.ofBessel lo0294b1 lo0294b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0294b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨1,by decide⟩
def hi0294b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨2,by decide⟩
def hi0294 : CheckedMoment :=
  CheckedMoment.ofBessel hi0294b1 hi0294b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0294 : meanBracketCheck (1153/10000) lo0294 hi0294=true := by decide +kernel
def bracket0294 : MeanBracket := meanBracketOfMoments (1153/10000) lo0294 hi0294 accepted0294
def lo0295b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨6,by decide⟩
def lo0295b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨7,by decide⟩
def lo0295 : CheckedMoment :=
  CheckedMoment.ofBessel lo0295b1 lo0295b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0295b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨11,by decide⟩
def hi0295b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨12,by decide⟩
def hi0295 : CheckedMoment :=
  CheckedMoment.ofBessel hi0295b1 hi0295b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0295 : meanBracketCheck (231/2000) lo0295 hi0295=true := by decide +kernel
def bracket0295 : MeanBracket := meanBracketOfMoments (231/2000) lo0295 hi0295 accepted0295
def lo0296b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨16,by decide⟩
def lo0296b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨17,by decide⟩
def lo0296 : CheckedMoment :=
  CheckedMoment.ofBessel lo0296b1 lo0296b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0296b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨21,by decide⟩
def hi0296b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨22,by decide⟩
def hi0296 : CheckedMoment :=
  CheckedMoment.ofBessel hi0296b1 hi0296b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0296 : meanBracketCheck (1157/10000) lo0296 hi0296=true := by decide +kernel
def bracket0296 : MeanBracket := meanBracketOfMoments (1157/10000) lo0296 hi0296 accepted0296
def lo0297b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨26,by decide⟩
def lo0297b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨27,by decide⟩
def lo0297 : CheckedMoment :=
  CheckedMoment.ofBessel lo0297b1 lo0297b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0297b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨31,by decide⟩
def hi0297b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨32,by decide⟩
def hi0297 : CheckedMoment :=
  CheckedMoment.ofBessel hi0297b1 hi0297b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0297 : meanBracketCheck (1159/10000) lo0297 hi0297=true := by decide +kernel
def bracket0297 : MeanBracket := meanBracketOfMoments (1159/10000) lo0297 hi0297 accepted0297
def lo0298b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨36,by decide⟩
def lo0298b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨37,by decide⟩
def lo0298 : CheckedMoment :=
  CheckedMoment.ofBessel lo0298b1 lo0298b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0298b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨41,by decide⟩
def hi0298b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨42,by decide⟩
def hi0298 : CheckedMoment :=
  CheckedMoment.ofBessel hi0298b1 hi0298b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0298 : meanBracketCheck (1161/10000) lo0298 hi0298=true := by decide +kernel
def bracket0298 : MeanBracket := meanBracketOfMoments (1161/10000) lo0298 hi0298 accepted0298
def lo0299b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨46,by decide⟩
def lo0299b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨47,by decide⟩
def lo0299 : CheckedMoment :=
  CheckedMoment.ofBessel lo0299b1 lo0299b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0299b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨51,by decide⟩
def hi0299b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨52,by decide⟩
def hi0299 : CheckedMoment :=
  CheckedMoment.ofBessel hi0299b1 hi0299b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0299 : meanBracketCheck (1163/10000) lo0299 hi0299=true := by decide +kernel
def bracket0299 : MeanBracket := meanBracketOfMoments (1163/10000) lo0299 hi0299 accepted0299
def lo0300b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨56,by decide⟩
def lo0300b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨57,by decide⟩
def lo0300 : CheckedMoment :=
  CheckedMoment.ofBessel lo0300b1 lo0300b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0300b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨61,by decide⟩
def hi0300b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨62,by decide⟩
def hi0300 : CheckedMoment :=
  CheckedMoment.ofBessel hi0300b1 hi0300b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0300 : meanBracketCheck (233/2000) lo0300 hi0300=true := by decide +kernel
def bracket0300 : MeanBracket := meanBracketOfMoments (233/2000) lo0300 hi0300 accepted0300
def lo0301b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨2,by decide⟩
def lo0301b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨3,by decide⟩
def lo0301 : CheckedMoment :=
  CheckedMoment.ofBessel lo0301b1 lo0301b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0301b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨7,by decide⟩
def hi0301b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨8,by decide⟩
def hi0301 : CheckedMoment :=
  CheckedMoment.ofBessel hi0301b1 hi0301b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0301 : meanBracketCheck (1167/10000) lo0301 hi0301=true := by decide +kernel
def bracket0301 : MeanBracket := meanBracketOfMoments (1167/10000) lo0301 hi0301 accepted0301
def lo0302b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨12,by decide⟩
def lo0302b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨13,by decide⟩
def lo0302 : CheckedMoment :=
  CheckedMoment.ofBessel lo0302b1 lo0302b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0302b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨17,by decide⟩
def hi0302b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨18,by decide⟩
def hi0302 : CheckedMoment :=
  CheckedMoment.ofBessel hi0302b1 hi0302b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0302 : meanBracketCheck (1169/10000) lo0302 hi0302=true := by decide +kernel
def bracket0302 : MeanBracket := meanBracketOfMoments (1169/10000) lo0302 hi0302 accepted0302
def lo0303b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨22,by decide⟩
def lo0303b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨23,by decide⟩
def lo0303 : CheckedMoment :=
  CheckedMoment.ofBessel lo0303b1 lo0303b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0303b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨27,by decide⟩
def hi0303b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨28,by decide⟩
def hi0303 : CheckedMoment :=
  CheckedMoment.ofBessel hi0303b1 hi0303b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0303 : meanBracketCheck (1171/10000) lo0303 hi0303=true := by decide +kernel
def bracket0303 : MeanBracket := meanBracketOfMoments (1171/10000) lo0303 hi0303 accepted0303
#print axioms bracket0288
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0018
