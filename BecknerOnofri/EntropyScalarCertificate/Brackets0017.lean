module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0042
public import BecknerOnofri.EntropyScalarCertificate.Bessel0043
public import BecknerOnofri.EntropyScalarCertificate.Bessel0044

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0017
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0272b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨32,by decide⟩
def lo0272b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨33,by decide⟩
def lo0272 : CheckedMoment :=
  CheckedMoment.ofBessel lo0272b1 lo0272b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0272b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨37,by decide⟩
def hi0272b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨38,by decide⟩
def hi0272 : CheckedMoment :=
  CheckedMoment.ofBessel hi0272b1 hi0272b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0272 : meanBracketCheck (1109/10000) lo0272 hi0272=true := by decide +kernel
def bracket0272 : MeanBracket := meanBracketOfMoments (1109/10000) lo0272 hi0272 accepted0272
def lo0273b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨42,by decide⟩
def lo0273b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨43,by decide⟩
def lo0273 : CheckedMoment :=
  CheckedMoment.ofBessel lo0273b1 lo0273b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0273b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨47,by decide⟩
def hi0273b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨48,by decide⟩
def hi0273 : CheckedMoment :=
  CheckedMoment.ofBessel hi0273b1 hi0273b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0273 : meanBracketCheck (1111/10000) lo0273 hi0273=true := by decide +kernel
def bracket0273 : MeanBracket := meanBracketOfMoments (1111/10000) lo0273 hi0273 accepted0273
def lo0274b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨52,by decide⟩
def lo0274b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨53,by decide⟩
def lo0274 : CheckedMoment :=
  CheckedMoment.ofBessel lo0274b1 lo0274b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0274b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨57,by decide⟩
def hi0274b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨58,by decide⟩
def hi0274 : CheckedMoment :=
  CheckedMoment.ofBessel hi0274b1 hi0274b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0274 : meanBracketCheck (1113/10000) lo0274 hi0274=true := by decide +kernel
def bracket0274 : MeanBracket := meanBracketOfMoments (1113/10000) lo0274 hi0274 accepted0274
def lo0275b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨62,by decide⟩
def lo0275b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨63,by decide⟩
def lo0275 : CheckedMoment :=
  CheckedMoment.ofBessel lo0275b1 lo0275b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0275b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨3,by decide⟩
def hi0275b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨4,by decide⟩
def hi0275 : CheckedMoment :=
  CheckedMoment.ofBessel hi0275b1 hi0275b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0275 : meanBracketCheck (223/2000) lo0275 hi0275=true := by decide +kernel
def bracket0275 : MeanBracket := meanBracketOfMoments (223/2000) lo0275 hi0275 accepted0275
def lo0276b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨8,by decide⟩
def lo0276b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨9,by decide⟩
def lo0276 : CheckedMoment :=
  CheckedMoment.ofBessel lo0276b1 lo0276b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0276b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨13,by decide⟩
def hi0276b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨14,by decide⟩
def hi0276 : CheckedMoment :=
  CheckedMoment.ofBessel hi0276b1 hi0276b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0276 : meanBracketCheck (1117/10000) lo0276 hi0276=true := by decide +kernel
def bracket0276 : MeanBracket := meanBracketOfMoments (1117/10000) lo0276 hi0276 accepted0276
def lo0277b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨18,by decide⟩
def lo0277b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨19,by decide⟩
def lo0277 : CheckedMoment :=
  CheckedMoment.ofBessel lo0277b1 lo0277b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0277b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨23,by decide⟩
def hi0277b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨24,by decide⟩
def hi0277 : CheckedMoment :=
  CheckedMoment.ofBessel hi0277b1 hi0277b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0277 : meanBracketCheck (1119/10000) lo0277 hi0277=true := by decide +kernel
def bracket0277 : MeanBracket := meanBracketOfMoments (1119/10000) lo0277 hi0277 accepted0277
def lo0278b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨28,by decide⟩
def lo0278b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨29,by decide⟩
def lo0278 : CheckedMoment :=
  CheckedMoment.ofBessel lo0278b1 lo0278b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0278b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨33,by decide⟩
def hi0278b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨34,by decide⟩
def hi0278 : CheckedMoment :=
  CheckedMoment.ofBessel hi0278b1 hi0278b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0278 : meanBracketCheck (1121/10000) lo0278 hi0278=true := by decide +kernel
def bracket0278 : MeanBracket := meanBracketOfMoments (1121/10000) lo0278 hi0278 accepted0278
def lo0279b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨38,by decide⟩
def lo0279b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨39,by decide⟩
def lo0279 : CheckedMoment :=
  CheckedMoment.ofBessel lo0279b1 lo0279b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0279b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨43,by decide⟩
def hi0279b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨44,by decide⟩
def hi0279 : CheckedMoment :=
  CheckedMoment.ofBessel hi0279b1 hi0279b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0279 : meanBracketCheck (1123/10000) lo0279 hi0279=true := by decide +kernel
def bracket0279 : MeanBracket := meanBracketOfMoments (1123/10000) lo0279 hi0279 accepted0279
def lo0280b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨48,by decide⟩
def lo0280b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨49,by decide⟩
def lo0280 : CheckedMoment :=
  CheckedMoment.ofBessel lo0280b1 lo0280b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0280b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨53,by decide⟩
def hi0280b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨54,by decide⟩
def hi0280 : CheckedMoment :=
  CheckedMoment.ofBessel hi0280b1 hi0280b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0280 : meanBracketCheck (9/80) lo0280 hi0280=true := by decide +kernel
def bracket0280 : MeanBracket := meanBracketOfMoments (9/80) lo0280 hi0280 accepted0280
def lo0281b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨58,by decide⟩
def lo0281b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨59,by decide⟩
def lo0281 : CheckedMoment :=
  CheckedMoment.ofBessel lo0281b1 lo0281b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0281b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨63,by decide⟩
def hi0281b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨0,by decide⟩
def hi0281 : CheckedMoment :=
  CheckedMoment.ofBessel hi0281b1 hi0281b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0281 : meanBracketCheck (1127/10000) lo0281 hi0281=true := by decide +kernel
def bracket0281 : MeanBracket := meanBracketOfMoments (1127/10000) lo0281 hi0281 accepted0281
def lo0282b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨4,by decide⟩
def lo0282b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨5,by decide⟩
def lo0282 : CheckedMoment :=
  CheckedMoment.ofBessel lo0282b1 lo0282b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0282b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨9,by decide⟩
def hi0282b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨10,by decide⟩
def hi0282 : CheckedMoment :=
  CheckedMoment.ofBessel hi0282b1 hi0282b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0282 : meanBracketCheck (1129/10000) lo0282 hi0282=true := by decide +kernel
def bracket0282 : MeanBracket := meanBracketOfMoments (1129/10000) lo0282 hi0282 accepted0282
def lo0283b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨14,by decide⟩
def lo0283b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨15,by decide⟩
def lo0283 : CheckedMoment :=
  CheckedMoment.ofBessel lo0283b1 lo0283b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0283b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨19,by decide⟩
def hi0283b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨20,by decide⟩
def hi0283 : CheckedMoment :=
  CheckedMoment.ofBessel hi0283b1 hi0283b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0283 : meanBracketCheck (1131/10000) lo0283 hi0283=true := by decide +kernel
def bracket0283 : MeanBracket := meanBracketOfMoments (1131/10000) lo0283 hi0283 accepted0283
def lo0284b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨24,by decide⟩
def lo0284b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨25,by decide⟩
def lo0284 : CheckedMoment :=
  CheckedMoment.ofBessel lo0284b1 lo0284b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0284b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨29,by decide⟩
def hi0284b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨30,by decide⟩
def hi0284 : CheckedMoment :=
  CheckedMoment.ofBessel hi0284b1 hi0284b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0284 : meanBracketCheck (1133/10000) lo0284 hi0284=true := by decide +kernel
def bracket0284 : MeanBracket := meanBracketOfMoments (1133/10000) lo0284 hi0284 accepted0284
def lo0285b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨34,by decide⟩
def lo0285b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨35,by decide⟩
def lo0285 : CheckedMoment :=
  CheckedMoment.ofBessel lo0285b1 lo0285b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0285b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨39,by decide⟩
def hi0285b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨40,by decide⟩
def hi0285 : CheckedMoment :=
  CheckedMoment.ofBessel hi0285b1 hi0285b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0285 : meanBracketCheck (227/2000) lo0285 hi0285=true := by decide +kernel
def bracket0285 : MeanBracket := meanBracketOfMoments (227/2000) lo0285 hi0285 accepted0285
def lo0286b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨44,by decide⟩
def lo0286b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨45,by decide⟩
def lo0286 : CheckedMoment :=
  CheckedMoment.ofBessel lo0286b1 lo0286b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0286b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨49,by decide⟩
def hi0286b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨50,by decide⟩
def hi0286 : CheckedMoment :=
  CheckedMoment.ofBessel hi0286b1 hi0286b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0286 : meanBracketCheck (1137/10000) lo0286 hi0286=true := by decide +kernel
def bracket0286 : MeanBracket := meanBracketOfMoments (1137/10000) lo0286 hi0286 accepted0286
def lo0287b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨54,by decide⟩
def lo0287b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨55,by decide⟩
def lo0287 : CheckedMoment :=
  CheckedMoment.ofBessel lo0287b1 lo0287b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0287b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨59,by decide⟩
def hi0287b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨60,by decide⟩
def hi0287 : CheckedMoment :=
  CheckedMoment.ofBessel hi0287b1 hi0287b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0287 : meanBracketCheck (1139/10000) lo0287 hi0287=true := by decide +kernel
def bracket0287 : MeanBracket := meanBracketOfMoments (1139/10000) lo0287 hi0287 accepted0287
#print axioms bracket0272
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0017
