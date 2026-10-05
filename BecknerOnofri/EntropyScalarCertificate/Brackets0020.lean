module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0050
public import BecknerOnofri.EntropyScalarCertificate.Bessel0051
public import BecknerOnofri.EntropyScalarCertificate.Bessel0052

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0020
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0320b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨0,by decide⟩
def lo0320b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨1,by decide⟩
def lo0320 : CheckedMoment :=
  CheckedMoment.ofBessel lo0320b1 lo0320b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0320b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨5,by decide⟩
def hi0320b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨6,by decide⟩
def hi0320 : CheckedMoment :=
  CheckedMoment.ofBessel hi0320b1 hi0320b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0320 : meanBracketCheck (241/2000) lo0320 hi0320=true := by decide +kernel
def bracket0320 : MeanBracket := meanBracketOfMoments (241/2000) lo0320 hi0320 accepted0320
def lo0321b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨10,by decide⟩
def lo0321b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨11,by decide⟩
def lo0321 : CheckedMoment :=
  CheckedMoment.ofBessel lo0321b1 lo0321b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0321b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨15,by decide⟩
def hi0321b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨16,by decide⟩
def hi0321 : CheckedMoment :=
  CheckedMoment.ofBessel hi0321b1 hi0321b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0321 : meanBracketCheck (1207/10000) lo0321 hi0321=true := by decide +kernel
def bracket0321 : MeanBracket := meanBracketOfMoments (1207/10000) lo0321 hi0321 accepted0321
def lo0322b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨20,by decide⟩
def lo0322b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨21,by decide⟩
def lo0322 : CheckedMoment :=
  CheckedMoment.ofBessel lo0322b1 lo0322b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0322b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨25,by decide⟩
def hi0322b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨26,by decide⟩
def hi0322 : CheckedMoment :=
  CheckedMoment.ofBessel hi0322b1 hi0322b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0322 : meanBracketCheck (1209/10000) lo0322 hi0322=true := by decide +kernel
def bracket0322 : MeanBracket := meanBracketOfMoments (1209/10000) lo0322 hi0322 accepted0322
def lo0323b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨30,by decide⟩
def lo0323b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨31,by decide⟩
def lo0323 : CheckedMoment :=
  CheckedMoment.ofBessel lo0323b1 lo0323b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0323b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨35,by decide⟩
def hi0323b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨36,by decide⟩
def hi0323 : CheckedMoment :=
  CheckedMoment.ofBessel hi0323b1 hi0323b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0323 : meanBracketCheck (1211/10000) lo0323 hi0323=true := by decide +kernel
def bracket0323 : MeanBracket := meanBracketOfMoments (1211/10000) lo0323 hi0323 accepted0323
def lo0324b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨40,by decide⟩
def lo0324b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨41,by decide⟩
def lo0324 : CheckedMoment :=
  CheckedMoment.ofBessel lo0324b1 lo0324b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0324b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨45,by decide⟩
def hi0324b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨46,by decide⟩
def hi0324 : CheckedMoment :=
  CheckedMoment.ofBessel hi0324b1 hi0324b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0324 : meanBracketCheck (1213/10000) lo0324 hi0324=true := by decide +kernel
def bracket0324 : MeanBracket := meanBracketOfMoments (1213/10000) lo0324 hi0324 accepted0324
def lo0325b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨50,by decide⟩
def lo0325b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨51,by decide⟩
def lo0325 : CheckedMoment :=
  CheckedMoment.ofBessel lo0325b1 lo0325b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0325b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨55,by decide⟩
def hi0325b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨56,by decide⟩
def hi0325 : CheckedMoment :=
  CheckedMoment.ofBessel hi0325b1 hi0325b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0325 : meanBracketCheck (243/2000) lo0325 hi0325=true := by decide +kernel
def bracket0325 : MeanBracket := meanBracketOfMoments (243/2000) lo0325 hi0325 accepted0325
def lo0326b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨60,by decide⟩
def lo0326b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨61,by decide⟩
def lo0326 : CheckedMoment :=
  CheckedMoment.ofBessel lo0326b1 lo0326b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0326b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨1,by decide⟩
def hi0326b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨2,by decide⟩
def hi0326 : CheckedMoment :=
  CheckedMoment.ofBessel hi0326b1 hi0326b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0326 : meanBracketCheck (1217/10000) lo0326 hi0326=true := by decide +kernel
def bracket0326 : MeanBracket := meanBracketOfMoments (1217/10000) lo0326 hi0326 accepted0326
def lo0327b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨6,by decide⟩
def lo0327b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨7,by decide⟩
def lo0327 : CheckedMoment :=
  CheckedMoment.ofBessel lo0327b1 lo0327b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0327b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨11,by decide⟩
def hi0327b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨12,by decide⟩
def hi0327 : CheckedMoment :=
  CheckedMoment.ofBessel hi0327b1 hi0327b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0327 : meanBracketCheck (1219/10000) lo0327 hi0327=true := by decide +kernel
def bracket0327 : MeanBracket := meanBracketOfMoments (1219/10000) lo0327 hi0327 accepted0327
def lo0328b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨16,by decide⟩
def lo0328b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨17,by decide⟩
def lo0328 : CheckedMoment :=
  CheckedMoment.ofBessel lo0328b1 lo0328b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0328b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨21,by decide⟩
def hi0328b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨22,by decide⟩
def hi0328 : CheckedMoment :=
  CheckedMoment.ofBessel hi0328b1 hi0328b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0328 : meanBracketCheck (1221/10000) lo0328 hi0328=true := by decide +kernel
def bracket0328 : MeanBracket := meanBracketOfMoments (1221/10000) lo0328 hi0328 accepted0328
def lo0329b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨26,by decide⟩
def lo0329b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨27,by decide⟩
def lo0329 : CheckedMoment :=
  CheckedMoment.ofBessel lo0329b1 lo0329b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0329b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨31,by decide⟩
def hi0329b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨32,by decide⟩
def hi0329 : CheckedMoment :=
  CheckedMoment.ofBessel hi0329b1 hi0329b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0329 : meanBracketCheck (1223/10000) lo0329 hi0329=true := by decide +kernel
def bracket0329 : MeanBracket := meanBracketOfMoments (1223/10000) lo0329 hi0329 accepted0329
def lo0330b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨36,by decide⟩
def lo0330b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨37,by decide⟩
def lo0330 : CheckedMoment :=
  CheckedMoment.ofBessel lo0330b1 lo0330b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0330b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨41,by decide⟩
def hi0330b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨42,by decide⟩
def hi0330 : CheckedMoment :=
  CheckedMoment.ofBessel hi0330b1 hi0330b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0330 : meanBracketCheck (49/400) lo0330 hi0330=true := by decide +kernel
def bracket0330 : MeanBracket := meanBracketOfMoments (49/400) lo0330 hi0330 accepted0330
def lo0331b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨46,by decide⟩
def lo0331b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨47,by decide⟩
def lo0331 : CheckedMoment :=
  CheckedMoment.ofBessel lo0331b1 lo0331b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0331b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨51,by decide⟩
def hi0331b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨52,by decide⟩
def hi0331 : CheckedMoment :=
  CheckedMoment.ofBessel hi0331b1 hi0331b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0331 : meanBracketCheck (1227/10000) lo0331 hi0331=true := by decide +kernel
def bracket0331 : MeanBracket := meanBracketOfMoments (1227/10000) lo0331 hi0331 accepted0331
def lo0332b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨56,by decide⟩
def lo0332b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨57,by decide⟩
def lo0332 : CheckedMoment :=
  CheckedMoment.ofBessel lo0332b1 lo0332b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0332b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨61,by decide⟩
def hi0332b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨62,by decide⟩
def hi0332 : CheckedMoment :=
  CheckedMoment.ofBessel hi0332b1 hi0332b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0332 : meanBracketCheck (1229/10000) lo0332 hi0332=true := by decide +kernel
def bracket0332 : MeanBracket := meanBracketOfMoments (1229/10000) lo0332 hi0332 accepted0332
def lo0333b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨2,by decide⟩
def lo0333b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨3,by decide⟩
def lo0333 : CheckedMoment :=
  CheckedMoment.ofBessel lo0333b1 lo0333b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0333b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨7,by decide⟩
def hi0333b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨8,by decide⟩
def hi0333 : CheckedMoment :=
  CheckedMoment.ofBessel hi0333b1 hi0333b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0333 : meanBracketCheck (1231/10000) lo0333 hi0333=true := by decide +kernel
def bracket0333 : MeanBracket := meanBracketOfMoments (1231/10000) lo0333 hi0333 accepted0333
def lo0334b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨12,by decide⟩
def lo0334b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨13,by decide⟩
def lo0334 : CheckedMoment :=
  CheckedMoment.ofBessel lo0334b1 lo0334b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0334b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨17,by decide⟩
def hi0334b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨18,by decide⟩
def hi0334 : CheckedMoment :=
  CheckedMoment.ofBessel hi0334b1 hi0334b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0334 : meanBracketCheck (1233/10000) lo0334 hi0334=true := by decide +kernel
def bracket0334 : MeanBracket := meanBracketOfMoments (1233/10000) lo0334 hi0334 accepted0334
def lo0335b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨22,by decide⟩
def lo0335b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨23,by decide⟩
def lo0335 : CheckedMoment :=
  CheckedMoment.ofBessel lo0335b1 lo0335b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0335b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨27,by decide⟩
def hi0335b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨28,by decide⟩
def hi0335 : CheckedMoment :=
  CheckedMoment.ofBessel hi0335b1 hi0335b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0335 : meanBracketCheck (247/2000) lo0335 hi0335=true := by decide +kernel
def bracket0335 : MeanBracket := meanBracketOfMoments (247/2000) lo0335 hi0335 accepted0335
#print axioms bracket0320
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0020
