module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0142
public import BecknerOnofri.EntropyScalarCertificate.Bessel0143
public import BecknerOnofri.EntropyScalarCertificate.Bessel0144

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0057
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0912b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨32,by decide⟩
def lo0912b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨33,by decide⟩
def lo0912 : CheckedMoment :=
  CheckedMoment.ofBessel lo0912b1 lo0912b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0912b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨37,by decide⟩
def hi0912b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨38,by decide⟩
def hi0912 : CheckedMoment :=
  CheckedMoment.ofBessel hi0912b1 hi0912b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0912 : meanBracketCheck (197/500) lo0912 hi0912=true := by decide +kernel
def bracket0912 : MeanBracket := meanBracketOfMoments (197/500) lo0912 hi0912 accepted0912
def lo0913b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨42,by decide⟩
def lo0913b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨43,by decide⟩
def lo0913 : CheckedMoment :=
  CheckedMoment.ofBessel lo0913b1 lo0913b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0913b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨47,by decide⟩
def hi0913b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨48,by decide⟩
def hi0913 : CheckedMoment :=
  CheckedMoment.ofBessel hi0913b1 hi0913b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0913 : meanBracketCheck (79/200) lo0913 hi0913=true := by decide +kernel
def bracket0913 : MeanBracket := meanBracketOfMoments (79/200) lo0913 hi0913 accepted0913
def lo0914b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨52,by decide⟩
def lo0914b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨53,by decide⟩
def lo0914 : CheckedMoment :=
  CheckedMoment.ofBessel lo0914b1 lo0914b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0914b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨57,by decide⟩
def hi0914b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨58,by decide⟩
def hi0914 : CheckedMoment :=
  CheckedMoment.ofBessel hi0914b1 hi0914b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0914 : meanBracketCheck (99/250) lo0914 hi0914=true := by decide +kernel
def bracket0914 : MeanBracket := meanBracketOfMoments (99/250) lo0914 hi0914 accepted0914
def lo0915b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨62,by decide⟩
def lo0915b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨63,by decide⟩
def lo0915 : CheckedMoment :=
  CheckedMoment.ofBessel lo0915b1 lo0915b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0915b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨3,by decide⟩
def hi0915b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨4,by decide⟩
def hi0915 : CheckedMoment :=
  CheckedMoment.ofBessel hi0915b1 hi0915b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0915 : meanBracketCheck (397/1000) lo0915 hi0915=true := by decide +kernel
def bracket0915 : MeanBracket := meanBracketOfMoments (397/1000) lo0915 hi0915 accepted0915
def lo0916b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨8,by decide⟩
def lo0916b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨9,by decide⟩
def lo0916 : CheckedMoment :=
  CheckedMoment.ofBessel lo0916b1 lo0916b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0916b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨13,by decide⟩
def hi0916b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨14,by decide⟩
def hi0916 : CheckedMoment :=
  CheckedMoment.ofBessel hi0916b1 hi0916b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0916 : meanBracketCheck (199/500) lo0916 hi0916=true := by decide +kernel
def bracket0916 : MeanBracket := meanBracketOfMoments (199/500) lo0916 hi0916 accepted0916
def lo0917b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨18,by decide⟩
def lo0917b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨19,by decide⟩
def lo0917 : CheckedMoment :=
  CheckedMoment.ofBessel lo0917b1 lo0917b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0917b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨23,by decide⟩
def hi0917b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨24,by decide⟩
def hi0917 : CheckedMoment :=
  CheckedMoment.ofBessel hi0917b1 hi0917b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0917 : meanBracketCheck (399/1000) lo0917 hi0917=true := by decide +kernel
def bracket0917 : MeanBracket := meanBracketOfMoments (399/1000) lo0917 hi0917 accepted0917
def lo0918b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨28,by decide⟩
def lo0918b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨29,by decide⟩
def lo0918 : CheckedMoment :=
  CheckedMoment.ofBessel lo0918b1 lo0918b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0918b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨33,by decide⟩
def hi0918b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨34,by decide⟩
def hi0918 : CheckedMoment :=
  CheckedMoment.ofBessel hi0918b1 hi0918b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0918 : meanBracketCheck (2/5) lo0918 hi0918=true := by decide +kernel
def bracket0918 : MeanBracket := meanBracketOfMoments (2/5) lo0918 hi0918 accepted0918
def lo0919b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨38,by decide⟩
def lo0919b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨39,by decide⟩
def lo0919 : CheckedMoment :=
  CheckedMoment.ofBessel lo0919b1 lo0919b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0919b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨43,by decide⟩
def hi0919b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨44,by decide⟩
def hi0919 : CheckedMoment :=
  CheckedMoment.ofBessel hi0919b1 hi0919b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0919 : meanBracketCheck (401/1000) lo0919 hi0919=true := by decide +kernel
def bracket0919 : MeanBracket := meanBracketOfMoments (401/1000) lo0919 hi0919 accepted0919
def lo0920b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨48,by decide⟩
def lo0920b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨49,by decide⟩
def lo0920 : CheckedMoment :=
  CheckedMoment.ofBessel lo0920b1 lo0920b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0920b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨53,by decide⟩
def hi0920b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨54,by decide⟩
def hi0920 : CheckedMoment :=
  CheckedMoment.ofBessel hi0920b1 hi0920b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0920 : meanBracketCheck (201/500) lo0920 hi0920=true := by decide +kernel
def bracket0920 : MeanBracket := meanBracketOfMoments (201/500) lo0920 hi0920 accepted0920
def lo0921b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨58,by decide⟩
def lo0921b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨59,by decide⟩
def lo0921 : CheckedMoment :=
  CheckedMoment.ofBessel lo0921b1 lo0921b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0921b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨63,by decide⟩
def hi0921b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨0,by decide⟩
def hi0921 : CheckedMoment :=
  CheckedMoment.ofBessel hi0921b1 hi0921b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0921 : meanBracketCheck (403/1000) lo0921 hi0921=true := by decide +kernel
def bracket0921 : MeanBracket := meanBracketOfMoments (403/1000) lo0921 hi0921 accepted0921
def lo0922b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨4,by decide⟩
def lo0922b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨5,by decide⟩
def lo0922 : CheckedMoment :=
  CheckedMoment.ofBessel lo0922b1 lo0922b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0922b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨9,by decide⟩
def hi0922b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨10,by decide⟩
def hi0922 : CheckedMoment :=
  CheckedMoment.ofBessel hi0922b1 hi0922b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0922 : meanBracketCheck (101/250) lo0922 hi0922=true := by decide +kernel
def bracket0922 : MeanBracket := meanBracketOfMoments (101/250) lo0922 hi0922 accepted0922
def lo0923b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨14,by decide⟩
def lo0923b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨15,by decide⟩
def lo0923 : CheckedMoment :=
  CheckedMoment.ofBessel lo0923b1 lo0923b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0923b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨19,by decide⟩
def hi0923b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨20,by decide⟩
def hi0923 : CheckedMoment :=
  CheckedMoment.ofBessel hi0923b1 hi0923b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0923 : meanBracketCheck (81/200) lo0923 hi0923=true := by decide +kernel
def bracket0923 : MeanBracket := meanBracketOfMoments (81/200) lo0923 hi0923 accepted0923
def lo0924b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨24,by decide⟩
def lo0924b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨25,by decide⟩
def lo0924 : CheckedMoment :=
  CheckedMoment.ofBessel lo0924b1 lo0924b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0924b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨29,by decide⟩
def hi0924b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨30,by decide⟩
def hi0924 : CheckedMoment :=
  CheckedMoment.ofBessel hi0924b1 hi0924b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0924 : meanBracketCheck (203/500) lo0924 hi0924=true := by decide +kernel
def bracket0924 : MeanBracket := meanBracketOfMoments (203/500) lo0924 hi0924 accepted0924
def lo0925b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨34,by decide⟩
def lo0925b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨35,by decide⟩
def lo0925 : CheckedMoment :=
  CheckedMoment.ofBessel lo0925b1 lo0925b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0925b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨39,by decide⟩
def hi0925b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨40,by decide⟩
def hi0925 : CheckedMoment :=
  CheckedMoment.ofBessel hi0925b1 hi0925b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0925 : meanBracketCheck (407/1000) lo0925 hi0925=true := by decide +kernel
def bracket0925 : MeanBracket := meanBracketOfMoments (407/1000) lo0925 hi0925 accepted0925
def lo0926b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨44,by decide⟩
def lo0926b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨45,by decide⟩
def lo0926 : CheckedMoment :=
  CheckedMoment.ofBessel lo0926b1 lo0926b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0926b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨49,by decide⟩
def hi0926b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨50,by decide⟩
def hi0926 : CheckedMoment :=
  CheckedMoment.ofBessel hi0926b1 hi0926b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0926 : meanBracketCheck (51/125) lo0926 hi0926=true := by decide +kernel
def bracket0926 : MeanBracket := meanBracketOfMoments (51/125) lo0926 hi0926 accepted0926
def lo0927b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨54,by decide⟩
def lo0927b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨55,by decide⟩
def lo0927 : CheckedMoment :=
  CheckedMoment.ofBessel lo0927b1 lo0927b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0927b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨59,by decide⟩
def hi0927b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨60,by decide⟩
def hi0927 : CheckedMoment :=
  CheckedMoment.ofBessel hi0927b1 hi0927b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0927 : meanBracketCheck (409/1000) lo0927 hi0927=true := by decide +kernel
def bracket0927 : MeanBracket := meanBracketOfMoments (409/1000) lo0927 hi0927 accepted0927
#print axioms bracket0912
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0057
