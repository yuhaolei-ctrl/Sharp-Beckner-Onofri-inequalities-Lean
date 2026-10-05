module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0132
public import BecknerOnofri.EntropyScalarCertificate.Bessel0133
public import BecknerOnofri.EntropyScalarCertificate.Bessel0134

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0053
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0848b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨32,by decide⟩
def lo0848b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨33,by decide⟩
def lo0848 : CheckedMoment :=
  CheckedMoment.ofBessel lo0848b1 lo0848b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0848b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨37,by decide⟩
def hi0848b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨38,by decide⟩
def hi0848 : CheckedMoment :=
  CheckedMoment.ofBessel hi0848b1 hi0848b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0848 : meanBracketCheck (33/100) lo0848 hi0848=true := by decide +kernel
def bracket0848 : MeanBracket := meanBracketOfMoments (33/100) lo0848 hi0848 accepted0848
def lo0849b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨42,by decide⟩
def lo0849b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨43,by decide⟩
def lo0849 : CheckedMoment :=
  CheckedMoment.ofBessel lo0849b1 lo0849b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0849b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨47,by decide⟩
def hi0849b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨48,by decide⟩
def hi0849 : CheckedMoment :=
  CheckedMoment.ofBessel hi0849b1 hi0849b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0849 : meanBracketCheck (331/1000) lo0849 hi0849=true := by decide +kernel
def bracket0849 : MeanBracket := meanBracketOfMoments (331/1000) lo0849 hi0849 accepted0849
def lo0850b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨52,by decide⟩
def lo0850b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨53,by decide⟩
def lo0850 : CheckedMoment :=
  CheckedMoment.ofBessel lo0850b1 lo0850b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0850b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨57,by decide⟩
def hi0850b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨58,by decide⟩
def hi0850 : CheckedMoment :=
  CheckedMoment.ofBessel hi0850b1 hi0850b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0850 : meanBracketCheck (83/250) lo0850 hi0850=true := by decide +kernel
def bracket0850 : MeanBracket := meanBracketOfMoments (83/250) lo0850 hi0850 accepted0850
def lo0851b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨62,by decide⟩
def lo0851b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨63,by decide⟩
def lo0851 : CheckedMoment :=
  CheckedMoment.ofBessel lo0851b1 lo0851b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0851b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨3,by decide⟩
def hi0851b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨4,by decide⟩
def hi0851 : CheckedMoment :=
  CheckedMoment.ofBessel hi0851b1 hi0851b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0851 : meanBracketCheck (333/1000) lo0851 hi0851=true := by decide +kernel
def bracket0851 : MeanBracket := meanBracketOfMoments (333/1000) lo0851 hi0851 accepted0851
def lo0852b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨8,by decide⟩
def lo0852b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨9,by decide⟩
def lo0852 : CheckedMoment :=
  CheckedMoment.ofBessel lo0852b1 lo0852b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0852b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨13,by decide⟩
def hi0852b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨14,by decide⟩
def hi0852 : CheckedMoment :=
  CheckedMoment.ofBessel hi0852b1 hi0852b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0852 : meanBracketCheck (167/500) lo0852 hi0852=true := by decide +kernel
def bracket0852 : MeanBracket := meanBracketOfMoments (167/500) lo0852 hi0852 accepted0852
def lo0853b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨18,by decide⟩
def lo0853b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨19,by decide⟩
def lo0853 : CheckedMoment :=
  CheckedMoment.ofBessel lo0853b1 lo0853b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0853b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨23,by decide⟩
def hi0853b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨24,by decide⟩
def hi0853 : CheckedMoment :=
  CheckedMoment.ofBessel hi0853b1 hi0853b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0853 : meanBracketCheck (67/200) lo0853 hi0853=true := by decide +kernel
def bracket0853 : MeanBracket := meanBracketOfMoments (67/200) lo0853 hi0853 accepted0853
def lo0854b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨28,by decide⟩
def lo0854b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨29,by decide⟩
def lo0854 : CheckedMoment :=
  CheckedMoment.ofBessel lo0854b1 lo0854b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0854b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨33,by decide⟩
def hi0854b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨34,by decide⟩
def hi0854 : CheckedMoment :=
  CheckedMoment.ofBessel hi0854b1 hi0854b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0854 : meanBracketCheck (42/125) lo0854 hi0854=true := by decide +kernel
def bracket0854 : MeanBracket := meanBracketOfMoments (42/125) lo0854 hi0854 accepted0854
def lo0855b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨38,by decide⟩
def lo0855b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨39,by decide⟩
def lo0855 : CheckedMoment :=
  CheckedMoment.ofBessel lo0855b1 lo0855b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0855b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨43,by decide⟩
def hi0855b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨44,by decide⟩
def hi0855 : CheckedMoment :=
  CheckedMoment.ofBessel hi0855b1 hi0855b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0855 : meanBracketCheck (337/1000) lo0855 hi0855=true := by decide +kernel
def bracket0855 : MeanBracket := meanBracketOfMoments (337/1000) lo0855 hi0855 accepted0855
def lo0856b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨48,by decide⟩
def lo0856b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨49,by decide⟩
def lo0856 : CheckedMoment :=
  CheckedMoment.ofBessel lo0856b1 lo0856b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0856b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨53,by decide⟩
def hi0856b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨54,by decide⟩
def hi0856 : CheckedMoment :=
  CheckedMoment.ofBessel hi0856b1 hi0856b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0856 : meanBracketCheck (169/500) lo0856 hi0856=true := by decide +kernel
def bracket0856 : MeanBracket := meanBracketOfMoments (169/500) lo0856 hi0856 accepted0856
def lo0857b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨58,by decide⟩
def lo0857b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨59,by decide⟩
def lo0857 : CheckedMoment :=
  CheckedMoment.ofBessel lo0857b1 lo0857b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0857b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨63,by decide⟩
def hi0857b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨0,by decide⟩
def hi0857 : CheckedMoment :=
  CheckedMoment.ofBessel hi0857b1 hi0857b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0857 : meanBracketCheck (339/1000) lo0857 hi0857=true := by decide +kernel
def bracket0857 : MeanBracket := meanBracketOfMoments (339/1000) lo0857 hi0857 accepted0857
def lo0858b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨4,by decide⟩
def lo0858b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨5,by decide⟩
def lo0858 : CheckedMoment :=
  CheckedMoment.ofBessel lo0858b1 lo0858b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0858b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨9,by decide⟩
def hi0858b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨10,by decide⟩
def hi0858 : CheckedMoment :=
  CheckedMoment.ofBessel hi0858b1 hi0858b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0858 : meanBracketCheck (17/50) lo0858 hi0858=true := by decide +kernel
def bracket0858 : MeanBracket := meanBracketOfMoments (17/50) lo0858 hi0858 accepted0858
def lo0859b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨14,by decide⟩
def lo0859b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨15,by decide⟩
def lo0859 : CheckedMoment :=
  CheckedMoment.ofBessel lo0859b1 lo0859b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0859b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨19,by decide⟩
def hi0859b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨20,by decide⟩
def hi0859 : CheckedMoment :=
  CheckedMoment.ofBessel hi0859b1 hi0859b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0859 : meanBracketCheck (341/1000) lo0859 hi0859=true := by decide +kernel
def bracket0859 : MeanBracket := meanBracketOfMoments (341/1000) lo0859 hi0859 accepted0859
def lo0860b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨24,by decide⟩
def lo0860b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨25,by decide⟩
def lo0860 : CheckedMoment :=
  CheckedMoment.ofBessel lo0860b1 lo0860b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0860b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨29,by decide⟩
def hi0860b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨30,by decide⟩
def hi0860 : CheckedMoment :=
  CheckedMoment.ofBessel hi0860b1 hi0860b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0860 : meanBracketCheck (171/500) lo0860 hi0860=true := by decide +kernel
def bracket0860 : MeanBracket := meanBracketOfMoments (171/500) lo0860 hi0860 accepted0860
def lo0861b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨34,by decide⟩
def lo0861b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨35,by decide⟩
def lo0861 : CheckedMoment :=
  CheckedMoment.ofBessel lo0861b1 lo0861b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0861b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨39,by decide⟩
def hi0861b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨40,by decide⟩
def hi0861 : CheckedMoment :=
  CheckedMoment.ofBessel hi0861b1 hi0861b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0861 : meanBracketCheck (343/1000) lo0861 hi0861=true := by decide +kernel
def bracket0861 : MeanBracket := meanBracketOfMoments (343/1000) lo0861 hi0861 accepted0861
def lo0862b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨44,by decide⟩
def lo0862b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨45,by decide⟩
def lo0862 : CheckedMoment :=
  CheckedMoment.ofBessel lo0862b1 lo0862b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0862b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨49,by decide⟩
def hi0862b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨50,by decide⟩
def hi0862 : CheckedMoment :=
  CheckedMoment.ofBessel hi0862b1 hi0862b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0862 : meanBracketCheck (43/125) lo0862 hi0862=true := by decide +kernel
def bracket0862 : MeanBracket := meanBracketOfMoments (43/125) lo0862 hi0862 accepted0862
def lo0863b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨54,by decide⟩
def lo0863b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨55,by decide⟩
def lo0863 : CheckedMoment :=
  CheckedMoment.ofBessel lo0863b1 lo0863b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0863b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨59,by decide⟩
def hi0863b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0134.rows BesselBatch0134.accepted ⟨60,by decide⟩
def hi0863 : CheckedMoment :=
  CheckedMoment.ofBessel hi0863b1 hi0863b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0863 : meanBracketCheck (69/200) lo0863 hi0863=true := by decide +kernel
def bracket0863 : MeanBracket := meanBracketOfMoments (69/200) lo0863 hi0863 accepted0863
#print axioms bracket0848
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0053
