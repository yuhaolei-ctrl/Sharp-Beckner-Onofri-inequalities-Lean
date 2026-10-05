module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0027
public import BecknerOnofri.EntropyScalarCertificate.Bessel0028
public import BecknerOnofri.EntropyScalarCertificate.Bessel0029

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0011
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0176b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨32,by decide⟩
def lo0176b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨33,by decide⟩
def lo0176 : CheckedMoment :=
  CheckedMoment.ofBessel lo0176b1 lo0176b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0176b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨37,by decide⟩
def hi0176b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨38,by decide⟩
def hi0176 : CheckedMoment :=
  CheckedMoment.ofBessel hi0176b1 hi0176b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0176 : meanBracketCheck (917/10000) lo0176 hi0176=true := by decide +kernel
def bracket0176 : MeanBracket := meanBracketOfMoments (917/10000) lo0176 hi0176 accepted0176
def lo0177b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨42,by decide⟩
def lo0177b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨43,by decide⟩
def lo0177 : CheckedMoment :=
  CheckedMoment.ofBessel lo0177b1 lo0177b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0177b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨47,by decide⟩
def hi0177b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨48,by decide⟩
def hi0177 : CheckedMoment :=
  CheckedMoment.ofBessel hi0177b1 hi0177b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0177 : meanBracketCheck (919/10000) lo0177 hi0177=true := by decide +kernel
def bracket0177 : MeanBracket := meanBracketOfMoments (919/10000) lo0177 hi0177 accepted0177
def lo0178b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨52,by decide⟩
def lo0178b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨53,by decide⟩
def lo0178 : CheckedMoment :=
  CheckedMoment.ofBessel lo0178b1 lo0178b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0178b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨57,by decide⟩
def hi0178b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨58,by decide⟩
def hi0178 : CheckedMoment :=
  CheckedMoment.ofBessel hi0178b1 hi0178b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0178 : meanBracketCheck (921/10000) lo0178 hi0178=true := by decide +kernel
def bracket0178 : MeanBracket := meanBracketOfMoments (921/10000) lo0178 hi0178 accepted0178
def lo0179b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨62,by decide⟩
def lo0179b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨63,by decide⟩
def lo0179 : CheckedMoment :=
  CheckedMoment.ofBessel lo0179b1 lo0179b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0179b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨3,by decide⟩
def hi0179b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨4,by decide⟩
def hi0179 : CheckedMoment :=
  CheckedMoment.ofBessel hi0179b1 hi0179b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0179 : meanBracketCheck (923/10000) lo0179 hi0179=true := by decide +kernel
def bracket0179 : MeanBracket := meanBracketOfMoments (923/10000) lo0179 hi0179 accepted0179
def lo0180b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨8,by decide⟩
def lo0180b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨9,by decide⟩
def lo0180 : CheckedMoment :=
  CheckedMoment.ofBessel lo0180b1 lo0180b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0180b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨13,by decide⟩
def hi0180b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨14,by decide⟩
def hi0180 : CheckedMoment :=
  CheckedMoment.ofBessel hi0180b1 hi0180b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0180 : meanBracketCheck (37/400) lo0180 hi0180=true := by decide +kernel
def bracket0180 : MeanBracket := meanBracketOfMoments (37/400) lo0180 hi0180 accepted0180
def lo0181b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨18,by decide⟩
def lo0181b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨19,by decide⟩
def lo0181 : CheckedMoment :=
  CheckedMoment.ofBessel lo0181b1 lo0181b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0181b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨23,by decide⟩
def hi0181b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨24,by decide⟩
def hi0181 : CheckedMoment :=
  CheckedMoment.ofBessel hi0181b1 hi0181b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0181 : meanBracketCheck (927/10000) lo0181 hi0181=true := by decide +kernel
def bracket0181 : MeanBracket := meanBracketOfMoments (927/10000) lo0181 hi0181 accepted0181
def lo0182b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨28,by decide⟩
def lo0182b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨29,by decide⟩
def lo0182 : CheckedMoment :=
  CheckedMoment.ofBessel lo0182b1 lo0182b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0182b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨33,by decide⟩
def hi0182b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨34,by decide⟩
def hi0182 : CheckedMoment :=
  CheckedMoment.ofBessel hi0182b1 hi0182b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0182 : meanBracketCheck (929/10000) lo0182 hi0182=true := by decide +kernel
def bracket0182 : MeanBracket := meanBracketOfMoments (929/10000) lo0182 hi0182 accepted0182
def lo0183b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨38,by decide⟩
def lo0183b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨39,by decide⟩
def lo0183 : CheckedMoment :=
  CheckedMoment.ofBessel lo0183b1 lo0183b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0183b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨43,by decide⟩
def hi0183b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨44,by decide⟩
def hi0183 : CheckedMoment :=
  CheckedMoment.ofBessel hi0183b1 hi0183b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0183 : meanBracketCheck (931/10000) lo0183 hi0183=true := by decide +kernel
def bracket0183 : MeanBracket := meanBracketOfMoments (931/10000) lo0183 hi0183 accepted0183
def lo0184b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨48,by decide⟩
def lo0184b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨49,by decide⟩
def lo0184 : CheckedMoment :=
  CheckedMoment.ofBessel lo0184b1 lo0184b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0184b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨53,by decide⟩
def hi0184b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨54,by decide⟩
def hi0184 : CheckedMoment :=
  CheckedMoment.ofBessel hi0184b1 hi0184b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0184 : meanBracketCheck (933/10000) lo0184 hi0184=true := by decide +kernel
def bracket0184 : MeanBracket := meanBracketOfMoments (933/10000) lo0184 hi0184 accepted0184
def lo0185b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨58,by decide⟩
def lo0185b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨59,by decide⟩
def lo0185 : CheckedMoment :=
  CheckedMoment.ofBessel lo0185b1 lo0185b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0185b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨63,by decide⟩
def hi0185b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨0,by decide⟩
def hi0185 : CheckedMoment :=
  CheckedMoment.ofBessel hi0185b1 hi0185b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0185 : meanBracketCheck (187/2000) lo0185 hi0185=true := by decide +kernel
def bracket0185 : MeanBracket := meanBracketOfMoments (187/2000) lo0185 hi0185 accepted0185
def lo0186b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨4,by decide⟩
def lo0186b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨5,by decide⟩
def lo0186 : CheckedMoment :=
  CheckedMoment.ofBessel lo0186b1 lo0186b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0186b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨9,by decide⟩
def hi0186b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨10,by decide⟩
def hi0186 : CheckedMoment :=
  CheckedMoment.ofBessel hi0186b1 hi0186b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0186 : meanBracketCheck (937/10000) lo0186 hi0186=true := by decide +kernel
def bracket0186 : MeanBracket := meanBracketOfMoments (937/10000) lo0186 hi0186 accepted0186
def lo0187b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨14,by decide⟩
def lo0187b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨15,by decide⟩
def lo0187 : CheckedMoment :=
  CheckedMoment.ofBessel lo0187b1 lo0187b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0187b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨19,by decide⟩
def hi0187b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨20,by decide⟩
def hi0187 : CheckedMoment :=
  CheckedMoment.ofBessel hi0187b1 hi0187b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0187 : meanBracketCheck (939/10000) lo0187 hi0187=true := by decide +kernel
def bracket0187 : MeanBracket := meanBracketOfMoments (939/10000) lo0187 hi0187 accepted0187
def lo0188b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨24,by decide⟩
def lo0188b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨25,by decide⟩
def lo0188 : CheckedMoment :=
  CheckedMoment.ofBessel lo0188b1 lo0188b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0188b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨29,by decide⟩
def hi0188b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨30,by decide⟩
def hi0188 : CheckedMoment :=
  CheckedMoment.ofBessel hi0188b1 hi0188b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0188 : meanBracketCheck (941/10000) lo0188 hi0188=true := by decide +kernel
def bracket0188 : MeanBracket := meanBracketOfMoments (941/10000) lo0188 hi0188 accepted0188
def lo0189b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨34,by decide⟩
def lo0189b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨35,by decide⟩
def lo0189 : CheckedMoment :=
  CheckedMoment.ofBessel lo0189b1 lo0189b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0189b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨39,by decide⟩
def hi0189b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨40,by decide⟩
def hi0189 : CheckedMoment :=
  CheckedMoment.ofBessel hi0189b1 hi0189b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0189 : meanBracketCheck (943/10000) lo0189 hi0189=true := by decide +kernel
def bracket0189 : MeanBracket := meanBracketOfMoments (943/10000) lo0189 hi0189 accepted0189
def lo0190b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨44,by decide⟩
def lo0190b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨45,by decide⟩
def lo0190 : CheckedMoment :=
  CheckedMoment.ofBessel lo0190b1 lo0190b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0190b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨49,by decide⟩
def hi0190b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨50,by decide⟩
def hi0190 : CheckedMoment :=
  CheckedMoment.ofBessel hi0190b1 hi0190b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0190 : meanBracketCheck (189/2000) lo0190 hi0190=true := by decide +kernel
def bracket0190 : MeanBracket := meanBracketOfMoments (189/2000) lo0190 hi0190 accepted0190
def lo0191b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨54,by decide⟩
def lo0191b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨55,by decide⟩
def lo0191 : CheckedMoment :=
  CheckedMoment.ofBessel lo0191b1 lo0191b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0191b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨59,by decide⟩
def hi0191b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨60,by decide⟩
def hi0191 : CheckedMoment :=
  CheckedMoment.ofBessel hi0191b1 hi0191b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0191 : meanBracketCheck (947/10000) lo0191 hi0191=true := by decide +kernel
def bracket0191 : MeanBracket := meanBracketOfMoments (947/10000) lo0191 hi0191 accepted0191
#print axioms bracket0176
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0011
