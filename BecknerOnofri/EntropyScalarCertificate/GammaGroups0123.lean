import BecknerOnofri.EntropyScalarCertificate.Bessel0153
import BecknerOnofri.EntropyScalarCertificate.Bessel0154
import BecknerOnofri.EntropyScalarCertificate.Bessel0155
import BecknerOnofri.EntropyScalarCertificate.Bessel0565
import BecknerOnofri.EntropyScalarCertificate.Bessel0566
import BecknerOnofri.EntropyScalarCertificate.Brackets0061
import BecknerOnofri.EntropyScalarCertificate.Brackets0062
import BecknerOnofri.EntropyScalarCertificate.Logs0123
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0984
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1056346850707518002145817056426583044557/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1056346850707518002145817056426583044557/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1059276202380104740367446782071251629729/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1059276202380104740367446782071251629729/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1057811526543811371256631919248917337143/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1057811526543811371256631919248917337143/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0984 BracketBatch0061.bracket0985 (1057811526543811371256631919248917337143/2000000000000000000000000000000000000000) (5055470419612398610917115808542659349/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0984 BracketBatch0061.bracket0985
  (1057811526543811371256631919248917337143/2000000000000000000000000000000000000000) (5055470419612398610917115808542659349/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0984
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0985
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (2648190505950261850918616955178129074321/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2648190505950261850918616955178129074321/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (5311056042859998924870753051599533559681/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5311056042859998924870753051599533559681/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (10607437054760522626707986961955791708323/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10607437054760522626707986961955791708323/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0985 BracketBatch0061.bracket0986 (10607437054760522626707986961955791708323/20000000000000000000000000000000000000000) (2040573662704926289206318997499788229/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0985 BracketBatch0061.bracket0986
  (10607437054760522626707986961955791708323/20000000000000000000000000000000000000000) (2040573662704926289206318997499788229/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0985
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0986
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2655528021429999462435376525799766779839/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2655528021429999462435376525799766779839/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1065151901319336500677213941982988806857/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1065151901319336500677213941982988806857/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (10636815549456681428256822761514477593963/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10636815549456681428256822761514477593963/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0986 BracketBatch0061.bracket0987 (10636815549456681428256822761514477593963/20000000000000000000000000000000000000000) (4118183644677002394852282557419746497/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0986 BracketBatch0061.bracket0987
  (10636815549456681428256822761514477593963/20000000000000000000000000000000000000000) (4118183644677002394852282557419746497/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0986
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0987
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2662879753298341251693034854957472017141/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2662879753298341251693034854957472017141/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (2670245782215616347208785913654415044857/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2670245782215616347208785913654415044857/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (2666562767756978799450910384305943530999/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2666562767756978799450910384305943530999/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0987 BracketBatch0061.bracket0988 (2666562767756978799450910384305943530999/5000000000000000000000000000000000000000) (5194358506347076881604308441812039929/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0987 BracketBatch0061.bracket0988
  (2666562767756978799450910384305943530999/5000000000000000000000000000000000000000) (5194358506347076881604308441812039929/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0987
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0988
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (5340491564431232694417571827308830089711/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5340491564431232694417571827308830089711/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (5355252378835319745149963655912604970079/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5355252378835319745149963655912604970079/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (1069574394326655243956753548322143505979/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1069574394326655243956753548322143505979/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0988 BracketBatch0061.bracket0989 (1069574394326655243956753548322143505979/2000000000000000000000000000000000000000) (41930583259997836989214229116800005293/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0988 BracketBatch0061.bracket0989
  (1069574394326655243956753548322143505979/2000000000000000000000000000000000000000) (41930583259997836989214229116800005293/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0988
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0989
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1338813094708829936287490913978151242519/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1338813094708829936287490913978151242519/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1342510528360693804957863027725783706801/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1342510528360693804957863027725783706801/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (67033090576738093531133848542598373733/125000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (67033090576738093531133848542598373733/125000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0989 BracketBatch0061.bracket0990 (67033090576738093531133848542598373733/125000000000000000000000000000000000000) (10577249336719981562611780589997175061/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0989 BracketBatch0061.bracket0990
  (67033090576738093531133848542598373733/125000000000000000000000000000000000000) (10577249336719981562611780589997175061/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0989
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0990
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (5370042113442775219831452110903134827201/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5370042113442775219831452110903134827201/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (2692430466530435940483944674519652200329/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2692430466530435940483944674519652200329/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (10754903046503647100799341459942439227859/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10754903046503647100799341459942439227859/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0990 BracketBatch0061.bracket0991 (10754903046503647100799341459942439227859/20000000000000000000000000000000000000000) (42690125662991879766758597827663683323/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0990 BracketBatch0061.bracket0991
  (10754903046503647100799341459942439227859/20000000000000000000000000000000000000000) (42690125662991879766758597827663683323/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0990
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0991
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1076972186612174376193577869807860880131/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1076972186612174376193577869807860880131/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (5399709003681735937222142582637734003931/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5399709003681735937222142582637734003931/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (5392284968371303909095015965838519202293/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5392284968371303909095015965838519202293/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0123.rows ScalarLogs0123.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0991 BracketBatch0062.bracket0992 (5392284968371303909095015965838519202293/10000000000000000000000000000000000000000) (43073983639587566884156583180083318337/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0991 BracketBatch0062.bracket0992
  (5392284968371303909095015965838519202293/10000000000000000000000000000000000000000) (43073983639587566884156583180083318337/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0991
