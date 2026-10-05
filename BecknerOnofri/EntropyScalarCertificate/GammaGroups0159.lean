import BecknerOnofri.EntropyScalarCertificate.Bessel0198
import BecknerOnofri.EntropyScalarCertificate.Bessel0199
import BecknerOnofri.EntropyScalarCertificate.Bessel0200
import BecknerOnofri.EntropyScalarCertificate.Bessel0588
import BecknerOnofri.EntropyScalarCertificate.Brackets0079
import BecknerOnofri.EntropyScalarCertificate.Brackets0080
import BecknerOnofri.EntropyScalarCertificate.Logs0159
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1272
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (12014135661526581827745928184275151749457/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12014135661526581827745928184275151749457/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (12056768898879310329254822267430286694581/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12056768898879310329254822267430286694581/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (12035452280202946078500375225852719222019/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12035452280202946078500375225852719222019/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1272 BracketBatch0079.bracket1273 (12035452280202946078500375225852719222019/10000000000000000000000000000000000000000) (355282646385155486123084382251893527637/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1272 BracketBatch0079.bracket1273
  (12035452280202946078500375225852719222019/10000000000000000000000000000000000000000) (355282646385155486123084382251893527637/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1272
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1273
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (6028384449439655164627411133715143347289/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6028384449439655164627411133715143347289/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (3024925000627225737415268096239157852587/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3024925000627225737415268096239157852587/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (12078234450694106639457947326193459052463/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12078234450694106639457947326193459052463/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1273 BracketBatch0079.bracket1274 (12078234450694106639457947326193459052463/10000000000000000000000000000000000000000) (178869566228869817965722274229665573833/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1273 BracketBatch0079.bracket1274
  (12078234450694106639457947326193459052463/10000000000000000000000000000000000000000) (178869566228869817965722274229665573833/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1273
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1274
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2419940000501780589932214476991326282069/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2419940000501780589932214476991326282069/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1214293286364377658538061603603295452161/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1214293286364377658538061603603295452161/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (4848526573230535907008337684197917186391/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4848526573230535907008337684197917186391/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1274 BracketBatch0079.bracket1275 (4848526573230535907008337684197917186391/4000000000000000000000000000000000000000) (360213617572010992839252754603458574067/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1274 BracketBatch0079.bracket1275
  (4848526573230535907008337684197917186391/4000000000000000000000000000000000000000) (360213617572010992839252754603458574067/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1274
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1275
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (12142932863643776585380616036032954521607/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12142932863643776585380616036032954521607/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (12186471442609029041603240383029261810607/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12186471442609029041603240383029261810607/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (12164702153126402813491928209531108166107/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12164702153126402813491928209531108166107/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1275 BracketBatch0079.bracket1276 (12164702153126402813491928209531108166107/10000000000000000000000000000000000000000) (22669142683739771366103256387396444863/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1275 BracketBatch0079.bracket1276
  (12164702153126402813491928209531108166107/10000000000000000000000000000000000000000) (22669142683739771366103256387396444863/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1275
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1276
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (3046617860652257260400810095757315452651/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3046617860652257260400810095757315452651/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2446063954070083898343689736633938864047/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2446063954070083898343689736633938864047/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (24416791212959448533321689066198956130839/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (24416791212959448533321689066198956130839/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1276 BracketBatch0079.bracket1277 (24416791212959448533321689066198956130839/20000000000000000000000000000000000000000) (365217312505892944639698977552674760857/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1276 BracketBatch0079.bracket1277
  (24416791212959448533321689066198956130839/20000000000000000000000000000000000000000) (365217312505892944639698977552674760857/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1276
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1277
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1528789971293802436464806085396211790029/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1528789971293802436464806085396211790029/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (6137240974998929349141870394588176031357/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6137240974998929349141870394588176031357/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (12252400860174139095001094736173023191473/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12252400860174139095001094736173023191473/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1277 BracketBatch0079.bracket1278 (12252400860174139095001094736173023191473/10000000000000000000000000000000000000000) (367746893000130307526743222534623102437/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1277 BracketBatch0079.bracket1278
  (12252400860174139095001094736173023191473/10000000000000000000000000000000000000000) (367746893000130307526743222534623102437/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1277
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1278
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (12274481949997858698283740789176352062711/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12274481949997858698283740789176352062711/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (2463792431693914372900481254779695376363/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2463792431693914372900481254779695376363/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (12296722054233715281393073531537414472263/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12296722054233715281393073531537414472263/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1278 BracketBatch0079.bracket1279 (12296722054233715281393073531537414472263/10000000000000000000000000000000000000000) (185147606995676062666591123475744389819/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1278 BracketBatch0079.bracket1279
  (12296722054233715281393073531537414472263/10000000000000000000000000000000000000000) (185147606995676062666591123475744389819/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1278
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1279
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (3079740539617392966125601568474619220453/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3079740539617392966125601568474619220453/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1545470581014766867638725411532244640523/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1545470581014766867638725411532244640523/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (6170681701646926701403052391539108501499/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6170681701646926701403052391539108501499/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0159.rows ScalarLogs0159.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0079.bracket1279 BracketBatch0080.bracket1280 (6170681701646926701403052391539108501499/5000000000000000000000000000000000000000) (186431233970971393227378975619996139583/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0079.bracket1279 BracketBatch0080.bracket1280
  (6170681701646926701403052391539108501499/5000000000000000000000000000000000000000) (186431233970971393227378975619996139583/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1279
