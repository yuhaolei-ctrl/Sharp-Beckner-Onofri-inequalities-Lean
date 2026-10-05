import BecknerOnofri.EntropyScalarCertificate.Bessel0200
import BecknerOnofri.EntropyScalarCertificate.Bessel0201
import BecknerOnofri.EntropyScalarCertificate.Bessel0588
import BecknerOnofri.EntropyScalarCertificate.Bessel0589
import BecknerOnofri.EntropyScalarCertificate.Brackets0080
import BecknerOnofri.EntropyScalarCertificate.Logs0160
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1280
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (12363764648118134941109803292257957124181/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12363764648118134941109803292257957124181/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (12408893748419624523721146985017509479697/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12408893748419624523721146985017509479697/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (12386329198268879732415475138637733301939/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12386329198268879732415475138637733301939/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1280 BracketBatch0080.bracket1281 (12386329198268879732415475138637733301939/10000000000000000000000000000000000000000) (375448850263763299224888397042576671643/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1280 BracketBatch0080.bracket1281
  (12386329198268879732415475138637733301939/10000000000000000000000000000000000000000) (375448850263763299224888397042576671643/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1280
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1281
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (6204446874209812261860573492508754739847/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6204446874209812261860573492508754739847/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (12454353867707162192653521256939389056061/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12454353867707162192653521256939389056061/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0588.rows BesselBatch0588.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (4972649523225357343274933648391379707151/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4972649523225357343274933648391379707151/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1281 BracketBatch0080.bracket1282 (4972649523225357343274933648391379707151/4000000000000000000000000000000000000000) (378054559375241978424024145774241160821/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1281 BracketBatch0080.bracket1282
  (4972649523225357343274933648391379707151/4000000000000000000000000000000000000000) (378054559375241978424024145774241160821/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1281
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1282
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (6227176933853581096326760628469694528029/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6227176933853581096326760628469694528029/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (12500149494950176325826050274627893580179/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12500149494950176325826050274627893580179/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (24954503362657338518479571531567282636237/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (24954503362657338518479571531567282636237/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1282 BracketBatch0080.bracket1283 (24954503362657338518479571531567282636237/20000000000000000000000000000000000000000) (95169949189921428549430509807020457429/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1282 BracketBatch0080.bracket1283
  (24954503362657338518479571531567282636237/20000000000000000000000000000000000000000) (95169949189921428549430509807020457429/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1282
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1283
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (781259343434386020364128142164243348761/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (781259343434386020364128142164243348761/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (12546285201580748112740950785046136473687/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12546285201580748112740950785046136473687/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (25046434696530924438567001059674030053863/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25046434696530924438567001059674030053863/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1283 BracketBatch0080.bracket1284 (25046434696530924438567001059674030053863/20000000000000000000000000000000000000000) (95831191756209533266078978023183307673/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1283 BracketBatch0080.bracket1284
  (25046434696530924438567001059674030053863/20000000000000000000000000000000000000000) (95831191756209533266078978023183307673/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1283
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1284
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (3136571300395187028185237696261534118421/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3136571300395187028185237696261534118421/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (3148191410842113443348607070364659157439/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3148191410842113443348607070364659157439/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (314238135561865023576692238331309663793/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (314238135561865023576692238331309663793/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1284 BracketBatch0080.bracket1285 (314238135561865023576692238331309663793/250000000000000000000000000000000000000) (385989677963711451871084978457163902343/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1284 BracketBatch0080.bracket1285
  (314238135561865023576692238331309663793/250000000000000000000000000000000000000) (385989677963711451871084978457163902343/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1284
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1285
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (12592765643368453773394428281458636629753/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12592765643368453773394428281458636629753/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (3159898890586290475620996852658395640237/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3159898890586290475620996852658395640237/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (25232361205713615675878415692092219190701/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25232361205713615675878415692092219190701/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1285 BracketBatch0080.bracket1286 (25232361205713615675878415692092219190701/20000000000000000000000000000000000000000) (388674740616719320139904862565813573419/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1285 BracketBatch0080.bracket1286
  (25232361205713615675878415692092219190701/20000000000000000000000000000000000000000) (388674740616719320139904862565813573419/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1285
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1286
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (2527919112469032380496797482126716512189/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2527919112469032380496797482126716512189/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (6343389894390646740701308618302027197451/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6343389894390646740701308618302027197451/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (25326375351126455383886604647237636955847/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25326375351126455383886604647237636955847/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1286 BracketBatch0080.bracket1287 (25326375351126455383886604647237636955847/20000000000000000000000000000000000000000) (78276033867027688770482702630364552759/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1286 BracketBatch0080.bracket1287
  (25326375351126455383886604647237636955847/20000000000000000000000000000000000000000) (78276033867027688770482702630364552759/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1286
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1287
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (12686779788781293481402617236604054394899/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12686779788781293481402617236604054394899/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (12734323243215102496020715836738776803087/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12734323243215102496020715836738776803087/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (12710551515998197988711666536671415598993/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12710551515998197988711666536671415598993/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0160.rows ScalarLogs0160.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1287 BracketBatch0080.bracket1288 (12710551515998197988711666536671415598993/10000000000000000000000000000000000000000) (98526545461481820988523193890865598311/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1287 BracketBatch0080.bracket1288
  (12710551515998197988711666536671415598993/10000000000000000000000000000000000000000) (98526545461481820988523193890865598311/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1287
