import BecknerOnofri.EntropyScalarCertificate.Bessel0022
import BecknerOnofri.EntropyScalarCertificate.Bessel0023
import BecknerOnofri.EntropyScalarCertificate.Bessel0500
import BecknerOnofri.EntropyScalarCertificate.Brackets0009
import BecknerOnofri.EntropyScalarCertificate.Logs0018
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0144
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (428061099845883805930764244241674175121/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (428061099845883805930764244241674175121/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (53634018936144790724268866439942906521/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53634018936144790724268866439942906521/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (857133251335042131724915175761217427289/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (857133251335042131724915175761217427289/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0144 BracketBatch0009.bracket0145 (857133251335042131724915175761217427289/10000000000000000000000000000000000000000) (40955694177121439551664636454263853/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0144 BracketBatch0009.bracket0145
  (857133251335042131724915175761217427289/10000000000000000000000000000000000000000) (40955694177121439551664636454263853/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0144
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0145
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (858144302978316651588301863039086504333/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (858144302978316651588301863039086504333/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (860166510979063992536429075033918860797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (860166510979063992536429075033918860797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (171831081395738064412473093807300536513/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (171831081395738064412473093807300536513/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0145 BracketBatch0009.bracket0146 (171831081395738064412473093807300536513/2000000000000000000000000000000000000000) (20672773001534230775971265966129743/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0145 BracketBatch0009.bracket0146
  (171831081395738064412473093807300536513/2000000000000000000000000000000000000000) (20672773001534230775971265966129743/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0145
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0146
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (430083255489531996268214537516959430397/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (430083255489531996268214537516959430397/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (172437764789805562636321850532851179013/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (172437764789805562636321850532851179013/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (1722355334928091805718038327698174755859/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1722355334928091805718038327698174755859/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0146 BracketBatch0009.bracket0147 (1722355334928091805718038327698174755859/20000000000000000000000000000000000000000) (8347630327519939115669456005291271/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0146 BracketBatch0009.bracket0147
  (1722355334928091805718038327698174755859/20000000000000000000000000000000000000000) (8347630327519939115669456005291271/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0146
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0147
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (431094411974513906590804626332127947531/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (431094411974513906590804626332127947531/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (864211242143298291186568341859695060567/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (864211242143298291186568341859695060567/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1726400066092326104368177594523950955629/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1726400066092326104368177594523950955629/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0147 BracketBatch0009.bracket0148 (1726400066092326104368177594523950955629/20000000000000000000000000000000000000000) (21066762037760783384470046344602759/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0147 BracketBatch0009.bracket0148
  (1726400066092326104368177594523950955629/20000000000000000000000000000000000000000) (21066762037760783384470046344602759/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0147
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0148
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (216052810535824572796642085464923765141/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (216052810535824572796642085464923765141/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (866233765817037787970658246172446658491/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (866233765817037787970658246172446658491/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (346089001592067215831445317606428343811/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (346089001592067215831445317606428343811/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0148 BracketBatch0009.bracket0149 (346089001592067215831445317606428343811/4000000000000000000000000000000000000000) (8506335268580909649412302610154837/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0148 BracketBatch0009.bracket0149
  (346089001592067215831445317606428343811/4000000000000000000000000000000000000000) (8506335268580909649412302610154837/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0148
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0149
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (108279220727129723496332280771555832311/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (108279220727129723496332280771555832311/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (27133012350796282293728073873969945067/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27133012350796282293728073873969945067/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (216811270130314852671244576267435612579/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (216811270130314852671244576267435612579/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0149 BracketBatch0009.bracket0150 (216811270130314852671244576267435612579/2500000000000000000000000000000000000000) (21466310748544785804763389103633107/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0149 BracketBatch0009.bracket0150
  (216811270130314852671244576267435612579/2500000000000000000000000000000000000000) (21466310748544785804763389103633107/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0149
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0150
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (868256395225481033399298363967038242141/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (868256395225481033399298363967038242141/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (17405582612478706211871761579127714791/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17405582612478706211871761579127714791/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (1738535525849416343992886442923423981691/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1738535525849416343992886442923423981691/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0150 BracketBatch0009.bracket0151 (1738535525849416343992886442923423981691/20000000000000000000000000000000000000000) (8667274525338890710989028882091893/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0150 BracketBatch0009.bracket0151
  (1738535525849416343992886442923423981691/20000000000000000000000000000000000000000) (8667274525338890710989028882091893/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0150
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0151
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (870279130623935310593588078956385739547/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (870279130623935310593588078956385739547/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (436150986133890320430209562579950009391/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (436150986133890320430209562579950009391/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1742581102891715951454007204116285758329/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1742581102891715951454007204116285758329/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0018.rows ScalarLogs0018.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0151 BracketBatch0009.bracket0152 (1742581102891715951454007204116285758329/20000000000000000000000000000000000000000) (43742942851620338660823315318494279/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0151 BracketBatch0009.bracket0152
  (1742581102891715951454007204116285758329/20000000000000000000000000000000000000000) (43742942851620338660823315318494279/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0151
