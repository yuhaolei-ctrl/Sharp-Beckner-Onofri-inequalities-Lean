module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0163
public import BecknerOnofri.EntropyScalarCertificate.Bessel0164
public import BecknerOnofri.EntropyScalarCertificate.Bessel0165
public import BecknerOnofri.EntropyScalarCertificate.Bessel0570
public import BecknerOnofri.EntropyScalarCertificate.Bessel0571
public import BecknerOnofri.EntropyScalarCertificate.Brackets0065
public import BecknerOnofri.EntropyScalarCertificate.Brackets0066
public import BecknerOnofri.EntropyScalarCertificate.Logs0131
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1048
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (6283617364399157677432807201670863917941/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6283617364399157677432807201670863917941/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (393778257983764358099698666599195909627/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (393778257983764358099698666599195909627/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (12584069492139387407027985867257998471973/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12584069492139387407027985867257998471973/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1048 BracketBatch0065.bracket1049 (12584069492139387407027985867257998471973/20000000000000000000000000000000000000000) (8751286984090525097476602272231393231/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1048 BracketBatch0065.bracket1049
  (12584069492139387407027985867257998471973/20000000000000000000000000000000000000000) (8751286984090525097476602272231393231/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1048
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1049
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (6300452127740229729595178665587134554029/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6300452127740229729595178665587134554029/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (3158664135270259880785717956308877662283/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3158664135270259880785717956308877662283/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (2523556079656149898233322915640977975719/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2523556079656149898233322915640977975719/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1049 BracketBatch0065.bracket1050 (2523556079656149898233322915640977975719/4000000000000000000000000000000000000000) (35290971366084686709152873480968494719/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1049 BracketBatch0065.bracket1050
  (2523556079656149898233322915640977975719/4000000000000000000000000000000000000000) (35290971366084686709152873480968494719/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1049
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1050
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (6317328270540519761571435912617755324563/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6317328270540519761571435912617755324563/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1583561513729579841757182847346282220709/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1583561513729579841757182847346282220709/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (12651574325458839128600167302002884207399/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12651574325458839128600167302002884207399/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1050 BracketBatch0065.bracket1051 (12651574325458839128600167302002884207399/20000000000000000000000000000000000000000) (35578697511603430663138245670070857583/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1050 BracketBatch0065.bracket1051
  (12651574325458839128600167302002884207399/20000000000000000000000000000000000000000) (35578697511603430663138245670070857583/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1050
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1051
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (6334246054918319367028731389385128882833/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6334246054918319367028731389385128882833/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (793900718149251100291897117358528536089/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (793900718149251100291897117358528536089/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (2537090360022465633872781665650671434309/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2537090360022465633872781665650671434309/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1051 BracketBatch0065.bracket1052 (2537090360022465633872781665650671434309/4000000000000000000000000000000000000000) (224177107110972392134410149457638811/31250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1051 BracketBatch0065.bracket1052
  (2537090360022465633872781665650671434309/4000000000000000000000000000000000000000) (224177107110972392134410149457638811/31250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1051
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1052
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (6351205745194008802335176938868228288709/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6351205745194008802335176938868228288709/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (10189132172663232446886913001003252923/16000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10189132172663232446886913001003252923/16000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (794963334569283067602468597780953835349/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (794963334569283067602468597780953835349/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1052 BracketBatch0065.bracket1053 (794963334569283067602468597780953835349/1250000000000000000000000000000000000000) (564998454284390649954023422476339873/78125000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1052 BracketBatch0065.bracket1053
  (794963334569283067602468597780953835349/1250000000000000000000000000000000000000) (564998454284390649954023422476339873/78125000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1052
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1053
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (796025950989315034913040078203379134609/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (796025950989315034913040078203379134609/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (399078244492383208610232023383746412197/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (399078244492383208610232023383746412197/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (1594182439974081452133504124970871959003/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1594182439974081452133504124970871959003/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1053 BracketBatch0065.bracket1054 (1594182439974081452133504124970871959003/2500000000000000000000000000000000000000) (72906800432011108508285768652802120719/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1053 BracketBatch0065.bracket1054
  (1594182439974081452133504124970871959003/2500000000000000000000000000000000000000) (72906800432011108508285768652802120719/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1053
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1054
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (6385251911878131337763712374139942595149/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6385251911878131337763712374139942595149/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (6402338928159593545745526811301436384541/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6402338928159593545745526811301436384541/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (1278759084003772488350923918544137897969/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1278759084003772488350923918544137897969/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1054 BracketBatch0065.bracket1055 (1278759084003772488350923918544137897969/2000000000000000000000000000000000000000) (36748845524232032732304271694950203849/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1054 BracketBatch0065.bracket1055
  (1278759084003772488350923918544137897969/2000000000000000000000000000000000000000) (36748845524232032732304271694950203849/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1054
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1055
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (3201169464079796772872763405650718192269/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3201169464079796772872763405650718192269/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (6419468930135601870715716305623525134029/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6419468930135601870715716305623525134029/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (12821807858295195416461243116924961518567/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12821807858295195416461243116924961518567/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0131.rows ScalarLogs0131.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1055 BracketBatch0066.bracket1056 (12821807858295195416461243116924961518567/20000000000000000000000000000000000000000) (74092496053077409063663683584818944991/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1055 BracketBatch0066.bracket1056
  (12821807858295195416461243116924961518567/20000000000000000000000000000000000000000) (74092496053077409063663683584818944991/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1055
