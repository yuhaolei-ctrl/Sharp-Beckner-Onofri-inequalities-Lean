module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0325
public import BecknerOnofri.EntropyScalarCertificate.Bessel0326
public import BecknerOnofri.EntropyScalarCertificate.Bessel0651
public import BecknerOnofri.EntropyScalarCertificate.Bessel0652
public import BecknerOnofri.EntropyScalarCertificate.Brackets0130
public import BecknerOnofri.EntropyScalarCertificate.Logs0260
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2080
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (64147503808861710635667944975014631703047/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (64147503808861710635667944975014631703047/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1607637236987129395899444737873322796159/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1607637236987129395899444737873322796159/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (128452993288346886471645734489947543549407/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (128452993288346886471645734489947543549407/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2080 BracketBatch0130.bracket2081 (128452993288346886471645734489947543549407/20000000000000000000000000000000000000000) (2185459643434329701394282097701478559949/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2080 BracketBatch0130.bracket2081
  (128452993288346886471645734489947543549407/20000000000000000000000000000000000000000) (2185459643434329701394282097701478559949/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2080
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2081
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (64305489479485175835977789514932911846357/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (64305489479485175835977789514932911846357/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (3223213720682475207853733618201287621013/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3223213720682475207853733618201287621013/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (128769763893134679993052461878958664266617/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (128769763893134679993052461878958664266617/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2081 BracketBatch0130.bracket2082 (128769763893134679993052461878958664266617/20000000000000000000000000000000000000000) (218861123185159687539890160078348638577/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2081 BracketBatch0130.bracket2082
  (128769763893134679993052461878958664266617/20000000000000000000000000000000000000000) (218861123185159687539890160078348638577/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2081
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2082
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (64464274413649504157074672364025752420257/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (64464274413649504157074672364025752420257/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (64623864680163189209648503376246896167081/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (64623864680163189209648503376246896167081/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (64544069546906346683361587870136324293669/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64544069546906346683361587870136324293669/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2082 BracketBatch0130.bracket2083 (64544069546906346683361587870136324293669/10000000000000000000000000000000000000000) (2191771610792977801971819621589881421857/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2082 BracketBatch0130.bracket2083
  (64544069546906346683361587870136324293669/10000000000000000000000000000000000000000) (2191771610792977801971819621589881421857/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2082
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2083
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (32311932340081594604824251688123448083539/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32311932340081594604824251688123448083539/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (64784266409451421206559530405491251938813/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (64784266409451421206559530405491251938813/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (129408131089614610416208033781738148105891/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (129408131089614610416208033781738148105891/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2083 BracketBatch0130.bracket2084 (129408131089614610416208033781738148105891/20000000000000000000000000000000000000000) (274367603215947064787289076390069263063/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2083 BracketBatch0130.bracket2084
  (129408131089614610416208033781738148105891/20000000000000000000000000000000000000000) (274367603215947064787289076390069263063/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2083
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2084
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (6478426640945142120655953040549125193881/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6478426640945142120655953040549125193881/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (16236371448584996912772772122281081727047/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16236371448584996912772772122281081727047/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (64864876101895704428825309447307789423499/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64864876101895704428825309447307789423499/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2084 BracketBatch0130.bracket2085 (64864876101895704428825309447307789423499/10000000000000000000000000000000000000000) (1099059461239356617786670859183068565271/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2084 BracketBatch0130.bracket2085
  (64864876101895704428825309447307789423499/10000000000000000000000000000000000000000) (1099059461239356617786670859183068565271/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2084
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2085
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (12989097158867997530218217697824865381637/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12989097158867997530218217697824865381637/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (65107529090851172733464738414554950026823/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (65107529090851172733464738414554950026823/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (4064156715162223762017369590739977404219/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4064156715162223762017369590739977404219/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2085 BracketBatch0130.bracket2086 (4064156715162223762017369590739977404219/625000000000000000000000000000000000000) (1100652973613766553122947572302809377429/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2085 BracketBatch0130.bracket2086
  (4064156715162223762017369590739977404219/625000000000000000000000000000000000000) (1100652973613766553122947572302809377429/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2085
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2086
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3255376454542558636673236920727747501341/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3255376454542558636673236920727747501341/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (65270402619011870245607332842020498168147/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (65270402619011870245607332842020498168147/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (130377931709863042979072071256575448194967/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (130377931709863042979072071256575448194967/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2086 BracketBatch0130.bracket2087 (130377931709863042979072071256575448194967/20000000000000000000000000000000000000000) (1102250973258330156961203141309778212937/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2086 BracketBatch0130.bracket2087
  (130377931709863042979072071256575448194967/20000000000000000000000000000000000000000) (1102250973258330156961203141309778212937/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2086
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2087
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (4079400163688241890350458302626281135509/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4079400163688241890350458302626281135509/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (8179264095459266153807513254507462192273/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8179264095459266153807513254507462192273/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (16338064422835749934508429859760024463291/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16338064422835749934508429859760024463291/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0260.rows ScalarLogs0260.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2087 BracketBatch0130.bracket2088 (16338064422835749934508429859760024463291/2500000000000000000000000000000000000000) (220770696725389816201443976142497365623/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2087 BracketBatch0130.bracket2088
  (16338064422835749934508429859760024463291/2500000000000000000000000000000000000000) (220770696725389816201443976142497365623/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2087
