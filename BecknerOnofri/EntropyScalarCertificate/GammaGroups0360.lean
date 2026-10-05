module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0450
public import BecknerOnofri.EntropyScalarCertificate.Bessel0451
public import BecknerOnofri.EntropyScalarCertificate.Bessel0713
public import BecknerOnofri.EntropyScalarCertificate.Bessel0714
public import BecknerOnofri.EntropyScalarCertificate.Brackets0180
public import BecknerOnofri.EntropyScalarCertificate.Logs0360
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2880
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1117325652288545998243059802951822138983511/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1117325652288545998243059802951822138983511/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (5599112234490525302647591389394935649341/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5599112234490525302647591389394935649341/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (2237148099186651058772578080830809268851711/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2237148099186651058772578080830809268851711/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2880 BracketBatch0180.bracket2881 (2237148099186651058772578080830809268851711/20000000000000000000000000000000000000000) (3142157696192402097658381546064357107689/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2880 BracketBatch0180.bracket2881
  (2237148099186651058772578080830809268851711/20000000000000000000000000000000000000000) (3142157696192402097658381546064357107689/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2880
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2881
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1119822446898105060529518277878987129868197/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1119822446898105060529518277878987129868197/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (28058260948470118242246049540705447594579/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28058260948470118242246049540705447594579/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (2242152884836909790219360259507205033651357/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2242152884836909790219360259507205033651357/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2881 BracketBatch0180.bracket2882 (2242152884836909790219360259507205033651357/20000000000000000000000000000000000000000) (6287753289355277828703969190800652809623/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2881 BracketBatch0180.bracket2882
  (2242152884836909790219360259507205033651357/20000000000000000000000000000000000000000) (6287753289355277828703969190800652809623/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2881
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2882
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1122330437938804729689841981628217903783157/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1122330437938804729689841981628217903783157/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (11248497008922016232660266632530758939153/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11248497008922016232660266632530758939153/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (2247180138831006352955868644881293797698457/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2247180138831006352955868644881293797698457/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2882 BracketBatch0180.bracket2883 (2247180138831006352955868644881293797698457/20000000000000000000000000000000000000000) (6291198878466372471410508119526222249979/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2882 BracketBatch0180.bracket2883
  (2247180138831006352955868644881293797698457/20000000000000000000000000000000000000000) (6291198878466372471410508119526222249979/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2882
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2883
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1124849700892201623266026663253075893915297/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1124849700892201623266026663253075893915297/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (1127380311919866382505433144081747673648813/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1127380311919866382505433144081747673648813/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (225223001281206800577145980733482356756411/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (225223001281206800577145980733482356756411/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2883 BracketBatch0180.bracket2884 (225223001281206800577145980733482356756411/2000000000000000000000000000000000000000) (1258930440610800484130217585587269575357/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2883 BracketBatch0180.bracket2884
  (225223001281206800577145980733482356756411/2000000000000000000000000000000000000000) (1258930440610800484130217585587269575357/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2883
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2884
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (112738031191986638250543314408174767364881/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (112738031191986638250543314408174767364881/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (56496117393552938710423096745906469594783/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56496117393552938710423096745906469594783/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (225730265979092515671389507899987706554447/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (225730265979092515671389507899987706554447/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2884 BracketBatch0180.bracket2885 (225730265979092515671389507899987706554447/2000000000000000000000000000000000000000) (629811330326547758022799155538955872163/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2884 BracketBatch0180.bracket2885
  (225730265979092515671389507899987706554447/2000000000000000000000000000000000000000) (629811330326547758022799155538955872163/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2884
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2885
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1129922347871058774208461934918129391895657/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1129922347871058774208461934918129391895657/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1132475886290506979479137466408539461372031/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1132475886290506979479137466408539461372031/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (282799779270195719210949925165833606658461/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (282799779270195719210949925165833606658461/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2885 BracketBatch0180.bracket2886 (282799779270195719210949925165833606658461/2500000000000000000000000000000000000000) (1575395553049711838462194469060541719263/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2885 BracketBatch0180.bracket2886
  (282799779270195719210949925165833606658461/2500000000000000000000000000000000000000) (1575395553049711838462194469060541719263/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2885
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2886
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (283118971572626744869784366602134865343007/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (283118971572626744869784366602134865343007/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (567520502713146361569482788613351787047807/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (567520502713146361569482788613351787047807/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (1133758445858399851309051521817621517733821/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1133758445858399851309051521817621517733821/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2886 BracketBatch0180.bracket2887 (1133758445858399851309051521817621517733821/10000000000000000000000000000000000000000) (1261011792630717878129313674750501001991/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2886 BracketBatch0180.bracket2887
  (1133758445858399851309051521817621517733821/10000000000000000000000000000000000000000) (1261011792630717878129313674750501001991/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2886
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2887
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1135041005426292723138965577226703574095611/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1135041005426292723138965577226703574095611/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1137617784237843927632798152814249914565943/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1137617784237843927632798152814249914565943/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0714.rows BesselBatch0714.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (1136329394832068325385881865020476744330777/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1136329394832068325385881865020476744330777/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0360.rows ScalarLogs0360.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0180.bracket2887 BracketBatch0180.bracket2888 (1136329394832068325385881865020476744330777/10000000000000000000000000000000000000000) (6308543589632124952659277125863249666739/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0180.bracket2887 BracketBatch0180.bracket2888
  (1136329394832068325385881865020476744330777/10000000000000000000000000000000000000000) (6308543589632124952659277125863249666739/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2887
