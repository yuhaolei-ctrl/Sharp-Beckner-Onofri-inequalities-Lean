module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0106
public import BecknerOnofri.EntropyScalarCertificate.Bessel0107
public import BecknerOnofri.EntropyScalarCertificate.Bessel0542
public import BecknerOnofri.EntropyScalarCertificate.Brackets0042
public import BecknerOnofri.EntropyScalarCertificate.Brackets0043
public import BecknerOnofri.EntropyScalarCertificate.Logs0085
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0680
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1961808305863352106491491130592589947799/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1961808305863352106491491130592589947799/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (61372675645126338984496248826085775201/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (61372675645126338984496248826085775201/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (3925733926507394953995371093027334754231/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3925733926507394953995371093027334754231/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0680 BracketBatch0042.bracket0681 (3925733926507394953995371093027334754231/20000000000000000000000000000000000000000) (1085572494717414168864665830540417119/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0680 BracketBatch0042.bracket0681
  (3925733926507394953995371093027334754231/20000000000000000000000000000000000000000) (1085572494717414168864665830540417119/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0680
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0681
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1963925620644042847503879962434744806429/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1963925620644042847503879962434744806429/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1966043192403534161026547647549502896659/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1966043192403534161026547647549502896659/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (245623050815473563033151725624015481443/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (245623050815473563033151725624015481443/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0681 BracketBatch0042.bracket0682 (245623050815473563033151725624015481443/1250000000000000000000000000000000000000) (545063670678604569972687706314804731/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0681 BracketBatch0042.bracket0682
  (245623050815473563033151725624015481443/1250000000000000000000000000000000000000) (545063670678604569972687706314804731/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0681
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0682
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (122877699525220885064159227971843931041/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (122877699525220885064159227971843931041/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1968161021466247353524960674973901647269/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1968161021466247353524960674973901647269/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (157368168554791260582060332900936181757/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (157368168554791260582060332900936181757/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0682 BracketBatch0042.bracket0683 (157368168554791260582060332900936181757/800000000000000000000000000000000000000) (1751514578347610482375249016518193/16000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0682 BracketBatch0042.bracket0683
  (157368168554791260582060332900936181757/800000000000000000000000000000000000000) (1751514578347610482375249016518193/16000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0682
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0683
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (984080510733123676762480337486950823633/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (984080510733123676762480337486950823633/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (985139554078400966928074713087057232847/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (985139554078400966928074713087057232847/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (12307625405072029023065969066087550353/62500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12307625405072029023065969066087550353/62500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0683 BracketBatch0042.bracket0684 (12307625405072029023065969066087550353/62500000000000000000000000000000000000) (43971213446715983730692890391786833/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0683 BracketBatch0042.bracket0684
  (12307625405072029023065969066087550353/62500000000000000000000000000000000000) (43971213446715983730692890391786833/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0683
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0684
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1970279108156801933856149426174114465691/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1970279108156801933856149426174114465691/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (1972397452800015923036360517209406904747/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1972397452800015923036360517209406904747/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1971338280478408928446254971691760685219/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1971338280478408928446254971691760685219/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0684 BracketBatch0042.bracket0685 (1971338280478408928446254971691760685219/10000000000000000000000000000000000000000) (1103878546616805558844903910649882817/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0684 BracketBatch0042.bracket0685
  (1971338280478408928446254971691760685219/10000000000000000000000000000000000000000) (1103878546616805558844903910649882817/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0684
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0685
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (246549681600001990379545064651175863093/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (246549681600001990379545064651175863093/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (197451605572090616439318789160277275557/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (197451605572090616439318789160277275557/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (1973456754260461043714774204406089830157/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1973456754260461043714774204406089830157/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0685 BracketBatch0042.bracket0686 (1973456754260461043714774204406089830157/10000000000000000000000000000000000000000) (1108491274008982873001394442552199501/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0685 BracketBatch0042.bracket0686
  (1973456754260461043714774204406089830157/10000000000000000000000000000000000000000) (1108491274008982873001394442552199501/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0685
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0686
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1974516055720906164393187891602772755567/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1974516055720906164393187891602772755567/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (988317458622344317051466287667709339081/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (988317458622344317051466287667709339081/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (3951150972965594798496120466938191433729/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3951150972965594798496120466938191433729/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0686 BracketBatch0042.bracket0687 (3951150972965594798496120466938191433729/20000000000000000000000000000000000000000) (1113118549576798144411274631211635297/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0686 BracketBatch0042.bracket0687
  (3951150972965594798496120466938191433729/20000000000000000000000000000000000000000) (1113118549576798144411274631211635297/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0686
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0687
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1976634917244688634102932575335418678159/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1976634917244688634102932575335418678159/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (19787540376967787521139424111026899947/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19787540376967787521139424111026899947/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (3955388954941467386216874986438108672859/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3955388954941467386216874986438108672859/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0085.rows ScalarLogs0085.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0687 BracketBatch0043.bracket0688 (3955388954941467386216874986438108672859/20000000000000000000000000000000000000000) (558880202294996621757539378448440993/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0687 BracketBatch0043.bracket0688
  (3955388954941467386216874986438108672859/20000000000000000000000000000000000000000) (558880202294996621757539378448440993/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0687
