module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0137
public import BecknerOnofri.EntropyScalarCertificate.Bessel0138
public import BecknerOnofri.EntropyScalarCertificate.Bessel0557
public import BecknerOnofri.EntropyScalarCertificate.Bessel0558
public import BecknerOnofri.EntropyScalarCertificate.Brackets0055
public import BecknerOnofri.EntropyScalarCertificate.Logs0110
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0880
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (3886806543335654833607801114548732730497/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3886806543335654833607801114548732730497/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1949606509792711020463608560734204209413/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1949606509792711020463608560734204209413/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (7786019562921076874535018236017141149323/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7786019562921076874535018236017141149323/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0880 BracketBatch0055.bracket0881 (7786019562921076874535018236017141149323/20000000000000000000000000000000000000000) (7061315792619023754670475105083939883/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0880 BracketBatch0055.bracket0881
  (7786019562921076874535018236017141149323/20000000000000000000000000000000000000000) (7061315792619023754670475105083939883/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0880
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0881
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (3899213019585422040927217121468408418823/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3899213019585422040927217121468408418823/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1955817859181204830765847957404370102847/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1955817859181204830765847957404370102847/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (7810848737947831702458913036277148624517/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7810848737947831702458913036277148624517/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0881 BracketBatch0055.bracket0882 (7810848737947831702458913036277148624517/20000000000000000000000000000000000000000) (71420957143377531732228871743853923/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0881 BracketBatch0055.bracket0882
  (7810848737947831702458913036277148624517/20000000000000000000000000000000000000000) (71420957143377531732228871743853923/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0881
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0882
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (3911635718362409661531695914808740205691/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3911635718362409661531695914808740205691/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (122627335107661463048602167754621908917/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (122627335107661463048602167754621908917/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (1567142088361515295817393056591328258207/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1567142088361515295817393056591328258207/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0882 BracketBatch0055.bracket0883 (1567142088361515295817393056591328258207/4000000000000000000000000000000000000000) (7223588275797730818848392476107171377/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0882 BracketBatch0055.bracket0883
  (1567142088361515295817393056591328258207/4000000000000000000000000000000000000000) (7223588275797730818848392476107171377/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0882
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0883
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (3924074723445166817555269368147901085341/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3924074723445166817555269368147901085341/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (3936530119069945133732674626937801029683/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3936530119069945133732674626937801029683/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (491287802657194496955496499692856382189/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (491287802657194496955496499692856382189/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0883 BracketBatch0055.bracket0884 (491287802657194496955496499692856382189/1250000000000000000000000000000000000000) (14611596122625426943069531736187303413/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0883 BracketBatch0055.bracket0884
  (491287802657194496955496499692856382189/1250000000000000000000000000000000000000) (14611596122625426943069531736187303413/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0883
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0884
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (49206626488374314171658432836722512871/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (49206626488374314171658432836722512871/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (493625248741801993507036563534573867669/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (493625248741801993507036563534573867669/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (985691513625545135223620891901798996379/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (985691513625545135223620891901798996379/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0884 BracketBatch0055.bracket0885 (985691513625545135223620891901798996379/2500000000000000000000000000000000000000) (7388729676516390253443561499742505183/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0884 BracketBatch0055.bracket0885
  (985691513625545135223620891901798996379/2500000000000000000000000000000000000000) (7388729676516390253443561499742505183/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0884
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0885
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (3949001989934415948056292508276590941349/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3949001989934415948056292508276590941349/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (3961490421201422664877409379655256470463/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3961490421201422664877409379655256470463/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (1977623102783959653233425471982961852953/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1977623102783959653233425471982961852953/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0885 BracketBatch0055.bracket0886 (1977623102783959653233425471982961852953/5000000000000000000000000000000000000000) (1494477549693005980275741858726702629/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0885 BracketBatch0055.bracket0886
  (1977623102783959653233425471982961852953/5000000000000000000000000000000000000000) (1494477549693005980275741858726702629/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0885
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0886
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (198074521060071133243870468982762823523/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (198074521060071133243870468982762823523/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (3973995498502768653335761124814298555841/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3973995498502768653335761124814298555841/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (7935485919704191318213170504469555026301/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7935485919704191318213170504469555026301/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0886 BracketBatch0055.bracket0887 (7935485919704191318213170504469555026301/20000000000000000000000000000000000000000) (755677692574099736334638740149010609/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0886 BracketBatch0055.bracket0887
  (7935485919704191318213170504469555026301/20000000000000000000000000000000000000000) (755677692574099736334638740149010609/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0886
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0887
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1986997749251384326667880562407149277919/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1986997749251384326667880562407149277919/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (797303461588608219855265865082360764263/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (797303461588608219855265865082360764263/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (7960512806445809752612090450226102377153/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7960512806445809752612090450226102377153/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0110.rows ScalarLogs0110.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0887 BracketBatch0055.bracket0888 (7960512806445809752612090450226102377153/20000000000000000000000000000000000000000) (61135215028457190720666404023230513/40000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0887 BracketBatch0055.bracket0888
  (7960512806445809752612090450226102377153/20000000000000000000000000000000000000000) (61135215028457190720666404023230513/40000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0887
