module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0402
public import BecknerOnofri.EntropyScalarCertificate.Bessel0403
public import BecknerOnofri.EntropyScalarCertificate.Bessel0690
public import BecknerOnofri.EntropyScalarCertificate.Brackets0161
public import BecknerOnofri.EntropyScalarCertificate.Logs0322
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2576
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (415168784715629280975143934997513382627719/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (415168784715629280975143934997513382627719/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (83308770660791798078432130808784210799047/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (83308770660791798078432130808784210799047/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (415856319009794135683652294520717218311477/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (415856319009794135683652294520717218311477/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2576 BracketBatch0161.bracket2577 (415856319009794135683652294520717218311477/10000000000000000000000000000000000000000) (477160590662189612018178003808797613359/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2576 BracketBatch0161.bracket2577
  (415856319009794135683652294520717218311477/10000000000000000000000000000000000000000) (477160590662189612018178003808797613359/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2576
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2577
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (13016995415748718449755020438872532937351/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13016995415748718449755020438872532937351/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (417928089278027578974882782106955363487169/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (417928089278027578974882782106955363487169/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (834471942581986569367043436150876417482401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (834471942581986569367043436150876417482401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2577 BracketBatch0161.bracket2578 (834471942581986569367043436150876417482401/20000000000000000000000000000000000000000) (2388230636190650388984322259976463107509/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2577 BracketBatch0161.bracket2578
  (834471942581986569367043436150876417482401/20000000000000000000000000000000000000000) (2388230636190650388984322259976463107509/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2577
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2578
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (208964044639013789487441391053477681743583/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (208964044639013789487441391053477681743583/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (209660792309126362707078938032691165887479/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (209660792309126362707078938032691165887479/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (209312418474070076097260164543084423815531/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (209312418474070076097260164543084423815531/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2578 BracketBatch0161.bracket2579 (209312418474070076097260164543084423815531/5000000000000000000000000000000000000000) (298833333347043828479228669666390094693/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2578 BracketBatch0161.bracket2579
  (209312418474070076097260164543084423815531/5000000000000000000000000000000000000000) (298833333347043828479228669666390094693/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2578
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2579
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (83864316923650545082831575213076466354991/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (83864316923650545082831575213076466354991/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (210362216269844300169656652666375316469809/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (210362216269844300169656652666375316469809/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (840046017157941325753471181398132964714573/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (840046017157941325753471181398132964714573/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2579 BracketBatch0161.bracket2580 (840046017157941325753471181398132964714573/20000000000000000000000000000000000000000) (4786222195608837065070018127623015844717/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2579 BracketBatch0161.bracket2580
  (840046017157941325753471181398132964714573/20000000000000000000000000000000000000000) (4786222195608837065070018127623015844717/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2579
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2580
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (84144886507937720067862661066550126587923/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (84144886507937720067862661066550126587923/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (422136727512810992438113551598423527455451/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (422136727512810992438113551598423527455451/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (421430580026249796388713428465587080197533/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (421430580026249796388713428465587080197533/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2580 BracketBatch0161.bracket2581 (421430580026249796388713428465587080197533/10000000000000000000000000000000000000000) (4791127964973392107612582467857206157489/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2580 BracketBatch0161.bracket2581
  (421430580026249796388713428465587080197533/10000000000000000000000000000000000000000) (4791127964973392107612582467857206157489/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2580
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2581
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (52767090939101374054764193949802940931931/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (52767090939101374054764193949802940931931/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (52944820660590469337597033846634349085383/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52944820660590469337597033846634349085383/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (52855955799845921696180613898218645008657/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (52855955799845921696180613898218645008657/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2581 BracketBatch0161.bracket2582 (52855955799845921696180613898218645008657/1250000000000000000000000000000000000000) (4796050749031601521560756509680272834161/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2581 BracketBatch0161.bracket2582
  (52855955799845921696180613898218645008657/1250000000000000000000000000000000000000) (4796050749031601521560756509680272834161/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2581
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2582
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (423558565284723754700776270773074792683061/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (423558565284723754700776270773074792683061/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (84998008580159313642943938342693431059501/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (84998008580159313642943938342693431059501/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (424274304092760161457747981243270973990283/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (424274304092760161457747981243270973990283/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2582 BracketBatch0161.bracket2583 (424274304092760161457747981243270973990283/10000000000000000000000000000000000000000) (4800990656140986758458441075115283600189/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2582 BracketBatch0161.bracket2583
  (424274304092760161457747981243270973990283/10000000000000000000000000000000000000000) (4800990656140986758458441075115283600189/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2582
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2583
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (212495021450398284107359845856733577648751/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (212495021450398284107359845856733577648751/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (426431258726744292975534948747948335482899/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (426431258726744292975534948747948335482899/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (851421301627540861190254640461415490780401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (851421301627540861190254640461415490780401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0322.rows ScalarLogs0322.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2583 BracketBatch0161.bracket2584 (851421301627540861190254640461415490780401/20000000000000000000000000000000000000000) (4805947795642220141747493883867000204597/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2583 BracketBatch0161.bracket2584
  (851421301627540861190254640461415490780401/20000000000000000000000000000000000000000) (4805947795642220141747493883867000204597/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2583
