module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0107
public import BecknerOnofri.EntropyScalarCertificate.Bessel0108
public import BecknerOnofri.EntropyScalarCertificate.Bessel0542
public import BecknerOnofri.EntropyScalarCertificate.Bessel0543
public import BecknerOnofri.EntropyScalarCertificate.Brackets0043
public import BecknerOnofri.EntropyScalarCertificate.Logs0086
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0688
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1978754037696778752113942411102689994697/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1978754037696778752113942411102689994697/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1980873417402791693456684498056364082213/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1980873417402791693456684498056364082213/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (395962745509957044557062690915905407691/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (395962745509957044557062690915905407691/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0688 BracketBatch0043.bracket0689 (395962745509957044557062690915905407691/2000000000000000000000000000000000000000) (561208435177851202820668302419923001/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0688 BracketBatch0043.bracket0689
  (395962745509957044557062690915905407691/2000000000000000000000000000000000000000) (561208435177851202820668302419923001/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0688
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0689
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (198087341740279169345668449805636408221/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (198087341740279169345668449805636408221/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (991496528344271349970652237860402048477/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (991496528344271349970652237860402048477/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (990966618522833598349497243444292044791/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (990966618522833598349497243444292044791/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0689 BracketBatch0043.bracket0690 (990966618522833598349497243444292044791/5000000000000000000000000000000000000000) (5635439891092346797013880507033537/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0689 BracketBatch0043.bracket0690
  (990966618522833598349497243444292044791/5000000000000000000000000000000000000000) (5635439891092346797013880507033537/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0689
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0690
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1982993056688542699941304475720804096951/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1982993056688542699941304475720804096951/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (15508694967812870251901782864192274517/78125000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15508694967812870251901782864192274517/78125000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (3968106012568590092184732682337415235127/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3968106012568590092184732682337415235127/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0690 BracketBatch0043.bracket0691 (3968106012568590092184732682337415235127/20000000000000000000000000000000000000000) (565886879780132240197426618395268829/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0690 BracketBatch0043.bracket0691
  (3968106012568590092184732682337415235127/20000000000000000000000000000000000000000) (565886879780132240197426618395268829/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0690
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0691
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1985112955880047392243428206616611138173/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1985112955880047392243428206616611138173/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (198723311530352208237896283136350799027/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (198723311530352208237896283136350799027/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (3972346071183569474622391037980119128443/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3972346071183569474622391037980119128443/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0691 BracketBatch0043.bracket0692 (3972346071183569474622391037980119128443/20000000000000000000000000000000000000000) (142059280725062746278091292503583759/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0691 BracketBatch0043.bracket0692
  (3972346071183569474622391037980119128443/20000000000000000000000000000000000000000) (142059280725062746278091292503583759/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0691
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0692
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1987233115303522082378962831363507990267/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1987233115303522082378962831363507990267/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (994676767642692043284327796336313449711/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (994676767642692043284327796336313449711/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (3976586650588906168947618424036134889689/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3976586650588906168947618424036134889689/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0692 BracketBatch0043.bracket0693 (3976586650588906168947618424036134889689/20000000000000000000000000000000000000000) (1141189468396057060898879888735286757/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0692 BracketBatch0043.bracket0693
  (3976586650588906168947618424036134889689/20000000000000000000000000000000000000000) (1141189468396057060898879888735286757/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0692
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0693
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1989353535285384086568655592672626899419/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1989353535285384086568655592672626899419/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1991474216152252038493170250685576200913/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1991474216152252038493170250685576200913/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (995206937859409031265456460839550775083/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (995206937859409031265456460839550775083/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0693 BracketBatch0043.bracket0694 (995206937859409031265456460839550775083/5000000000000000000000000000000000000000) (1145919458841283244597546697089978069/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0693 BracketBatch0043.bracket0694
  (995206937859409031265456460839550775083/5000000000000000000000000000000000000000) (1145919458841283244597546697089978069/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0693
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0694
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (199147421615225203849317025068557620091/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (199147421615225203849317025068557620091/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (996797579115473101469721170791034486553/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (996797579115473101469721170791034486553/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (15566677243684368130596142938545488961/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15566677243684368130596142938545488961/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0694 BracketBatch0043.bracket0695 (15566677243684368130596142938545488961/78125000000000000000000000000000000000) (1150664248668029528864356649049049219/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0694 BracketBatch0043.bracket0695
  (15566677243684368130596142938545488961/78125000000000000000000000000000000000) (1150664248668029528864356649049049219/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0694
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0695
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1993595158230946202939442341582068973103/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1993595158230946202939442341582068973103/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0108.rows BesselBatch0108.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1995716361848488789839075964267978484641/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1995716361848488789839075964267978484641/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (249331970004964687048657394115627966109/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (249331970004964687048657394115627966109/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0086.rows ScalarLogs0086.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0043.bracket0695 BracketBatch0043.bracket0696 (249331970004964687048657394115627966109/1250000000000000000000000000000000000000) (1155423869445657717239416881659274337/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0043.bracket0695 BracketBatch0043.bracket0696
  (249331970004964687048657394115627966109/1250000000000000000000000000000000000000) (1155423869445657717239416881659274337/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0695
