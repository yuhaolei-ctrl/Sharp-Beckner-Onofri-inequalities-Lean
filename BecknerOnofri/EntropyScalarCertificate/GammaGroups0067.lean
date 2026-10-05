module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0083
public import BecknerOnofri.EntropyScalarCertificate.Bessel0084
public import BecknerOnofri.EntropyScalarCertificate.Bessel0085
public import BecknerOnofri.EntropyScalarCertificate.Bessel0530
public import BecknerOnofri.EntropyScalarCertificate.Bessel0531
public import BecknerOnofri.EntropyScalarCertificate.Brackets0033
public import BecknerOnofri.EntropyScalarCertificate.Brackets0034
public import BecknerOnofri.EntropyScalarCertificate.Logs0067
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0536
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1659436538826291654382479774504008817533/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1659436538826291654382479774504008817533/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1661520140496831158864483258737937361773/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1661520140496831158864483258737937361773/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1660478339661561406623481516620973089653/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1660478339661561406623481516620973089653/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0536 BracketBatch0033.bracket0537 (1660478339661561406623481516620973089653/10000000000000000000000000000000000000000) (113026364882309246093196881651302333/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0536 BracketBatch0033.bracket0537
  (1660478339661561406623481516620973089653/10000000000000000000000000000000000000000) (113026364882309246093196881651302333/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0536
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0537
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (166152014049683115886448325873793736177/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (166152014049683115886448325873793736177/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1663603954348132167511193598593835919321/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1663603954348132167511193598593835919321/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (3325124094844963326375676857331773281091/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3325124094844963326375676857331773281091/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0537 BracketBatch0033.bracket0538 (3325124094844963326375676857331773281091/20000000000000000000000000000000000000000) (56791592846791704171671863478402201/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0537 BracketBatch0033.bracket0538
  (3325124094844963326375676857331773281091/20000000000000000000000000000000000000000) (56791592846791704171671863478402201/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0537
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0538
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (831801977174066083755596799296917959659/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (831801977174066083755596799296917959659/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1665687980679126739993559481477840341683/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1665687980679126739993559481477840341683/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0530.rows BesselBatch0530.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (3329291935027258907504753080071676261001/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3329291935027258907504753080071676261001/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0538 BracketBatch0033.bracket0539 (3329291935027258907504753080071676261001/20000000000000000000000000000000000000000) (71338794516638605166957263066413721/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0538 BracketBatch0033.bracket0539
  (3329291935027258907504753080071676261001/20000000000000000000000000000000000000000) (71338794516638605166957263066413721/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0538
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0539
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (20821099758489084249919493518473004271/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20821099758489084249919493518473004271/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (41694305494722604731739300142815960613/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41694305494722604731739300142815960613/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (16667301002340154646315657435952393831/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16667301002340154646315657435952393831/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0539 BracketBatch0033.bracket0540 (16667301002340154646315657435952393831/100000000000000000000000000000000000000) (573515133318253771428907583358172753/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0539 BracketBatch0033.bracket0540
  (16667301002340154646315657435952393831/100000000000000000000000000000000000000) (573515133318253771428907583358172753/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0539
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0540
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1667772219788904189269572005712638424517/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1667772219788904189269572005712638424517/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1669856671976711343160408644061721283473/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1669856671976711343160408644061721283473/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (333762889176561553242998064977435970799/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (333762889176561553242998064977435970799/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0540 BracketBatch0033.bracket0541 (333762889176561553242998064977435970799/2000000000000000000000000000000000000000) (576330285969605908543402040666350281/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0540 BracketBatch0033.bracket0541
  (333762889176561553242998064977435970799/2000000000000000000000000000000000000000) (576330285969605908543402040666350281/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0540
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0541
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (166985667197671134316040864406172128347/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (166985667197671134316040864406172128347/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (835970668770976403108088445481226407499/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (835970668770976403108088445481226407499/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (835449502379666037344146383756043524617/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (835449502379666037344146383756043524617/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0541 BracketBatch0033.bracket0542 (835449502379666037344146383756043524617/5000000000000000000000000000000000000000) (14478896001713873221071920200674187/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0541 BracketBatch0033.bracket0542
  (835449502379666037344146383756043524617/5000000000000000000000000000000000000000) (14478896001713873221071920200674187/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0541
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0542
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (334388267508390561243235378192490562999/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (334388267508390561243235378192490562999/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (167402621678419122187183641251845282903/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (167402621678419122187183641251845282903/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (133838702173045761123520532139236225761/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (133838702173045761123520532139236225761/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0542 BracketBatch0033.bracket0543 (133838702173045761123520532139236225761/800000000000000000000000000000000000000) (581991821631639794982463735132375053/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0542 BracketBatch0033.bracket0543
  (133838702173045761123520532139236225761/800000000000000000000000000000000000000) (581991821631639794982463735132375053/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0542
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0543
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1674026216784191221871836412518452829027/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1674026216784191221871836412518452829027/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1676111310003147534893879515159557910537/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1676111310003147534893879515159557910537/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (837534381696834689191428981919502684891/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (837534381696834689191428981919502684891/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0067.rows ScalarLogs0067.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0033.bracket0543 BracketBatch0034.bracket0544 (837534381696834689191428981919502684891/5000000000000000000000000000000000000000) (584838256710562464702867286203002483/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0033.bracket0543 BracketBatch0034.bracket0544
  (837534381696834689191428981919502684891/5000000000000000000000000000000000000000) (584838256710562464702867286203002483/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0543
