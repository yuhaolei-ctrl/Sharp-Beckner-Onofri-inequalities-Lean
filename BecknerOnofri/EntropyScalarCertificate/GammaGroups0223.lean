module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0278
public import BecknerOnofri.EntropyScalarCertificate.Bessel0279
public import BecknerOnofri.EntropyScalarCertificate.Bessel0280
public import BecknerOnofri.EntropyScalarCertificate.Bessel0628
public import BecknerOnofri.EntropyScalarCertificate.Brackets0111
public import BecknerOnofri.EntropyScalarCertificate.Brackets0112
public import BecknerOnofri.EntropyScalarCertificate.Logs0223
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1784
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (20971725260433494134073091719503605612053/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20971725260433494134073091719503605612053/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (20986233482979090992339708087520812264137/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20986233482979090992339708087520812264137/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (4195795874341258512641279980702441787619/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4195795874341258512641279980702441787619/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1784 BracketBatch0111.bracket1785 (4195795874341258512641279980702441787619/2000000000000000000000000000000000000000) (850512519365792421331960008261640438827/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1784 BracketBatch0111.bracket1785
  (4195795874341258512641279980702441787619/2000000000000000000000000000000000000000) (850512519365792421331960008261640438827/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1784
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1785
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (10493116741489545496169854043760406132067/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10493116741489545496169854043760406132067/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (4200152931984877361664438252434296963557/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4200152931984877361664438252434296963557/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (41986998142903477800661899349692297081919/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41986998142903477800661899349692297081919/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1785 BracketBatch0111.bracket1786 (41986998142903477800661899349692297081919/20000000000000000000000000000000000000000) (851235316190983527095046905415072105797/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1785 BracketBatch0111.bracket1786
  (41986998142903477800661899349692297081919/20000000000000000000000000000000000000000) (851235316190983527095046905415072105797/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1785
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1786
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (10500382329962193404161095631085742408891/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10500382329962193404161095631085742408891/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (10507659423265651170346389040142268562803/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10507659423265651170346389040142268562803/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (10504020876613922287253742335614005485847/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10504020876613922287253742335614005485847/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1786 BracketBatch0111.bracket1787 (10504020876613922287253742335614005485847/5000000000000000000000000000000000000000) (106494871340922243612843044685047118971/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1786 BracketBatch0111.bracket1787
  (10504020876613922287253742335614005485847/5000000000000000000000000000000000000000) (106494871340922243612843044685047118971/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1786
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1787
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (21015318846531302340692778080284537125603/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21015318846531302340692778080284537125603/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (21029896098230814329376159699253559282747/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21029896098230814329376159699253559282747/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (840904298895242333401378755590761928167/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (840904298895242333401378755590761928167/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1787 BracketBatch0111.bracket1788 (840904298895242333401378755590761928167/400000000000000000000000000000000000000) (426341742199747252844540387373179149847/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1787 BracketBatch0111.bracket1788
  (840904298895242333401378755590761928167/400000000000000000000000000000000000000) (426341742199747252844540387373179149847/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1787
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1788
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (2628737012278851791172019962406694910343/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2628737012278851791172019962406694910343/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (5261124117655897072534892901594902745069/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5261124117655897072534892901594902745069/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (2103719628442720130975786565281658513151/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2103719628442720130975786565281658513151/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1788 BracketBatch0111.bracket1789 (2103719628442720130975786565281658513151/1000000000000000000000000000000000000000) (853408858634677852821014491880840682489/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1788 BracketBatch0111.bracket1789
  (2103719628442720130975786565281658513151/1000000000000000000000000000000000000000) (853408858634677852821014491880840682489/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1788
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1789
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (21044496470623588290139571606379610980273/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21044496470623588290139571606379610980273/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (2632390002435076776226840161562848351279/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2632390002435076776226840161562848351279/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (8420723298020840499990858579776479558101/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8420723298020840499990858579776479558101/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1789 BracketBatch0111.bracket1790 (8420723298020840499990858579776479558101/4000000000000000000000000000000000000000) (427067547431552675273674872251569760643/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1789 BracketBatch0111.bracket1790
  (8420723298020840499990858579776479558101/4000000000000000000000000000000000000000) (427067547431552675273674872251569760643/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1789
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1790
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (21059120019480614209814721292502786810229/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21059120019480614209814721292502786810229/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (21073766800743845158321794947349438477281/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21073766800743845158321794947349438477281/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (4213288682022445936813651623985222528751/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4213288682022445936813651623985222528751/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1790 BracketBatch0111.bracket1791 (4213288682022445936813651623985222528751/2000000000000000000000000000000000000000) (106857774314724245057420223493373751603/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1790 BracketBatch0111.bracket1791
  (4213288682022445936813651623985222528751/2000000000000000000000000000000000000000) (106857774314724245057420223493373751603/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1790
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1791
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (10536883400371922579160897473674719238639/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10536883400371922579160897473674719238639/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (21088436870526838833770980396905837825781/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21088436870526838833770980396905837825781/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (42162203671270683992092775344255276303059/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42162203671270683992092775344255276303059/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0223.rows ScalarLogs0223.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1791 BracketBatch0112.bracket1792 (42162203671270683992092775344255276303059/20000000000000000000000000000000000000000) (85559015903460717014973555884335259837/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1791 BracketBatch0112.bracket1792
  (42162203671270683992092775344255276303059/20000000000000000000000000000000000000000) (85559015903460717014973555884335259837/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1791
