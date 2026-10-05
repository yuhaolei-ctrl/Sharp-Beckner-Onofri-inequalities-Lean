module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0040
public import BecknerOnofri.EntropyScalarCertificate.Bessel0041
public import BecknerOnofri.EntropyScalarCertificate.Bessel0508
public import BecknerOnofri.EntropyScalarCertificate.Bessel0509
public import BecknerOnofri.EntropyScalarCertificate.Brackets0016
public import BecknerOnofri.EntropyScalarCertificate.Logs0032
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0256
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1083307267218620654467380418430761288221/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1083307267218620654467380418430761288221/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (108534270126163719213627344120932807701/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (108534270126163719213627344120932807701/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (2168649968480257846603653859640089365231/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2168649968480257846603653859640089365231/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0256 BracketBatch0016.bracket0257 (2168649968480257846603653859640089365231/20000000000000000000000000000000000000000) (839148964213002861884300660822641/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0256 BracketBatch0016.bracket0257
  (2168649968480257846603653859640089365231/20000000000000000000000000000000000000000) (839148964213002861884300660822641/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0256
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0257
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1085342701261637192136273441209328077007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1085342701261637192136273441209328077007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (543689134535645689921556620093786718189/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (543689134535645689921556620093786718189/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (434544194066585714395877336279380302677/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (434544194066585714395877336279380302677/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0257 BracketBatch0016.bracket0258 (434544194066585714395877336279380302677/4000000000000000000000000000000000000000) (105679842064964070384709516368603939/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0257 BracketBatch0016.bracket0258
  (434544194066585714395877336279380302677/4000000000000000000000000000000000000000) (105679842064964070384709516368603939/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0257
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0258
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (8699026152570331038744905921500587491/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8699026152570331038744905921500587491/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (108941397091184199634607155077541960489/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (108941397091184199634607155077541960489/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (435358447996626675237836958192598608253/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (435358447996626675237836958192598608253/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0258 BracketBatch0016.bracket0259 (435358447996626675237836958192598608253/4000000000000000000000000000000000000000) (10647046872806784883097213002763201/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0258 BracketBatch0016.bracket0259
  (435358447996626675237836958192598608253/4000000000000000000000000000000000000000) (10647046872806784883097213002763201/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0258
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0259
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1089413970911841996346071550775419604887/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1089413970911841996346071550775419604887/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (545724903523820656813508838692778678991/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (545724903523820656813508838692778678991/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (2180863777959483309973089228160976962869/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2180863777959483309973089228160976962869/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0259 BracketBatch0016.bracket0260 (2180863777959483309973089228160976962869/20000000000000000000000000000000000000000) (21453103411178373501358034386383729/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0259 BracketBatch0016.bracket0260
  (2180863777959483309973089228160976962869/20000000000000000000000000000000000000000) (21453103411178373501358034386383729/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0259
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0260
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1091449807047641313627017677385557357979/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1091449807047641313627017677385557357979/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (546742888871567648507969692197348217993/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (546742888871567648507969692197348217993/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (436987116958155322128591412356050758793/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (436987116958155322128591412356050758793/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0260 BracketBatch0016.bracket0261 (436987116958155322128591412356050758793/4000000000000000000000000000000000000000) (27016250905118939327309503089319339/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0260 BracketBatch0016.bracket0261
  (436987116958155322128591412356050758793/4000000000000000000000000000000000000000) (27016250905118939327309503089319339/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0260
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0261
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1093485777743135297015939384394696435983/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1093485777743135297015939384394696435983/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (273880470815715951368632965202525074099/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (273880470815715951368632965202525074099/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (2189007661005999102490471245204796732379/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2189007661005999102490471245204796732379/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0261 BracketBatch0016.bracket0262 (2189007661005999102490471245204796732379/20000000000000000000000000000000000000000) (108868945025951883176541141479388351/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0261 BracketBatch0016.bracket0262
  (2189007661005999102490471245204796732379/20000000000000000000000000000000000000000) (108868945025951883176541141479388351/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0261
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0262
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1095521883262863805474531860810100296393/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1095521883262863805474531860810100296393/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1097558123871460792039331363173354410797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1097558123871460792039331363173354410797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (219308000713432459751386322398345470719/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (219308000713432459751386322398345470719/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0262 BracketBatch0016.bracket0263 (219308000713432459751386322398345470719/2000000000000000000000000000000000000000) (109677357908553638928677512296705367/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0262 BracketBatch0016.bracket0263
  (219308000713432459751386322398345470719/2000000000000000000000000000000000000000) (109677357908553638928677512296705367/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0262
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0263
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (548779061935730396019665681586677205397/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (548779061935730396019665681586677205397/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1099594499833654504424770639792743689821/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1099594499833654504424770639792743689821/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (439430524741023059292820400593219620123/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (439430524741023059292820400593219620123/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0032.rows ScalarLogs0032.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0263 BracketBatch0016.bracket0264 (439430524741023059292820400593219620123/4000000000000000000000000000000000000000) (55245129468311879691770307559407461/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0263 BracketBatch0016.bracket0264
  (439430524741023059292820400593219620123/4000000000000000000000000000000000000000) (55245129468311879691770307559407461/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0263
