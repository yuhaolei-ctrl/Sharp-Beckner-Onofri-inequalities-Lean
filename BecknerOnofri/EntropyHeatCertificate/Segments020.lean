module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0160
public import BecknerOnofri.EntropyHeatCertificate.Panels0161
public import BecknerOnofri.EntropyHeatCertificate.Panels0162
public import BecknerOnofri.EntropyHeatCertificate.Panels0163
public import BecknerOnofri.EntropyHeatCertificate.Panels0164
public import BecknerOnofri.EntropyHeatCertificate.Panels0165
public import BecknerOnofri.EntropyHeatCertificate.Panels0166
public import BecknerOnofri.EntropyHeatCertificate.Panels0167

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments020
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨0, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨0, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨0, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨0, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨0, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨0, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨0, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=13496864595545535037308523964082322869321424347735873736789640713900232492300805555757081736169276237207967701867628308931718482032858039131614632049938076813693680727207457544556234508542731282039385662839456038/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨1, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨1, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨1, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨1, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨1, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨1, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨1, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=17009430596053370403054006417153590704991092100964728448593537738032659455791520761281978079307032612317729292438231722157686266200644516781169889153892050969923170666264143380414452767169004613924636188281070182/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨2, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨2, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨2, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨2, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨2, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨2, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨2, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=21579107706234666114773544706151962659059838073621356997756422765122291435118413436530781181899910676001596480728991591962197063492107713376452937767788664752941082465604067053241993696374436033081636282848119334/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨3, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨3, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨3, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨3, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨3, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨3, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨3, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=24370191703420550475585035069677905237237027755746959296844346572144139782435599969112649130611955301308441913412998057731378436268075702240819603030864509843814559471717907697300895589284634018928529888536250302/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨4, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨4, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨4, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨4, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨4, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨4, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨4, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=26957591352495373789748346548467047090625352316156974353491268900545561822605844631194007838838294980600016828379300405268324025813431077252484051298742348489937004633397147012302786555442627750723480024410729502/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨5, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨5, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨5, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨5, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨5, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨5, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨5, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=28985680237708147426363915473213963767944836722458969284100179487669401615105121481220997097950910312234265135946200988421242334001319541970996340620792305009064334497606728222323149504557605944981432320915491750/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨6, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨6, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨6, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨6, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨6, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨6, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨6, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=30700023479281868451522908013455316202690480908857437262123644991642758910649416127853796413875274962076342098282087664653157234315577952800081140618477951747924907225914084149505097872202606047198791528103945402/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨7, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨7, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨7, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨7, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨7, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨7, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨7, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=31948862508272017745807353809364791044319284875828373672720706332738721249627120785068797863084956065012741068733577919225145555369371410578482356497161964960229097904258810921639786690877921664308018871806554298/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨8, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨8, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨8, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨8, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨8, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨8, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨8, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=32821645575740607157369543740625107883970183515501910080537357548575024458312643795033283434108905227902787111883873406271376716559750902665812230420260722010262592408157794488308258304389002903341372039348654130/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨9, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨9, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨9, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨9, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨9, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨9, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨9, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=33508422139540694943877260805353363066585589716070625717078792218949647711146691670928817142900716965867990975218757500646603780068732526582310639152727187863702924134652485509298685384470560443711248295590700582/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨10, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨10, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨10, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨10, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨10, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨10, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨10, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=34023619547919956895235973930405400619825287372381777763296989816818907517469068276198629825581762892309666485962473409808896511788981842614528285456594864953954144581979779829642929378083272113053102308435457714/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨11, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨11, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨11, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨11, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨11, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨11, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨11, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=34410650688355248951923620576001688425805790177697559072737752155233099842873972338919217333886705115995276843732398122944932029551509400379321195197877480532517026314718840636435486449009196328275308302017803294/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0160 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0160.block Panels0160.accepted Panels0160.integerPanels Panels0160.aligned
    Panels0160.weightRows Panels0160.weights_checked ⟨12, by decide⟩
def b0161 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0161.block Panels0161.accepted Panels0161.integerPanels Panels0161.aligned
    Panels0161.weightRows Panels0161.weights_checked ⟨12, by decide⟩
def b0162 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0162.block Panels0162.accepted Panels0162.integerPanels Panels0162.aligned
    Panels0162.weightRows Panels0162.weights_checked ⟨12, by decide⟩
def b0163 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0163.block Panels0163.accepted Panels0163.integerPanels Panels0163.aligned
    Panels0163.weightRows Panels0163.weights_checked ⟨12, by decide⟩
def b0164 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0164.block Panels0164.accepted Panels0164.integerPanels Panels0164.aligned
    Panels0164.weightRows Panels0164.weights_checked ⟨12, by decide⟩
def b0165 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0165.block Panels0165.accepted Panels0165.integerPanels Panels0165.aligned
    Panels0165.weightRows Panels0165.weights_checked ⟨12, by decide⟩
def b0166 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0166.block Panels0166.accepted Panels0166.integerPanels Panels0166.aligned
    Panels0166.weightRows Panels0166.weights_checked ⟨12, by decide⟩
def b0167 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0167.block Panels0167.accepted Panels0167.integerPanels Panels0167.aligned
    Panels0167.weightRows Panels0167.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0160, b0161, b0162, b0163, b0164, b0165, b0166, b0167]
theorem chain_checked : blockChainCheck (1475846938003328726491487854557/10^30) (1894967158257301031874623425110/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=34432230896685960609331848031426559357728211057552478826529760733727813410945007556607233754170473888650656550539320972369138409839662534996004489213958094775033495229883847933929250911171560491782824816664302526/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments020
