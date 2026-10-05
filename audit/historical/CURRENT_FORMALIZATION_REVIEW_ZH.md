# 最新稿 Lean 陈述与证明对应性审计

唯一论文基准为 `beckner_onofri_full_manuscript_20260921T180354Z/sharp_beckner_onofri_flat_torus.pdf`（2026-09-21 版）。PDF SHA-256：`a0ce0e642370a4bd70da36c64d65fa9df02855ba2052fa50793261363a62e7b6`；相邻 TeX SHA-256：`cbe4ef788e1491fe4b0f62d869b6d40240aeaf59ff005bea1c680bcfa124ea3d`。

范围是所有维数、51条带标签命题的主要结论及证明所需引理，包含下文明确记录的技术替代。257个配置目标的整体构建、精确公理审计和禁用证明代码扫描已通过。**完整257目标 Comparator 于9月27日单次整组通过（退出码0，默认 Lean 内核接受）。9月30日复核确认当前证明和配置与该快照逐字相同，并重新构建及查询公理。** 9月30日重复启动的整组运行已主动停止，不计作通过。实时状态以 `verification/active_checkpoint.json` 为准；历史251及以前的审计保存在 `verification/full_manuscript_257/source_review_history_through_251.md`。

2026年9月30日外部引用与语义复核详见 `reference_audit_20260930/REPORT_ZH.md`。该复核逐项登记51处引用和31个被引来源，补齐两个空目标列表及四处不完整映射，并清理当前覆盖清单中过时的待验证文字。原周期化级数的所有导数局部一致收敛未单独作为注册目标：原密度的光滑性由已证明的连续性和Fourier指数衰减独立得到。因此本记录不声称全文每一句或引用文献的一般定理均已形式化。

TeX 的定理/引理/命题/推论环境已独立重新枚举：51条唯一标签与覆盖清单一一对应，无漏项或失效标签。清单证据为 `verification/source_assertion_inventory_257.json`。

## Challenge 陈述

目标使用实际 Haar 积分、Fourier 系数、Green 核、原始临界 Sobolev 空间、有限熵概率密度和扩展实数变分上确界。包含：低维尖锐不等式与等号分类；十一维显式竞争密度、严格相变区间、共存、实际 Hessian 和曲线折角；高维端点刚性、全部局部分支、全局全模分类和临界渐近。完整逐条映射见 `FULL_MANUSCRIPT_COVERAGE_20260925.json`，目标数不作为覆盖百分比。

此前最后缺口 `lem:fractional` 已由目标257闭合。它只假设任意 U 在闭余弦立方体上光滑，对所有非零多重指标、所有正实数 s，给出实际混合 Friedrichs 算子分数幂的定义域及交换公式。零指标坐标保留完整周期空间和正弦模态；Lebesgue 测度未被归一化。实际空间形式闭包、完整正交基、空间/谱图双向等价、自伴图等价和精确加权 l2 分数幂定义域均已证明。没有附加衰减、域归属或极值性前提。详见 `FRACTIONAL_FINAL_CORRESPONDENCE_20260927.md`。

原始定义另经复查：概率密度、有限熵、Sobolev 域不含待证估计；十一维阈值来自实际压力零点，Hessian 是真实二阶导数。详见 `RAW_DEFINITION_RECHECK_20260927.md`。

## Solution 与原文路线

低维采用标量证书、超几何混合与端点闭合；十一维采用 Student 竞争密度、Fourier/熵证书、严格次临界紧性与隐函数定理排除零极限；高维采用 circle–spin 熵估计、标量尾界和 Lyapunov–Schmidt 分支分析。分数 Jacobi 交换遵循共轭、截断、分部积分、特征函数、快速衰减级数与闭图极限的原文路线。

以下技术变体已明确记录，不声称逐行复现：

- 极值对应用 Gibbs 构造、Fourier Euler 唯一性和 Fourier/Wiener 正则化；原文的两条完整 gap 恒等式也已独立证明。
- 十一维 IFT 先在连续函数 Banach 空间实施，再闭合原始 H11 邻域；强紧性用 Fourier/Wiener 估计替代 Vitali 与 Sobolev bootstrap。连续性不是额外假设。
- 热流熵收敛用 L1 收缩、几乎处处子列和 Fatou 实现下半连续性。
- Student Fourier 公式通过 Gamma–Gaussian 积分和递推；有理数证书重新核验，不声称与附件证书字节或截断方式一致。
- 压力导数用解析振幅和逆参数商估计；没有对任意 big-O 形式直接求导。
- 圆周重排先证明极化的 L1 收缩并传至极限，再识别 layer-cake 规范代表。
- 论文引用的外部 Adams 定理，仅所需平坦环面特例由热 Green 比较、边缘熵和原始对偶性独立证明；未形式化一般紧流形版本。
- Friedrichs 截断用支配收敛证明形式范数收敛，没有单独导出原文显示的定量 O(δ^(2m−1)) 速率。绝对收敛余弦级数用整数 Fourier 索引保留重数，最后精确识别原轮廓。

这些差异不改变目标命题的假设和结论。各命题的进一步说明保存在逐条覆盖清单及专门 correspondence 文档中。

## 核验边界

`Challenge.lean` 保留可信占位 `sorry`；Solution 及辅助 Lean 源码无 `sorry`、`admit`、新增公理或 `native_decide`。257条目标的传递公理依赖均仅为 `propext`、`Quot.sound`、`Classical.choice`。构建、公理日志和冻结源码在 `verification/full_manuscript_257/` 及同名前缀日志中。

Comparator 使用官方 macOS development adapter：启用实际陈述/定义匹配、公理检查和默认 Lean kernel 重放；没有 Linux landrun 进程隔离。新增255–257增量已通过（退出码0，默认 Lean 内核接受）；完整257运行已通过（退出码0，默认 Lean 内核接受）。较早完整208或其他增量的通过不能替代当前完整配置的通过。

最终核验后的源码/配置与冻结257快照逐字一致，PDF/TeX 哈希仍与本审计基准一致。结果时间（UTC）：2026-09-27T09:04:06.223654+00:00。
