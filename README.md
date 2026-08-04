# bang-ride-lean-verification

Shi, Sass, Wu, Kim, Ma, Shin, Findeisen, Braatz,
*Bang-Ride Optimal Control: Monotonicity, External Positivity, and Fast Battery Charging*
（arXiv:2508.09010v3）Theorem 5.1 证明核心的 **Lean 4 零 axiom 机器验证**。

## 验证内容

| 模块 | 内容 |
|---|---|
| `BangRide/Core.lean` | Theorem 5.1 数据结构与 Assumption 5.1 假设束（全显式，零 axiom） |
| `BangRide/Chebyshev.lean` | Chebyshev 求和不等式（含严格版与零和推论） |
| `BangRide/VariationOfConstants.lean` | 变分常数公式 (46) 前向/后向（FTC 全证） |
| `BangRide/OrderPreservation.lean` | **定理 A**：论文序保持引理的反例（n=3 显式实例，全假设验证）；**定理 B**：修正版序保持（+轨迹分量非负） |
| `BangRide/ExternalPositivity.lean` | **主定理** `externallyPositive`：ψ(t) > 0（内点） |

**发现**：论文附录 E 的序保持引理在 Assumption 5.1 原假设下为假（双负终端协态对反例）；
主定理需要附加符号条件（p ≥ 0、轨迹分量非负）。详见 `docs/VERIFICATION.md`。

## 复现

```bash
export ELAN_HOME="D:/AI/lean/elan"
export PATH="D:/AI/lean/elan/bin:$PATH"
lake build          # 全绿，零 sorry，零自定义 axiom
```

## 文档

- `docs/formula-mapping.md` — 论文公式 ↔ Lean 定理对照表
- `docs/VERIFICATION.md` — 验证报告（范围、发现、PMP 边界）
- `docs/lean-work-notes.md` — Mathlib v4.32.2 实证与坑
- `docs/superpowers/` — 设计文档（spec）与实现计划（plan）
