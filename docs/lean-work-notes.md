# 执行期工作记录：Mathlib v4.32.2 实证与项目内坑

## 环境（2026-08-04 会话实证）

- 共享 mathlib 布局：`D:\AI\lean\mathlib`（.lake 有预编译 olean），项目 lakefile 用
  `[[require]] name = "mathlib" path = "../../mathlib"`；**不要**用 git rev（会全量编译）。
- lake 5.0 的 `lean_lib` 需要**根模块文件**：lib `BangRide` ⟹ 项目根 `BangRide.lean`
  （import 各子模块）；缺省会报 "some modules have bad imports"。
- 命令：`export ELAN_HOME="D:/AI/lean/elan"` + `export PATH="D:/AI/lean/elan/bin:$PATH"`
  后 `lake build`。
- lakefile 变更后需 `lake update mathlib` 同步 manifest。

## 本项目的 Mathlib 坑（新实证）

### 语法/标识符
- 积分语法：`∫ τ in a..b, f τ`（**无尾部 `dτ`**，否则解析成函数应用报错）。
- 标识符禁止 `*`/`λ`（`hλ` 直接报 "unexpected token"）。
- 向量字面量 `![a, b]` 默认推断为 **ℤ**：需 `(![5, 0, -3] : Fin 3 → ℝ)` 注解。

### 导数（HasDerivAt）
- `HasDerivAt.comp` 签名：`comp (x : 𝕜) (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x)`——
  **第一个显式参数是 x**：`.comp s hg`。
- `hasDerivAt_const (x) (c)`：**x 在前**。
- `hasDerivAt_exp` 给出 `NormedSpace.exp` ≠ `Real.exp`——用 `Real.hasDerivAt_exp`。
- `HasDerivAt.deriv : deriv f x = f'`（不是 `.deriv_eq`，后者不存在）。
- fun_prop 不支持 HasDerivAt 目标（报 "not a fun_prop goal"）。
- **convert 的目标顺序不稳定**（值/实例/函数等式次序随构建漂移）——用
  `all_goals first | rfl | ring | (funext x; ...)` 鲁棒模式；实例等式目标可用 `rfl` 关闭
  （结构实例在证明无关性下定义相等）。

### 求和（Finset）
- 对未使用绑定变量的求和必须显式类型：`∑ j : Fin n, a i * b i`（否则 Fintype 元变量）。
- `Finset.sum_const` 引入 `Fintype.card`：中间形式用 `Fintype.card (Fin n)`，
  末尾 `rw [Fintype.card_fin]`；`nsmul_eq_mul` 桥 ℕ→ℝ。
- `Finset.mul_sum`（(Σf)·a = Σ f·a）与 `Finset.sum_mul`（a·Σf = Σ a·f）方向相反，
  提取常数用 `rw [← Finset.mul_sum]` / `rw [← Finset.sum_mul]`。
- `Finset.sum_pos'`（每项 ≥ 0 且一项 > 0）而非 `sum_pos`（需全正）。
- `HasDerivAt.sum (u := Finset.univ)`：函数形式是"函数之和" `∑ i, fun s => ...`，
  与"和之函数" `fun s => ∑ i, ...` 非定义相等——convert + `simp [Finset.sum_apply]` 桥接。

### 分析
- `intervalIntegral.integral_eq_sub_of_hasDerivAt (hderiv : ∀ x ∈ uIcc a b, ...) (hint : IntervalIntegrable ...)`；
  `Continuous.intervalIntegrable hf a b`（a, b 显式）。
- `intervalIntegral.integral_mono_on (hab) (hf) (hg) (h : ∀ x ∈ Icc a b, f x ≤ g x)`。
- `Real.exp_le_exp_iff` 不存在——用 `(Real.exp_strictMono.le_iff_le).2`。
- `Real.one_le_exp_iff` / `Real.exp_le_one_iff` 存在（区间 ψ ≥ 0 证明用）。
- `ring_nf` 会重写 exp 参数内部（不同语法形式导致 atom 不一致）——用 `ring`（不碰内部）。
- 局部极小 ⟹ 导数 0：`IsLocalMin.deriv_eq_zero`（LocalExtr/Basic.lean）；
  `IsLocalMin` 用 `Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (...)` 构造。
- `mul_lt_mul_of_pos_left (hbc) (ha : 0 < a)` 参数顺序；(非负乘子在右时) 用
  `mul_le_mul_of_nonneg_right`。

### 其它
- `pow_le_pow_left₀ (ha : 0 ≤ a) (h : a ≤ b) (n : ℕ)`——三参数。
- `Real.exp_nat_mul 1 3 : exp (↑3·1) = exp 1 ^ 3`，反向 `rw [← Real.exp_nat_mul 1 3]` + norm_num。
- `theorem` 类型未提及的 `variable` 不会被自动绑定——体内引用报 "Unknown identifier"；
  **把 A 显式写进签名** `(A : D.Assumptions) (k : Fin n)`（example 无此问题）。
- linter：`linter.unreachableTactic`/`linter.unusedTactic` 可文件级 set_option；
  `linter.flexible` 是 **scoped** 选项，需 `set_option linter.flexible false in` 挂在具体声明前。

## 数学发现（Lean 驱动）

- **ODE (45) 的解是指数正的**：λₖ(t) = e^{aₖ(tf-t)}λ₀ₖ（λ̇ₖ = -aₖλₖ）。早期反例设计
  用了 e^{-aₖ(tf-t)}（符号错），被 Lean 拒绝；修正后反例需**双负 λ₀ 对**（见 VERIFICATION.md 发现 1）。
