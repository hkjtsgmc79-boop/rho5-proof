/-
D17 — 全阶段轨迹峰值 `tracePeak`
================================

冻结接口（D18 直接消费）：`Rho5.GrowthModel.tracePeak values = values.foldr max 0`。
它是**真实各阶段最大条目序列的峰值**（最大值），不是最后一项；空列表的峰值是 `0`
（`foldr` 的单位元，不是 `max` 的中性元缺失造成的附加约定）。

本文件只建立该定义本身服务的最小事实集合（卡目标 1），不做通用 list/`foldr`
框架：

* `tracePeak` 是 `foldr max 0` 本身（`rfl` 展开，`tracePeak_cons`/`tracePeak_nil`）；
* 非负（`tracePeak_nonneg`）、每个成员 ≤ 峰值（`le_tracePeak`）；
* 全体成员 ≤ `B` 且 `0 ≤ B` 时峰值 ≤ `B`（`tracePeak_le`）；
* 非负标量下 `tracePeak (values.map (fun v => a * v)) = a * tracePeak values`
  （`tracePeak_map_mul`，需要 `0 ≤ a`；用于下一步对 `|c|` 实例化）。

三个辅助引理按 `List` 的递归等式模式（term mode）书写，不用 `induction … with`
的 case binder：在本工具链（Lean 4.30.0）里后者的引荐名不可靠，term mode 让每个
归纳变量与归纳假设都显式命名，避免依赖内部命名。

复用（只读冻结输入，哈希见 `INPUT_HASHES.json`）：`Rho5.Matrix5`、
`Rho5.matrixEntryMax`（`Rho5.Shared.Conventions`）与 D08 的入口模块
`Rho5.Shared.MatrixNormalization`（本身只读复用冻结 pilot 的 `Conventions`/`Pivot`）。
本文件不引入第二套范数、不重新定义任何冻结语义。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice
import Rho5.Shared.MatrixNormalization

namespace Rho5.GrowthModel

/-! ## 定义 -/

/-- **冻结定义（D17 卡）**：合法轨迹的**全阶段峰值**，即真实各阶段最大条目序列
`values` 的最大值。空轨迹（`0 × 0` 的终止阶段）的峰值是 `0`。

这是 D18 组装的固定公开名，语义固定为 `values.foldr max 0`；不改写成“最后一项”、
也不改写成 `List.maximum`（后者带上 `Option`，会给后继证书引入额外分支）。 -/
def tracePeak (values : List ℝ) : ℝ := values.foldr max 0

/-! ## 展开与辅助（仅服务本定义） -/

/-- 展开式：`max` 从右侧折叠，空列表返回 `0`。 -/
theorem tracePeak_eq_foldr (values : List ℝ) : tracePeak values = values.foldr max 0 := rfl

/-- 空列表的峰值是 `0`。 -/
@[simp] theorem tracePeak_nil : tracePeak ([] : List ℝ) = 0 := rfl

/-- 非空列表的峰值是首项与尾部峰值的最大值。 -/
@[simp] theorem tracePeak_cons (a : ℝ) (values : List ℝ) :
    tracePeak (a :: values) = max a (tracePeak values) := rfl

/-- 辅助（仅供 `tracePeak` 使用）：`B` 是全体元素的上界且 `0 ≤ B` 时，
`foldr max 0` 也 ≤ `B`。 -/
private theorem foldr_max_le {B : ℝ} (h0 : 0 ≤ B) {l : List ℝ}
    (h : ∀ v ∈ l, v ≤ B) : l.foldr max 0 ≤ B :=
  match l with
  | [] => h0
  | a :: _ => max_le (h a List.mem_cons_self) (foldr_max_le h0 fun v hv =>
      h v (List.mem_cons_of_mem a hv))

/-- 辅助（仅供 `tracePeak` 使用）：非负常数与 `max` 可交换，逐元素乘进列表后
折叠的结果等于 `a` 乘以原折叠结果。 -/
private theorem foldr_max_map_mul {a : ℝ} (ha : 0 ≤ a) (l : List ℝ) :
    (l.map (fun v => a * v)).foldr max 0 = a * l.foldr max 0 :=
  match l with
  | [] => by simp
  | x :: t => by
      rw [List.map_cons, List.foldr_cons, foldr_max_map_mul ha t, List.foldr_cons,
        mul_max_of_nonneg x (t.foldr max 0) ha]

/-! ## 卡目标 1：峰值的基本性质 -/

/-- **卡目标 1（成员 ≤ 峰值）**：轨迹的每个阶段值都不超过全阶段峰值。 -/
theorem le_tracePeak {v : ℝ} : ∀ {values : List ℝ}, v ∈ values → v ≤ tracePeak values
  | [], hv => by simp at hv
  | x :: t, hv => by
      rcases List.mem_cons.mp hv with h | hv'
      · rw [h]
        exact le_max_left x (tracePeak t)
      · exact (le_tracePeak hv').trans (le_max_right x (tracePeak t))

/-- **卡目标 1（非负）**：峰值非负。轨迹的每个条目都是绝对值（D13），空列表的峰值
是 `0`，`max` 保持非负。 -/
theorem tracePeak_nonneg : ∀ values : List ℝ, 0 ≤ tracePeak values
  | [] => le_refl 0
  | _ :: t => (tracePeak_nonneg t).trans (le_max_right _ (tracePeak t))

/-- **卡目标 1（全体成员 ≤ B 且 0 ≤ B 则峰值 ≤ B)**：峰值是全体元素上界中的最小者，
所以任何非负上界都控制峰值。`0 ≤ B` 不可省：空轨迹的峰值是 `0`。 -/
theorem tracePeak_le {values : List ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v ∈ values, v ≤ B) : tracePeak values ≤ B :=
  foldr_max_le hB h

/-- **卡目标 1（非负标量下的峰值齐次性）**：`0 ≤ a` 时
`tracePeak (values.map (fun v => a * v)) = a * tracePeak values`；空列表也成立
（两边都是 `0`）。负标量不在此陈述中出现，`|c|` 的实例化在 `Scalar` 中给出。 -/
theorem tracePeak_map_mul {a : ℝ} (ha : 0 ≤ a) (values : List ℝ) :
    tracePeak (values.map (fun v => a * v)) = a * tracePeak values :=
  foldr_max_map_mul ha values

end Rho5.GrowthModel
