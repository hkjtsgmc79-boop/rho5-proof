/-
D86 — 实际 leading 三阶继承：定义层
=====================================

卡片 `parallel/D86/TASK.md` 阶段 A 的构造部分。对实际五阶 `M`（`M 0 0 = 1`，`PolyCP M`）
构造两个**实际** `3 × 3` 矩阵：

* `firstNested M` —— `M` 的 leading `3 × 3`（首主元 `M 0 0 = 1`）；
* `secondNested M` —— `S4 M` 的 leading `3 × 3` 除以正 `p M`（首主元 `p M / p M = 1`）。

读数 `secondPivot` / `thirdPivot` 与 D83 外脑包络的 `secondMagnitude` / `thirdMagnitude`
**同式**（`|fixedSchur · 0 0|`，第三读数带"第二主元为 0 则停机到 0"约定），
`LeadingThreeNormalized` 与 `FixedOrderNormalized3` **同内容**。三者在此**独立定义**
（D83 尚未编译），阶段 B 再逐条桥接到 D83 的具名定义并消费其包络定理。

**未付**：阶段 A 不声称 `r ≤ 4`、不消费任何包络、不假设子块资格；读数与归一化都要在本
lane 内由 `PolyCP` 的有限子式界与实际 Schur 更新付清。
-/
import Rho5.Shared.PrefixBorderedMinors.Identities
import Rho5.Shared.Pivot

namespace Rho5.NestedThreePivot

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r)

/-- 三阶实际矩阵。 -/
abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ

/-- 二阶实际矩阵。 -/
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

/-- `M` 的 leading 三个下标嵌入 `Fin 5`。 -/
def idx3 : Fin 3 → Fin 5 := fun i => i.castSucc.castSucc

/-- `S4 M` 的 leading 三个下标嵌入 `Fin 4`。 -/
def idx4 : Fin 3 → Fin 4 := fun i => i.castSucc

/-- **第一矩阵**：`M` 的 leading `3 × 3`（首主元 `M 0 0`）。 -/
noncomputable def firstNested (M : Matrix5) : Matrix3 := fun i j => M (idx3 i) (idx3 j)

/-- **第二矩阵**：`S4 M` 的 leading `3 × 3` 除以 `p M`（首主元 `1`，需 `p M ≠ 0`）。 -/
noncomputable def secondNested (M : Matrix5) : Matrix3 :=
  fun i j => S4 M (idx4 i) (idx4 j) / p M

/-- 固定顺序**第二读数** `|fixedSchur A 0 0|`（与 D83 包络 `secondMagnitude` 同式）。 -/
noncomputable def secondPivot (A : Matrix3) : ℝ := |Rho5.Pivot.fixedSchur A 0 0|

/-- 固定顺序**第三读数**：第二读数为 `0` 时停机到 `0`，否则 `|fixedSchur (fixedSchur A) 0 0|`
（与 D83 包络 `thirdMagnitude` 同式）。 -/
noncomputable def thirdPivot (A : Matrix3) : ℝ :=
  if Rho5.Pivot.fixedSchur A 0 0 = 0 then 0
  else |Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur A) 0 0|

/-- **固定顺序归一化三阶**（与 D83 包络 `FixedOrderNormalized3` 同内容：条目界、首主元绝对
值为 `1`、首 Schur 的 `(0,0)` 仍是完整主元）。 -/
def LeadingThreeNormalized (A : Matrix3) : Prop :=
  (∀ i j, |A i j| ≤ 1) ∧ |A 0 0| = 1 ∧
    Rho5.Pivot.IsCompletePivot (Rho5.Pivot.fixedSchur A) 0 0

end Rho5.NestedThreePivot
