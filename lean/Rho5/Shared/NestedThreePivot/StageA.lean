/-
D86 — 阶段 A：实际 leading 三阶继承、条目界、首 Schur 完整主元与精确读数
==========================================================================

在 `M 0 0 = 1` 与 `PolyCP M` 下（`PolyCP` 已由 D62 编译并自审，其正向给出四层实际 CP 与
`p, k, r > 0`），本文件**支付**两个实际 `3 × 3` 矩阵的全部资格：

* 条目界 `∀ i j, |A i j| ≤ 1`：由 `PolyCP` 的 25 个原条目界与 16/9 个 border 子式界，
  经 D61 的 `m2_eq_S4` / `m3_eq_p_mul_S3` 精确支付（**不是**假设子块合法）；
* 首 Schur 完整主元 `IsCompletePivot (fixedSchur A) 0 0`：由同一批有限子式界与实际
  `fixedSchur` 公式逐条目限制付清；
* **精确读数**：第一矩阵 `secondPivot = p M`、`thirdPivot = k M`；
  第二矩阵 `secondPivot = k M / p M`、`thirdPivot = r M / p M`。

缩放/嵌入全部复用既有已付件：D37 的 `S4/S3/S3_apply`、D61 的 border 子式恒等式、
冻结 `Rho5.Pivot.fixedSchur`；本文件**不**新建 `LegalTrace`、**不**重审 D49、
**不**消费任何包络定理（阶段 B 才消费 D83/D85 的完整回执）。 -/
import Rho5.Shared.NestedThreePivot.Defs
import Rho5.Shared.MinorCPDomain.Poly

namespace Rho5.NestedThreePivot

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r S4_apply S3_apply T2_apply)
open Rho5.PrefixBorderedMinors (m2 m3 m2_eq_S4 m3_eq_p_mul_S3 m2_zero_zero m3_zero_zero)
open Rho5.MinorCPDomain (PolyCP)

/-! ## 0. 具体下标归一化（`rfl` 级，供 `simp only` 使用） -/

@[simp] theorem idx3_zero : idx3 (0 : Fin 3) = 0 := rfl
@[simp] theorem idx3_one : idx3 (1 : Fin 3) = 1 := rfl
@[simp] theorem idx4_zero : idx4 (0 : Fin 3) = 0 := rfl
@[simp] theorem idx4_one : idx4 (1 : Fin 3) = 1 := rfl
@[simp] theorem fin2_castSucc_zero3 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
@[simp] theorem fin2_castSucc_one3 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
@[simp] theorem fin2_castSucc_castSucc_zero4 : ((0 : Fin 2).castSucc.castSucc : Fin 4) = 0 := rfl
@[simp] theorem fin2_castSucc_castSucc_one4 : ((1 : Fin 2).castSucc.castSucc : Fin 4) = 1 := rfl

/-! ## 1. 第一矩阵：`M` 的 leading `3 × 3` -/

/-- 第一矩阵首主元就是 `M 0 0`。 -/
theorem firstNested_zero_zero (M : Matrix5) (h00 : M 0 0 = 1) : firstNested M 0 0 = 1 := by
  simpa [firstNested, idx3] using h00

/-- 第一矩阵的实际条目界（直接取 `PolyCP` 的原条目界）。 -/
theorem firstNested_entries (M : Matrix5) (hent : ∀ i j : Fin 5, |M i j| ≤ 1) :
    ∀ i j : Fin 3, |firstNested M i j| ≤ 1 := fun a b => hent (idx3 a) (idx3 b)

/-- 第一矩阵的首 Schur **逐条目**等于 border `2 × 2` 子式 `m2`（`M 0 0 = 1`）。 -/
theorem firstNested_fixedSchur_apply (M : Matrix5) (h00 : M 0 0 = 1) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (firstNested M) i j = m2 M i.castSucc.castSucc j.castSucc.castSucc := by
  simp only [Rho5.Pivot.fixedSchur]
  rw [m2_eq_S4 M h00, S4_apply]
  simp only [firstNested, idx3, Fin.castSucc_succ, Fin.castSucc_zero, h00, div_one]

/-- 第一矩阵的首 Schur 完整主元：由 `PolyCP` 的 16 个 `m2` 界付清。 -/
theorem firstNested_cp (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hm2 : ∀ i j : Fin 4, |m2 M i j| ≤ Rho5.MinorCPDomain.A M) :
    Rho5.Pivot.IsCompletePivot (Rho5.Pivot.fixedSchur (firstNested M)) 0 0 := by
  intro i j
  rw [firstNested_fixedSchur_apply M h00 i j, firstNested_fixedSchur_apply M h00 0 0]
  simp only [fin2_castSucc_castSucc_zero4]
  rw [m2_zero_zero M h00, abs_of_pos hp]
  have h2 := hm2 i.castSucc.castSucc j.castSucc.castSucc
  rwa [Rho5.MinorCPDomain.A_eq M h00] at h2

/-- 第一读数的精确值：`p M`。 -/
theorem firstNested_secondPivot (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) :
    secondPivot (firstNested M) = p M := by
  rw [secondPivot, firstNested_fixedSchur_apply M h00 0 0]
  simp only [fin2_castSucc_castSucc_zero4]
  rw [m2_zero_zero M h00, abs_of_pos hp]

/-- 第一矩阵的第二次 Schur 值：`k M`（由 `m2`/`S4`/`S3` 精确限制）。 -/
theorem firstNested_secondSchur_zero_zero (M : Matrix5) (h00 : M 0 0 = 1) :
    Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (firstNested M)) 0 0 = k M := by
  have h00A : Rho5.Pivot.fixedSchur (firstNested M) 0 0 = p M := by
    rw [firstNested_fixedSchur_apply M h00 0 0]
    simp only [fin2_castSucc_castSucc_zero4]
    rw [m2_zero_zero M h00]
  have h11 := firstNested_fixedSchur_apply M h00 1 1
  have h10 := firstNested_fixedSchur_apply M h00 1 0
  have h01 := firstNested_fixedSchur_apply M h00 0 1
  have hgoal : Rho5.Pivot.fixedSchur (firstNested M) 1 1
      - Rho5.Pivot.fixedSchur (firstNested M) 1 0
        * Rho5.Pivot.fixedSchur (firstNested M) 0 1
        / Rho5.Pivot.fixedSchur (firstNested M) 0 0 = k M := by
    rw [h11, h10, h01, h00A]
    simp only [fin2_castSucc_castSucc_zero4, fin2_castSucc_castSucc_one4]
    rw [m2_eq_S4 M h00, m2_eq_S4 M h00, m2_eq_S4 M h00, show p M = S4 M 0 0 from rfl]
    have hstep : S4 M 1 1 - S4 M 1 0 * S4 M 0 1 / S4 M 0 0 = S3 M 0 0 :=
      (S3_apply M 0 0).symm
    rw [hstep]
    rfl
  simpa only [Rho5.Pivot.fixedSchur] using hgoal

/-- 第三读数的精确值：`k M`。 -/
theorem firstNested_thirdPivot (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    thirdPivot (firstNested M) = k M := by
  have h00A : Rho5.Pivot.fixedSchur (firstNested M) 0 0 = p M := by
    rw [firstNested_fixedSchur_apply M h00 0 0]
    simp only [fin2_castSucc_castSucc_zero4]
    rw [m2_zero_zero M h00]
  have h2 := firstNested_secondSchur_zero_zero M h00
  rw [thirdPivot, h00A, if_neg (ne_of_gt hp), h2, abs_of_pos hk]

/-- 第一矩阵满足固定顺序归一化三阶条件。 -/
theorem firstNested_normalized (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hent : ∀ i j : Fin 5, |M i j| ≤ 1)
    (hm2 : ∀ i j : Fin 4, |m2 M i j| ≤ Rho5.MinorCPDomain.A M) :
    LeadingThreeNormalized (firstNested M) :=
  ⟨firstNested_entries M hent, by rw [firstNested_zero_zero M h00, abs_one],
    firstNested_cp M h00 hp hm2⟩

/-! ## 2. 第二矩阵：`S4 M` 的 leading `3 × 3` 除以正 `p M` -/

/-- 第二矩阵首主元为 `1`（`p M ≠ 0`）。 -/
theorem secondNested_zero_zero (M : Matrix5) (hp : p M ≠ 0) : secondNested M 0 0 = 1 := by
  simp only [secondNested, idx4, Fin.castSucc_zero]
  rw [show S4 M 0 0 = p M from rfl, div_self hp]

/-- 第二矩阵首 Schur 的逐条目公式：`S3 M` 的左上 `2 × 2` 除以 `p M`。 -/
theorem secondNested_fixedSchur_apply (M : Matrix5) (hp : p M ≠ 0)
    (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (secondNested M) i j = S3 M i.castSucc j.castSucc / p M := by
  have hA00 : secondNested M 0 0 = 1 := secondNested_zero_zero M hp
  simp only [Rho5.Pivot.fixedSchur]
  rw [hA00]
  simp only [secondNested, idx4, Fin.castSucc_succ, Fin.castSucc_zero, div_one]
  rw [S3_apply, show S4 M 0 0 = p M from rfl]
  field_simp

/-- `S4 M` 的实际条目界：由 16 个 `m2` 界付清。 -/
theorem abs_S4_entry_le_p (M : Matrix5) (h00 : M 0 0 = 1)
    (hm2 : ∀ i j : Fin 4, |m2 M i j| ≤ Rho5.MinorCPDomain.A M) (i j : Fin 4) :
    |S4 M i j| ≤ p M := by
  rw [← m2_eq_S4 M h00 i j, ← Rho5.MinorCPDomain.A_eq M h00]
  exact hm2 i j

/-- `S3 M` 的实际条目界：由 9 个 `m3` 界与 `B = p * k` 付清。 -/
theorem abs_S3_entry_le_k (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hm3 : ∀ i j : Fin 3, |m3 M i j| ≤ Rho5.MinorCPDomain.B M) (i j : Fin 3) :
    |S3 M i j| ≤ k M := by
  have hpne : p M ≠ 0 := ne_of_gt hp
  have h3 : m3 M i j = p M * S3 M i j := m3_eq_p_mul_S3 M h00 hpne i j
  have hB : Rho5.MinorCPDomain.B M = p M * k M := Rho5.MinorCPDomain.B_eq M h00 hpne
  have hkabs : |S3 M 0 0| = k M := by
    rw [show S3 M 0 0 = k M from rfl, abs_of_pos hk]
  have h := hm3 i j
  rw [hB, h3, abs_mul, abs_of_pos hp, ← hkabs] at h
  rw [← hkabs]
  by_contra hlt
  have hlt' : |S3 M 0 0| < |S3 M i j| := lt_of_not_ge hlt
  exact absurd h (not_le_of_gt (mul_lt_mul_of_pos_left hlt' hp))

/-- 第二矩阵的实际条目界（除以正 `p M`）。 -/
theorem secondNested_entries (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hm2 : ∀ i j : Fin 4, |m2 M i j| ≤ Rho5.MinorCPDomain.A M) :
    ∀ i j, |secondNested M i j| ≤ 1 := by
  intro i j
  rw [secondNested, abs_div, abs_of_pos hp, div_le_one hp]
  exact abs_S4_entry_le_p M h00 hm2 _ _

/-- 第二矩阵的首 Schur 完整主元：由 9 个 `m3` 界付清。 -/
theorem secondNested_cp (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hm3 : ∀ i j : Fin 3, |m3 M i j| ≤ Rho5.MinorCPDomain.B M) :
    Rho5.Pivot.IsCompletePivot (Rho5.Pivot.fixedSchur (secondNested M)) 0 0 := by
  have hpne : p M ≠ 0 := ne_of_gt hp
  have hkabs : |S3 M 0 0| = k M := by
    rw [show S3 M 0 0 = k M from rfl, abs_of_pos hk]
  intro i j
  rw [secondNested_fixedSchur_apply M hpne i j, secondNested_fixedSchur_apply M hpne 0 0]
  simp only [fin2_castSucc_zero3, abs_div, abs_of_pos hp, hkabs]
  exact div_le_div_of_nonneg_right (abs_S3_entry_le_k M h00 hp hk hm3 _ _) (le_of_lt hp)

/-- 第二矩阵首 Schur 的 `(0,0)`：`k M / p M`。 -/
theorem secondNested_fixedSchur_zero_zero (M : Matrix5) (hp : p M ≠ 0) :
    Rho5.Pivot.fixedSchur (secondNested M) 0 0 = k M / p M := by
  rw [secondNested_fixedSchur_apply M hp 0 0]
  simp only [fin2_castSucc_zero3]
  rfl

/-- 第二读数的精确值：`k M / p M`。 -/
theorem secondNested_secondPivot (M : Matrix5) (hp : 0 < p M)
    (hk : 0 < k M) : secondPivot (secondNested M) = k M / p M := by
  rw [secondPivot, secondNested_fixedSchur_zero_zero M (ne_of_gt hp)]
  simp only [abs_div, abs_of_pos hp, abs_of_pos hk]

/-- 第二矩阵的第二次 Schur 值：`r M / p M`。 -/
theorem secondNested_secondSchur_zero_zero (M : Matrix5)
    (hp : 0 < p M) :
    Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (secondNested M)) 0 0 = r M / p M := by
  have hpne : p M ≠ 0 := ne_of_gt hp
  have hA00 : Rho5.Pivot.fixedSchur (secondNested M) 0 0 = k M / p M :=
    secondNested_fixedSchur_zero_zero M hpne
  have h11 : Rho5.Pivot.fixedSchur (secondNested M) 1 1 = S3 M 1 1 / p M := by
    rw [secondNested_fixedSchur_apply M hpne 1 1]
    simp only [fin2_castSucc_one3]
  have h10 : Rho5.Pivot.fixedSchur (secondNested M) 1 0 = S3 M 1 0 / p M := by
    rw [secondNested_fixedSchur_apply M hpne 1 0]
    simp only [fin2_castSucc_one3, fin2_castSucc_zero3]
  have h01 : Rho5.Pivot.fixedSchur (secondNested M) 0 1 = S3 M 0 1 / p M := by
    rw [secondNested_fixedSchur_apply M hpne 0 1]
    simp only [fin2_castSucc_one3, fin2_castSucc_zero3]
  have hr : r M = S3 M 1 1 - S3 M 1 0 * S3 M 0 1 / S3 M 0 0 := by
    rw [show r M = T2 M 0 0 from rfl, T2_apply M 0 0]
    rfl
  have hgoal : Rho5.Pivot.fixedSchur (secondNested M) 1 1
      - Rho5.Pivot.fixedSchur (secondNested M) 1 0
        * Rho5.Pivot.fixedSchur (secondNested M) 0 1
        / Rho5.Pivot.fixedSchur (secondNested M) 0 0 = r M / p M := by
    rw [h11, h10, h01, hA00, hr, show S3 M 0 0 = k M from rfl]
    field_simp
  simpa only [Rho5.Pivot.fixedSchur] using hgoal

/-- 第三读数的精确值：`r M / p M`。 -/
theorem secondNested_thirdPivot (M : Matrix5) (hp : 0 < p M)
    (hk : 0 < k M) (hr : 0 < r M) : thirdPivot (secondNested M) = r M / p M := by
  have hpne : p M ≠ 0 := ne_of_gt hp
  have hA00 : Rho5.Pivot.fixedSchur (secondNested M) 0 0 = k M / p M :=
    secondNested_fixedSchur_zero_zero M hpne
  have h2 := secondNested_secondSchur_zero_zero M hp
  rw [thirdPivot, hA00, if_neg (div_ne_zero (ne_of_gt hk) hpne), h2,
    abs_of_pos (div_pos hr hp)]

/-- 第二矩阵满足固定顺序归一化三阶条件。 -/
theorem secondNested_normalized (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hm2 : ∀ i j : Fin 4, |m2 M i j| ≤ Rho5.MinorCPDomain.A M)
    (hm3 : ∀ i j : Fin 3, |m3 M i j| ≤ Rho5.MinorCPDomain.B M) :
    LeadingThreeNormalized (secondNested M) :=
  ⟨secondNested_entries M h00 hp hm2,
    by rw [secondNested_zero_zero M (ne_of_gt hp), abs_one],
    secondNested_cp M h00 hp hk hm3⟩

/-! ## 3. 阶段 A 主定理（`M 0 0 = 1` 与 `PolyCP M` 下的一次性交付） -/

/-- **D86 阶段 A 主定理**：`M 0 0 = 1` 且 `PolyCP M` 时，`M` 的 leading `3 × 3` 与
`S4 M` 的 leading `3 × 3` 除以 `p M` 都是**实际**固定顺序归一化三阶矩阵，且读数精确：

* `secondPivot (firstNested M) = p M`，`thirdPivot (firstNested M) = k M`；
* `secondPivot (secondNested M) = k M / p M`，`thirdPivot (secondNested M) = r M / p M`。

`p, k, r > 0` 也在此由 `PolyCP` 的 `A/B/C` 正性按卡片顺序**导出**（不是假设）。 -/
theorem leading_three_inheritance (M : Matrix5) (h00 : M 0 0 = 1) (hP : PolyCP M) :
    LeadingThreeNormalized (firstNested M) ∧
      secondPivot (firstNested M) = p M ∧ thirdPivot (firstNested M) = k M ∧
        LeadingThreeNormalized (secondNested M) ∧
          secondPivot (secondNested M) = k M / p M ∧
            thirdPivot (secondNested M) = r M / p M := by
  obtain ⟨hA, hB, hC, hent, hm2, hm3, -⟩ := hP
  have hp : 0 < p M := by
    rw [← Rho5.MinorCPDomain.A_eq M h00]
    exact hA
  have hpne : p M ≠ 0 := ne_of_gt hp
  have hk : 0 < k M := by
    have hB' : 0 < p M * k M := by
      rw [← Rho5.MinorCPDomain.B_eq M h00 hpne]
      exact hB
    have hB'' : 0 < k M * p M := by
      rw [mul_comm]
      exact hB'
    exact pos_of_mul_pos_left hB'' (le_of_lt hp)
  have hr : 0 < r M := by
    have hC' : 0 < p M * k M * r M := by
      rw [← Rho5.MinorCPDomain.C_eq M h00 hp hk]
      exact hC
    exact pos_of_mul_pos_right hC' (le_of_lt (mul_pos hp hk))
  exact ⟨firstNested_normalized M h00 hp hent hm2,
    firstNested_secondPivot M h00 hp,
    firstNested_thirdPivot M h00 hp hk,
    secondNested_normalized M h00 hp hk hm2 hm3,
    secondNested_secondPivot M hp hk,
    secondNested_thirdPivot M hp hk hr⟩

end Rho5.NestedThreePivot
