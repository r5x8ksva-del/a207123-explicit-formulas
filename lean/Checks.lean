import A207123

/-!
# 计算核对（不是证明的一部分）

用 `native_decide`（依赖编译器求值，会引入公理 `Lean.ofReduceBool`）把 Lean 中的定义与任务说明第 2 节的
数据表（以及 (C3) 的 N 三角形）对照。证明本身（`A207123/` 下各文件）不依赖本文件。
由 `U_eq_F`，`U k m` 可以用闭式 `F m k` 计算；由 `N_inv`，`N k q` 可以用 `U` 的容斥式计算。
-/

namespace A207123

-- 任务说明第 2 节：k=10 一行的 U_10(0..6) = 1, 100, 1222, 7629, 32971, 112349, 323647
theorem table_k10 : (List.range 7).map (fun m => F m 10) = [1, 100, 1222, 7629, 32971, 112349, 323647] := by
  native_decide

-- k=7 一行：1, 31, 214, 873, 2669, 6778, 15108
theorem table_k7 : (List.range 7).map (fun m => F m 7) = [1, 31, 214, 873, 2669, 6778, 15108] := by
  native_decide

-- R_k = U_k(1)，k=1..10：2,4,6,9,14,21,31,46,68,100
theorem table_R : (List.range 10).map (fun k => F 1 (k + 1)) = [2, 4, 6, 9, 14, 21, 31, 46, 68, 100] := by
  native_decide

-- 由 U_eq_F 换回 U：U_10(6) = 323647
theorem U_10_6 : U 10 6 = 323647 := by
  rw [U_eq_F]; native_decide

-- 原题 a_3(n)，n=1..6：6, 36, 102, 289, 612, 1296（a_eq 把它化成 U 的乘积）
theorem a3_values : (List.range 6).map (fun n => F ((n + 2) / 2) 3 * F ((n + 1) / 2) 3)
    = [6, 36, 102, 289, 612, 1296] := by
  native_decide

-- 任务说明 (C3) 的 N 三角形 k=7 一行：q=1..7 为 1,29,124,199,139,38,2（q=0 为 0）；
-- 由 N_inv 与 U_eq_F 化为 F 的整数组合后计算
theorem N_row7 : ∀ q ∈ List.range 8,
    (N 7 q : ℤ) = [0, 1, 29, 124, 199, 139, 38, 2].getD q 0 := by
  intro q hq
  rw [N_inv 7 q (by norm_num)]
  simp only [U_eq_F]
  revert q
  native_decide

-- N 三角形 k=10 一行：1,98,925,3337,6051,6012,3257,871,86,2
theorem N_row10 : ∀ q ∈ List.range 11,
    (N 10 q : ℤ) = [0, 1, 98, 925, 3337, 6051, 6012, 3257, 871, 86, 2].getD q 0 := by
  intro q hq
  rw [N_inv 10 q (by norm_num)]
  simp only [U_eq_F]
  revert q
  native_decide

-- 按上升数细化（T2.4 第二式 Us_explicit）：U_6(3,s)，s=0..6 为 84, 238, 97, 0, 0, 0, 0，
-- 和为 U_6(3) = 419（任务说明第 2 节）；U_7(2,s) 为 36, 113, 65, 0, …，和为 U_7(2) = 214。
-- 两行数据另由 Python 按原始定义暴力枚举得到（全部 4^6、3^7 个序列）。
theorem Us_row_6_3 : (List.range 7).map (fun s => Us 6 3 s) = [84, 238, 97, 0, 0, 0, 0] := by
  simp only [Us_explicit]
  native_decide

theorem Us_row_7_2 : (List.range 8).map (fun s => Us 7 2 s) = [36, 113, 65, 0, 0, 0, 0, 0] := by
  simp only [Us_explicit]
  native_decide

end A207123
