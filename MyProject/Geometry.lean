/-
  平面几何定理的 Lean 4 形式化证明
  ================================

  本文件不依赖 Mathlib,只用 Lean 4 核心库,采用「坐标法/向量法」:
  把点表示为整数坐标,把几何命题翻译成代数命题,再用策略(tactic)证明。

  包含的定理:
  1. `distSq_symm`        —— 距离的对称性:|AB|² = |BA|²
  2. `pythagoras`         —— 勾股定理(直角三角形斜边平方 = 两直角边平方和)
  3. `pythagoras_3_4_5`   —— 勾股定理的具体实例:3-4-5 直角三角形
  4. `midsegment`         —— 三角形中位线定理(中位线平行于底边且等于其一半)
  5. `parallelogram_diag` —— 平行四边形的对角线互相平分
  6. `centroid_divides`   —— 三角形重心把中线分成 2:1
-/

namespace Geometry

/-- 平面上的点,用整数坐标表示。
    (用 `Int` 而不是实数是为了不依赖 Mathlib;
    这些定理的代数本质在任何交换环上都成立。) -/
structure Point where
  x : Int
  y : Int
  deriving DecidableEq, Repr

/-- 从点 `A` 指向点 `B` 的向量(仍用 `Point` 表示其坐标)。 -/
def vec (A B : Point) : Point :=
  ⟨B.x - A.x, B.y - A.y⟩

/-- 向量的标量乘法:`k • v`。 -/
def smul (k : Int) (v : Point) : Point :=
  ⟨k * v.x, k * v.y⟩

/-- 向量点积(内积)。点积为零 ⟺ 两向量垂直。 -/
def dot (u v : Point) : Int :=
  u.x * v.x + u.y * v.y

/-- 两点距离的平方。
    (整数上开不了根号,但比较「距离的平方」和比较「距离」是等价的。) -/
def distSq (A B : Point) : Int :=
  (B.x - A.x) * (B.x - A.x) + (B.y - A.y) * (B.y - A.y)

/-! ## 代数引理

几何证明最终都归结为多项式恒等式。
先证一个展开平方差的引理,后面反复使用。 -/

/-- 完全平方公式:(a-b)² = a² - 2ab + b² -/
theorem sub_mul_self (a b : Int) :
    (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a]
  omega

/-! ## 定理 1:距离的对称性 -/

/-- **A 到 B 的距离等于 B 到 A 的距离**:|AB|² = |BA|²。

    证明思路:(bx-ax)² = (ax-bx)²,因为 (-t)·(-t) = t·t。 -/
theorem distSq_symm (A B : Point) : distSq A B = distSq B A := by
  simp only [distSq, sub_mul_self]
  rw [Int.mul_comm A.x B.x, Int.mul_comm A.y B.y]
  omega

/-! ## 定理 2:勾股定理 -/

/-- 勾股定理的「向量版」:若向量 u ⊥ v(点积为零),则 |v - u|² = |u|² + |v|²。

    证明思路:|v - u|² = |v|² - 2(u·v) + |u|²(完全平方公式),
    由 u·v = 0 立得。展开后交给 `omega` 做线性算术。 -/
theorem pythagoras_vec (ux uy vx vy : Int)
    (h : ux * vx + uy * vy = 0) :
    (vx - ux) * (vx - ux) + (vy - uy) * (vy - uy)
      = (ux * ux + uy * uy) + (vx * vx + vy * vy) := by
  rw [sub_mul_self vx ux, sub_mul_self vy uy,
      Int.mul_comm vx ux, Int.mul_comm vy uy]
  omega

/-- **勾股定理**:若 ∠A 是直角(即向量 AB 与 AC 垂直,点积为零),
    则 |BC|² = |AB|² + |AC|²。

    证明思路:设 u = AB, v = AC,则 BC = v - u,套用向量版引理。 -/
theorem pythagoras (A B C : Point)
    (h : dot (vec A B) (vec A C) = 0) :
    distSq B C = distSq A B + distSq A C := by
  simp only [dot, vec, distSq] at *
  -- 把 (C.x - B.x) 改写成 (C.x - A.x) - (B.x - A.x),使各项都以 A 为基点
  have hx : C.x - B.x = (C.x - A.x) - (B.x - A.x) := by omega
  have hy : C.y - B.y = (C.y - A.y) - (B.y - A.y) := by omega
  rw [hx, hy]
  exact pythagoras_vec _ _ _ _ h

/-! ## 定理 3:勾股定理的具体实例 -/

/-- **3-4-5 直角三角形**:O(0,0)、A(3,0)、B(0,4),
    直角在 O,斜边 AB 的平方 = 3² + 4² = 25。

    对于具体数值,`decide` 策略直接把命题算出来。 -/
theorem pythagoras_3_4_5 :
    distSq ⟨3, 0⟩ ⟨0, 4⟩ = distSq ⟨0, 0⟩ ⟨3, 0⟩ + distSq ⟨0, 0⟩ ⟨0, 4⟩ := by
  decide

/-! ## 定理 4:三角形中位线定理 -/

/-- **中位线定理**:M、N 分别是 AB、AC 的中点,
    则 MN ∥ BC 且 |MN| = |BC| / 2。

    为避免整数除法,中点条件写成 `2M = A + B`(逐坐标),
    结论写成 `2 · (向量 MN) = 向量 BC` —— 这同时给出「平行」和「一半长」。 -/
theorem midsegment (A B C M N : Point)
    (hM : smul 2 M = ⟨A.x + B.x, A.y + B.y⟩)   -- M 是 AB 中点
    (hN : smul 2 N = ⟨A.x + C.x, A.y + C.y⟩)   -- N 是 AC 中点
    : smul 2 (vec M N) = vec B C := by
  simp only [smul, vec, Point.mk.injEq] at *
  -- 展开定义后只剩线性整数方程组,omega 一步解决
  omega

/-! ## 定理 5:平行四边形的对角线互相平分 -/

/-- **平行四边形对角线互相平分**:
    若 ABCD 是平行四边形(向量 AB = 向量 DC),
    则对角线 AC 与 BD 的中点重合。

    「中点重合」表述为:A + C = B + D(逐坐标,两边同乘 2 后的中点条件)。 -/
theorem parallelogram_diag (A B C D : Point)
    (h : vec A B = vec D C) :
    A.x + C.x = B.x + D.x ∧ A.y + C.y = B.y + D.y := by
  simp only [vec, Point.mk.injEq] at h
  omega

/-! ## 定理 6:重心把中线分成 2:1 -/

/-- **重心定理**:G 是三角形 ABC 的重心(3G = A + B + C),
    M 是 BC 的中点(2M = B + C),
    则 G 在中线 AM 上且 AG : GM = 2 : 1,
    即向量 AG = 2 · 向量 GM。 -/
theorem centroid_divides (A B C G M : Point)
    (hG : smul 3 G = ⟨A.x + B.x + C.x, A.y + B.y + C.y⟩)  -- G 是重心
    (hM : smul 2 M = ⟨B.x + C.x, B.y + C.y⟩)               -- M 是 BC 中点
    : vec A G = smul 2 (vec G M) := by
  simp only [smul, vec, Point.mk.injEq] at *
  omega

end Geometry

/-! ## 快速验算(#eval 不是证明,只是跑一下看看数值) -/

#eval Geometry.distSq ⟨0, 0⟩ ⟨3, 4⟩          -- 25:著名的 3-4-5
#eval Geometry.dot ⟨1, 2⟩ ⟨-2, 1⟩            -- 0:两向量垂直
