# my_project — 用 Lean 4 证明几何定理

这是一个 Lean 4 入门项目,用几个经典的**平面几何定理**演示「机器验证的数学证明」是怎么回事。所有证明都在 [`MyProject/Geometry.lean`](MyProject/Geometry.lean) 中,不依赖 Mathlib,只用 Lean 4 核心库,`lake build` 几秒钟就能完成编译验证。

## Lean 是什么?

[Lean](https://lean-lang.org/) 是微软研究院发起、现由 Lean FRO 维护的**定理证明器**(theorem prover),同时也是一门函数式编程语言。它最出名的应用是 [Mathlib](https://leanprover-community.github.io/) —— 一个由全球数学家协作构建的、超过一百万行的形式化数学库,连陶哲轩(Terence Tao)都在用它验证自己的论文。

### Lean 怎么「证明」定理?

核心思想只有一句话:**命题即类型,证明即程序**(Curry–Howard 对应)。

- 一个数学命题(比如「勾股定理」)在 Lean 里是一个**类型**;
- 这个命题的证明,就是构造出一个属于该类型的**值**(一段程序);
- Lean 的**类型检查器**验证这段程序类型正确 —— 类型检查通过,就等于证明被机器逐步核验无误。

所以 Lean 证明的可信度不依赖「审稿人有没有看仔细」,而是依赖一个很小的内核(kernel)对每一步推理的机械检查。**只要编译通过,定理就是对的**(前提是你没写错命题本身)。

### 证明长什么样?

Lean 证明通常用**策略(tactic)**书写。策略是「证明指令」,告诉 Lean 如何一步步把目标(goal)化简到显然成立。本项目用到的策略:

| 策略 | 作用 |
|---|---|
| `simp only [...]` | 用指定的定义/引理改写目标,比如把 `distSq` 展开成坐标表达式 |
| `rw [...]` | 用等式从左到右改写目标(比如套用完全平方公式) |
| `omega` | **自动**判定线性整数算术命题(加减法、不等式方程组) |
| `decide` | 对可判定的具体命题直接算出真假(比如 3² + 4² = 5²) |
| `exact` | 给出恰好匹配目标的证明项 |

一个可以在文件里直接体验的最小例子:

```lean
example (a b : Int) : a + b = b + a := by
  omega    -- 交给线性算术决策过程,一步搞定
```

把 `omega` 删掉,Lean 会立刻报错并显示当前未证完的目标 —— 这种「随时能看到还剩什么要证」的交互体验是 Lean 的精髓,建议用 VS Code + [Lean 4 扩展](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)打开本项目体验。

## 本项目的几何定理

几何题如何变成 Lean 能处理的代数题?本项目用的是**坐标法**(解析几何):

1. 把「点」定义为一对整数坐标 `structure Point where x : Int; y : Int`;
2. 把「向量」「点积」「距离平方」定义为坐标上的运算;
3. 几何命题(垂直、中点、平行)翻译成代数等式;
4. 用 `simp` 展开定义,再用 `omega` / `rw` 完成代数推理。

> 为什么用整数而不是实数?实数在 Lean 里需要 Mathlib(约几 GB 的依赖)。这些定理的代数本质在任何交换环上都成立,用 `Int` 既能自包含编译,又不失一般性精神。为避免整数除法,「M 是 AB 的中点」统一写成 `2M = A + B` 的形式。

`MyProject/Geometry.lean` 中的六个定理:

### 1. 距离的对称性 `distSq_symm`

**|AB|² = |BA|²**。热身题:本质是 `(a-b)² = (b-a)²`。先用完全平方公式 `sub_mul_self` 展开两边,再交换乘法顺序,剩下的线性等式交给 `omega`。

### 2. 勾股定理 `pythagoras`

**若 ∠A 为直角,则 |BC|² = |AB|² + |AC|²**。「直角」形式化为「向量 AB 与 AC 的点积为零」。证明分两层:

- `pythagoras_vec`(向量版引理):|v − u|² = |u|² + |v|² − 2(u·v),当 u·v = 0 时即得结论;
- `pythagoras` 把 BC 改写为「以 A 为基点」的 (AC − AB),然后套用引理。

这体现了形式化证明的常见做法:**把核心代数事实抽成引理,几何定理只做「翻译 + 套用」**。

### 3. 具体实例 `pythagoras_3_4_5`

O(0,0)、A(3,0)、B(0,4) 构成的直角三角形满足 3² + 4² = 5²。因为全是具体数字,一个 `decide` 就让 Lean 自己算出来 —— 展示了「可判定命题」与「需要推理的普遍命题」的区别。

### 4. 三角形中位线定理 `midsegment`

**连接两边中点的线段平行于第三边,且长度是它的一半**。结论写成向量等式 `2 · MN = BC`,一条等式同时编码了「平行」和「一半长」。展开定义后是纯线性方程组,`omega` 一步解决。

### 5. 平行四边形对角线互相平分 `parallelogram_diag`

**若 AB ∥= DC(平行四边形),则对角线 AC、BD 的中点重合**。同样是线性代数,展开后交给 `omega`。

### 6. 重心分中线 2:1 `centroid_divides`

**三角形重心 G 把中线 AM 分成 AG : GM = 2 : 1**。重心条件写成 `3G = A + B + C`,结论是向量等式 `AG = 2 · GM`。

### 一个完整证明示例

```lean
/-- 中位线定理:M、N 是 AB、AC 中点 ⟹ 2·MN = BC -/
theorem midsegment (A B C M N : Point)
    (hM : smul 2 M = ⟨A.x + B.x, A.y + B.y⟩)   -- M 是 AB 中点
    (hN : smul 2 N = ⟨A.x + C.x, A.y + C.y⟩)   -- N 是 AC 中点
    : smul 2 (vec M N) = vec B C := by
  simp only [smul, vec, Point.mk.injEq] at *   -- 展开定义,化成坐标等式
  omega                                        -- 线性整数算术,自动完成
```

读法:`(hM : ...)` 是**假设**,冒号后面 `smul 2 (vec M N) = vec B C` 是**待证目标**,`by` 后面是策略脚本。Lean 检查这个脚本确实能把目标化为真,定理即告成立。

## 如何构建与运行

```bash
# 构建整个项目(即验证所有证明)
lake build

# 运行可执行文件
lake exe my_project
```

`lake build` 无报错 = 所有定理都被 Lean 内核验证通过。你可以试着把某个定理的结论改错(比如把 `2 : 1` 改成 `3 : 1`),再 build 就会看到 Lean 拒绝接受。

## 不熟悉 Lean?看 Mathematica 对照版

如果你更熟悉 Mathematica,项目里提供了一个**一一对应的 Wolfram 笔记本**(内容为英文,避免 .nb 中文乱码):

```bash
wolframscript -file generate_notebook.wls
# 若 wolframscript 不在 PATH 中,用完整路径:
/Applications/Mathematica.app/Contents/MacOS/wolframscript -file generate_notebook.wls
```

脚本会先在内核里把六个定理各验证一遍(逐条打印 `True`),然后生成 `GeometryProofs.nb`。用 Mathematica 打开后 Evaluation → Evaluate Notebook,每个定理对应一个 Section:同样的坐标法定义(`vec`、`dot`、`distSq`),用 `Simplify` / `Expand` 验证同样的代数恒等式,最后还有一张 3-4-5 三角形与中位线的图。

两者的区别值得体会:**Mathematica 的 `Simplify` 是计算机代数验算**(你信任 CAS 的实现);**Lean 是证明助理**,每一步推理都被一个极小的逻辑内核核验,编译通过本身就是证明。数学内容则完全相同——这个笔记本正好可以当作读懂 `Geometry.lean` 的桥梁。

## 项目结构

```
├── lakefile.toml           # Lake(Lean 的构建工具)配置
├── lean-toolchain          # 固定 Lean 版本(v4.31.0)
├── Main.lean               # 可执行入口
├── MyProject.lean          # 库的根模块,汇总导入
├── MyProject/
│   ├── Basic.lean          # 初始示例
│   └── Geometry.lean       # ★ 几何定理及其证明
├── generate_notebook.wls   # 生成 Mathematica 对照笔记本的脚本
└── GeometryProofs.nb       # 生成的笔记本(英文,可重新生成)
```

## 想更进一步?

- **加入 Mathlib**:可以用真正的实数、欧氏空间 `EuclideanSpace ℝ (Fin 2)`、角度 `∠ A B C`,以及 `ring`、`linarith`、`polyrith` 等强大策略。Mathlib 里现成的勾股定理叫 `EuclideanGeometry.dist_sq_add_dist_sq_eq_dist_sq_iff_angle_eq_pi_div_two`。
- **教程资源**:
  - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) — 数学家视角的 Lean 教程
  - [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) — 官方定理证明教程
  - [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) — 游戏化入门,从皮亚诺公理证到加法交换律
