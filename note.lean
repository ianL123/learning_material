import Mathlib.Tactic
-- 几乎所有的Lean关键字都是tactic，接下来我们都译作策略。

-- # A函数

example (A B : Type) (f : A → B) (a : A) : B :=
by
  apply f
  exact a
/-
对B `apply f` 会根据“A可以推出B”将证明目标改为A。
-/

example (A: Type) : A → A :=
by
  intro x
  exact x
/-
由于现在的目标是一个函数，`intro`可以导出一个条件变量
这里是`x : A`。同时将证明目标改为结论也就是A。
-/

-- # BC基础逻辑（或与蕴含等价非）

example (hpq : P ∨ Q) : Q ∨ P :=
by
  cases hpq with
  | inl h =>
    right
    exact h
  | inr h =>
    left
    exact h
/-
使用`inl`和`inr`可以对hpq的两种情况进行分类。
在每一种分类中，使用`right`和`left`对结论中需要被证明的
一侧进行选择。
例如假如你有`(hp : P)`，则可以直接`right`然后`exact hp`。
-/

example (h: P ∧ Q) : Q ∧ P :=
by
  obtain ⟨hp, hq⟩ :=h
  constructor
  · exact hq
  · exact hp
example (h: P ∧ Q) : Q ∧ P :=
by
  constructor
  · exact h.2
  · exact h.1
/-
可以使用`obtain`将合取式拆成两个命题，也可以直接取出1和2。
要证明一个合取式，使用`constructor`和`· `按顺序证明出每一部分。
-/

/-
imply的做法与最前面两节的函数做法相同。
也只需要使用`intro`和`apply`两个。
-/

/-
iff的语法和合取相同，也就是说可以被`obtain`拆成正反两个imply的命题，
同理可以直接取1和2。
而要证明一个等价，也可以使用`constructor`和`· `按顺序证明正反两个方向
的imply命题即可。
你可以参考下面这个例子：
-/
example : (P ↔ Q) ↔ (P → Q) ∧ (Q → P):=
by
  constructor
  · intro hpq
    constructor
    · exact hpq.1
    · exact hpq.2
  · intro y
    constructor
    · intro z
      apply y.1
      exact z
    · intro z
      apply y.2
      exact z

/-
小故事：
还记得去年在Logic里面学的分析表(tableau)吗？
要证明satisfiable需要open tableau。
而要证明¬ φ valid需要其在所有分支上close。
故而我们之前的所有工作都是等价于在寻找所有分支上是否有条件P
与所求结论等价，由于其之后就与结论的非矛盾，就证明了原命题。
因此，对于任何条件中已经包含矛盾的情况，可以证明任何命题为真。
因为任何命题的非在主分支上就已经遇到了条件矛盾。原命题自然恒成立。
-/
example (P Q : Prop) (hp: P) (hnp: ¬ P) : Q :=
by
  contradiction
/-
使用`contradiction`证明条件中存在矛盾的论证。
-/
example (P : Prop) : ¬ (P ∧ ¬P):=
by
  intro h
  obtain ⟨hp,hnp⟩:= h
  contradiction
/-
`¬ P`实际上被定义为`P → False`，也就是说，可以像对待函数一样`intro `它。
-/

example (P : Prop) : ¬¬ P → P:=
by
  intro hnp
  by_cases hp : P
-- 依次对指定的命题正反进行枚举，例如此处是P与非P。
  · exact hp
  · contradiction
-- 这里是`hp: ¬P`和`hnp: ¬¬P`矛盾完成的证明。
example (P : Prop) : P → True :=
by
  intro _
  trivial
/-
需要对某个命题的真伪进行分类讨论时，使用`by_cases`
对于所求结论是`⊢ True`时可以使用`trivial`直接结束。
-/

-- # D一阶逻辑

section
variable (A : Type)
variable (P Q : A → Prop) -- Some `predicate`s on a type A
/-
在本节中，我们需要回顾一阶逻辑新增的语法——谓词(predicate)。
在这里我们定义了三个变量，这些变量之后将持续生效，分别是
一个普通元素集A，两个谓词P、Q，可以根据A中元素输入的情况输出一个命题结果。
举例而言，A是ℕ ,P是“n是偶数”。那么它就可以对所有偶数输出真，奇数输出伪。
-/

example (h : ∀a, P a) : P b:=
by
  apply h
/-
对于有条件是全称量词的，可以直接用`apply`证明
-/
example (hp : ∀a, P a) (hq : ∀a, Q a) : ∀x, (P x ∧ Q x) :=
by
  intro x
  specialize hp x
  -- 得到`hp : P x`
  specialize hq x
  constructor
  · exact hp
  · exact hq
/-
对于包含`all`的结论，使用`intro x`把其变成`⊢ P x ∧ Q x`
对于使用全称量词的条件，如果有`x : A`（这里的A要符合表达式中的谓词的定义域）
可以使用`specialize h x`把`h`变成`h : P x`
如果你要多次使用`h`，可以使用`have`转为多个特定代入的语句。
例如`have h0 := h 0`和`have h1 := h 1`。
-/

example (h : ∃ a, P a) : ∃ b, P b ∨ Q b:=
by
  obtain ⟨a, ha⟩ := h
  -- 得到`a : A`和`ha : P a`
  use a
  left -- 选择`or`左侧
  exact ha
/-
对于存在量词，可以使用`obtain`进行拆分。
而对于需要证明的存在量词结论，使用`use`指定某个例子即可证明其成立。
例如在上面的代码中，我们指定使用`P a ∨ Q a`
作为证明结论在某种情况下成立的例子。
-/

example (hpq: ∀x y, P x → Q y) : (∀z, Q z) ∨ (∀z,¬ P z) :=
by
  by_contra h
  -- Goal is now `⊢ False`, and we have a new hypothesis
  -- `h : ¬((∀ (z : A), Q z) ∨ ∀ (z : A), ¬P z)`
  -- We can simplify `h` by pushing the negation inside
  push_neg at h
  -- Now have `h : (∃ (z : A), ¬Q z) ∧ ∃ (z : A), P z`
  obtain ⟨hq,hp⟩:= h
  obtain ⟨b, hb⟩:= hq
  obtain ⟨a, ha⟩:= hp
  apply hb (hpq a b ha)
/-
有两个非常好用的策略——`push_neg`和`by_contra`。
`push_neg`可以对一个外部是否定的表达式使用，
对否定内部进行一次否运算转化。
`by_contra`可以将结论的否定转化到条件空间中，并留下一个False。
另外在最后那个apply中，`hpq a b : P a → Q b`，`ha : P a`，
前者对后者生效，所以`(hpq a b ha) : Q b`，而`hb : ¬Q b`所以得证。
-/

end

-- # E相等

example (i j : ℕ) : i + j = i + j :=
by
  rfl
example (n : ℕ) : n + 0 = n :=
by
  rfl
/-
当只剩下定义相等的表达式，或者经过`reduce`两侧的结果定义相同。
可以直接使用`rfl`(reflexivity)结束证明。
-/

example (P : Prop) : P ↔ P :=
by
  rfl
example : 2 ∣ n ↔ ∃ k, n = 2 * k:=
by
  rfl
/-
不仅仅是`=`，`↔`也是一种可以被对称直接证明的关系。
-/

example  : 0 + n = n :=
by
  exact zero_add n -- 这里rfl不会成功
/-
`n + 0`和`0 + n`是定义不同的命题与lean的定义方式有关，这里不展开。
-/

example  (h1: i = j) (h2 : j = k) : i = k :=
by
  rw [h1]
  exact h2
example  (h1: i = j) (h2 : j = k) : i = k :=
by
  rwa [h1]
example  (k : ℕ) (h1: i = j + k) (h2 : j = k + k) : i = k + k + k:=
by
  rw [h1,h2]
/-
可以使用`rw`(rewrite)代入一个等式到结论中，
其结尾会自动应用一次`rfl`所以最后一个例子会直接通过。
但是也可以使用`rwa`使得最后自动在整个context中尝试一次匹配。
-/

example (h1 : i = j) (h2: j = k) (h3 : m = k) (h4 : n = m) : i = n :=
by
  rw [← h4] at h3
  rw [← h3] at h2
  rwa [h1]
/-
在代入时需要注意，代入`h : a = b`是把`a`换成`b`。反之需要输入`← `。
-/

section
variable (k m n : ℕ)

example (hcomm : ∀ (i j : ℕ), i + j = j + i) : 7 + n = n + 7 :=
by
  rw [hcomm]
example (hcomm: ∀ (i j : ℕ), i + j = j + i) : k + m + n = n + (m + k) :=
by
  rw [hcomm]
  rw [hcomm k]
/-
如果条件里包含全称代词语句，也可以将其用于覆写。
其标准语句是`rw [hcomm i j]`，其中`i`和`j`如果省略，lean会自动尝试进行匹配。
在上面的例子中，只有第三句证明指定了一个`k`，因为这是唯一一个自动匹配不到的。
-/
end

example {a b x : ℝ} (h : b ≤ a) (hx : 0 ≤ x) :
    x * a ≥ x * b := by
  rel [h]

/-
有等式自然有不等式，
而`rw`不能用于不等式的覆写。
这时可以使用`rel`策略。
-/

-- # F自然数

inductive N
| zero : N
| succ (n : N) : N
namespace N
instance : OfNat N 0 where
  ofNat := zero
instance : OfNat N 1 where
  ofNat := succ 0
def add : N → N → N
| a , 0   => a
| a , succ b => succ (add a b)
instance : Add N where
  add := add
/-
自然数`ℕ `在Lean中被定义为了递归的结构。注意这里我们用`N`代替，
以防止后续证明意外使用Mathlib中的方法。
-/

theorem add_succ (a b : N) : a + b.succ = (a + b).succ:=
by
  rfl
/-
如上一节所说，在定义上相同的式子可以直接用rfl证明。
同时，当我们证明了`theorem`之后，其就可以被直接使用。
-/

theorem zero_add (n : N) : 0 + n = n :=
by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [add_succ,ih]
/-
而上一节中我们直接使用的`zero_add`其具体证明方法如上。
其使用了`induction`也就是递归的方式来证明。
与大家学过的递归证明相同，需要先证明base case。
然后证明后续步骤。这里的`ih : 0 + n = n`，`rw`完成了下面的转化：
⊢ 0 + n.succ = n.succ
⊢ (0 + n).succ = n.succ
⊢ n.succ = n.succ
-/

theorem succ_ne_zero (n : N) : n.succ ≠ 0 :=
by
  intro
  contradiction
/-
这里我们通过`intro`得到`a✝ : n.succ = 0`。
zero和succ是不同的构造器因而不可能相等，
所以这时lean可以直接使用`contradiction`识别
-/

theorem succ_inj (n m : N) : n.succ = m.succ → n = m :=
by
  intro h
  injection h
/-
`injection`根据递归的性质——在递归结构中相同的两项，
它们的前导（succ出它们的那项）也相同。
于是我们可以用`h : n.succ = m.succ`推出`⊢ n = m`。
-/

end N

theorem zero_pow1 (n : ℕ) (h : n ≠ 0) : 0 ^ n = 0:=
by
  cases n with
  | zero =>
    contradiction
  | succ n =>
    simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow]
/-
有时在不需要递归的情况下，也可以使用`cases`进行分类。
这里使用`simp?`后，Lean会自动搜索Mathlib中的简化定理进行证明。
结果会转化为`simp only`，只使用指定的定理进行简化。
-/

#check zero_pow
/-
当你需要使用Mathlib中的某个定理时，可以使用`#check`查看其具体内容。
同时，在证明过程中使用`exact?`，Lean会自动搜索Mathlib中是否有可以直接使用的定理。
如果不行，尝试`apply?`。
-/

-- # G函数与集合

def double1 : ℕ → ℕ :=
by
  intro n
  exact 2 * n
def double2 : ℕ → ℕ := fun n => 2 * n
/-
在lean中我们可以定义函数，上面的两个函数实际上定义相同。
前者是通过策略定义的，后者是通过`fun`定义的。
其格式是先输入前面的`n`作为接受的参数，然后`=>`后面是输出的结果。
-/

def double3 : ℕ → ℕ := fun n => n + n

example : double3 = double1 :=
by
  ext x
  rw [double3,double1,two_mul]
/-
与数学相等相同，我们也需要判断定义相同之外函数的实质性相同。
其被称为`Function extensionality`也就是`f = g` iff `∀a, f a = g a`。
其策略为`ext`，其会将结论变为`double3 x = double1 x`也就是为它们代入指定参数`x`。
之后的证明过程就与上两章相同。
**在面对答案中出现的函数时，你首先考虑的方法之一就是使用ext代入**
-/

example (A : Type) (s t: Set A) (heq : ∀x, x ∈ s ↔ x ∈ t) : s = t :=
by
  ext; apply heq
/-
这里定义 `x : A`和`s t : Set A`。于是我们有了集合的概念。
`x ∈ s ∪ t`、`x ∈ s ∩ t`、`x ∉ s`、`x ∈ sᶜ`、`x ∈ s \ t`都是常见的集合关系。
`s ⊆ t`表示两个集合之间的关系，`∀x, x ∈ s → x ∈ t`。
在关于任何主题（这里是A）的集合中，总有“全集”和“空集”两个特殊集合。在类型正确的情况下：
全集`x ∈ univ`总是`True`
空集`x ∈ ∅`总是`False`
证明与之前六章类似。
-/

-- # SA结构化策略

example (a b c : ℕ) (h : c < a)  : 0 < a + b - c :=
by
  refine Nat.sub_pos_of_lt ?h
  exact Nat.lt_add_right b h
/-
`refine`是一个类似`exact`的策略，但是它允许我们在需要的参数处使用`?_`，
以代替一个我们当前没有的参数。Lean会将这个`?_`变成一个新的证明目标。
-/

example (f g : ℕ → ℝ) (a b : ℕ) (hac : a = b) (hfg : f = g) : f a = g b :=
by
  congr!
/-
如果结论是多个相等的组合，例如`f a = g b`，可以使用`congr!`一次性完成这个证明。
当然也可以使用`rw`分步完成。
`congr!`实际上是一个很激进的策略，其会尝试推进看到的每一部分证明并
将其作为需要证明的目标。其需要使用`· `打头分别证明。
当其过于激进时，可以在其后加上自然数限制其拆解步数。语法是`congr! n`。
-/

example (f g : ℕ → ℕ) (h : ∀ n, g n = f n) (hm : Monotone f) : Monotone g :=
by
  convert hm
  ext
  apply h
example (f : ℕ → ℝ) (h : StrictMono (f + f)) : StrictMono (2 * f):=
by
  convert h using 1
  exact two_mul f
/-
`convert`类似于`refine`，当结论和一个条件只有细微差别时，其将目标替换为这个差异。
同样的，其也可以使用自然数限制拆解步数。语法是`convert h using n`。
-/

example (a b : ℕ) (h : a = b) : b = a :=
by
  symm
  exact h
/-
对于具有对称性的关系符（如`=`）使用`symm`将其翻转。
-/
example (a b c : ℕ) (h1 : a = b) (h2 : c = b) : a = c :=
by
  trans b
  · exact h1
  · exact h2.symm
/-
同理其可以翻转可以对称的条件。
使用`trans t`将结论变为`a = t`和`t = c`两个需要证明的目标。
-/

example (a b c d : ℕ) (h1 : a = b) (h2 : c = d): (a + b + a)*(c + d) = (a + b + b)*(c + c):=
by
  congr!
  symm
  exact h2
/-
总之不要怕
-/

-- `h : x ∈ Set.range f` 那么其定义其实同`∃ y : α, f y = x`，表示
example
  (f : ℤ → ℤ) (h₀ : f 0 = -1) (h₁ : f 1 = 1) (h : ∀ x, f x = -1 ∨ f x = 1):
  Set.range f = {-1, 1} := by
  ext x
  constructor
  · intro ha                -- 这里也可以使用`rintro ⟨y, rfl⟩`
    obtain ⟨y, rfl⟩ := ha    -- 它是`intro`与`obtain`的语法糖
    exact h y
  · rintro (rfl | rfl)
    use 0, h₀
    exact ⟨1, h₁⟩
/-
虽然我们有时候在练习里写`rintro`，但是其没有`obtain`容易理解。
此时`ha`的定义实际上等于`ha : ∃ y, f y = x`
我们直接在表达式侧运用一次`rfl`，这会直接运算一次`f y = x`
那么原本的`⊢ x ∈ {-1, 1}`就会变成`⊢ f y ∈ {-1, 1}`
-/

-- # SB高阶策略

lemma sq_add (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  rw [sq, mul_add, add_mul, add_mul, ← sq, ← sq, mul_comm, two_mul, add_mul,
      add_assoc, add_assoc, add_assoc]
lemma sq_add' (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  ring

#print sq_add
#print sq_add'
/-
任何属于环的结构（如ℝ, ℤ, ℚ等）都可以使用`ring`策略简化两侧相等部分。
-/

lemma less_than : (123123123123123 : ℝ) < 212312312312312 :=
by
  norm_num
lemma small_prime : Nat.Prime 13 :=
by
  decide
lemma larger_prime: Nat.Prime 110017 :=
by
  norm_num
/-
`norm_num`可以完成数值表达式的证明。
`decide`可以完成Lean知道其算法的命题证明。
在一些情况下`decide`会失败，这时可以尝试`norm_num`。
在一些`rfl`无法完成的数值等式证明中也可以尝试`norm_num`。
-/

lemma linear_ineq (a b c : ℝ) (h1: a ≤ 2 * b) (h2: b ≤ 3 * c) : 2 * a ≤ 12 *c:=
by
  linarith
example (a b : ℝ) : 0 ≤ (a + b)^2 - 2*a*b :=
by
  ring
  nlinarith
/-
与`rw`不能覆盖不等式相同，`rfl`也不能完成不等式的证明。
`linarith`可以完成线性不等式的证明。
`nlinarith`可以完成非线性不等式的证明。
-/

-- # HChave与Calc

/-
我们之前在为全称量词多次代入时使用了`have`策略：
`have h0 := h 0`和`have h1 := h 1`。
-/
example (a b : Nat) : (a + b) ^ 2 = a^2 + 2*a*b + b^2 := by
  have h2 : (a + b) ^ 2 = (a + b) * (a + b)
  · exact Nat.pow_two (a + b)
  rw [h2]
  calc
    (a + b) * (a + b) -- 可以被替换成`_`
      = a*a + a*b + b*a + b*b := by ring
    _ = a^2 + 2*a*b + b^2 := by ring
    -- 最后的表达式也可以替换成`_`，因为这个表达式来自结论
/-
而实际上其可以运行我们构造任意的条件。
例如`h0`的条件就是在h中代入0。
而下面的例子中，我们在`· `中证明了`h2`，所以我们就可以在后续的证明中使用它。

`calc`块可以让我们分步证明一个等式或者不等式。
我们只需要在每一次推导后给与对应证明即可。
-/

example
  (m : ℕ) (h : 0 < m) : (2 * m) ^ 2 + (m ^ 2 - 1) ^ 2 = (m ^ 2 + 1) ^ 2
    := by
  have hk : ∃ k, m = k + 1 := by
    exact Nat.exists_eq_add_of_le' h
  obtain ⟨k, pls⟩ := hk
  rw[pls]
  sorry
/-
遇到一个不等式定理可以将某个数的范围进行限缩时，可以用`have`来处理。
使用如上的情况，就可以通过这种操作获得一个带`∃`的`hk`
进而可以使用`obtain`得到不带范围的`hk`。
-/

def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε
example (n : ℕ) : Cts (fun x => x ^ n) 0 := by
  intro e he
  cases n with
  | zero =>
    use e, he, by norm_num [he]
  | succ _ =>
    -- we can take `δ = ε` unless `ε > 1` in which case we use `δ = 1`
    use min e 1
    constructor
    · apply lt_min he zero_lt_one
    · intro x hx
      norm_num at hx ⊢
      calc
        _ ≤ |x|   := pow_le_of_le_one (abs_nonneg _) hx.2.le (Nat.succ_ne_zero _)
        _ < _     := hx.1
/-
极限相关的证明非常经典，结构通常非常相似，请学习这段证明。
-/

-- # FS有限集合

open Finset
#reduce range 5 -- {0, 1, 2, 3, 4}
/-
`Finset`是一个特殊的命名空间，我们在介绍`ext`的时候介绍过`Set`。
而有限集合由于特殊的构造方式，会稍不直观一些，并且无法使用一些`Set`可以用的方法。
例如你会看到上面`range 5`的定义不太能一眼看懂，没关系，其实它和0到4没有区别。
-/

lemma sum_nat (n : ℕ) : 2 * ∑ i ∈ range n.succ, i = n * (n + 1):=
by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [sum_range_succ,mul_add, ih]
    ring
/-
注意这里的`∑ i ∈ range n.succ, i`是一个整体。它是
For i in range n+1, sum of i
的意思。
-/

example (s t: Set ℝ ) (hx : x ∈ s ∪ t) : s.Nonempty ∨ t.Nonempty :=
by
  cases hx with
  | inl h => sorry
  | inr h => sorry
example (s t: Finset ℝ) (hx : x ∈ s ∪ t) : s.Nonempty ∨ t.Nonempty :=
by
--  cases hx -- 会失败
  rw [mem_union] at hx
  cases hx with
  | inl h =>
    left
    use x
  | inr h =>
    right
    use x
/-
由于定义问题，当假设中的表达是有限集合的时候，部分策略会无法直接使用。
此时只要`rw`一下就可以了。
-/

def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε
notation "limₙ " => sLim
theorem sLim_imp_bd (hx : limₙ x a) : ∃ C, ∀ n, |x n| ≤ C :=
by
  specialize hx 1 (by norm_num)
  /-
  在没有`by norm_num`的情况下（效果等于`zero_lt_one0`）会得到
  `0 < 1 → ∃ N, ∀ (n : ℕ), N ≤ n → |x n - a| < 1`
  通过`by norm_num`我们直接给出了`0 < 1`的证明，从而
  得到了`∃ N, ∀ (n : ℕ), N ≤ n → |x n - a| < 1`
  -/
  obtain ⟨K,hK⟩ := hx
  let I := range K.succ
  /-
  `let`策略可以根据已有变量定义新的变量。
  -/
  have hne : I.Nonempty := by exact nonempty_range_succ
  let J := I.image |x|
  let B := J.max' (by exact Nonempty.image hne |x|)
  use max B (|a| + 1)
  intro n
  by_cases hn : n ≤ K
 -- In this case |x n| ≤ B because |x n| ∈ J
  · have hx_in_J : |x n| ∈ J :=
      mem_image_of_mem |x| (mem_range_succ_iff.mpr hn)
    apply le_max_of_le_left
    exact le_max' J |x n| hx_in_J
 -- In this case |x n| ≤ (|a| + 1) since K ≤ n
  · apply le_max_of_le_right
    have : |x n| < |a| + 1 :=
    calc
      |x n| = |x n - a + a| := by ring
      _ ≤ |x n - a| + |a| := abs_add (x n - a) a
      _ < 1 + |a| := add_lt_add_right (hK n (le_of_not_le hn)) |a|
      _ = |a| + 1 := by ring
    linarith

-- # CS类型转换

variable (n : ℕ) (x : ℝ)
#check x = n
/-
在Lean中面对不同的类型，可能会执行`cast`（类型转换）`coercion`（强制类型提升）
因为不同的类型的变量是不可以相等的。但是如自然数和实数显然是有关联的类型。
这时你就能看到x = ↑n，其中`↑`表示类型提升，是把n从自然数提升到实数，
这样等式两侧的类型就重新变得相等，这个等式就得到了Lean的认可。
-/

example (a b : ℕ) (c : ℤ) : (a + b : ℕ) + (c : ℤ) = (((a : ℤ) + (b + c : ℚ) : ℝ) : ℂ) :=
by
  push_cast
  apply add_assoc
example (n : ℕ) (z : ℤ) (h : n - z < (5 : ℚ)) : n - z < 5 :=
by
  norm_cast at h
/-
除了可以直接`rfl`的式子之外，你可以尝试`push_cast`和`norm_cast`来推进证明。
-/

example (a b c: ℕ) (h : c = a + b) : (a : ℤ) - c = -b :=
by
  rw [h]
  push_cast
  exact sub_add_cancel_left _ _
/-
在有类型差异的情况下，可以尝试先`push_cast`然后再`exact?`。
在这种情况下，`exact?`的结果可能会有点不准，此时Lean会再次给出建议
`sub_add_cancel'` has been deprecated, use `sub_add_cancel_left` instead
此时可能还需要人工确认合适的参数。
-/

-- # SC结构和类别
@[ext]
structure Plane where
  x : ℤ
  y : ℤ
/-
在Lean中有很多类型，如`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`, `ℕ → ℝ`等。
使用`structure`语法可以定义新的语法结构。其中x, y被称为"fields"。
-/

namespace Plane
def A : Plane where
  x := 1
  y := 3
def B : Plane := ⟨-4,7⟩
def origin : Plane := {x := 0, y:= 0}
/-
上述三种语法是等价的三种定义类型中的元素的方法。
-/

#eval A.x
#check Plane.ext A B
/-
你可以在点后加元素的"fields"的名字，可以调用出它的赋值。
由于我们在定义`Plane`的时候加了`@[ext]`，我们可以使用`ext`来证明两个
类型是`Plane`的对象相等。
-/

example : (⟨1,2⟩ : Plane) = ⟨1,n - n + 2⟩ := by
  ext
  · rfl
  · dsimp
    rw [sub_self, zero_add]
/-
使用`ext``dsimp`之后就可以按之前学的内容证明了。
-/

def my_addition (P Q : Plane) : Plane := ⟨P.x + Q.x, P.y + Q.y⟩
instance : Add Plane where
  add := my_addition
#check A + B
/-
如此我们使用`def`和`instance`为`Plane`定义了一个加法操作。
-/

lemma add_def (P Q : Plane) : P + Q = ⟨P.x + Q.x, P.y + Q.y⟩ := rfl
lemma add_x (P Q : Plane) : (P + Q).x = P.x + Q.x := rfl
lemma add_y (P Q : Plane) : (P + Q).y = P.y + Q.y := rfl
/-
定义完类似的结构后，建议为其定义一些基本的lemma以方便后续使用。
-/

/-
在笔记中还有一系列的引理，尤其是关于零和负数的定义，此处略。
当你证明完这些引理后，你就可以定义`AddCommGroup`的实例了：
instance : AddCommGroup Plane where
  add_assoc     := my_add_assoc
  zero_add      := my_zero_add
  add_zero      := my_add_zero
  add_left_neg  := my_neg_add_self
  add_comm      := my_add_comm
  nsmul := nsmulRec
  zsmul := zsmulRec
它使得Lean知道`Plane`是一个加法交换群，
从而可以使用Mathlib中关于加法交换群的所有定理。
同时，由于其是加法交换群，Lean也可以允许对它使用`•`来数乘。
-/

end Plane

class MyGroup (G : Type) extends Mul G, Inv G, One G where
  ax_assoc    : ∀ x y z : G, (x * y) * z = x * (y * z)
  ax_mul_one  : ∀ x : G, x * 1 = x
  ax_one_mul  : ∀ x : G, 1 * x = x
  ax_mul_inv  : ∀ x : G, x * x⁻¹ = 1
  ax_inv_mul  : ∀ x : G, x⁻¹ * x = 1
/-
上面我们定义了一个群，群应该有满足结合律的乘法`*`，逆元`⁻¹`，单位元`1`。
我们通过`extends`简化了部分定义，在`Mul`、`Inv`和`One`上按ctrl左键可以跳转。
其它的引理需要我们自己定义。
当然，`Group`已经在Mathlib中定义好了，这里只是为了练习自己定义。
-/

variable {G : Type} [MyGroup G]
namespace MyGroup

lemma inv_eq (x y : G) (h : x * y = 1) : x⁻¹ = y :=
calc
  x⁻¹ = x⁻¹ * 1         := by rw [ax_mul_one]
  _   = x⁻¹ * (x * y)   := by rw [h]
  _   = (x⁻¹ * x) * y   := by rw [ax_assoc]
  _   = 1 * y           := by rw [ax_inv_mul]
  _   = y               := by rw [ax_one_mul]
lemma inv_mul (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
by
  apply inv_eq
  rw [ax_assoc, ←ax_assoc y, ax_mul_inv, ax_one_mul, ax_mul_inv]
/-
可以注意到，这里的证明就是很平常的之前的证明方法。
-/

end MyGroup

variable {G H : Type} [Group G] [Group H]
example (x : G) : (x⁻¹)⁻¹ = x :=
by
  exact DivisionMonoid.inv_inv x
/-
这里我们直接使用了Mathlib中已经定义好的`Group`结构。
绝大多数显然的结论可以`exact?`获得。
-/
example (x y : G) : x*y*x⁻¹*y^2*y⁻¹^2*x*y⁻¹*x^2 = x^3 :=
by
  group
/-
实际上还可以使用`group`完成只需要群公理就可以完成的等式证明。
如果需要假设，则需要`rw`。
-/

open Set

def Trivial_subgroup : Subgroup G where
  carrier := {1}
  mul_mem' := by
    intro a b ha hb
    rw [mem_singleton_iff] at *
    rw [ha, hb, one_mul]
  one_mem' := rfl
  inv_mem' := by
    intro a ha
    dsimp at ha ⊢
    rw [mem_singleton_iff] at *
    rw [ha, inv_one]
/-
要定义`Subgroup G`，需要包含以下字段：
  `carrier` - `G`的一个子集（子群的元素）。
  `mul_mem'` - 证明如果`g`和`h`属于`carrier`，那么`g * h`也属于`carrier`，
  `one_mem'` - 证明`1`属于`carrier`，
  `inv_mem'` - 证明如果`g ∈ carrier`，那么`g⁻¹ ∈ carrier`。
这里以定义平凡子群为例进行了说明。
-/

#check G →* H
def trivial_hom : G →* H where
  toFun := fun _ ↦ 1
  map_one' := rfl
  map_mul' := by
    intro x y
    dsimp
    exact self_eq_mul_left.mpr rfl
/-
对群`G`和`H`，`G →* H`是从`G`到`H`的群同态的`Type`。
这是一个包含以下字段的结构：
  `toFun` 一个函数 `G → H`，
  `map_mul'` 一个证明，证明 `toFun (g * g') = toFun g * toFun g'`，
  `map_one'` 一个证明，证明 `toFun 1 = 1`。
这里我们定义了一个平凡同态为例，将`G`中的每个元素映射到`H`中的单位元`1`。
-/
