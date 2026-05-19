# Hall の結婚定理：パターンマッチ指向スタイルでの定式化

## 定理

二部グラフ $G = (X \cup Y, E)$ が X を覆う完全マッチングを持つ ⇔ X の任意の部分集合 S について |N(S)| ≥ |S|（**Hall 条件**）。

本ファイルでは、特に **Hall 条件のパターン化** と、その帰結としての **完全マッチングの取り出し** に焦点を当てる。Hall の定理の本体（条件 → マッチング存在）の証明は induction によるため pattern syntax で書く意義が薄く、ここでは扱わない。

---

## 基本定義

### Lean 4 での定義

```lean
variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

structure BipartiteGraph (X Y : Type) where
  edge : Set (X × Y)

def neighborhood (G : BipartiteGraph X Y) (S : Finset X) : Finset Y :=
  Finset.univ.filter (fun y => ∃ x ∈ S, (x, y) ∈ G.edge)

def hallCondition (G : BipartiteGraph X Y) : Prop :=
  ∀ S : Finset X, S.card ≤ (neighborhood G S).card

def perfectMatching (G : BipartiteGraph X Y) (f : X → Y) : Prop :=
  Function.Injective f ∧ ∀ x, (x, f x) ∈ G.edge

theorem hall (G : BipartiteGraph X Y) (h : hallCondition G) :
    ∃ f : X → Y, perfectMatching G f
```

`hallCondition` は `∀ S : Finset X` という二階の量化、補助述語 `neighborhood`、カーディナリティ比較 `S.card ≤ ...` を経由する。`perfectMatching` も「単射性」と「∀ x, ...」の二つの conjunct で書かれる。

---

## A. Hall 条件のパターン化：素朴な版

Hall 条件の否定は「**ある k に対して k+1 個の左頂点が k 個の右頂点しか持たない**」である。これを「悪い構造の不在」として直接書く：

```
HallCondition (E : multiset (X × Y)) ≡
    ¬ ( X matches $x₁ :: $x₂ :: ... :: $xₖ₊₁ :: _
      ∧ Y matches $y₁ :: $y₂ :: ... :: $yₖ :: _
      ∧ ¬ ( E matches ((#x₁ | #x₂ | ... | #xₖ₊₁),
                       ($y & !#y₁ & !#y₂ & ... & !#yₖ)) :: _ ) )
```

### 読み解き

- 最外の `¬ (... ∧ ... ∧ ¬ ...)`: 「以下を満たす選び方は **存在しない**」
- `X matches $x₁ :: ... :: $xₖ₊₁ :: _`: X から k+1 個の相異なる左頂点を取る（multiset `::` の挙動より相異性が自動）
- `Y matches $y₁ :: ... :: $yₖ :: _`: Y から k 個の相異なる右頂点を取る
- `¬ E matches ((#x₁ | ... | #xₖ₊₁), ($y & !#y₁ & ... & !#yₖ)) :: _`:
  - 取った x たちのいずれか（`(#x₁ | ... | #xₖ₊₁)` の or パターン）から、
  - 取った y たちのいずれでもない右頂点（`$y & !#y₁ & ... & !#yₖ` の and-not 結合）へ、
  - 向かう辺が **E に存在しない**

つまり「{x₁,...,xₖ₊₁} から出る辺の終点はすべて {y₁,...,yₖ} に入る」（= N(X') ⊆ Y' で |X'| = k+1 > k = |Y'|、Hall 条件違反）。

### 複雑さの源

1. **可変長パターン** `x₁ :: ... :: xₖ₊₁`：パラメータ k に依存する長さの列挙。pattern syntax の正式な構成要素として「可変長 cons 連鎖」を導入するか、メタ的に展開する必要がある。
2. **三重否定**：`¬ (... ∧ ¬ ...)` という構造はド・モルガンで畳めば「∀ x's, ∀ y's, ∃ edge」と読めるが、pattern として書くと読みづらい。
3. **or パターンと and-not 結合**：`#x₁ | ... | #xₖ₊₁` と `$y & !#y₁ & ... & !#yₖ` の k 依存の連鎖が二重に出現。

このまま論文 statement に置くのは厳しい。

---

## B. Hall 条件のパターン化：bipartite_graph matcher 経由（推奨）

新しい matcher `bipartite_graph` を導入し、「**部分グラフ閉包**」を表すパターンコンストラクタ `⤳` を提供する：

```
G matches $X' ⤳ $Y'    as bipartite_graph X Y
```

意味：X' ⊆ X、Y' ⊆ Y で、X' から出るすべての辺が Y' に入る（つまり N_G(X') ⊆ Y'）。X' と Y' はそれぞれ pattern 変数として束縛される。

これを使うと Hall 条件は：

```
HallCondition (G : bipartite_graph X Y) ≡
    ¬ ( G matches $X' ⤳ $Y'   where |X'| > |Y'|
        as bipartite_graph X Y )
```

**2行に縮む**。素朴版の三重否定・可変長・or/and-not 結合がすべて matcher 内部に押し込まれる。

### Matcher 内部での実装

`bipartite_graph` matcher は `⤳` パターンコンストラクタを次のように分解する：

```
matcher bipartite_graph X Y where
  | $X' ⤳ $Y' as (subset X, subset Y) with
    | $G ->
        matchAll G as set (X × Y) with
          | _ ->
              -- X' は X の部分集合、Y' = N_G(X') の上界
              let X' := chosen subset of X
              let Y' := chosen subset of Y
              guard (∀ (x, y) ∈ G. x ∈ X' → y ∈ Y')
              return (X', Y')
```

詳細は matcher の定義（別途）に譲るが、**「X' から出る辺はすべて Y' に入る」という構造的拘束を matcher 側で実装** することで、利用者側の pattern は劇的に簡潔になる。

### 完全マッチングのパターン化

同じく `bipartite_graph` matcher に `matching_of` パターンコンストラクタを用意する：

```
G matches $f    as matching_of (bipartite_graph X Y)
```

意味：`f : X → Y` は単射で、∀ x. (x, f x) ∈ E（つまり X を覆う完全マッチング）。

これにより Hall の定理の主張は：

```
theorem hall (G : bipartite_graph X Y) (h : HallCondition G)
    matches $f
    as matching_of G
```

Lean 版の `∃ f : X → Y, Function.Injective f ∧ ∀ x, (x, f x) ∈ G.edge` が、pattern 一個に吸収される。

---

## C. 主張と適用の対応

Hall の定理を **適用** する場面でも、同じ pattern が match の腕として現れる：

```
-- 例：完全マッチング f を取り出して使う
match G as matching_of G with
| $f => 
    -- ここで f : X → Y は完全マッチングとして使える
    ...
exhaustive by hall G h_hall
```

pwl-ramsey の `pigeonhole_edges`、pwl-schur の `color_dichotomy` と同じ構造：

- **補題側**: `matches $f as matching_of G`（Hall の主張）
- **適用側**: `match G as matching_of G with | $f => ...`（同じ pattern を destructure）
- **接続子**: `exhaustive by hall G h_hall`

「主張と適用が同じパターン言語に閉じる」という研究プログラムの核心が、Hall でも具体化される。

---

## D. 比較

### 量的比較

| | Lean 4 | パターンマッチ指向（素朴版） | パターンマッチ指向（matcher 経由） |
|---|---|---|---|
| Hall 条件の定義 | `∀ S : Finset X, S.card ≤ (neighborhood G S).card` | 三重否定 + 可変長パターン | `¬ (G matches $X' ⤳ $Y' where ...)`（2行） |
| 完全マッチングの定義 | `∃ f, Injective f ∧ ∀ x, (x, f x) ∈ E` | （素朴版なし） | `G matches $f as matching_of G` |
| 補助述語 | `neighborhood`、`hallCondition`、`perfectMatching` | （多数のメタ的展開） | 0（すべて matcher 内部） |
| 高階の量化 | `∀ S : Finset X` | 可変長 cons でパターン化 | matcher 内部に隠蔽 |

### 設計上の判断

- **素朴版は statement として論文に出すには複雑すぎる**。可変長パターンと三重否定の組み合わせは読者に負担をかける。
- **matcher 経由版は読みやすいが、新規 matcher の設計コストが高い**。`⤳` の意味論と健全性を別途厳密化する必要がある。
- **論文 narrative**: 素朴版を「naive 表現」として一度示し、その複雑さを動機として bipartite_graph matcher を導入する流れが説得力を持つ。「matcher 抽象が statement を救う」という主張の具体例になる。

---

## E. Matcher 設計の論点

### `⤳` パターンの非決定性

`$X' ⤳ $Y'` は X' と Y' のペアを **すべての可能な選び方** で列挙する非決定的パターン。pwl-ramsey の `multiset` matcher の `$x :: $xs` と同種の非決定性。

利用例：
```
-- Hall 条件違反の証拠を探す
matchAll G as bipartite_graph X Y with
  | $X' ⤳ $Y' where |X'| > |Y'| -> (X', Y')
```

複数の (X', Y') ペアが Hall 条件違反を示しうるので、結果はリスト。`matchAll` で全列挙、`match` で単一の存在判定。

### 計算量

- `⤳` の判定：左 X' を固定すると N_G(X') は決定論的に計算でき、Y' ⊇ N_G(X') の選び方は 2^|Y \ N(X')| 通り。X' の選び方が 2^|X| 通りで、全体としては指数的だが有限。
- `matching_of`：二部マッチングは Hopcroft–Karp で O(E √V)。判定は多項式。

健全性の議論：`matcher bipartite_graph` の定義が正確に `⤳` と `matching_of` のセマンティクスを実現しているかを別途証明する必要がある。

### Sym2 / multiset matcher との関係

二部グラフは Sym2 ではなく X × Y 上の集合なので、pwl-ramsey の `Sym2 (Fin 6)` のような順序なし対 matcher は使えない。`bipartite_graph X Y` は新規 matcher として独立に設計する。ただし内部実装は `set (X × Y)` または `multiset (X × Y)` への reduction で書けるはず。

---

## まとめ

- Hall 条件の素朴なパターン化は可変長と三重否定で複雑化する
- `bipartite_graph` matcher と `⤳` / `matching_of` パターンコンストラクタを導入すると、statement が劇的に簡潔になる
- Hall の定理の主張・適用は、ramsey / schur と同じく「pattern 一個」に閉じる
- 論文 narrative としては、**「素朴版で複雑さを示し、matcher 抽象で救う」** という流れが効く

定理本体の証明（Hall 条件 → 完全マッチング存在）は induction または augmenting path 法で行う。これは pattern syntax 固有の利点が薄いため、本ファイルでは扱わない。証明側ではなく **statement 側で matcher 抽象が威力を発揮する** 例として位置付ける。
