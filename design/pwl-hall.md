# Hall の結婚定理：パターンマッチ指向スタイルでの定式化

以下は現在の設計を示す証明スケッチである。提案言語の実装と証明の検査に
必要な作業は [review.md](review.md) に記す。

## 定理

二部グラフ $G = (X \cup Y, E)$ が X を覆う完全マッチングを持つ ⇔ X の任意の部分集合 S について |N(S)| ≥ |S|（**Hall 条件**）。

本ファイルでは、**Hall 条件のパターン化**、定理の主張と適用、
および **完全マッチングの取り出し** を説明する。
一般形の存在証明とマッチャーの正しさの証明に必要な作業は、
[設計上の課題](review.md) §4 にまとめる。

---

## 基本定義

### Lean 4 での定義

```lean
variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

structure BipartiteGraph (X Y : Type) where
  edge : Set (X × Y)

noncomputable def neighborhood (G : BipartiteGraph X Y) (S : Finset X) : Finset Y := by
  classical
  exact Finset.univ.filter (fun y => ∃ x ∈ S, (x, y) ∈ G.edge)

def hallCondition (G : BipartiteGraph X Y) : Prop :=
  ∀ S : Finset X, S.card ≤ (neighborhood G S).card

def perfectMatching (G : BipartiteGraph X Y) (f : X → Y) : Prop :=
  Function.Injective f ∧ ∀ x, (x, f x) ∈ G.edge

theorem hall (G : BipartiteGraph X Y) (h : hallCondition G) :
    ∃ f : X → Y, perfectMatching G f
```

`hallCondition` は `∀ S : Finset X` という二階の量化、補助述語 `neighborhood`、カーディナリティ比較 `S.card ≤ ...` を経由する。`perfectMatching` も「単射性」と「∀ x, ...」の二つの conjunct で書かれる。

---

## A. Hall 条件のパターン化

matcher `bipartite_graph` は、「**部分グラフ閉包**」を表すパターンコンストラクタ `⤳` を提供する：

```
G matches $X' ⤳ $Y'    as bipartite_graph X Y
```

意味：X' ⊆ X、Y' ⊆ Y で、X' から出るすべての辺が Y' に入る（つまり N_G(X') ⊆ Y'）。X' と Y' はそれぞれ pattern 変数として束縛される。

これを使うと Hall 条件は：

```
HallCondition (G : BipartiteGraph X Y) ≡
    ¬ ( G matches $X' ⤳ $Y'   where |X'| > |Y'|
        as bipartite_graph X Y )
```

（`BipartiteGraph X Y` は**型**、`bipartite_graph X Y` はその型に対する **matcher**。型注釈には型を、`as` 節には matcher を書く。）

この2行は、Hall 条件に違反する部分集合の組が存在しないことを表す。
部分集合の選択と近傍の包含関係は matcher の意味論が与える。

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

`bipartite_graph` matcher から、完全マッチングを取り出す matcher を作る変換 `matching_of` を用意する：

```
G matches $f    as matching_of (bipartite_graph X Y)
```

意味：`f : X → Y` は単射で、∀ x. (x, f x) ∈ E（つまり X を覆う完全マッチング）。

これにより Hall の定理の主張は：

```
theorem hall (G : BipartiteGraph X Y) (h : HallCondition G)
    matches $f
    as matching_of (bipartite_graph X Y)
```

Lean 版の `∃ f : X → Y, Function.Injective f ∧ ∀ x, (x, f x) ∈ G.edge` が、pattern 一個に吸収される。

---

## B. 主張と適用の対応

Hall の定理を **適用** する場面でも、同じ pattern が match の腕として現れる：

```
-- 例：完全マッチング f を取り出して使う
match G as matching_of (bipartite_graph X Y) with
| $f => 
    -- ここで f : X → Y は完全マッチングとして使える
    ...
exhaustive by hall G h_hall
```

pwl-ramsey の `pigeonhole_edges_at`、pwl-schur の `color_dichotomy` と同じ構造：

- **補題側**: `matches $f as matching_of (bipartite_graph X Y)`（Hall の主張）
- **適用側**: `match G as matching_of (bipartite_graph X Y) with | $f => ...`（同じ pattern を destructure）
- **接続子**: `exhaustive by hall G h_hall`

「主張と適用が同じパターン言語に閉じる」という研究プログラムの核心が、Hall でも具体化される。

---

## C. Lean 4 との比較

| | Lean 4 | パターンマッチ指向 |
|---|---|---|
| Hall 条件の定義 | `∀ S : Finset X, S.card ≤ (neighborhood G S).card` | `¬ (G matches $X' ⤳ $Y' where …)` |
| 完全マッチングの存在 | `∃ f, Injective f ∧ ∀ x, (x, f x) ∈ E` | `G matches $f as matching_of (bipartite_graph X Y)` |
| 構造を述べる補助述語 | `neighborhood`、`perfectMatching` | `⤳` と `matching_of` の意味論で表す |
| 部分集合の量化 | `∀ S : Finset X` | matcher が部分集合を選択する |

パターンマッチ指向版では、近傍の包含関係と完全マッチングの性質を
matcher が与える。`⤳` と `matching_of` の型・意味論・健全性を明示し、
利用者が導入する matcher についても同じ条件を検査できるようにする必要がある。

---

## D. Matcher 設計の論点

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
- `matching_of`：完全マッチングの存在判定と1個の構成には、Hopcroft–Karp の O((|E|+|V|)√|V|) のアルゴリズムを使える（V は頂点集合。出典：[Hopcroft と Karp の論文](https://epubs.siam.org/doi/10.1137/0202019)）。すべての完全マッチングを `matchAll` で列挙するコストは、出力するマッチングの個数にも依存する。

健全性の議論：`matcher bipartite_graph` の定義が正確に `⤳` パターンと `matching_of` による matcher の意味論を実現しているかを別途証明する必要がある。

### Sym2 / multiset matcher との関係

二部グラフは Sym2 ではなく X × Y 上の集合なので、pwl-ramsey の `Sym2 (Fin 6)` のような順序なし対 matcher は使えない。`bipartite_graph X Y` は新規 matcher として独立に設計する。ただし内部実装は `set (X × Y)` または `multiset (X × Y)` への reduction で書けるはず。

---

## まとめ

- Hall 条件は、`⤳` パターンで表す「近傍を含む部分集合の組」に対する大きさの条件として述べる。
- 完全マッチングの存在は、`matching_of` が与える matcher とパターン変数 `$f` で述べる。
- Hall の定理を適用するときも同じパターンを使い、`exhaustive by hall G h_hall` で f を取り出す。

定理本体の証明には帰納法または増加路（マッチングに含む辺と含まない辺を交互に通り、
辺の選び方を入れ替えてマッチングを大きくする経路）を使う。
一般形の存在証明と matcher の健全性証明の完成は、[設計上の課題](review.md) §4 に記す。
