# パターンマッチ指向証明：言語設計

## 背景と動機

Egison および λP 型システムの研究の延長として、**パターンマッチを定理の主張と証明の構成要素として直接用いる証明スタイル**（pattern-match-oriented proof）を提案する。Ramsey R(3,3)=6 を典型例として設計したパターンマッチ指向証明では、定理の主張をパターン構文で直接表現できる：

```
theorem ramsey_3_3_6 (edge : Sym2 (Fin 6) → Color)
    matches ($x, $y) → $c :: (#y, $z) → #c :: (#z, #x) → #c :: _
    as multiset (Sym2 (Fin 6) → Color)
```

この提案の核心的価値は **証明の簡潔性ではなく、定理の主張・適用の双方を informal な数学的記述に近い形でパターンとして書ける** ことにある。具体的には：

- `monochromatic` のような補助定義を経由せず、構造を直接表現
- 存在量化、相異性、非線形性（同色性）がパターン構文に吸収される
- 数学者が思考するときの「三角形・単色」という構造的把握と一致
- 定理の適用も同じパターン言語で行える：定理が成り立つということは「対象がこのパターンにマッチする／しない」という主張として読め、適用は `matches P as M` 命題に対する推論として一様に扱える

### 主張と適用の一致：具体例

完全な作業例は [pwl-ramsey.md](pwl-ramsey.md) を参照。最も鮮明な対応として、補題 `pigeonhole_edges` の主張側のパターン

```
matches ($v, $x) → $c :: (#v, $y) → #c :: (#v, $z) → #c :: _
    as multiset (Sym2 (Fin 6) → Color)
```

は、`ramsey_3_3_6` の証明中の `match` 腕

```
| ($v, $x) → $c :: (#v, $y) → #c :: (#v, $z) → #c :: _ => ...
```

と文字通り同一の構文を持ち、`exhaustive by pigeonhole_edges edge` がこの一致を補題として要求する。主張側では「∃ 形の命題」として、適用側では「destructuring」として、同じパターン文字列が双方向に使われる。この対応は `two_color_exhaustive` と内側の `match` でも同様に繰り返されており、原理が二段で働くことが確認できる。

組合せ論的定理（Erdős–Szekeres、Schur、Hall）でも同様の利点が得られると予想される。

## 研究プログラムにおける位置付け

Egison の三本柱（λP, テンソル記法, CAS）に対し、これは λP の自然な延長である。長期的には **「パターン = 構造記述言語」という思想の到達点** として位置付ける：

- λP：パターンで関数を書く
- テンソル記法：パターンでテンソル演算を書く
- パターンマッチ指向証明：**パターンで定理を書く**

## 実装方針

### 最小核言語をフルスクラッチで

Lean 4 拡張や Egison ベースの拡張ではなく、**新規の最小核言語** を一から実装する。設計の自由度を優先する。

### 実装言語：Haskell

- 依存型ライクな構造の実装ノウハウが豊富
- 既存の Egison 実装との連続性
- パーサ・pretty printer・テストフレームワーク（megaparsec、prettyprinter、QuickCheck）が揃っている

## 核言語の設計

### ベース

- 依存関数型 `(x : A) → B`
- 宇宙 `Type`（1宇宙）
- 帰納型
- Martin-Löf identity type `Id A x y` と path induction

CoC や MLTT 全体は実装せず、最小核に絞る。

### 新規機能

#### 1. `matches P as M` 命題

- 意味論：`∃ binding, P[binding] matches e by matcher M`
- パターン変数を存在量化された束縛変数として扱う
- 非線形パターン `#c` は equality reflection として展開

#### 2. 非自由データ型用 matcher

- multiset matcher（プリミティブとして組み込む）
- Sym2 matcher
- quotient type による定式化ではなく、プリミティブ matcher として導入（実装簡素化）

#### 3. `exhaustive by lemma` 構文

```
Γ ⊢ e : T   Γ ⊢ lemma : e matches (p₁ | ... | pₙ) as M
Γ, x₁:τ₁ ⊢ b₁ : U   ...   Γ, xₙ:τₙ ⊢ bₙ : U
─────────────────────────────────────────────────────
Γ ⊢ match e as M with | p₁ ⇒ b₁ | ... | pₙ ⇒ bₙ exhaustive by lemma : U
```

- 補題が選言パターンの網羅性を保証
- ネストした match の `_` 節も同様の構造で型付け

### Pattern matching as derived form

通常の `match` 構文は `matches` 命題と eliminator から派生形として定義する（Coq の Equations プロジェクトに近い設計）。これにより健全性証明が分離できる。

## 健全性の議論

健全性は以下の2点に帰着：

1. `matches P as M` 命題の意味論的妥当性（matcher の定義と整合）
2. `exhaustive by` による case 分析の網羅性（補題による）

核言語自体の type safety（progress + preservation）を別途証明する。

### 技術的制約

- **非線形パターンは decidable equality を要求**：`Color` のような有限・decidable 型でのみ使用可能
- **マッチング判定の決定可能性**：multiset matcher については Egison の既存アルゴリズムを借用

## Formalize する例

### 中心的な例

- **Ramsey R(3,3) = 6**：詳細あり（[pwl-ramsey.md](pwl-ramsey.md)）。`multiset` matcher + 非線形 `#c`
- **Schur S(2) = 4**：詳細あり（[pwl-schur.md](pwl-schur.md)）。`set` matcher + 値パターン `#(x+y)` を追加
- **鳩の巣原理（一般形）**：`multiset` matcher の典型例

### 拡張例

- **Erdős–Szekeres**：順序付き multiset matcher の追加実装が必要
- **Hall の結婚定理**：詳細あり（[pwl-hall.md](pwl-hall.md)）。`bipartite_graph` matcher による Hall 条件と完全マッチングの pattern 化

## 関連研究

- **Egison**（APLAS 2018、Programming 2020）：基盤
- **λP**：型システムの直接の前身
- **Coq の Equations**（Sozeau）：dependent pattern matching
- **Agda の with abstraction**（McBride）
- **Views**（Wadler、McBride の deriving）
- **Idris**（Brady）
- **Pattern fragment**（Miller）
