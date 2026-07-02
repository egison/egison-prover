# パターンマッチ指向証明：言語設計

## 背景と動機

Egison および λP 型システムの研究の延長として、**パターンマッチを定理の主張と証明の構成要素として直接用いる証明スタイル**（pattern-match-oriented proof）を提案する。

Ramsey R(3,3)=6 を典型例として設計したパターンマッチ指向証明では、定理の主張をパターン構文で直接表現できる：

```
theorem ramsey_3_3_6 (edge : Sym2 (Fin 6) → Color)
    matches ($x, $y) → $c :: (#y, $z) → #c :: (#z, #x) → #c :: _
    as multiset (Sym2 (Fin 6) → Color)
```

この提案の核心的価値は **証明の簡潔性ではなく、定理の主張・適用の双方を informal な数学的記述に近い形でパターンとして書ける** ことにある：

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

と文字通り同一の構文を持ち、`exhaustive by pigeonhole_edges edge` がこの一致を補題として要求する。主張側では「∃ 形の命題」として、適用側では「destructuring」として、同じパターン文字列が双方向に使われる。

## scope：組合せ的存在定理に focus

本研究は **組合せ的存在定理**（combinatorial existence theorems）を主たる射程とする。これは「特定分野への限定」ではなく、**証明スタイルへの focus** である：

組合せ的存在定理は数学全体に偏在する：
- グラフ理論（Ramsey、Hall、Dilworth、König）
- 数論的組合せ論（Schur、van der Waerden、Erdős–Ko–Rado）
- 形式言語と計算理論（Pumping lemma、Myhill–Nerode）
- 順序理論（Dilworth、Mirsky）
- 加法的組合せ論（Cauchy–Davenport）
- 離散幾何（Sperner、Helly の有限版）

これらに共通する構造的特徴：

> **container + size 制約 + 構造的 witness**

| | container | size 制約 | 構造的 witness |
|---|---|---|---|
| Ramsey | 辺の multiset | 5辺 > 2色 × 2（⌈5/2⌉ = 3） | 単色三角形 |
| Schur | 彩色関数の set | 5 > S(2) = 4 | 同色加法組 |
| Hall | 二部グラフ | Hall 条件 | マッチング |
| Pumping | DFA 走行の list | \|w\| ≥ \|Q\| | 同状態の2回訪問 |

この共通構造が **pattern style と一対一に対応**する：

- container → 適切な matcher（multiset / set / list / graph）
- size 制約 → matcher の意味論またはハイパシスとして与えられる
- 構造的 witness → 非線形パターン変数および pattern コンストラクタで syntactic に表現

### scope 外の定理タイプ

明示的に scope 外として外す：

- **濃度・割り切り中心の主張**（例：Lagrange の `\|H\| ∣ \|G\|`）：pattern style は notation 改善以上にならない
- **等式・準同型中心の主張**（例：環の準同型定理）：等式変形主体で pattern の出番が薄い
- **解析・連続性が本質の主張**：離散的 destructure を持たない
- **帰納が主役の主張**：pattern 抽象の恩恵が小さい

この境界線は pattern style の限界というより、**pattern style が genuinely 効く対象の characterization** である。研究の主張の純度を保つために scope を明示的に画定する。

## 統一的な主張：鳩の巣論法の syntactic 表現

本研究の最も重要な observation：

> **「鳩の巣論法 = 非線形パターン `#x` による構造表現」**

Ramsey、Schur、Pumping の三例すべてにおいて、定理の本質は「ある容器の中に size 制約があれば、同じ何かが繰り返し現れる箇所がある」という鳩の巣構造である。これを pattern として書くと：

```
container matches _ ... $x ... #x ... _    as appropriate_matcher
```

の形に統一される：

- Ramsey: `→ $c :: ... → #c :: ... → #c :: _`（同色辺が3本）
- Schur: `→ $col :: ... → #col :: #(x+y) → #col :: _`（同色値が加法閉）
- Pumping: `_ ++ $q :: _ ++ #q :: _`（同状態が2回）

**非線形パターン `#x` が鳩の巣論法の native な構文** である。これは pattern style の言語設計と数学的内容の深い対応であり、本研究の中核的な貢献の一つ。

Hall は鳩の巣論法とは異なるが、**matcher による主張側の語彙拡張**（`⤳` パターンコンストラクタ）という第二の中核 contribution の旗艦例である。

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
- 非線形パターン `#c` は等式制約として展開（主張側の意味論は命題等式 `Id` で与え、match 実行・`decide` 時に decidable equality で判定する）
- target は定理パラメータでも派生値でもよい（pwl-pumping を参照）

#### 2. 非自由データ型用 matcher

組合せ的存在定理に必要な matcher を体系的に揃える：

- **`multiset` matcher**：順序なし、重複あり（Ramsey の辺集合）
- **`set` matcher**：順序なし、取り出しても target が減らない＝同一要素の重複取り出し可（Schur の彩色。x = y を許す主張に必須）
- **`list` matcher**：順序あり、重複あり（Pumping の DFA 走行）
- **`Sym2` matcher**：順序なしペア（無向辺）
- **構造的 matcher**：`bipartite_graph`、その他の数学的構造を内包する matcher（Hall）

quotient type による定式化ではなく、プリミティブ matcher として導入（実装簡素化）。

#### 3. `exhaustive by lemma` 構文

```
Γ ⊢ e : T   Γ ⊢ lemma : e matches (p₁ | ... | pₙ) as M
Γ, x₁:τ₁ ⊢ b₁ : U   ...   Γ, xₙ:τₙ ⊢ bₙ : U
─────────────────────────────────────────────────────
Γ ⊢ match e as M with | p₁ ⇒ b₁ | ... | pₙ ⇒ bₙ exhaustive by lemma : U
```

- 補題が選言パターンの網羅性を保証
- ネストした match の `_` 節も同様の構造で型付け

#### 4. 値パターン `#(expr)`

- pwl-schur で導入。pattern 中の位置に `#(expr)` を書くと、その位置の値が `expr` と等しいことを要求
- 算術式（`#(x+y)`、`#(a*x + b*y)` など）に拡張可能
- 範囲制約（target に該当値がなければマッチ失敗）も自動で扱う

#### 5. 派生値への `matches`（pwl-pumping で導入）

- target を定理パラメータの **派生値** にできる
- 例：`M.run(w) matches _ ++ $q :: _ ++ #q :: _ as list ...`
- 制約：matcher として整合する型に値が落ちる場合のみ
- 計算的構造（アルゴリズム trace、走行列など）を扱える

### Pattern matching as derived form

通常の `match` 構文は `matches` 命題と eliminator から派生形として定義する（Coq の Equations プロジェクトに近い設計）。これにより健全性証明が分離できる。

## 健全性の議論

健全性は以下の3点に帰着：

1. `matches P as M` 命題の意味論的妥当性（matcher の定義と整合）
2. `exhaustive by` による case 分析の網羅性（補題による）
3. 各 matcher の declarative semantics と operational semantics の一致

核言語自体の type safety（progress + preservation）を別途証明する。

### 技術的制約

- **非線形パターンの match 実行は decidable equality を要求**：`Color`、`Q`（DFA 状態）のような decidable equality を持つ型でのみ実行可能（有限性は必須でない。`Nat` も可）。なお `matches` 命題の意味論自体は命題等式で与えられるため、この制約は match 実行と `decide` に関する操作的なものであり、主張側での `#` の使用そのものを制限しない
- **マッチング判定の決定可能性**：multiset / set / list matcher は Egison の既存アルゴリズムを借用
- **構造的 matcher の健全性**：`bipartite_graph` のような専用 matcher については、対応する数学的構造との整合性を個別に証明

## Formalize する例

### 中心的な例（実装と論文の核）

すべて組合せ的存在定理：

- **[Ramsey R(3,3) = 6](pwl-ramsey.md)**：`multiset` matcher + 非線形 `#c`。pattern style の最初の旗艦例
- **[Schur S(2) = 4](pwl-schur.md)**：`set` matcher + 値パターン `#(x+y)`。値パターンの導入
- **[Pumping lemma](pwl-pumping.md)**：`list` matcher + `_ ++ x :: _` 慣用句 + 派生値 target。順序付き構造への拡張、形式言語分野への射程
- **[Hall の結婚定理](pwl-hall.md)**：`bipartite_graph` matcher + `⤳` パターンコンストラクタ。matcher による主張側語彙拡張の旗艦例

### 拡張候補（実装と評価次第で追加）

- **鳩の巣原理（一般形）**：`multiset` matcher の典型例として軽量に
- **Erdős–Szekeres**：順序付き multiset matcher の追加。Ramsey 系と Pumping 系の中間
- **Dilworth の定理**：order 構造を持つ matcher への拡張
- **Sperner の補題**：単体分割と色付きの組合せ的拘束
- **van der Waerden の小ケース**（W(2,3) = 9）：等差数列の存在型主張

## 関連研究

- **Egison**（APLAS 2018、Programming 2020）：基盤
- **λP**：型システムの直接の前身
- **Coq の Equations**（Sozeau）：dependent pattern matching（term 構築側）
- **Agda の dependent pattern matching**（Norell, Cockx）：term 構築側の pattern。本研究は **statement 側** で独自
- **Agda の with abstraction**（McBride）
- **SSReflect / Mathlib の intro patterns**（Gonthier 系）：tactic 駆動の destructure
- **Views**（Wadler、McBride の deriving）
- **Idris**（Brady）
- **Pattern fragment**（Miller）

## 主たる貢献の要約

1. **Statement-side pattern matching**：定理の主張を pattern で書く設計。既存の proof assistant 設計が proof term 側に pattern を限定してきたのに対し、本研究は主張側に pattern を持ち込む
2. **鳩の巣論法の syntactic 表現**：非線形パターン `#x` が組合せ的存在定理の core idiom に native 対応する観察
3. **Matcher による主張語彙拡張**：`bipartite_graph` のような matcher を導入することで、特殊な数学的構造を扱う statement が劇的に簡潔化される（Hall の `⤳` が旗艦例）
4. **適用と主張の構文的一致**：補題の statement と適用先の `match` 腕が同一の pattern 文字列で書ける `exhaustive by` 構文
