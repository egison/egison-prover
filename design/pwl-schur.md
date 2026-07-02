# Schur S(2) = 4 の証明：パターンマッチ指向スタイルの比較

## 定理

{1, ..., 5} の各要素を赤・青の2色で塗ると、必ず単色な x, y, z（x + y = z、x = y も許す）が存在する。

これは Schur 数 s(2) = 4 の主張に対応する：{1,...,4} は同色 Schur triple を持たないように2色塗りできるが、{1,...,5} は不可能。

---

## 基本定義

### Lean 4 での定義

```lean
inductive Color | red | blue deriving DecidableEq

inductive D | one | two | three | four | five deriving DecidableEq, Fintype

def D.val : D → Nat
  | .one => 1 | .two => 2 | .three => 3 | .four => 4 | .five => 5

def monochromatic_schur (c : D → Color) (x y z : D) : Prop :=
  ∃ col, c x = col ∧ c y = col ∧ c z = col ∧ x.val + y.val = z.val

theorem schur_2 (c : D → Color) :
    ∃ (x y z : D), monochromatic_schur c x y z
```

### パターンマッチ指向での定義

```egison
inductive Color | red | blue

theorem schur_2 (c : {1..5} → Color)
    matches $x → $col :: $y → #col :: #(x+y) → #col :: _
    as set ({1..5} → Color)
```

`matches` は任意の `c` に対してこのパターンが必ずマッチすることを主張する。
`as set ({1..5} → Color)` により、関数 `c` を (入力, 出力) ペアの集合として扱う。

**`set` matcher を使う理由**: Schur triple では `x = y` を許す（例: `1 + 1 = 2`）。`set` matcher は要素を取り出してもターゲットが減らない（集合は各要素を無限個含むとみなす）ため、`$x` と `$y` が同じ値を取ることを許す。pwl-ramsey.md の `multiset` matcher は3辺の相異性を要求するため、ここでは適切でない。

この記法により以下が吸収される：
- **`monochromatic_schur` の定義**: パターン自体が「同色 Schur triple」を表現
- **`∃ (x y z)`**: パターン変数 `$x`, `$y` と値パターン `#(x+y)` に吸収（z は独立変数ではなく x + y そのもの）
- **`∃ col`**: パターン変数 `$col` と非線形パターン `#col` に吸収
- **加算条件 `x + y = z`**: 値パターン `#(x+y)` に吸収
- **z が定義域内であること**: 値パターン `#(x+y)` のマッチ成功が、x + y ∈ {1..5} を要求する（範囲外なら集合に該当要素なし）

Lean 4 版では (1) 補助述語 `monochromatic_schur`、(2) `∃ col` の明示、(3) 加算条件 `x.val + y.val = z.val` の明示が必要だが、パターンマッチ指向版ではこれらすべてがパターン構文に吸収される。

---

## A. Lean 4 / Mathlib スタイル

### 補助補題

```lean
def Color.opp : Color → Color
  | .red => .blue
  | .blue => .red

-- Color は2値なので、col と異なる色は col.opp
lemma Color.ne_eq_opp (a col : Color) : a ≠ col → a = col.opp := by
  cases a <;> cases col <;> simp [Color.opp]
```

### 証明

```lean
theorem schur_2 (c : D → Color) :
    ∃ (x y z : D), monochromatic_schur c x y z := by
  -- c(1) の色を col とおく
  set col := c .one with hcol
  -- c(2) で場合分け
  rcases Decidable.em (c .two = col) with h2 | h2
  · -- 1 + 1 = 2 mono col
    exact ⟨.one, .one, .two, col, hcol.symm, hcol.symm, h2, rfl⟩
  have h2' : c .two = col.opp := Color.ne_eq_opp _ _ h2
  -- c(4) で場合分け
  rcases Decidable.em (c .four = col.opp) with h4 | h4
  · -- 2 + 2 = 4 mono col.opp
    exact ⟨.two, .two, .four, col.opp, h2', h2', h4, rfl⟩
  have h4' : c .four = col := by
    have := Color.ne_eq_opp _ _ h4
    cases col <;> simp_all [Color.opp]
  -- c(5) で場合分け
  rcases Decidable.em (c .five = col) with h5 | h5
  · -- 1 + 4 = 5 mono col
    exact ⟨.one, .four, .five, col, hcol.symm, h4', h5, rfl⟩
  have h5' : c .five = col.opp := by
    have := Color.ne_eq_opp _ _ h5
    cases col <;> simp_all [Color.opp]
  -- c(3) で場合分け
  rcases Decidable.em (c .three = col.opp) with h3 | h3
  · -- 2 + 3 = 5 mono col.opp
    exact ⟨.two, .three, .five, col.opp, h2', h3, h5', rfl⟩
  have h3' : c .three = col := by
    have := Color.ne_eq_opp _ _ h3
    cases col <;> simp_all [Color.opp]
  -- 1 + 3 = 4 mono col
  exact ⟨.one, .three, .four, col, hcol.symm, h3', h4', rfl⟩
```

---

## B. パターンマッチ指向スタイル

### 補助補題

```egison
-- 色の二分法: 任意の色は基準色 col と等しいか異なる
lemma color_dichotomy (col : Color) (a : Color)
    matches #col | (!#col & $col') := by decide

-- 2色の網羅性: 異なる2色 col, col' に対し、任意の色はそのどちらか
lemma color_exhaustive {col col' : Color} (h : col ≠ col') (a : Color)
    matches #col | #col' := by decide
```

`color_dichotomy` は内側マッチの最初の分岐（c(2) で col と≠col に分ける）に使う。
`color_exhaustive` は以降の分岐（col と col' の2値が既に確定した後）に使う。

### 証明

```egison
theorem schur_2 (c : {1..5} → Color)
    matches $x → $col :: $y → #col :: #(x+y) → #col :: _
    as set ({1..5} → Color) := by

  -- c(1) を col と束縛（c は全関数なので必ず何らかの色）
  match c as set ({1..5} → Color) with
  | 1 → $col :: _ =>

    -- c(2) で場合分け
    match c as set ({1..5} → Color) with
    | 2 → #col :: _ =>
        exact ⟨1, col, 1⟩  -- 1 + 1 = 2 mono col
    | 2 → (!#col & $col') :: _ =>
        -- c(2) = col' ≠ col。c(4) で場合分け
        match c as set ({1..5} → Color) with
        | 4 → #col' :: _ =>
            exact ⟨2, col', 2⟩  -- 2 + 2 = 4 mono col'
        | 4 → #col :: _ =>
            -- c(4) = col。c(5) で場合分け
            match c as set ({1..5} → Color) with
            | 5 → #col :: _ =>
                exact ⟨1, col, 4⟩  -- 1 + 4 = 5 mono col
            | 5 → #col' :: _ =>
                -- c(5) = col'。c(3) で場合分け
                match c as set ({1..5} → Color) with
                | 3 → #col' :: _ =>
                    exact ⟨2, col', 3⟩  -- 2 + 3 = 5 mono col'
                | 3 → #col :: _ =>
                    exact ⟨1, col, 3⟩  -- 1 + 3 = 4 mono col
                exhaustive by color_exhaustive ‹col ≠ col'› (c 3)
            exhaustive by color_exhaustive ‹col ≠ col'› (c 5)
        exhaustive by color_exhaustive ‹col ≠ col'› (c 4)
    exhaustive by color_dichotomy col (c 2)
```

注: ここの `exhaustive by` は、**色の値**（`c 2`, `c 3` など）上の補題（パターン `#col | #col'`）で、**関数 `c`** 上の match 腕（パターン `2 → #col :: _` など）の網羅性を正当化している。対象も matcher も異なるため、overview.md の `exhaustive by` 規則（補題と腕のパターンの字面一致）をそのまま適用することはできず、「キー `k` での射影マッチ `k → P :: _` と値マッチ `P` on `c k` の同値」というアダプタ規則（lifting）を暗黙に使っている。この規則の形式化は未了（review_20260612.md B-2）。pwl-ramsey の改訂版が補題側を edge の multiset に揃えて字面一致を回復したのと同様に、補題側を関数 `c` 上のパターンに揃える書き換えも検討に値する。

#### パターン変数間の関係の自動導出

pwl-ramsey と同じ原理が働く。各 `match` の腕にマッチした時点で、パターン構造から関係が自動導出される：

- **外側 `1 → $col :: _`**: `c 1 = col` を導出。
- **内側 `2 → (!#col & $col') :: _`**: `c 2 = col'` かつ `col' ≠ col` を導出。後者は `!#col` 否定パターンに由来する。
- **以降 `4 → #col :: _`, `5 → #col' :: _`, etc.**: それぞれ `c 4 = col`, `c 5 = col'` 等を導出。
- **最深の `exact ⟨1, col, 1⟩`** などで定理のパターン `$x → $col :: $y → #col :: #(x+y) → #col :: _` に対して値を列挙する際:
  - `x = 1`, `col = col`, `y = 1`、暗黙に `x + y = 2`
  - 系が要求する関係：`c 1 = col`（外側より自動）、`c 1 = col`（y = 1 なので同じ）、`c 2 = col`（この内側分岐の前提より自動）、`1 + 1 = 2 ∈ {1..5}`（算術と範囲チェック）
  - すべて導出済みなので、`exact` には値の列挙のみで十分。

Lean 4 版では `monochromatic_schur` の各 conjunct を明示的に渡す必要があるが、パターンマッチ指向版では関係はパターンマッチの成立から自動的に得られる。

#### 値パターン `#(x+y)` の役割

新規要素として、Schur では値パターン `#(x+y)` が登場する。これは：
- **算術制約**: マッチした第3要素の入力が、先に束縛された x と y の和でなければならない。
- **範囲制約**: 集合 `{1..5}` 内に `(x+y, col)` のペアが存在することを要求し、x + y > 5 ならマッチ失敗。

Lean 4 版では `x.val + y.val = z.val` を明示的に書き、各 `exact` で `rfl` として証明する。Schur triple として 1+1=2、2+2=4、1+4=5、2+3=5、1+3=4 の5パターンを使うが、いずれも算術により自明（`rfl` で閉じる）。

---

## C. 比較

### 量的比較

| | Lean 4 | パターンマッチ指向 |
|---|---|---|
| 定理の主張 | `∃ x y z, monochromatic_schur c x y z` | `matches $x → $col :: $y → #col :: #(x+y) → #col :: _` |
| 補助定義 | `monochromatic_schur`、`Color.opp` | 不要 |
| 補助補題 | `Color.ne_eq_opp`（1つ、約2行） | `color_dichotomy`、`color_exhaustive`（2つ、各1行） |
| 存在量化 (`∃ x y z`) | 明示的に `∃` | パターン変数に吸収 |
| 存在量化 (`∃ col`) | `exact ⟨..., col, ...⟩` で明示 | パターン変数 `$col` に吸収 |
| 加算条件 `x + y = z` | conjunct として明示、各 `exact` で `rfl` | 値パターン `#(x+y)` に吸収 |
| 範囲制約 `z ∈ {1..5}` | `D` の型から自動 | 値パターンのマッチ成立から自動 |
| 行数（主定理の証明） | 約30行 | 約20行 |
| `rcases Decidable.em` | 4箇所（c(2), c(4), c(5), c(3)） | 0箇所（パターン分岐に吸収） |
| `have h : c .i = ...` | 4箇所（色の二分法の明示） | 0箇所（パターンの非線形変数 `#col`, `#col'` から自動） |
| 2値性の利用 | `cases col <;> simp_all` を3回 | `color_exhaustive` の `decide` 1回（補題側） |

### 補助補題を含めた総量

Lean 4 版：本体 ~30行 + `monochromatic_schur` + `Color.opp` + `Color.ne_eq_opp` で合計 ~38行。さらに `D` と `Color` の型定義。

パターンマッチ指向版：本体 ~20行 + `color_dichotomy` + `color_exhaustive` で合計 ~24行。`monochromatic_schur` 相当は不要。

### pwl-ramsey との対比で新規となる要素

| 要素 | pwl-ramsey | pwl-schur |
|---|---|---|
| matcher | `multiset` | `set`（同一要素の重複取り出しを許す） |
| 値パターン | `#x`, `#y`, `#c`（非線形のみ） | `#(x+y)` を追加（算術式の値パターン） |
| 主張側の関係 | 相異性、三角形性、単色性 | 加算条件、範囲制約、単色性 |
| 証明の骨格 | 鳩の巣 + 3辺の場合分け（2段） | 強制手番チェーン（5段） |
| 補助補題の役割 | `pigeonhole_edges` で構造抽出、`two_color_exhaustive` で網羅性 | `color_dichotomy` / `color_exhaustive` で各段の網羅性のみ |

### 場合分けの構造の比較

Lean 4 版・パターンマッチ指向版とも、c(2), c(4), c(5), c(3) の4箇所で2分岐する **強制手番チェーン** で構造は同一。各段で「同色 Schur triple が成立」または「次の値の色が確定」のいずれかで進む。

- **Lean 4 版**: 各段で `rcases Decidable.em` により2分岐し、正のケースで `exact` してゴールを閉じ、負のケースで `Color.ne_eq_opp` 経由で反対色を取り出す。色の代入を `have h : c .i = col(.opp)` として明示的に保持する。
- **パターンマッチ指向版**: 各段で `match` の2腕により2分岐し、非線形パターン `#col` / `#col'` で同色性を自動的に拘束。色の代入は腕にマッチした時点で自動的に文脈に入る。

両者の差は **bookkeeping の量** に現れる。Lean 4 版は色の二分法を補題と `have` で繰り返し明示し、加算条件を `rfl` で個別に閉じる。パターンマッチ指向版は同じ役割をパターン構文の意味論に吸収させ、最終 `exact` ではパターン変数の値を列挙するだけでよい。
