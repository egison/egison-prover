# Ramsey R(3,3) = 6 の証明：パターンマッチ指向スタイルの比較

## 定理

K₆（6頂点の完全グラフ）の辺を赤・青の2色で塗ると、必ず単色三角形が存在する。

---

## 基本定義

### Lean 4 での定義

```lean
inductive Color | red | blue

def monochromatic (edge : Sym2 (Fin 6) → Color) (x y z : Fin 6) : Prop :=
  ∃ c, edge ⟦(x,y)⟧ = c ∧ edge ⟦(y,z)⟧ = c ∧ edge ⟦(x,z)⟧ = c

theorem ramsey_3_3_6 (edge : Sym2 (Fin 6) → Color) :
    ∃ (x y z : Fin 6), monochromatic edge x y z
```

### パターンマッチ指向での定義

```egison
inductive Color | red | blue

theorem ramsey_3_3_6 (edge : Sym2 (Fin 6) → Color)
    matches ($x, $y) -> $c :: (#y, $z) -> #c :: (#z, #x) -> #c :: _
    as multiset (Sym2 (Fin 6) -> Color)
```

`matches` は「任意の `edge` に対してこのパターンが必ずマッチする」という主張であり、
定理の証明はこのパターンの網羅性を示すことに対応する。
`as multiset (Sym2 (Fin 6) -> Color)` により、関数 `edge` を入出力ペアの multiset として扱う。
`Sym2 (Fin 6)` は順序なしペアなので、`($x, $y)` は順序を問わずマッチする。

この記法により以下が吸収される：
- **`monochromatic` の定義**: パターン自体が「単色三角形」を表現
- **`∃ (x y z : Fin 6)`**: パターン変数 `$x, $y, $z` に吸収
- **`∃ c`**: パターン変数 `$c` と非線形パターン `#c` に吸収

さらに、各パターン変数が満たすべき関係もパターンの構造から自動的に導かれる。
具体的には、`($x, $y) -> $c :: (#y, $z) -> #c :: (#z, #x) -> #c :: _` というパターンから：
- **相異性**: `$x`, `$y`, `$z` は `Sym2 (Fin 6)` の異なる辺を構成するため、互いに異なる値でなければならない（`x ≠ y`, `y ≠ z`, `z ≠ x`）。`Sym2` は自己ループ `⟦(v, v)⟧` を持たないため、各辺の両端が異なることも保証される。
- **三角形の構成**: 3つの辺 `⟦(x,y)⟧`, `⟦(y,z)⟧`, `⟦(z,x)⟧` が三角形を形成すること。
- **単色性**: 非線形パターン変数 `#c` により、3辺すべてが同じ色 `c` であること。

Lean 4 版では `monochromatic` の定義内でこれらの関係を明示的に記述する必要があるが、パターンマッチ指向版ではパターンの構文そのものがこれらの制約を暗黙に表現している。

---

## A. Lean 4 / Mathlib スタイル

```lean
def same_color_neighbors (edge : Sym2 (Fin 6) → Color) (v : Fin 6) (c : Color) :
    Finset (Fin 6) :=
  Finset.univ.filter (fun w => w ≠ v ∧ edge ⟦(v, w)⟧ = c)

theorem ramsey_3_3_6 (edge : Sym2 (Fin 6) → Color) :
    ∃ (x y z : Fin 6), monochromatic edge x y z := by
  let v : Fin 6 := 0
  -- 鳩の巣原理（色を存在量化で受ける）
  have h_pigeonhole : ∃ c, (same_color_neighbors edge v c).card ≥ 3 := by
    by_contra h
    push_neg at h
    have hr := h .red
    have hb := h .blue
    have h_total : (same_color_neighbors edge v .red).card
                 + (same_color_neighbors edge v .blue).card = 5 := by
      ...
    omega
  obtain ⟨c, hc⟩ := h_pigeonhole
  -- S から 3 頂点を取り出す
  let S := same_color_neighbors edge v c
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.exists_three_le_card S hc
  -- v-x, v-y, v-z は全て色 c
  have edge_vx : edge ⟦(v, x)⟧ = c := by
    exact (Finset.mem_filter.mp hx).2.2
  have edge_vy : edge ⟦(v, y)⟧ = c := by
    exact (Finset.mem_filter.mp hy).2.2
  have edge_vz : edge ⟦(v, z)⟧ = c := by
    exact (Finset.mem_filter.mp hz).2.2
  -- x-y, y-z, x-z の色で場合分け（3辺の色をフラットに分岐）
  rcases Decidable.em (edge ⟦(x, y)⟧ = c) with hxy | hxy
  · exact ⟨v, x, y, ⟨c, edge_vx, hxy, edge_vy⟩⟩
  rcases Decidable.em (edge ⟦(y, z)⟧ = c) with hyz | hyz
  · exact ⟨v, y, z, ⟨c, edge_vy, hyz, edge_vz⟩⟩
  rcases Decidable.em (edge ⟦(x, z)⟧ = c) with hxz | hxz
  · exact ⟨v, x, z, ⟨c, edge_vx, hxz, edge_vz⟩⟩
  -- 全て c でない → 反対色の三角形
  exact ⟨x, y, z, ⟨opposite c,
    by cases edge ⟦(x, y)⟧ <;> cases c <;> simp_all,
    by cases edge ⟦(y, z)⟧ <;> cases c <;> simp_all,
    by cases edge ⟦(x, z)⟧ <;> cases c <;> simp_all⟩⟩
```

---

## B. パターンマッチ指向スタイル

### 補助補題

```egison
-- 鳩の巣原理: v からの 5 辺を 2 色で塗ると、同色 3 辺以上が存在する
-- 主定理の外側マッチのワイルドカード節の背理法に使用
lemma pigeonhole_edges (edge : Sym2 (Fin 6) → Color)
    matches ($v, $x) -> $c :: (#v, $y) -> #c :: (#v, $z) -> #c :: _
    as multiset (Sym2 (Fin 6) -> Color) := by
  -- v の次数は 5（K₆ で自己ループなし）
  -- 5 辺を 2 色に分けるので、鳩の巣原理から ⌈5/2⌉ = 3
  ...

-- 2色の3値の網羅性:
-- 3つの Color 値に対し、以下の4パターンのいずれかが必ずマッチする
-- 主定理の内側マッチのワイルドカード節の背理法に使用
lemma two_color_exhaustive (c : Color) ((x, y, z) : (Color, Color, Color))
    matches (#c, _, _) | (_, #c, _) | (_, _, #c) | ($c', #c', #c') := by
  cases x <;> cases y <;> cases z <;> cases c <;> simp_all
  -- 2⁴ = 16 通りの全数検査で自動証明
```

`pigeonhole_edges` は主定理と同じ `matches ... as multiset` 形式。
`∃ c` やカーディナリティ `≥ 3` がパターン変数と `::` に吸収される。

`two_color_exhaustive` は `|`（パターンの選択肢）を使った `matches`。
ターゲット `(x, y, z)` が4つのパターンのいずれかに必ずマッチすることを主張する。
主定理や `pigeonhole_edges` ではターゲットが引数 `edge` なので暗黙だが、
ここではターゲットが構成された式なので明示が必要。
Color は代数的データ型なので `as` は不要。

### 証明

```egison
theorem ramsey_3_3_6 (edge : Sym2 (Fin 6) → Color)
    matches ($x, $y) -> $c :: (#y, $z) -> #c :: (#z, #x) -> #c :: _
    as multiset (Sym2 (Fin 6) -> Color) := by

  -- ★ 外側のパターンマッチ: edge から同色 3 辺を取り出す
  match edge as multiset (Sym2 (Fin 6) -> Color)
    with
  | ($v, $x) -> $c :: (#v, $y) -> #c :: (#v, $z) -> #c :: _ =>

    -- このパターンにマッチしたことから、以下の関係が自動的に導かれる：
    --   (1) v ≠ x, v ≠ y, v ≠ z（Sym2 は自己ループを持たないため）
    --   (2) x ≠ y, x ≠ z, y ≠ z（multiset から :: で取り出した要素は互いに異なるため）
    --   (3) edge ⟦(v,x)⟧ = c, edge ⟦(v,y)⟧ = c, edge ⟦(v,z)⟧ = c
    --       （非線形パターン #v, #c によるマッチから）
    -- Lean 4 版では (1)(2) を Finset.mem_filter や hxy, hxz, hyz として明示的に保持し、
    -- (3) を have edge_vx, edge_vy, edge_vz として個別に証明する必要がある。
    -- パターンマッチ指向版では、これらすべてがマッチの成立から自動的に得られる。

    -- ★ 内側のパターンマッチ: 残り 3 辺の色で場合分け
    --
    -- 各ケースでは、パターンマッチで束縛された値を返すだけでよい。
    -- 返された束縛が定理の matches パターンを満たすことは、
    -- 外側・内側のマッチで得られる証明項から自動的に補完される。
    -- 例: 最初のケースでは v-x, v-y, x-y
    --   の各制約（同色性）が充足されることが自動で導かれる。
    match edge as multiset (Sym2 (Fin 6) -> Color)
    | (#x, #y) -> #c =>
        exact ⟨v, x, c, y⟩

    | (#y, #z) -> #c =>
        exact ⟨v, y, c, z⟩

    | (#x, #z) -> #c =>
        exact ⟨v, x, c, z⟩

    | (#x, #y) -> $c' :: (#y, #z) -> #c' :: (#x, #z) -> #c' :: _ =>
        exact ⟨x, y, c', z⟩

    | _ => by
        -- 網羅性: 上の 4 ケースにマッチしないと仮定して背理法。
        -- two_color_exhaustive により 4 ケースは全可能性を尽くすので矛盾。
        exfalso
        have h := two_color_exhaustive c (edge ⟦(x,y)⟧) (edge ⟦(y,z)⟧) (edge ⟦(x,z)⟧)
        simp_all

  | _ => by
      -- 網羅性: 同色 3 辺が取り出せないと仮定して背理法。
      -- 鳩の巣原理（色を存在量化で受ける。ここは Lean 4 版と同じ）
      have h_pigeonhole := pigeonhole_edges edge
      obtain ⟨c, hc⟩ := h_pigeonhole
      -- hc より同色 3 辺が存在するので矛盾。
      exfalso
      exact absurd hc (by omega)
```

---

## C. 比較

### 量的比較

| | Lean 4 | パターンマッチ指向 |
|---|---|---|
| 定理の主張 | `∃ (x y z), monochromatic edge x y z` | `matches ($x, $y) -> $c :: ...` |
| 補助定義 | `monochromatic` が必要 | 不要（パターンが定義） |
| 存在量化 | 明示的に `∃` | パターン変数に吸収 |
| 行数（証明本体） | 約35行 | 約30行 |
| 補助補題 | なし | 2つ（鳩の巣原理、2色網羅性） |
| `obtain`（3頂点の取り出し） | 1箇所 | 0箇所（multiset `::` に吸収） |
| `have`（辺の色の証明） | 3箇所 | 0箇所（`⇒` に吸収） |
| 辺の色の場合分け | `rcases` フラット4ケース | `match` フラット4ケース |
| 反対色の導出 | `cases ... <;> simp_all` 3箇所 | multiset マッチで自動 |
| マッチャー正当性の証明 | 不要（標準パターンマッチのみ） | 1箇所（`with` で multiset マッチャー） |
| 網羅性の証明 | 不要（`rcases` は構造的に網羅的） | 2箇所（ワイルドカード節で背理法） |

### 補助補題を含めた総量

Lean 4 版は `rcases` が構造的に網羅的なので補助補題が不要だが、
証明本体がやや長い（約35行）。さらに `monochromatic` の定義が別途必要。

パターンマッチ指向版は `monochromatic` の定義が不要で証明本体も短い（約30行）が、
網羅性の背理法証明のために補助補題 `two_color_exhaustive` が必要。
ただしこれは `decide` で閉じる1行の補題である。
`pigeonhole_edges` は Lean 4 版でも `h_pigeonhole` として
実質同じ内容を証明している（形式が異なるだけ）。

### 場合分けの構造の比較

Lean 4 版では `rcases Decidable.em` を連鎖させることで場合分けをフラットに記述できる。
各 `rcases` の正のケース（`= c`）で即座にゴールを閉じ、
負のケースのみが次の `rcases` に進むため、構造的には4つのフラットなケースとなる。

パターンマッチ指向版も `match` の4ケースでフラットに記述される。
両者のケース数と構造は同等だが、以下の点が異なる：

- **Lean 4 版**: 各ケースで `edge_vx`, `hxy` 等の証明項を明示的に `exact` に渡す必要がある。
  反対色ケースでは `cases ... <;> simp_all` による Color 全数検査が3箇所必要。
- **パターンマッチ指向版**: 各ケースでは束縛変数を返すだけでよい。
  非線形パターン `#c` によるマッチから同色性の証明が自動的に得られるため、
  明示的な証明項の構築が不要。反対色ケースも multiset マッチで自動的に処理される。

