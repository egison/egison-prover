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
  -- x-y の色で場合分け
  by_cases hxy_color : edge ⟦(x, y)⟧ = c
  · exact ⟨v, x, y, ⟨c, edge_vx, hxy_color, edge_vy⟩⟩
  · -- y-z の色で場合分け
    by_cases hyz_color : edge ⟦(y, z)⟧ = c
    · exact ⟨v, y, z, ⟨c, edge_vy, hyz_color, edge_vz⟩⟩
    · -- x-z の色で場合分け
      by_cases hxz_color : edge ⟦(x, z)⟧ = c
      · exact ⟨v, x, z, ⟨c, edge_vx, hxz_color, edge_vz⟩⟩
      · -- 全て c でない → 反対色を導出
        have hxy_c' : edge ⟦(x, y)⟧ = opposite c := by
          cases edge ⟦(x, y)⟧ <;> cases c <;> simp_all
        have hyz_c' : edge ⟦(y, z)⟧ = opposite c := by
          cases edge ⟦(y, z)⟧ <;> cases c <;> simp_all
        have hxz_c' : edge ⟦(x, z)⟧ = opposite c := by
          cases edge ⟦(x, z)⟧ <;> cases c <;> simp_all
        exact ⟨x, y, z, ⟨opposite c, hxy_c', hyz_c', hxz_c'⟩⟩
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
  | ($v, $x) -> $c
    :: (#v, $y) -> #c
    :: (#v, $z) -> #c
    :: _ =>

    -- ★ 内側のパターンマッチ: 残り 3 辺の色で場合分け
    --
    -- 各ケースでは、パターンマッチで束縛された値を返すだけでよい。
    -- 返された束縛が定理の matches パターンを満たすことは、
    -- 外側・内側のマッチで得られる証明項から自動的に補完される。
    -- 例: 最初のケースでは v-x, v-y, x-y
    --   の各制約（同色性）が充足されることが自動で導かれる。
    match edge as multiset (Sym2 (Fin 6) -> Color)
    | (#x, #y) -> #c ⇒ hxy_c =>
        exact ⟨v, x, c, y⟩

    | (#y, #z) -> #c ⇒ hyz_c =>
        exact ⟨v, y, c, z⟩

    | (#x, #z) -> #c ⇒ hxz_c =>
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
| 行数（証明本体） | 約40行 | 約30行 |
| 補助補題 | なし | 2つ（鳩の巣原理、2色網羅性） |
| `obtain`（3頂点の取り出し） | 1箇所 | 0箇所（multiset `::` に吸収） |
| `have`（辺の色の証明） | 3箇所 | 0箇所（`⇒` に吸収） |
| 辺の色の場合分け | `by_cases` 3段入れ子 | フラット4ケース |
| 反対色の導出 | `have` 3箇所 + `cases ... <;> simp_all` | multiset マッチで自動 |
| マッチャー正当性の証明 | 不要（標準パターンマッチのみ） | 1箇所（`with` で multiset マッチャー） |
| 網羅性の証明 | 不要（`by_cases` は構造的に網羅的） | 2箇所（ワイルドカード節で背理法） |

### 補助補題を含めた総量

Lean 4 版は `by_cases` が構造的に網羅的なので補助補題が不要だが、
証明本体が長い（約40行）。さらに `monochromatic` の定義が別途必要。

パターンマッチ指向版は `monochromatic` の定義が不要で証明本体も短い（約30行）が、
網羅性の背理法証明のために補助補題 `two_color_exhaustive` が必要。
ただしこれは `decide` で閉じる1行の補題である。
`pigeonhole_edges` は Lean 4 版でも `h_pigeonhole` として
実質同じ内容を証明している（形式が異なるだけ）。

