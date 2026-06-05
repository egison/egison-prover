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
    matches ($x, $y) → $c :: (#y, $z) → #c :: (#z, #x) → #c :: _
    as multiset (Sym2 (Fin 6) → Color)
```

`matches` は「任意の `edge` に対してこのパターンが必ずマッチする」という主張であり、
定理の証明はこのパターンの網羅性を示すことに対応する。
`as multiset (Sym2 (Fin 6) → Color)` により、関数 `edge` を入出力ペアの multiset として扱う。
`Sym2 (Fin 6)` は順序なしペアなので、`($x, $y)` は順序を問わずマッチする。

この記法により以下が吸収される：
- **`monochromatic` の定義**: パターン自体が「単色三角形」を表現
- **`∃ (x y z : Fin 6)`**: パターン変数 `$x, $y, $z` に吸収
- **`∃ c`**: パターン変数 `$c` と非線形パターン `#c` に吸収

さらに、各パターン変数が満たすべき関係もパターンの構造から自動的に導かれる。
具体的には、`($x, $y) → $c :: (#y, $z) → #c :: (#z, #x) → #c :: _` というパターンから：
- **相異性**: `$x`, `$y`, `$z` は `Sym2 (Fin 6)` の異なる辺を構成するため、互いに異なる値でなければならない（`x ≠ y`, `y ≠ z`, `z ≠ x`）。`Sym2` は自己ループ `⟦(v, v)⟧` を持たないため、各辺の両端が異なることも保証される。
- **三角形の構成**: 3つの辺 `⟦(x,y)⟧`, `⟦(y,z)⟧`, `⟦(z,x)⟧` が三角形を形成すること。
- **単色性**: 非線形パターン変数 `#c` により、3辺すべてが同じ色 `c` であること。

Lean 4 版では `monochromatic` の定義内でこれらの関係を明示的に記述する必要があるが、パターンマッチ指向版ではパターンの構文そのものがこれらの制約を暗黙に表現している。

---

## A. Lean 4 / Mathlib スタイル

### 補助補題

```lean
def same_color_neighbors (edge : Sym2 (Fin 6) → Color) (v : Fin 6) (c : Color) :
    Finset (Fin 6) :=
  Finset.univ.filter (fun w => w ≠ v ∧ edge ⟦(v, w)⟧ = c)

-- 鳩の巣原理: v からの 5 辺を 2 色で塗ると、同色 3 辺以上が存在する
lemma pigeonhole_edges (edge : Sym2 (Fin 6) → Color) (v : Fin 6) :
    ∃ c, (same_color_neighbors edge v c).card ≥ 3 := by
  by_contra h
  push_neg at h
  have hr := h .red
  have hb := h .blue
  have h_total : (same_color_neighbors edge v .red).card
               + (same_color_neighbors edge v .blue).card = 5 := by
    ...
  omega
```

### 証明

```lean
theorem ramsey_3_3_6 (edge : Sym2 (Fin 6) → Color) :
    ∃ (x y z : Fin 6), monochromatic edge x y z := by
  let v : Fin 6 := 0
  -- 鳩の巣原理
  obtain ⟨c, hc⟩ := pigeonhole_edges edge v
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

### 改訂方針

この節では、完全グラフの辺色関数 `edge : Sym2 (Fin 6) → Color` を最後まで
`as multiset (Sym2 (Fin 6) → Color)` として直接観察する。

そのため、固定した頂点 `v` から出る5本の辺を取り出すために、
`spokes` のような射影関数は導入しない。
代わりに、パターン中で `(#v, $x)` と書くことで、
`edge` 全体の multiset から「始点 `v` に接続する辺」だけを直接拾う。

また、三角形内部の3辺についても、色の3つ組 `(Color, Color, Color)` には変換しない。
`edge` 自体を multiset として見たまま、
「`x,y,z` の内部辺のどれか1本が色 `c`」という1つのパターンと、
「内部3辺がすべて反対色」という1つのパターンで網羅性を表現する。
これにより、`.xy`, `.yz`, `.zx` のようなラベルごとの成功分岐を並べずに済む。

### 補助補題

```egison
-- 鳩の巣原理: 固定した v からの 5 辺を 2 色で塗ると、同色 3 辺以上が存在する。
-- v は補題の引数として固定し、edge 全体を multiset として直接マッチする。
lemma pigeonhole_edges_at (edge : Sym2 (Fin 6) → Color) (v : Fin 6)
    matches (#v, $x) → $c :: (#v, $y) → #c :: (#v, $z) → #c :: _
    as multiset (Sym2 (Fin 6) → Color) := by
  -- v の次数は 5（K₆ で自己ループなし）。
  -- 5 辺を 2 色に分けるので、鳩の巣原理から ⌈5/2⌉ = 3。
  -- ここでは edge を spokes のような補助関数に射影せず、
  -- (#v, $x) というパターンで v に接続する辺だけを直接取り出す。
  match edge as multiset (Sym2 (Fin 6) → Color) with
  | (#v, $x) → $c :: $edge' =>
    match edge' as multiset (Sym2 (Fin 6) → Color) with
    | (#v, $y) → #c :: $edge'' =>
      match edge'' as multiset (Sym2 (Fin 6) → Color) with
      | (#v, $z) → #c :: _ =>
          exact ⟨x, c, y, z⟩
      | (#v, $x') → (!#c & $c') ::
        (#v, $y') → #c' ::
        (#v, $z') → #c' :: _ =>
          exact ⟨x', c', y', z'⟩
    | (#v, $x') → (!#c & $c') ::
      (#v, $y') → #c' ::
      (#v, $z') → #c' :: _ =>
        exact ⟨x', c', y', z'⟩

-- 三角形内部の 3 辺に関する 2 色の網羅性。
-- 色のタプルではなく、edge 自体を multiset として扱う。
--
-- 1. {x,y,z} の内部辺のどれか1本が色 c である。
-- 2. そうでなければ、内部3辺すべてが同じ反対色 c' である。
lemma triangle_two_color_exhaustive
    (edge : Sym2 (Fin 6) → Color)
    (c : Color) (x y z : Fin 6)
    matches
      (($p & (#x | #y | #z)), ($q & (#x | #y | #z))) → #c :: _
    | (#x, #y) → (!#c & $c') ::
      (#y, #z) → #c' ::
      (#z, #x) → #c' :: _
    as multiset (Sym2 (Fin 6) → Color) := by
  cases edge ⟦(x,y)⟧ <;>
  cases edge ⟦(y,z)⟧ <;>
  cases edge ⟦(z,x)⟧ <;>
  cases c <;>
  simp_all
  -- 2⁴ = 16 通りの全数検査で自動証明。
```

`pigeonhole_edges_at` は、始点 `v` を補題の引数として固定する。
旧版のように `($v, $x)` で `v` 自体を探索するのではなく、
`(#v, $x)` によって、指定された `v` から出る辺だけを `edge` の multiset から直接拾う。
したがって、この補題の内容は完全グラフ全体に対するパターンではなく、
「固定した1頂点から出る5本の辺」に対する鳩の巣原理である。

`triangle_two_color_exhaustive` は、旧版の `two_color_exhaustive` のように
`(edge ⟦(x,y)⟧, edge ⟦(y,z)⟧, edge ⟦(x,z)⟧)` というタプルを対象にしない。
あくまで `edge` を `as multiset (Sym2 (Fin 6) → Color)` として見たまま、
`x,y,z` の内部辺に限定するパターンを直接書く。

第1節

```egison
(($p & (#x | #y | #z)), ($q & (#x | #y | #z))) → #c :: _
```

は、両端が `x,y,z` のいずれかである辺、つまり三角形内部のどれか1辺が
色 `c` であることを表す。
見つかった辺の両端は `$p`, `$q` として束縛されるので、主定理側では
`exact ⟨v, p, c, q⟩` と書ける。
この1節が、旧版の `(#x, #y) → #c`, `(#y, #z) → #c`, `(#x, #z) → #c`
の3節をまとめている。

第2節

```egison
(#x, #y) → (!#c & $c') ::
(#y, #z) → #c' ::
(#z, #x) → #c' :: _
```

は、内部3辺がすべて同じ反対色 `c'` であることを表す。
ここでは3辺を1つの multiset パターンの中で同時に要求しているだけであり、
3つの成功分岐に分けているわけではない。

### 証明

```egison
theorem ramsey_3_3_6 (edge : Sym2 (Fin 6) → Color)
    matches ($x, $y) → $c :: (#y, $z) → #c :: (#z, #x) → #c :: _
    as multiset (Sym2 (Fin 6) → Color) := by

  let v : Fin 6 := 0

  -- ★ 外側のパターンマッチ:
  -- 固定した v から出る同色 3 辺を、edge 自体から直接取り出す。
  match edge as multiset (Sym2 (Fin 6) → Color) with
  | (#v, $x) → $c :: (#v, $y) → #c :: (#v, $z) → #c :: _ =>

    -- ★ 内側のパターンマッチ:
    -- x,y,z の内部辺を、edge 自体の multiset として順序なしに見る。
    match edge as multiset (Sym2 (Fin 6) → Color) with

    -- 内部辺のどれか1本が外側と同じ色 c なら、v とその両端で単色三角形。
    | (($p & (#x | #y | #z)), ($q & (#x | #y | #z))) → #c :: _ =>
        exact ⟨v, p, c, q⟩

    -- 内部辺に色 c がないなら、内部3辺がすべて同じ反対色 c'。
    | (#x, #y) → (!#c & $c') ::
      (#y, #z) → #c' ::
      (#z, #x) → #c' :: _ =>
        exact ⟨x, y, c', z⟩

    exhaustive by
      triangle_two_color_exhaustive edge c x y z

  exhaustive by
    pigeonhole_edges_at edge v
```

この証明では、`edge` 以外の補助的な辺色関数は作らない。
外側でも内側でも、同じ `edge : Sym2 (Fin 6) → Color` を
`as multiset (Sym2 (Fin 6) → Color)` として直接マッチしている。

外側の `match` は

```egison
(#v, $x) → $c :: (#v, $y) → #c :: (#v, $z) → #c :: _
```

により、固定した `v` から出る同色3辺を取り出す。
網羅性は `pigeonhole_edges_at edge v` によって与えられる。

内側の `match` は2ケースだけである。
第1ケースは、`x,y,z` の内部辺のどれか1本が色 `c` である場合で、
その辺の両端を `$p`, `$q` として受け取る。
外側のマッチから `v-p`, `v-q` も色 `c` なので、`v,p,q` が単色三角形になる。
第2ケースは、内部辺に色 `c` がない場合で、2色性から内部3辺が反対色 `c'` でそろう。

#### パターン変数間の関係の自動導出と自動検証

一般に、パターン中のパターン変数の間の関係のうち、パターンの構造から自然に導かれる性質（相異性、等価性、型の制約など）の証明はすべて自動的に導出される。これはパターンマッチ指向証明の基本原理であり、証明者がこれらの関係を明示的に記述・証明する必要がない。この原理は、定理の `matches` パターンと証明内部の `match` パターンの両方に適用される。

**定理の `matches` パターンからの関係の列挙:**
定理のパターン `($x, $y) → $c :: (#y, $z) → #c :: (#z, #x) → #c :: _` からは、証明すべき以下の関係が自動的に列挙される：
- **相異性**: `x ≠ y`, `y ≠ z`, `z ≠ x`（`Sym2` の性質と multiset の `::` から）
- **三角形の構成**: 3辺 `⟦(x,y)⟧`, `⟦(y,z)⟧`, `⟦(z,x)⟧` の形成
- **単色性**: `edge ⟦(x,y)⟧ = c`, `edge ⟦(y,z)⟧ = c`, `edge ⟦(z,x)⟧ = c`（非線形パターン `#c` から）

**証明内部の外側 `match` パターンからの関係の導出:**
外側のパターン `(#v, $x) → $c :: (#v, $y) → #c :: (#v, $z) → #c :: _` にマッチしたことから、以下の関係が自動的に導出される：
1. **頂点の相異性（Sym2 の性質から）**: `v ≠ x`, `v ≠ y`, `v ≠ z` — `Sym2` は自己ループを持たないため、各辺の両端は異なる。
2. **辺の相異性（multiset の `::` から）**: `x ≠ y`, `x ≠ z`, `y ≠ z` — multiset から `::` で取り出した要素は互いに異なるため。
3. **同色性（非線形パターンから）**: `edge ⟦(v,x)⟧ = c`, `edge ⟦(v,y)⟧ = c`, `edge ⟦(v,z)⟧ = c` — 非線形パターン `#v`, `#c` によるマッチから。

**証明内部の内側 `match` パターンからの関係の導出:**
内側の第1ケース

```egison
(($p & (#x | #y | #z)), ($q & (#x | #y | #z))) → #c :: _
```

からは、`p` と `q` が `x,y,z` のいずれかであること、
`edge ⟦(p,q)⟧ = c` であることが自動的に導出される。
外側のマッチからは `v` と `x,y,z` のそれぞれを結ぶ辺が色 `c` であることが得られているので、
`v,p,q` が定理の単色三角形パターンを満たすことが自動検証される。

内側の第2ケースからは、`edge ⟦(x,y)⟧ = c'`, `edge ⟦(y,z)⟧ = c'`,
`edge ⟦(z,x)⟧ = c'` が得られる。
したがって、`x,y,z` が色 `c'` の単色三角形を形成する。

Lean 4 版では、外側の同色辺を `edge_vx`, `edge_vy`, `edge_vz` として明示的に保持し、
内側の各辺についても `hxy`, `hyz`, `hxz` のような証明項を個別に扱う必要がある。
パターンマッチ指向版では、これらの関係はすべてマッチの成立から自動的に得られる。

**`exact` での証明の完了:**
各ケースで `exact` に定理の `matches` パターン中のパターン変数に対応する値を列挙するだけでよい。証明内部のパターンマッチで導出された関係が、定理のパターンから列挙された関係をすべて含んでいるかが自動的にチェックされるためである。

例えば、内側の第1ケースでは：
- 外側のマッチから: `edge ⟦(v,x)⟧ = c`, `edge ⟦(v,y)⟧ = c`, `edge ⟦(v,z)⟧ = c`
- 内側のマッチから: `p,q ∈ {x,y,z}`, `edge ⟦(p,q)⟧ = c`

これらを合わせると、`v,p,q` が色 `c` の単色三角形であることが自動で確認される。
証明者は `exact ⟨v, p, c, q⟩` として変数の対応を指示するだけでよく、
関係の証明を明示的に構築する必要がない。

---

## C. 比較

### 量的比較

| | Lean 4 | パターンマッチ指向 |
|---|---|---|
| 定理の主張 | `∃ (x y z), monochromatic edge x y z` | `matches ($x, $y) → $c :: ...` |
| 補助定義 | `monochromatic` + `same_color_neighbors` が必要 | 不要（パターンが定義） |
| 存在量化 | 明示的に `∃` | パターン変数に吸収 |
| 始点からの5辺 | `same_color_neighbors edge v c` で集合として切り出す | `(#v, $x)` で `edge` から直接マッチ |
| 行数（主定理の証明） | 約25行 | 約15行 |
| 補助補題 | 1つ（鳩の巣原理、約10行） | 2つ（固定始点の鳩の巣原理、三角形内部の網羅性） |
| 鳩の巣原理の証明 | `by_contra` + `omega` | 固定した `v` に対するネストされた multiset マッチ |
| `obtain`（3頂点の取り出し） | 1箇所 | 0箇所（multiset `::` に吸収） |
| `have`（辺の色の証明） | 3箇所 | 0箇所（非線形パターンに吸収） |
| 辺の色の場合分け | `rcases` フラット4ケース | `match` 2ケース（内部辺のどれかが `c` / 内部3辺が反対色） |
| 反対色の導出 | `cases ... <;> simp_all` 3箇所 | `triangle_two_color_exhaustive` の multiset マッチで処理 |
| 網羅性の証明 | 不要（`rcases` は構造的に網羅的） | 外側: `pigeonhole_edges_at`; 内側: `triangle_two_color_exhaustive` |
| `exact` に渡す証明項 | 明示的な証明項の構築が必要 | パターン変数の列挙のみ（関係は自動検証） |

### 補助補題を含めた総量

両者とも鳩の巣原理を補助補題として切り出している。

Lean 4 版は主定理が約25行、補助補題 `pigeonhole_edges` が約10行で、
合計約35行。さらに `monochromatic` と `same_color_neighbors` の定義が別途必要。

パターンマッチ指向版は、主定理では外側・内側とも `edge` 自体を
`as multiset (Sym2 (Fin 6) → Color)` として直接マッチする。
補助補題は `pigeonhole_edges_at` と `triangle_two_color_exhaustive` の2つである。
前者は固定した始点 `v` から出る5本の辺だけに関する鳩の巣原理であり、
後者は三角形内部の3辺をタプルではなく multiset として扱う網羅性補題である。
`monochromatic` や `same_color_neighbors` の定義は不要である。

### 場合分けの構造の比較

Lean 4 版では `rcases Decidable.em` を連鎖させることで場合分けをフラットに記述できる。
各 `rcases` の正のケース（`= c`）で即座にゴールを閉じ、
負のケースのみが次の `rcases` に進むため、構造的には4つのフラットなケースとなる。

改訂後のパターンマッチ指向版では、内側の成功ケースを3つに分けない。
旧版では

```egison
| (#x, #y) → #c => ...
| (#y, #z) → #c => ...
| (#x, #z) → #c => ...
```

のように、内部辺ごとに成功分岐を列挙していた。
改訂版では、これを

```egison
| (($p & (#x | #y | #z)), ($q & (#x | #y | #z))) → #c :: _ =>
    exact ⟨v, p, c, q⟩
```

という1節にまとめる。
これにより、三角形内部の3辺を順序付きタプルではなく、
`edge` の multiset の中にある「両端が `x,y,z` に属する辺」として扱っていることが明確になる。

両者の違いは次のように整理できる：

- **Lean 4 版**: 各ケースで `edge_vx`, `hxy` 等の証明項を明示的に `exact` に渡す必要がある。
  反対色ケースでは `cases ... <;> simp_all` による Color 全数検査が3箇所必要。
- **旧パターンマッチ指向版**: 明示的な証明項は不要だが、内部辺の成功ケースを `xy`, `yz`, `xz` の3節に分けていた。
- **改訂後のパターンマッチ指向版**: 内部辺の成功ケースを1節にまとめ、反対色ケースも1つの multiset パターンとして扱う。
  非線形パターン `#c` と conjunctive pattern `$p & (...)` により、必要な同色性・所属関係・相異性はマッチから自動的に得られる。

このため、改訂後のB節では、
「補助関数で対象を加工してから証明する」のではなく、
「元の `edge` を multiset として観察し、必要な部分構造をパターンで直接取り出す」
という方針がより徹底されている。
