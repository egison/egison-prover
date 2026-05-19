# Pumping Lemma：パターンマッチ指向スタイルでの定式化

## 定理

正則言語 L を受理する DFA M = (Q, Σ, δ, q₀, F) に対し、|w| ≥ |Q| を満たす任意の w ∈ L は w = xyz と分解でき、以下を満たす：

- |xy| ≤ |Q|
- |y| ≥ 1
- ∀ k ≥ 0. xy^k z ∈ L

ここでは DFA で受理される言語に対する pumping lemma を扱う。pumping length は |Q| として取る。

---

## 基本定義

### Lean 4 での定義

```lean
variable {Σ : Type} [DecidableEq Σ]

structure DFA (Q Σ : Type) [Fintype Q] [DecidableEq Q] where
  step : Q → Σ → Q
  start : Q
  accept : Q → Prop

def DFA.run (M : DFA Q Σ) (w : List Σ) : List Q :=
  w.scanl M.step M.start

def DFA.accepts (M : DFA Q Σ) (w : List Σ) : Prop :=
  M.accept ((M.run w).getLast (by simp [DFA.run]))

def IsPumpingDecomposition (M : DFA Q Σ) (w x y z : List Σ) (n : ℕ) : Prop :=
  w = x ++ y ++ z
  ∧ (x ++ y).length ≤ n
  ∧ y.length ≥ 1
  ∧ ∀ k, M.accepts (x ++ List.replicate k y ++ z)

theorem pumping_lemma (M : DFA Q Σ) (w : List Σ)
    (h_long : w.length ≥ Fintype.card Q)
    (h_acc : M.accepts w) :
    ∃ x y z, IsPumpingDecomposition M w x y z (Fintype.card Q)
```

主張内に `∃ x y z`（三重存在量化）、`= ... ∧ ... ∧ ... ∧ ∀ k, ...`（四項連言＋内側全称）が並ぶ。補助述語 `IsPumpingDecomposition` に切り出しても、その内部で同じ複雑さが現れる。

### パターンマッチ指向での定義

```egison
theorem pumping_lemma (M : DFA Q Σ) (w : List Σ)
    (h_long : |w| ≥ |Q|) (h_acc : M ⊢ w)
    : M.run(w)  matches  _ ++ $q :: _ ++ #q :: _
                   as list (M.run(w) trimmed to first |Q|+1 elements)
```

`matches` は「`M.run(w)` の最初の |Q|+1 ステップに、同じ状態が2回出現する箇所が必ずある」と主張する。これは鳩の巣原理の直接表現。pumping lemma 本体は、この pattern が成立すれば自然に従う。

この記法により以下が吸収される：

- **`IsPumpingDecomposition` の定義**: pattern 自体が分解構造を表現
- **`∃ x y z`**: list pattern `_ ++ $q :: _ ++ #q :: _` の split に吸収
- **`w = x ++ y ++ z`**: pattern の構造そのもの（list の3分割）
- **`|y| ≥ 1`**: 二つの `::` の間に少なくとも1要素が挟まる構造から自動
- **`|xy| ≤ |Q|`**: matcher の trim 制約（最初の |Q|+1 要素のみ対象）から自動
- **同状態への2回訪問**: 非線形パターン `#q`（Ramsey の `#c` と同型）
- **位置の前後関係 `i < j`**: list の順序構造から自動（WLOG 議論不要）

x, y, z は独立した存在変数ではなく、走行列の prefix / middle / suffix から派生する定義。具体的には、pattern マッチで走行列が `prefix_states ++ [q] ++ middle_states ++ [q] ++ suffix_states` の形に分かれたとき、x = w[0..|prefix_states|]、y = w[|prefix_states|..|prefix_states|+|middle_states|+1]、z = w[残り]。

Lean 4 版では (1) `∃ x y z` の明示、(2) 各連言の個別証明、(3) `i < j` の `hij` としての保持、(4) `replicate k y` による pumping の帰納証明が必要。パターンマッチ指向版ではこれらすべてが pattern の構造、matcher の意味論、および補題 `dfa_loop_iteration` に吸収される。

---

## A. Lean 4 / Mathlib スタイル

### 補助補題

```lean
-- 鳩の巣原理 (list 上): 長さが値域より大きい list の中に重複する要素が
-- 順序付きで存在する
lemma pigeonhole_list (xs : List Q) [Fintype Q]
    (h : xs.length > Fintype.card Q) :
    ∃ i j : Fin xs.length, i < j ∧ xs.get i = xs.get j := by
  by_contra h_neq
  push_neg at h_neq
  -- xs.get は単射 → |xs| ≤ |Q| となり矛盾
  have h_inj : Function.Injective xs.get := by
    intro i j h_eq
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with hlt | hgt
    · exact h_neq i j hlt h_eq
    · exact h_neq j i hgt h_eq.symm
  have := Fintype.card_le_of_injective xs.get h_inj
  simp at this
  omega

-- DFA で状態 q から q への loop は何回繰り返しても受理性に影響しない
lemma dfa_loop_iteration (M : DFA Q Σ) (x y z : List Σ) (q : Q)
    (h_x : (M.run x).getLast (by simp [DFA.run]) = q)
    (h_y : List.foldl M.step q y = q)
    (h_acc : M.accepts (x ++ y ++ z)) :
    ∀ k, M.accepts (x ++ List.replicate k y ++ z) := by
  intro k
  induction k with
  | zero => simp; exact ... -- y を消した版が受理されることを示す
  | succ k ih => ...
```

### 証明

```lean
theorem pumping_lemma (M : DFA Q Σ) (w : List Σ)
    (h_long : w.length ≥ Fintype.card Q)
    (h_acc : M.accepts w) :
    ∃ x y z, IsPumpingDecomposition M w x y z (Fintype.card Q) := by
  -- 走行列の最初の |Q|+1 要素を取り出す
  let n := Fintype.card Q
  let states := (M.run w).take (n + 1)
  have h_states_len : states.length = n + 1 := by
    simp [states, DFA.run]; omega
  -- 鳩の巣で重複状態を取り出す
  obtain ⟨i, j, hij, h_eq⟩ := pigeonhole_list states (by simp [h_states_len])
  -- 分解を構成
  let x := w.take i
  let y := (w.drop i).take (j - i)
  let z := w.drop j
  refine ⟨x, y, z, ?_, ?_, ?_, ?_⟩
  · -- w = x ++ y ++ z
    simp [x, y, z, List.take_append_drop]
    ...
  · -- |xy| ≤ n
    simp [x, y, List.length_take]
    have : (j : ℕ) ≤ n := by ...
    omega
  · -- |y| ≥ 1
    have : (i : ℕ) < j := hij
    simp [y, List.length_take]
    omega
  · -- ∀ k, M.accepts (x ++ replicate k y ++ z)
    apply dfa_loop_iteration M x y z (states.get i)
    · -- run x の最終状態が states.get i に等しい
      ...
    · -- y を読むと同じ状態に戻る（h_eq から）
      ...
    · exact h_acc
```

主張の四つの連言を `refine` で一つずつ開き、それぞれ別個に証明。長さ計算、分解の正しさ、loop の繰り返しという3種の議論が並列に展開される。

---

## B. パターンマッチ指向スタイル

### 補助補題

```egison
-- 鳩の巣原理 (list 版): 長さが値域より大きい list には
-- 同要素が前後関係で2回出現する
lemma pigeonhole_list {Q : Type} [Fintype Q] (xs : List Q) (h : |xs| > |Q|)
    : xs  matches  _ ++ $q :: _ ++ #q :: _
            as list Q := by
  -- xs から要素を順次取り出すと、|Q| 種類しかないので
  -- |Q|+1 個目で必ず重複が発生する
  ...

-- DFA の loop 繰り返し性質: 同状態に戻る部分 y は何回繰り返しても受理性が保たれる
-- 主定理の exhaustive 節で用いる
lemma dfa_loop_iteration (M : DFA Q Σ) (x y z : List Σ) (q : Q)
    : (M ⊢ x ++ y ++ z) ∧ (M.run x ends at q) ∧ (y loops q to q)
      → ∀ k. M ⊢ x ++ y^k ++ z := by
  induction k <;> simp [DFA.step_append, ...]
```

`pigeonhole_list` は pwl-ramsey の `pigeonhole_edges` に対応する補助補題。違いは matcher：

- `pigeonhole_edges`: **multiset** 上の鳩の巣（v からの5辺 → 同色3辺以上）
- `pigeonhole_list`: **list** 上の鳩の巣（|Q|+1 要素 → 同要素が順序付きで2回）

`dfa_loop_iteration` は pwl-ramsey の `two_color_exhaustive` や pwl-schur の `color_dichotomy` と同じ構造的役割：pattern マッチで吸収しきれない部分（ここでは「loop の繰り返しが受理性を保つ」という DFA 性質）を補題として外出しする。

### 証明

```egison
theorem pumping_lemma (M : DFA Q Σ) (w : List Σ)
    (h_long : |w| ≥ |Q|) (h_acc : M ⊢ w)
    : M.run(w)  matches  _ ++ $q :: _ ++ #q :: _
                   as list (M.run(w) trimmed to |Q|+1 elements) := by

  -- 走行列の最初の |Q|+1 要素は |Q| 種類の状態を含むので鳩の巣が直接適用できる
  apply pigeonhole_list

  -- pumping 性 (∀ k. xy^k z ∈ L) は loop 繰り返し補題で閉じる
  exhaustive by dfa_loop_iteration M x y z q
```

主定理本体は2行で終わる。鳩の巣補題を `apply` で呼び出し、pumping 性を `exhaustive by` で外出しするだけ。pwl-ramsey / pwl-schur と同じ「鳩の巣＋網羅性補題」の二段構成。

#### パターン変数間の関係の自動導出

list pattern `_ ++ $q :: _ ++ #q :: _` がマッチした時点で、以下が自動導出される：

1. **同状態への2回訪問**: 非線形 `#q` から、走行列の異なる2位置 i, j で同じ状態 q を訪れる。
2. **位置の前後関係 `i < j`**: list の構造から自動。最初の `_ ++` で消費された prefix の長さ = i、二つ目の `_ ++` 開始点 = j。WLOG 議論は不要。
3. **`|y| = j - i ≥ 1`**: 二つの `::` の間に必ず middle list があり、`($q ::)` と `(#q ::)` の間隔は最低1。よって y は非空。
4. **`|xy| ≤ |Q|`**: matcher の trim 制約により list 全体が |Q|+1 以下、よって j ≤ |Q|。

派生定義として x = w[0..i]、y = w[i..j]、z = w[j..]。これらは pattern マッチの prefix/middle/suffix から計算的に取り出せる。

Lean 4 版では (i, j) を `pigeonhole_list` の出力として取り出し、`i < j` を `hij` として保持し、x, y, z をそれぞれ `take` / `drop` で構成、各性質を個別に `omega` / `simp` で証明する。パターンマッチ指向版ではこれらすべてが pattern の成立と matcher の意味論から自動。

#### `exact` での証明の完了について

最深の `exhaustive by` のケースで、定理の主張 `M.run(w) matches _ ++ $q :: _ ++ #q :: _` に対して証明が完了することは、`pigeonhole_list` の戻り値である pattern マッチ自体がそのまま定理の主張に対応するため、追加の値の列挙を要しない。pwl-ramsey の `exact ⟨v, x, c, y⟩` のような明示的構成は不要で、`apply pigeonhole_list` が直接定理を閉じる。

これは pwl-ramsey や pwl-schur と異なる構造：あちらでは内側マッチで取り出した値（v, x, y, z, c）を `exact` で渡す必要があったが、Pumping ではマッチ結果そのものが定理の主張と同じ形をしているため。これは pumping lemma の構造的単純さの反映であり、pattern 言語の表現力の証左でもある。

---

## C. 比較

### 量的比較

| | Lean 4 | パターンマッチ指向 |
|---|---|---|
| 定理の主張 | `∃ x y z, IsPumpingDecomposition ...` | `M.run(w) matches _ ++ $q :: _ ++ #q :: _` |
| 補助定義 | `IsPumpingDecomposition`、`DFA.run`、`DFA.accepts` | 不要（pattern が定義） |
| 存在量化 `∃ x y z` | 明示的に `refine ⟨x, y, z, ...⟩` | list pattern の split に吸収 |
| `w = x ++ y ++ z` の証明 | `simp [List.take_append_drop]` | pattern 構造そのもの |
| `\|y\| ≥ 1` の証明 | `omega`（`i < j` 経由） | `::` 構造から自動 |
| `\|xy\| ≤ \|Q\|` の証明 | `omega`（位置範囲経由） | matcher の trim から自動 |
| `i < j` の保持 | `hij` として明示 | list 順序から自動 |
| 鳩の巣 | `pigeonhole_list`（list 上、約8行） | `pigeonhole_list`（list 上、同等） |
| 行数（主定理の証明） | 約25行 | 約2行 |
| pumping 性 `∀ k` の証明 | `dfa_loop_iteration` を `apply` | `exhaustive by dfa_loop_iteration` |

### 補助補題を含めた総量

Lean 4 版：主定理証明 約25行 + `pigeonhole_list` 約10行 + `dfa_loop_iteration` 約10行 + `IsPumpingDecomposition` 定義 = 約50行。さらに DFA, run, accepts の基本定義。

パターンマッチ指向版：主定理 約2行 + `pigeonhole_list` 約8行 + `dfa_loop_iteration` 約6行 = 約16行。`IsPumpingDecomposition` 相当は不要。

主定理本体の圧縮率が他の pwl-* より極端に高いのは、pumping lemma の主張が「鳩の巣＋構造分解」というpattern style の最も得意な形そのものだから。

### 場合分けの構造の比較

Lean 4 版は四つの連言を `refine` で開いて並列に証明する。各連言は独立した議論（長さ計算、分解の正しさ、非空性、pumping 性）で、それぞれに `omega`、`simp`、補題適用が必要。

パターンマッチ指向版は場合分けが存在しない。鳩の巣補題の単一適用と pumping 性の網羅性補題の参照のみで完結する。これは pattern が「pumping 分解の存在」をそのまま syntactic に表現しているため、複数の連言を個別に閉じる必要がない。

両者の差は **bookkeeping の有無** に最も顕著に現れる：Lean 4 版は分解の各構成要素について明示的な計算と等式変形を要し、パターンマッチ指向版は pattern と matcher の意味論にこれらを吸収させる。

---

## D. pwl-* シリーズ内での新規性

### target が「派生値」であること

pwl-pumping は pwl-* シリーズで初めて、`matches` の target が **定理パラメータの派生値** となる例。

| 定理 | target | 由来 |
|---|---|---|
| pwl-ramsey | `edge` | 定理パラメータそのもの |
| pwl-schur | `c` | 定理パラメータそのもの |
| pwl-hall | `G` | 定理パラメータそのもの |
| **pwl-pumping** | **`M.run(w)`** | **パラメータ M, w から計算される値** |

これは pwl-* の意味論の拡張：`matches` の左辺に派生値を許す。pattern 言語の表現力を「直接与えられた構造」から「構造から計算される値」に広げる。

派生値の `matches` を無制限に許すと健全性に問題が出るので、**「matcher として整合する型に値が落ちる場合のみ許す」** という制約が必要。`M.run(w)` は `list Q` 型なので `list` matcher に整合し、健全性は保たれる。この制約の意味論的詳細は別途整理が必要。

この拡張により、計算過程・アルゴリズムの中間値・derived data structure に対しても pattern 言語が適用可能になる。Bézout（ユークリッド算法の trace）、CRT（中国剰余の reconstruction trace）、Lagrange（剰余類分解）など、計算的構造を持つ多くの定理がこの拡張の恩恵を受ける。

### list matcher の導入

pwl-ramsey の multiset matcher は順序情報を持たないため、Pumping の `i < j` 制約や x/y/z の前後関係を表現できない。Pumping の鳩の巣は **順序付きの鳩の巣** であり、list matcher が本質的に必要。

これは pwl-* の研究観察：

> **数学的対象の構造的本性（順序の有無、重複の許可、構造的拘束など）が、適切な matcher の選択を強制する。**

| 数学的対象 | 適切な matcher | pwl-* での例 |
|---|---|---|
| 順序なし、重複あり | multiset | pwl-ramsey の `edge` |
| 順序なし、重複なし | set | pwl-schur の `c` |
| **順序あり、重複あり** | **list** | **pwl-pumping の `M.run(w)`** |
| 構造的制約あり | 専用 matcher | pwl-hall の `bipartite_graph` |

「定理の主張を pattern で書く」作業は、自然と「定理が本質的にどの数学的構造を使っているか」を明示化する作業になる。**multiset で書こうとして違和感がある定理は、実は list 構造を本質的に使っている**、という診断的役割を pattern 言語が果たす。

### `_ ++ x :: _` 慣用句

list pattern `_ ++ x :: _` は関数型プログラミングで「list 中のどこかに x が現れる」を表す古典的慣用句。これを2回連鎖させた `_ ++ $q :: _ ++ #q :: _` で「同要素が順序付きで2回出現」を表現。

- 第1の `_ ++ ($q ::)`: 前方のどこかで $q を取り出し、prefix の長さで位置 i が決まる
- 第2の `_ ++ (#q ::)`: 後方のどこかで同じ q を取り出し、middle の長さで間隔 j-i が決まる
- 末尾の `_`: 残りの suffix

list の順序により「前方」「後方」が自動的に意味付けされる。multiset では実現できない表現。

### Ramsey との対比

Pumping と Ramsey は **構造的に同型の鳩の巣論法** を使うが、対象の構造が異なる：

| 観点 | pwl-ramsey | pwl-pumping |
|---|---|---|
| 鳩の巣の対象 | v からの5辺 | DFA の |Q|+1 ステップ走行 |
| 容器 | multiset（順序なし） | list（順序あり） |
| 重複検出 | 同色辺3本 | 同状態2回 |
| 非線形パターン | `#c`（色の一致） | `#q`（状態の一致） |
| 派生分解 | 三角形の3頂点 (x, y, z) | 語の3分割 (x, y, z) |
| 網羅性補題 | `two_color_exhaustive` | `dfa_loop_iteration` |

両者を pwl-* 内で並べることで、「鳩の巣論法は pattern style で **構造を変えても同じ骨格で書ける**」という主張が成立する。これは pattern 言語の **汎化可能性** の証明として論文の中核主張の一つを支える。

---

## まとめ

- pumping lemma の主張は「DFA 走行内の鳩の巣」として pattern 一つで表現できる
- multiset ではなく list matcher を使うことで、順序情報・前後関係・分解構造が syntactic に保たれる
- target を派生値 `M.run(w)` に取ることで、計算的構造を持つ定理に pattern 言語が拡張される
- 主定理本体は2行に縮み、鳩の巣補題と loop 繰り返し補題のみで閉じる
- pwl-ramsey との対比により、pattern 言語が「鳩の巣論法の構造的骨格」を抽出し、対象の構造（multiset / list）に応じて自然に適応することが示される

論文 narrative としては、pwl-ramsey で multiset 上の鳩の巣を導入したあと、pwl-pumping で同じ骨格を list 上に転用する流れが説得力を持つ。「matcher を変えるだけで別分野（組合せ論 → 形式言語）に pattern style が transfer する」という主張の具体例になる。

形式言語側への拡張により、pwl-* の射程は組合せ論にとどまらず、計算的構造を持つ定理一般に及ぶことが示される。
