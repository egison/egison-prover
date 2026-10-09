# 証明の途中で使うパターン：等式変形と帰納法の例

パターンによる選択・分解を、定理の主張と証明の途中の推論に使う。
主張そのものを `matches` 命題にする中心例は [設計概要](overview.md) にある。
ここでは、等式変形や帰納法の各段階での使い方を考える。
[固定点のない対合の例](pwl-involution.md) では、要素数の偶数性と有限和の等式を扱う。

型・補助補題・主定理を含む完全なコードを次に置く。

| 例 | Lean | パターンマッチ指向版 | 証拠を明示した Lean 版 |
|---|---|---|---|
| 群の語 | [全文](examples/lean/DesignExamples/GroupWords.lean) | [全文](examples/pmop/DesignExamples/GroupWords.pmop) | [全文](examples/lean/DesignExamples/PatternStyle/GroupWords.lean) |
| 有限置換 | [全文](examples/lean/DesignExamples/Permutations.lean) | [全文](examples/pmop/DesignExamples/Permutations.pmop) | [全文](examples/lean/DesignExamples/PatternStyle/Permutations.lean) |
| 歩道と道 | [全文](examples/lean/DesignExamples/WalkPaths.lean) | [全文](examples/pmop/DesignExamples/WalkPaths.pmop) | [全文](examples/lean/DesignExamples/PatternStyle/WalkPaths.lean) |
| 隣接する同一要素の消去の局所合流性 | [全文](examples/lean/DesignExamples/LocalConfluence.lean) | [全文](examples/pmop/DesignExamples/LocalConfluence.pmop) | [全文](examples/lean/DesignExamples/PatternStyle/LocalConfluence.lean) |
| 離れた逆元対の全候補と任意の個数への拡張 | [全文](examples/lean/DesignExamples/TwoCancellations.lean) | [全文](examples/pmop/DesignExamples/TwoCancellations.pmop) | [全文](examples/lean/DesignExamples/PatternStyle/TwoCancellations.lean) |

`$x` は値を束縛し、`#e` は式 e との等式を要求する。
`::` は要素と残りへの分解、`++` は列を前後に分割するパターンである。
`match h : …` は分解の証拠を h として受け取る。
記法・依存関係・検査方法は [コードの一覧と仕様](examples/README.md) に記す。
`.pmop` の直接の検査は処理系への実装が必要である。

複数の分解を同時に扱う例として、[局所合流性](pwl-local-confluence.md) の完全なコードも置く。
同じ語から得た2つの書換えの位置関係を分類し、両結果の共通の消去先を構成する。
この例では、同じ補助補題を用いる Lean 版も短く書けるため、証明全体の短縮は確認できない。
分解の条件をパターンで読めることと、証明の記述量が減ることは、別々に評価する。

[わかりやすさと記述量の条件](proof-brevity.md) では、Ramsey を基準に、選んだ構造と推論が
読み取れるかを評価する。すべてのマッチ結果に同じ推論を適用する例も扱う。
選択の結果に分解の等式と条件の証拠を保持し、逆元対の消去について積の保存と長さの減少を示す。
任意の n 箇所への拡張では、残りについての証明を再帰関数の結果の型に含める。
所属からの証拠の復元と独立した帰納法の記述を省けるが、通常の列挙との対応証明も含む
現在の完全なコードでは総量は減らない。Lean の自動化でも短い証明が得られることを併記する。

## 1. 群の語から隣接する逆元を消去する

群 G は、結合的な積、単位元1、各要素 g の逆元 inv(g) を持つ型である。
語 w : List G は群の要素の有限列であり、eval(w) をその順の積とする。
空の語の積は1である。積の交換律は仮定しない。

語の途中に隣接して現れる g と inv(g) を消去しても、積は変わらないことを証明する。
例えば、p、g、inv(g)、q という順の語から p、q という語を作れる。
消去できる場所を次のパターンで取り出す。

```text
$pre ++ $g :: #(inv g) :: $post
```

このマッチから

\[
w=\mathrm{pre}\mathbin{++}[g,\mathrm{inv}(g)]\mathbin{++}\mathrm{post}
\]

という分解の証拠を得る。w' = pre ++ post とすると、列の連結と積の一般的な補題により、

\[
\begin{aligned}
\mathrm{eval}(w)
&=\mathrm{eval}(\mathrm{pre})\cdot(g\cdot\mathrm{inv}(g))
  \cdot\mathrm{eval}(\mathrm{post})\\
&=\mathrm{eval}(\mathrm{pre})\cdot1\cdot\mathrm{eval}(\mathrm{post})\\
&=\mathrm{eval}(w').
\end{aligned}
\]

この等式を繰り返し適用すると、隣接する逆元の組を消去する処理が語の値を保つことを証明できる。
1回の消去で語の長さが2減るため、語の長さについての帰納法で停止と値の保存を扱える。
逆元の組が存在しない場合はその語を返す。実行して消去箇所を探すには、G の等式の判定が必要になる。

この例では、取り出す位置にかかわらず、各マッチ結果に同じ等式の証明を適用する。
語全体の連結に沿って等式を持ち上げる補題と、群の結合法則・逆元の法則が必要である。
`list` マッチャーと計算を含むバリューパターンを使う例になる。

## 2. 有限置換を互換の積へ分解する帰納法

**置換** π は全単射である。コードでは π : A→A を、有限部分集合 S の外を固定する全単射として表す。
S 上の置換を、S の外で恒等写像として拡張した表現である。
**互換** τ(a,c) は異なる2要素 a,c を入れ替え、他の要素を固定する置換を表す。
定理は「任意の有限置換は有限個の互換の合成で表せる」である。

$|S|$ について帰納法を使う。S が空なら恒等置換であり、互換の個数は0でよい。
S が空でなければ a ∈ S を一つ固定する。
π のグラフを、各入力をちょうど1回含む入出力ペアの多重集合 `graph S π` として観察する。
ここでは残りの対象の型を `Multiset (A × A)` と明示する。

```text
graph S π matches (#a, #a) :: $R
  | (#a, ($b & !#a)) :: ($c, #a) :: $R
  as multiset (A × A)
```

`&` は同じ値について両方の条件を要求する andパターン、
`!#a` は a と異なることを要求するパターンである。
第1の腕は π(a) = a の場合である。R は S \ {a} 上の置換のグラフになる。
これに帰納仮定を適用し、得た互換を a を固定する置換として S 全体へ拡張する。

第2の腕は π(a) = b ≠ a と π(c) = a を取り出す。
全射性によって c が存在し、π(a) ≠ a から c ≠ a である。
R に含まれるペアと (c,b) を合わせ、T = S \ {a} 上の置換 π' を作る。
すなわち、a → b と c → a を除き、c → b でつなぎ直す。

π' が置換であることは、マッチの分解と π の全単射性から証明する。
入力側では a,c が取り除かれ、c だけが戻る。出力側では b,a が取り除かれ、b だけが戻る。
したがって入力と出力はともに T の各要素をちょうど1回含む。
この証明で、残り R の入力・出力に重複がないことも使う。

コードでは A 上の置換 π' = π ∘ τ(a,c) を直接構成する。
π' は a と S の外を固定し、T 上では上述のつなぎ直した置換として働く。
合成 (f ∘ g)(z) = f(g(z)) の向きを用いると、

\[
\pi=\pi'\circ\tau(a,c)
\]

が成立する。a では a → c → b、c では c → a → a、他の要素では π と同じ写像になる。
帰納仮定で π' の互換への分解を得て、最後に τ(a,c) を合成すればよい。
$|T|=|S|-1$ であるため、帰納仮定を適用できる。

例えば π が 1 → 3、3 → 2、2 → 1 と対応させる場合、a = 1 とすると b = 3、c = 2 である。
π' は {2,3} 上の互換になり、π = τ(2,3) ∘ τ(1,2) と得られる。

2腕の網羅性は、π(a) = a かどうかの場合分けと、π の全射性で証明する。
新たに作ったグラフが全単射であること、恒等的な拡張と合成の等式は、証明側の補題として扱う。
この例は、有限関数の複数の入出力関係を非線形パターンで取り出し、
残りから小さい構造を再構成して帰納仮定を使う設計を検討するために役立つ。

## 3. 歩道から重複頂点を除いて道を構成する

グラフの **歩道（walk）** は、隣り合う頂点が辺で結ばれた有限列である。
ここでは、頂点の重複がない歩道を **道（path）** と呼ぶ。
長さ0の、1頂点だけからなる道も許す。グラフは有向でも無向でもよい。

定理は「s から t への歩道があれば、s から t への道がある」である。
歩道を表す空でない頂点列 w の長さについて帰納法を使う。
重複頂点を含むとき、次のパターンで2回の出現とその前後を取り出す。

```text
$pre ++ $v :: $mid ++ #v :: $post
```

このマッチが与える分解は

\[
w=\mathrm{pre}\mathbin{++}[v]\mathbin{++}\mathrm{mid}
  \mathbin{++}[v]\mathbin{++}\mathrm{post}
\]

である。ここから w' = pre ++ [v] ++ post を作る。
前半の v から後半の v までの閉じた部分を除去する操作である。

w' が歩道であることを、分解の証拠と w の辺の証拠から示す。
pre から v に入る辺はそのまま使える。post が空でなければ、
後半の v から post の先頭へ出る辺を、同じ頂点である前半の v から出る辺として使える。
pre や post が空の場合も、始点 s と終点 t は保たれる。

頂点列の長さは

\[
|w|-|w'|=|\mathrm{mid}|+1>0
\]

だけ減る。mid が空でも、2回の出現の一方を除くので長さは減る。
帰納仮定を w' に適用すると、s から t への道を得る。
重複がなければ w 自体が道である。

例えば w = [s,a,b,a,t] なら、v = a、pre = [s]、mid = [b]、post = [t] を取り出し、
w' = [s,a,t] を作る。s = t の場合も、閉じた部分を順に除いて [s] という道へ進める。

「重複がある、またはない」という場合分けと、重複時の2箇所の分解を網羅性補題で与える。
各腕で受け取る位置・長さの関係を、歩道の証拠の引き継ぎと帰納法の停止に使う。
この例は [pumping lemma](pwl-pumping.md) と同じ、リスト中の同じ値の2回の出現を扱う
パターンを再利用できる。

## 主証明のコード

群の語の完全な簡約の存在証明は次のように書く。
使用する `Reduced` と `cancel_pair` の定義・証明は上記の全文に含める。

```lean
theorem exists_reduced (w : List G) :
    ∃ r, Reduced r ∧ r.prod = w.prod ∧ r.length ≤ w.length := by
  classical
  suffices h : ∀ n, ∀ w : List G, w.length = n →
      ∃ r, Reduced r ∧ r.prod = w.prod ∧ r.length ≤ w.length from h w.length w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn
    by_cases hr : Reduced w
    · exact ⟨w, hr, rfl, le_rfl⟩
    obtain ⟨pre, g, post, rfl⟩ := not_not.mp hr
    have hlt : (pre ++ post).length < n := by simp_all; omega
    obtain ⟨r, hred, hprod, hlen⟩ := ih _ hlt (pre ++ post) rfl
    refine ⟨r, hred, hprod.trans (cancel_pair pre g post).symm, ?_⟩
    simp only [List.length_append, List.length_cons] at *
    omega
```

```egison
theorem exists_reduced (w : List G) :
    ∃ r, Reduced r ∧ r.prod = w.prod ∧ r.length ≤ w.length := by
  classical
  suffices h : ∀ n, ∀ w : List G, w.length = n →
      ∃ r, Reduced r ∧ r.prod = w.prod ∧ r.length ≤ w.length from h w.length w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn
    match heq : w as list G with
    | !($pre ++ $g :: #(g⁻¹) :: $post) =>
      exact ⟨w, heq, rfl, le_rfl⟩
    | $pre ++ $g :: #(g⁻¹) :: $post =>
      subst w
      have hlt : (pre ++ post).length < n := by simp_all; omega
      obtain ⟨r, hred, hprod, hlen⟩ := ih _ hlt (pre ++ post) rfl
      refine ⟨r, hred, hprod.trans (cancel_pair pre g post).symm, ?_⟩
      simp only [List.length_append, List.length_cons] at *
      omega
    exhaustive by Classical.em (∃ pre g post, w = pre ++ g :: g⁻¹ :: post)
```

置換では、`π : Equiv.Perm A` が有限部分集合 S の外を固定すると仮定する。
この表現により、小さい集合の置換を拡張する操作を `π * swap a c` として実装できる。
`graph_cases` が2腕を証明し、`factor_of_support` が集合を1要素ずつ小さくする帰納法を完結させる。
`finite_permutation_factors` は S を型全体の有限集合に取ることで、任意の有限置換についての定理を得る。

歩道では、辺の関係を任意の `E : A → A → Prop` とし、
隣接する頂点間の辺の証拠を `List.IsChain E` で保持する。
`splice_chain` と `splice_walk` が分解後の辺と始点・終点を保つことを証明し、
`walk_to_path` が列の長さについての帰納法を完結させる。
辺の推移性、頂点型の有限性、始点と終点の相異性は要求しない。

## 4. 適用範囲と実装への示唆

| 例 | 主張の形 | 証明の途中で取り出すもの | 次に必要な推論 |
|---|---|---|---|
| [固定点のない対合](pwl-involution.md) | 要素数の偶数性、有限和の等式 | x、σ(x)、残り | 残りの閉性と帰納仮定の適用 |
| 群の語 | 積の等式、簡約処理の値の保存 | 逆元の組と前後の列 | 結合法則、逆元の法則、長さの減少 |
| 有限置換 | 互換の積としての表現 | a → b、c → a、残りのグラフ | 小さい置換の構成、合成の等式 |
| 歩道と道 | 同じ始点・終点を持つ道の存在 | 同じ頂点の2回の出現と前後の列 | 辺の証拠の引き継ぎ、長さの減少 |
| [局所合流性](pwl-local-confluence.md) | 2つの書換え結果の共通の消去先 | 同じ語に対する2箇所の一致・重なり・分離 | 一致時の反射性、分離時の残る組の消去 |
| [逆元対の全候補](proof-brevity.md) | すべての消去結果の積と長さ | 順序を保つ、互いに重ならない逆元対とその証拠 | 各結果の同じ等式変形、再帰結果の証拠の引き継ぎ |

これらには `multiset` と `list` の汎用的な分解を使える。
数学的な性質は、マッチから得た関係と、各分野の補題を組み合わせて証明する。
要素数や長さを用いた帰納法、分解で得た等式による証拠の置換、
残りからの関数の再構成を、基礎の証明規則として用意する必要がある。

評価では、主張をパターンで表せる例と、証明の途中でパターンを使う例をともに扱う。
各例について、対象の型、分解後の型、各腕で受け取る証拠、網羅性の補題、
帰納仮定に進む際の条件を明示することで、複数の証明に使える規則を確かめる。

## 5. 検証の扱い

処理系から独立した Python の有限列挙で、各変換の条件を確認した。

| 例 | 列挙した範囲 | 確認した変換 |
|---|---|---|
| 対合 | 0〜8要素上の全1,116対合と、条件を満たす7,689部分集合 | 各要素を選ぶ22,872通りで、残りの閉性、重複の不在、要素数の減少と偶数性 |
| 部分集合の符号反転 | 1〜8要素の集合の全510部分集合 | 1の追加・削除による対合、符号反転と和が0になること |
| 有限置換 | 0〜7要素上の全5,914置換 | a を指定する40,319通りで、小さい置換の全単射性と合成の等式 |
| 群の語 | 3要素上の置換の群における、長さ0〜5の全9,331語 | 5,910箇所の逆元消去で、積の保存と長さの減少 |
| 歩道 | 3頂点上の全512有向グラフ（自己ループを含む）と、頂点列の長さ1〜6の54,624歩道 | 235,776通りの重複頂点の除去で、始点・終点・辺の保存と長さの減少 |

これらの有限ケースの確認に加え、上記の Lean 版と、パターンの証拠を明示した Lean 版で
一般の定理を機械的に検査する。対合は任意の有限部分集合、群は非可換な群も含み、
置換は任意の有限置換、歩道は任意の有向・無向の辺の関係を扱う。
提案言語の直接の型検査には、[設計上の課題](review.md) に記す変換と核の実装が必要である。
逆元対の全候補については、等式の判定が可能な任意の群・有限語・消去する個数に対する証明を Lean に置く。
通常の列挙と証拠を保持する列挙が、順序と重複を含めて等しいことも検査する。
