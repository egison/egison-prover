# 構造と推論が見える証明の例

[わかりやすさの基準](proof-brevity.md) に従い、選ぶ配置、構成要素の関係、場合分けの理由、
結論の作り方をパターンから読める例を比較する。
**解消規則の正しさ**、**閉じた歩道の挿入**、**行列式の積の公式**を、完全なコードで比較する。
推論の形、構造の接続、等式を証明する途中の打ち消しを、パターンから読めるようにする。

既存の例も含めると、次がこの基準に合う。

| 例 | パターンに現れる配置 | その配置を使う推論 |
|---|---|---|
| [Ramsey](pwl-ramsey.md) | 同色3辺と、その先の三角形 | 内部辺の色で場合分けし、単色三角形を作る |
| 解消規則 | p を含む節と、¬p を含む節、その残り | p の真偽にかかわらず、残りを合わせた節が真になる |
| 閉じた歩道の挿入 | 元の歩道の途中の v と、v から出て v に戻る歩道 | 同じ頂点で接続し、始点・終点を保った歩道を作る |
| 行列式の積の公式 | 中間の添字を選ぶ写像の、同じ像を持つ二つの入力 | その2位置を交換し、重みが同じで符号が反対の項を打ち消す |
| [Pumping](pwl-pumping.md) | 走行列の同じ状態が現れる2位置 | その間をループとして反復する |
| [局所合流性](pwl-local-confluence.md) | 二つの消去箇所の一致・重なり・分離 | 位置関係ごとに共通の消去先を作る |
| [Schur](pwl-schur.md) | x、y、x+y と共通の色 | 加法の関係を持つ同色の三つ組を作る |

Ramsey と解消規則では、選んだ要素の関係が場合分けと結論に直接つながる。
歩道の挿入と pumping lemma では、パターンで選んだ区間が、その後の構成に直接使われる。
局所合流性では、各腕が数学的な位置関係を表すことに価値がある。
Schur は主張の x+y と色の関係が見え、証明では個々の数の色を順に調べる。
行列式では、選んだ二つの入力の像が等しいことが、交換後の積を保つ理由になる。
何が見えるようになるかを例ごとに示し、すべてを同じ効果として扱わない。

## 1. 解消規則：相補的なリテラルを含む二つの節

**リテラル**は命題変数 p、またはその否定 ¬p である。
**節**はリテラルの選言であり、いずれかのリテラルが真なら真になる。
論理式を節の連言として表し、すべての節が真なら論理式も真とする。
SAT は、この論理式を真にする割当が存在するかを調べる問題である。

**解消規則（resolution）**は、p∨X と ¬p∨Y から X∨Y を導く規則である。
ここで X と Y は、それぞれ選んだリテラルを取り除いた残りの節である。

```text
p ∨ X       ¬p ∨ Y
------------------
       X ∨ Y
```

コードでは節をリテラルの多重集合として表す。
多重集合は順序を区別せず、同じリテラルの複数回の出現を許す。
`pos p` と `neg p` が正・負のリテラル、`xs + ys` が残りを合わせた節である。
多重集合の `::` は一つの出現と残りへ分解する。
照合する C,D は元の二つの節、R は結論の節である。

```egison
match heq : (C, D, R) as
    (multiset (Literal V), multiset (Literal V), multiset (Literal V)) with
| (pos $p :: $xs, neg #p :: $ys, #(xs + ys)) =>
```

第一の節で選んだ p を第二の節で `#p` として参照するため、同じ変数の正・負の出現が見える。
第三の成分は、与えられた結論 R が残り xs,ys を合わせた節であることを示す。
各対象がどの前提・結論を表すかを、この一つの形で読める。

### 主証明

`σ : V → Prop` は各変数に対応する命題を与える割当である。
`ClauseHolds σ C` は、その割当で節 C が真になることを表す。
`Resolves C D R` は上の分解の存在と三つの等式を表す関係であり、正しさの結論を含まない。

通常の Lean では、その関係の証拠から構成要素を取り出す。

```lean
theorem resolution_sound (σ : V → Prop) {C D R : Clause V} (h : Resolves C D R)
    (hC : ClauseHolds σ C) (hD : ClauseHolds σ D) : ClauseHolds σ R := by
  classical
  obtain ⟨p, xs, ys, rfl, rfl, rfl⟩ := h
  by_cases hp : σ p
  · apply (clause_add σ _ _).mpr
    right
    simpa [clause_cons, Holds, hp] using hD
  · apply (clause_add σ _ _).mpr
    left
    simpa [clause_cons, Holds, hp] using hC
```

提案ソースでは、同じ推論を選んだ節の形に続けて書く。

```egison
theorem resolution_sound (σ : V → Prop) {C D R : Clause V} (h : Resolves C D R)
    (hC : ClauseHolds σ C) (hD : ClauseHolds σ D) : ClauseHolds σ R := by
  classical
  match heq : (C, D, R) as
      (multiset (Literal V), multiset (Literal V), multiset (Literal V)) with
  | (pos $p :: $xs, neg #p :: $ys, #(xs + ys)) =>
    subst C D R
    by_cases hp : σ p
    · apply (clause_add σ _ _).mpr
      right
      simpa [clause_cons, Holds, hp] using hD
    · apply (clause_add σ _ _).mpr
      left
      simpa [clause_cons, Holds, hp] using hC
  exhaustive by h
```

p が真なら ¬p は偽なので、第二の節の残り ys が真である。
p が偽なら、第一の節の残り xs が真である。
どちらの場合も xs+ys が真になる。
`clause_cons` と `clause_add` は、それぞれ節の分解・合併を選言として解釈する汎用補題であり、
その証明を両版で共有する。解消規則の正しさそのものは、上の腕で証明する。

### 導出全体への適用と具体例

`Derivable F C` は、元の論理式 F の節から有限回の解消で C を導けることを表す帰納型である。
`derivable_sound` は導出についての帰納法で、各段階の結果が真であることを示す。
解消の段階では、二つの前提についての帰納仮定を `resolution_sound` へ渡す。
空の節は常に偽なので、空の節の導出から元の論理式の充足不可能性を得る。

具体例は次の3節である。

```text
p        ¬p ∨ q        ¬q
 \       /             /
     q                /
       \             /
          空の節
```

`example_derivation` はこの2段階の導出を構成し、両版の `example_unsatisfiable` が
真にする割当の不在を証明する。一般の正しさは任意の変数型、任意の節・有限導出について成立し、
変数の有限性や等式の判定可能性を要求しない。真偽の分岐には古典論理を使う。

| 内容 | Lean | 提案ソース |
|---|---|---|
| 型、意味、規則、具体的な導出 | [ResolutionCommon.lean](examples/lean/DesignExamples/ResolutionCommon.lean) | [ResolutionCommon.pmop](examples/pmop/DesignExamples/ResolutionCommon.pmop) |
| 規則・導出の正しさと充足不可能性 | [Resolution.lean](examples/lean/DesignExamples/Resolution.lean) | [Resolution.pmop](examples/pmop/DesignExamples/Resolution.pmop) |
| パターンの関係と腕の手動展開 | [PatternStyle/Resolution.lean](examples/lean/DesignExamples/PatternStyle/Resolution.lean) | — |

この配置は [pmo-paper3 の SAT の例](../../pmo-paper3/main.tex) で、解消の結果を列挙するために
使われている。本例は同じ配置を、推論の正しさの証明と帰納仮定の適用に使う。

## 2. 閉じた歩道を共有頂点で挿入する

**歩道**は隣り合う頂点が辺で結ばれた列、**閉じた歩道**は始点と終点が同じ歩道である。
頂点や辺の重複を許す。辺の関係 `E : A → A → Prop` は任意とし、有向グラフも扱う。

s から t への歩道 w が頂点 v を通り、別の歩道が v から出て v に戻るとする。
w のその位置で閉じた歩道を挟み込むと、s から t への新しい歩道を作れる。

```text
元の歩道： pre ++ v :: post
挿入する歩道：v :: (mid ++ [v])
新しい歩道：pre ++ v :: (mid ++ v :: post)
```

二つの対象を同時に照合する。

```egison
match heq : (w, loop) as (list A, list A) with
| ($pre ++ #v :: $post, #v :: $mid ++ #v :: []) =>
```

元の歩道の途中と、閉じた歩道の両端に `#v` が現れるため、どこで接続できるかを読める。
選んだ pre,mid,post を、新しい歩道の同じ場所に置いて構成する。
一頂点だけの閉じた歩道 `[v]` も許し、その腕では元の歩道を返す。

### 主証明

`Walk E s t w` は、辺がつながり、始点が s、終点が t であることを表す。
`Inserted v w loop r` は上の挿入の形で r が作られるという関係である。
主定理は、この関係、歩道の性質、長さの関係をすべて満たす r の存在を示す。

```egison
theorem insert_closed_walk (E : A → A → Prop) (s t v : A) (w loop : List A)
    (hw : Walk E s t w) (hc : Walk E v v loop) (hv : v ∈ w) :
    ∃ r, Inserted v w loop r ∧ Walk E s t r ∧ r.length + 1 = w.length + loop.length := by
  match heq : (w, loop) as (list A, list A) with
  | ($pre ++ #v :: $post, #v :: []) =>
    subst w loop
    refine ⟨pre ++ v :: post, ⟨pre, post, rfl, Or.inl ⟨rfl, rfl⟩⟩, hw, ?_⟩
    simp
  | ($pre ++ #v :: $post, #v :: $mid ++ #v :: []) =>
    subst w loop
    exact ⟨pre ++ v :: (mid ++ v :: post),
      ⟨pre, post, rfl, Or.inr ⟨mid, rfl, rfl⟩⟩,
      insert_walk E s t pre v mid post hw hc, insert_length pre v mid post⟩
  exhaustive by insertion_cases E hv hc
```

通常の Lean 版では、`List.mem_iff_append` で v の位置を取り出し、`closed_split` で閉じた歩道の
両端を取り出す。以降は同じ構成と同じ補助証明を使う。

網羅性の補題 `insertion_cases` は v の所属と閉じた歩道の両端から二つの形を導く。
挿入後の歩道の正しさを網羅性の前提に置かない。
`insert_chain` は、元の歩道の前半、閉じた歩道、元の歩道の後半を共有する v で接続する。
`insert_walk` は始点・終点の保存も示し、`insert_length` は長さの増加を示す。
長さは閉じた歩道の辺の数、すなわち `loop.length - 1` だけ増える。
pre,mid,post は空でもよく、s,t,v の相異性、頂点の有限性や等式の判定可能性も要求しない。

### 具体例

```text
元の歩道：    [0,1,4]
閉じた歩道：  [1,2,3,1]
挿入後：      [0,1,2,3,1,4]
```

辺 0→1、1→4、1→2、2→3、3→1 を持つ具体的なグラフを `exampleEdges` として定義する。
`example_insertion` は、構成の関係、歩道の性質、長さの関係を上の列について証明する。

| 内容 | Lean | 提案ソース |
|---|---|---|
| 型、網羅性、接続の証明、具体例 | [WalkInsertionCommon.lean](examples/lean/DesignExamples/WalkInsertionCommon.lean) | [WalkInsertionCommon.pmop](examples/pmop/DesignExamples/WalkInsertionCommon.pmop) |
| 挿入した歩道の構成 | [WalkInsertion.lean](examples/lean/DesignExamples/WalkInsertion.lean) | [WalkInsertion.pmop](examples/pmop/DesignExamples/WalkInsertion.pmop) |
| パターンの関係と腕の手動展開 | [PatternStyle/WalkInsertion.lean](examples/lean/DesignExamples/PatternStyle/WalkInsertion.lean) | — |

`Walk` は [歩道から道への変換](pwl-proof-steps.md) と共有する。
その例が同じ頂点の間を除くのに対し、本例は同じ頂点で別の歩道を挟み込む。
どちらも選んだ頂点と区間を、構成結果へ引き継ぐ使い方である。

## 3. 行列式の積の公式：同じ中間添字を使う項を打ち消す

行列式の積の公式は、正方行列 M,N について

\[
\det(MN)=\det(M)\det(N)
\]

を述べる。行列式を置換の符号付きの和として展開し、行列積の各成分も展開すると、
中間添字を選ぶ写像 p と、置換 σ についての和になる。
**置換**は有限集合から自身への全単射、**互換**は異なる2要素を交換する置換である。
置換の符号は +1 または −1 であり、互換を合成すると反転する。

\[
\det(MN)
=\sum_{p:I\to I}\sum_{\sigma\in\mathrm{Perm}(I)}
  \operatorname{sgn}(\sigma)\prod_{x\in I}M_{\sigma(x),p(x)}N_{p(x),x}.
\]

p が単射でなければ、i≠j かつ p(i)=p(j)=k となる二つの入力を選べる。
単射とは、異なる入力が必ず異なる出力を持つ写像である。
提案ソースでは、写像の入出力ペアを多重集合として観察し、次の形で選ぶ。

```text
$i → $k :: $j → #k :: _
```

全入力を1回ずつ観察するため、二つの選択は異なる入力 i,j を持つ。
同じ中間添字 k はパターンの二つの出力に現れる。
この i,j を使って、σ を σ∘swap(i,j) に対応させる。
二つの M の因子は

\[
M_{\sigma(i),k}M_{\sigma(j),k}
\quad\longleftrightarrow\quad
M_{\sigma(j),k}M_{\sigma(i),k}
\]

となるので積を保ち、N の因子は変わらない。符号だけが反転し、二つの項の和は0になる。
交換を2回行うと元に戻り、i≠j なので置換 σ 自身と対応先は異なる。
このような、2回の適用で元に戻る写像を**対合**という。
同じ p に対する和の中では i,j を一度選んで固定するため、対応付けも一貫して定まる。

### 証明の中心部分と全体

通常の Lean では `Function.not_injective_iff` から i,j と等式を取り出す。
提案ソースの主たる違いは、この選択を交換のすぐ前のパターンとして表すことである。
`ε σ` は σ の符号を係数の環へ移した値である。
環は加減乗算ができる型で、ここでは乗算の交換律も仮定する。

```egison
theorem noninjective_cancel {M : Matrix I J R} {N : Matrix J I R} {p : I → J}
    (hp : ¬Injective p) :
    (∑ σ : Perm I, ε σ * ∏ x, M (σ x) (p x) * N (p x) x) = 0 := by
  match h : p as multiset (I → J) with
  | $i → $k :: $j → #k :: _ =>
    have hij : i ≠ j := h.1
    have hpij : p i = p j := h.2.1.trans h.2.2.symm
    exact
      sum_involution (fun σ _ => σ * Equiv.swap i j)
        (fun σ _ => by
          have : (∏ x, M (σ x) (p x)) = ∏ x, M ((σ * Equiv.swap i j) x) (p x) :=
            Fintype.prod_equiv (swap i j) _ _ (by simp [apply_swap_eq_self hpij])
          simp [this, sign_swap hij, -sign_swap', prod_mul_distrib])
        (fun σ _ _ => (not_congr mul_swap_eq_iff).mpr hij) (fun _ _ => mem_univ _) fun σ _ =>
        mul_swap_involutive i j σ
  exhaustive by shared_image_of_not_injective p hp
```

`sum_involution` は、有限和の項を固定点のない対合で組にし、各組の和が0なら全体の和が0と
なることを述べる汎用補題である。積の保存、符号の反転、固定点の不在、2回の交換で戻ることは、
上の腕で証明する。`shared_image_of_not_injective` は分解の存在だけを示す補題である。

有限集合 I から自身への写像では、単射であることと全単射であることが同値である。
したがって全単射でない p の項が消え、残った p を置換として添字付け直せる。
残りの二重和を整理すると det(M)det(N) になる。
両版の `det_product` は、展開、打ち消し、全単射の項の整理をすべて含む。
Mathlib の [行列式の証明](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det_mul)
に基づき、同じ展開・有限和・積・置換の補題を使う。
通常の版も同じ像を持つ2添字を直接取り出すため、選択の関係と後続の交換の対応を比較できる。

検査する主定理は任意の有限な添字型 I と任意の可換環 R について成立する。
打ち消しの補題 `noninjective_cancel` は、M が I×J、N が J×I の長方形行列の場合も扱い、
中間添字型 J の有限性を要求しない。証明では2で割らず、各組の和が0であることを使う。

| 内容 | Lean | 提案ソース |
|---|---|---|
| 同じ像を持つ二つの入力と網羅性 | [DeterminantProductCommon.lean](examples/lean/DesignExamples/DeterminantProductCommon.lean) | [DeterminantProductCommon.pmop](examples/pmop/DesignExamples/DeterminantProductCommon.pmop) |
| 打ち消しと行列式の積の公式の全証明 | [DeterminantProduct.lean](examples/lean/DesignExamples/DeterminantProduct.lean) | [DeterminantProduct.pmop](examples/pmop/DesignExamples/DeterminantProduct.pmop) |
| パターンの関係と腕の手動展開 | [PatternStyle/DeterminantProduct.lean](examples/lean/DesignExamples/PatternStyle/DeterminantProduct.lean) | — |

Mathlib から改変した証明部分の著作権表示を各ソースに残し、Apache 2.0 のライセンスを
[LICENSE-Mathlib](examples/LICENSE-Mathlib) に置く。

## 4. 重要な定理の証明へ広げる候補

### Cauchy–Binet の公式

m×n 行列 A と n×m 行列 B について、積の行列式を部分行列の行列式の和で表す。
A の S 列と B の S 行を、同じ昇順の添字で並べた正方行列をそれぞれ A[:,S],B[S,:] とすると、

\[
\det(AB)=\sum_{S\subseteq\{1,\ldots,n\},\ |S|=m}
  \det(A[:,S])\det(B[S,:]).
\]

上の打ち消しはこの証明でも使える。展開の中間添字を選ぶ写像 p:{1,…,m}→{1,…,n} のうち、
同じ像を持つ2入力がある場合を同じパターンで取り出し、その p の項を打ち消す。
単射の p を、その像 S と S を並べる置換へ分けると右辺になる。
[公式と打ち消しの証明](https://faabian.github.io/algebraic-combinatorics/blueprint/sect0037.html)
を参照する。正方行列の場合は上の積の公式になる。

任意の長方形行列についての打ち消しは検査済みである。
公式全体へ進めるには、単射の写像を像と置換で添字付け直す証明と、
二つの部分行列の行列式へ和を分ける証明を加える。
等式を証明する途中で、パターンによる選択が項の消去に直接使われる候補である。

### Lindström–Gessel–Viennot の補題

有限有向グラフに有向閉路がないとする。辺の重みを可換環の値とし、道の重みを通る辺の重みの積とする。
aᵢ から bⱼ への道の重みの総和を行列の (i,j) 成分に置くと、その行列式は、
頂点を共有しない道の組の重みの符号付きの和になる。
符号は終点の対応を表す置換の符号である。
証明では、交差する道の組を打ち消す。
[定理と証明](https://ocw.mit.edu/courses/18-212-algebraic-combinatorics-spring-2019/resources/mit18_212s19_lec36/)
にこの操作が示されている。

選んだ二つの道 Pᵢ,Pⱼ を同時に分解するパターンの形は、次のようになる。

```text
($preI ++ $v :: $tailI, $preJ ++ #v :: $tailJ)
```

同じ頂点 v 以降の部分を交換すると、構成結果は次の形になる。

```text
(preI ++ v :: tailJ, preJ ++ v :: tailI)
```

共有頂点、交換する部分、終点の交換が、選択と構成の形から見える。
二つの道を合わせて通る辺は重複も含めて保存されるため、重みの積を保ち、符号は反転する。
道の形を組み替える操作で行列式の等式を証明するため、数学的な構成と代数的な結論の対応が明瞭である。

対合を作るには、交点の選び方も定める必要がある。
交差する道のうち最小の添字 i、その道で最初の交点 v、v を通る他の道の最小の添字 j を選ぶ。
交換後もこの i,v,j が選ばれることを証明することで、2回の適用で元に戻る。
存在だけを保証する任意のマッチ結果からは、この選択の保存は導かれない。
パターンは配置を表し、交点の選択条件と保存の証明も明示して渡す設計が必要になる。
この定理全体と、重みの保存・符号反転・選択の保存は、完全な両版を作る次の対象である。

### オイラー閉路の存在定理

有限で連結な無向グラフは、すべての頂点の次数が偶数なら、すべての辺をちょうど1回通って
出発点に戻る**オイラー閉路**を持つ。次数は頂点につながる辺の数である。
証明では、一度作った閉じた歩道上の頂点から、未使用の辺だけで別の閉じた歩道を作り、
共有頂点で挿入する操作を繰り返す。
[構成による証明](https://www.maths.tcd.ie/~stalker/22C00/notes/7.10-eulerian-trails-and-circuits.html)
で使われるこの操作を、§2 のパターンで示せる。

定理全体へ進めるには、辺を1回ずつ通る条件、使用した辺の集合と残りの辺の集合、
残りの次数の偶数性、未使用の辺があるとき共有頂点を選べることを証明する。
挿入によって使用済みの辺が増え、有限回で全辺を使うことも示す。
§2 の検査済み `Walk` は辺の反復を許すため、これらの証拠を加えてオイラー閉路を構成する。

これらの候補では、**証明中に条件を満たす部分構造を選び、それを組み替えて等式や存在を導く**。
行列式の打ち消しと道の接続を合わせて扱うことで、等式の証明と構成的な存在証明の両方を比較できる。

## 検査と設計への反映

§1–3 の通常の Lean 版と、パターンの証拠を手動で展開した版を `lake build` に含める。
全定義と補助証明を保存し、両版で同じ数学的なライブラリと補助補題を使う。
[Audit.lean](examples/lean/Audit.lean) で公理への依存を確認する。
検査環境と `.pmop` の位置付けは [コードの仕様](examples/README.md) に揃える。
`.pmop` の構文解析と証明項への自動変換は実装する必要がある。

設計上は、**複数の構成要素が共有する値を、選択の形と構成結果の両方に示せること**を重視する。
解消規則では共有する変数 p、歩道の挿入では共有する頂点 v が推論を成立させる。
したがって、複数の前提から選んだ部分構造が同じ値でつながり、残りを使って結論を作る証明は、
次の例を探す際にも有望な候補となる。
主張と腕が同じ関係を使い、その関係の証拠を場合分け・再構成・帰納仮定へ渡せることを検査する。
