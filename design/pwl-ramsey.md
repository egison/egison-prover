# Ramsey R(3,3)=6

この文書の提案例は，マッチャー定義からパターンの条件を得て暗黙に使えることを前提とする．
その具体的な機構は今後設計する．共通の方針と検査用の Lean 版との区別は
[パターンの条件を暗黙に使う方針](implicit-conditions.md) に記す．

6頂点の完全グラフの辺を赤・青の2色で塗ると、必ず単色の三角形が存在する。
5頂点では単色三角形を持たない彩色があるため、必要な頂点数は6である。
`Color` は `inductive Color where | red | blue` により定義し、
`DecidableEq`（等式を判定する方法）と `Fintype`（全要素の有限列挙）を導出する。
`Sym2 A` は順序を区別しない2要素の組であり、型自体は同じ要素の組も含む。
辺を選ぶペアパターンでは両端の相異性を要求する。
彩色関数はコードでは `coloring`，数式では $χ$ と表す．

固定した頂点 v からの5辺には同色の3辺がある。
その先の3頂点を x,y,z、色を c とすると、内部辺に c の辺があれば
v とその両端が単色三角形を作る。内部辺に c がなければ、x,y,z 自身が反対色の三角形を作る。

## 完全なコード

- [Lean 版の全文](examples/lean/DesignExamples/Ramsey.lean)
- [パターンマッチ指向版の全文](examples/pmop/DesignExamples/Ramsey.pmop)
- [パターンの証拠を明示した Lean 版](examples/lean/DesignExamples/PatternStyle/Ramsey.lean)

全文には定義・補助補題・主定理の証明を含む。共通の型、標準ライブラリへの依存、
記法、検査方法は [コードの一覧と仕様](examples/README.md) にまとめる。
Lean 版と、パターンの証拠を明示した Lean 版は Lean 4.31.0 / Mathlib v4.31.0 で検査する。
`.pmop` は完全な提案ソースであり、現在の処理系では直接検査できない。

以下は主証明を抜き出したもの。使用する定義・補助補題は上記の全文にある。

### Lean

```lean
theorem ramsey_six (coloring : Sym2 (Fin 6) → Color) :
    ∃ x y z : Fin 6, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      coloring s(x, y) = coloring s(y, z) ∧ coloring s(y, z) = coloring s(x, z) := by
  let v : Fin 6 := 0
  obtain ⟨c, hc⟩ := pigeonhole_edges coloring v
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (neighbors coloring v c).card)
  have hvx := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1
  have hvy := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
  have hvz := (Finset.mem_erase.mp (Finset.mem_filter.mp hz).1).1
  have evx := (Finset.mem_filter.mp hx).2
  have evy := (Finset.mem_filter.mp hy).2
  have evz := (Finset.mem_filter.mp hz).2
  by_cases hcx : coloring s(x, y) = c
  · exact ⟨v, x, y, hvx.symm, hxy, hvy.symm, evx.trans hcx.symm, hcx.trans evy.symm⟩
  by_cases hcy : coloring s(y, z) = c
  · exact ⟨v, y, z, hvy.symm, hyz, hvz.symm, evy.trans hcy.symm, hcy.trans evz.symm⟩
  by_cases hcz : coloring s(x, z) = c
  · exact ⟨v, x, z, hvx.symm, hxz, hvz.symm, evx.trans hcz.symm, hcz.trans evz.symm⟩
  have exy := Color.eq_opposite_of_ne hcx
  have eyz := Color.eq_opposite_of_ne hcy
  have exz := Color.eq_opposite_of_ne hcz
  exact ⟨x, y, z, hxy, hyz, hxz, exy.trans eyz.symm, eyz.trans exz.symm⟩
```

### パターンマッチ指向スタイル

```egison
theorem ramsey_six (coloring : Sym2 (Fin 6) → Color) :
    coloring matches ($x, $y) → $c :: (#y, $z) → #c :: (#z, #x) → #c :: _
      as multiset (Sym2 (Fin 6) → Color) := by
  let v : Fin 6 := 0
  match coloring as multiset (Sym2 (Fin 6) → Color) with
  | (#v, $x) → $c :: (#v, $y) → #c :: (#v, $z) → #c :: _ =>
    match coloring as multiset (Sym2 (Fin 6) → Color) with
    | (($p & (#x | #y | #z)),
       ($q & (#x | #y | #z))) → #c :: _ =>
      exact ⟨v, p, c, q⟩
    | (#x, #y) → #(c.opposite) ::
      (#y, #z) → #(c.opposite) ::
      (#z, #x) → #(c.opposite) :: _ =>
      exact ⟨x, y, c.opposite, z⟩
    exhaustive by
      triangle_two_color_exhaustive coloring c x y z
  exhaustive by
    pigeonhole_edges_at coloring v
```

## 条件の暗黙の利用

結論のパターン変数は初出順に `x,y,c,z` なので，第1の腕は `⟨v,p,c,q⟩`，
第2の腕は `⟨x,y,c.opposite,z⟩` を与える．第1の腕では，外側の星の条件と
`p,q ∈ {x,y,z}`，`p ≠ q`，`coloring s(p,q) = c` を合わせ，
`v ≠ p`，`p ≠ q`，`v ≠ q` と三辺の色を示す．第2の腕では，
外側の三頂点の相異性と，内側の反対色の三辺を使う．順序なしペアの対称性も使う．
内側の網羅性補題が要求する三頂点の相異性は，外側の条件から補うものとする．
条件をマッチャー定義から得て合成し，これらの証明項を構成する具体的な機構は今後設計する．

## パターンが与える条件

`$x` は値の束縛、`#e` は式 e との等式を要求するバリューパターンである。
関数 `coloring` を全入出力ペアの多重集合として観察する。
外側のパターンが与える `Star` は、v と各頂点の相異性、
x,y,z の相異性、v からの3辺の色が c であることを含む。
網羅性補題 `pigeonhole_edges_at` は、色ごとの近傍の要素数の和が5であることを証明し、
要素数が3以上の色の集合から3頂点を取り出す。補題の証明も両版の全文に含める。

内側の第1の腕では p,q が x,y,z のいずれかであること、p≠q、辺の色を受け取る。
第2の腕では3辺が反対色であることを受け取る。
`triangle_two_color_exhaustive` が両腕の網羅性を証明する。
第2の腕は前の腕の探索失敗に依存せず、その腕の色の証拠だけを使う。
主張と証明中の分解を同じパターンで書けることが、この例の中心である。

多重集合の `::` は異なる出現を選ぶ。関数のグラフでは各入力辺が一度だけ現れ、
共通端点を持つ辺の相異性から x,y,z の相異性を導ける。
残りを束縛する場合の型は `Multiset (Sym2 (Fin 6) × Color)` である。
内側の照合は元の `coloring` を再び観察するため、残りを全関数として扱う処理は必要ない。

## 配置と推論の対応

外側のパターンには v からの同色3辺、内側の各腕にはその先の3頂点の内部辺の条件、
主張には単色三角形が現れる。読者は、選ぶ配置と、その配置から結論を作る理由を
証明の記述に沿って追える。共通の頂点を `#v`、共通の色を `#c` として辺のところに書くことで、
構成要素の関係も同じ場所に示せる。

この例は、[わかりやすさの評価条件](proof-brevity.md) の基準とする。
選んだ構造，場合分けの理由，結論の構成の対応を確認し，
補助証明を含む記述量と区別して比較する．

## 同じ補助補題を与えた比較

[PatternContracts.lean](examples/lean/DesignExamples/PatternContracts.lean) の
`ramsey_six_shared_helpers` は，通常の Lean にも星の存在と内部辺の網羅性の
補題を与えた主証明である．両分岐は，存在命題と選言の通常の除去で記述できる．
したがって，三辺の個別の検査を二つの場合へまとめた効果は，補助補題の効果として扱う．
パターンが選んだ辺と共有する値を分岐に示す効果や，保持した条件から証拠を補う
機構による効果と区別する．この比較も `lake build` と公理依存の検査に含める．

## 下界のコード

`counterexample` は5角形の周上の辺を赤、対角線を青に塗る。
`ramsey_five_counterexample` が単色三角形の不在を `decide` で証明する。
自己ループは言明に直接記述した頂点の相異性によって除外される。
上界と下界の両方を全文に含める。

`pattern_iff_ordinary` がパターンで表す主張と通常の存在命題の同値性を証明する。
証拠を明示した Lean 版にもこの同値性の完全な証明を含める。
