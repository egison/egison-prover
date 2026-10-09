# 一般の有限 Hall の結婚定理

二部グラフは、左の頂点型 X、右の頂点型 Y、辺の関係 `E : X → Y → Prop` で表す。
X,Yを有限とする。左側を覆うマッチングは、各 x を隣接する頂点 f(x) に対応させ、
異なる x を異なる頂点へ写す関数 f である。

近傍 N(S) は、S のいずれかの頂点と辺で結ばれた右側の頂点全体である。
Hall 条件は、すべての有限部分集合 S について |S|≤|N(S)| という条件である。
定理は、この条件と左側を覆うマッチングの存在の同値性を述べる。
任意の大きさの有限二部グラフを扱う。

## 完全なコード

- [Lean 版の全文](examples/lean/DesignExamples/Hall.lean)
- [パターンマッチ指向版の全文](examples/pmop/DesignExamples/Hall.pmop)
- [パターンの証拠を明示した Lean 版](examples/lean/DesignExamples/PatternStyle/Hall.lean)

全文には定義・補助補題・主定理の証明を含む。共通の型、標準ライブラリへの依存、
記法、検査方法は [コードの一覧と仕様](examples/README.md) にまとめる。
Lean 版と、パターンの証拠を明示した Lean 版は Lean 4.31.0 / Mathlib v4.31.0 で検査する。
`.pmop` は完全な提案ソースであり、現在の処理系では直接検査できない。

以下は主証明を抜き出したもの。使用する定義・補助補題は上記の全文にある。

### Lean

```lean
theorem hall (E : X → Y → Prop) [DecidableRel E] (h : HallCondition E) :
    ∃ f, Matching E f := by
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x => Finset.univ.filter (E x))).mp h
  exact ⟨f, hfinj, fun x => (Finset.mem_filter.mp (hf x)).2⟩
```

### パターンマッチ指向スタイル

```egison
theorem hall (E : X → Y → Prop) [DecidableRel E]
    (h : ¬(E matches $S ⤳ $T where T.card < S.card as bipartite_graph X Y)) :
    E matches $f as matching_of E := by
  have hc : HallCondition E := (hall_iff_no_bad_pair E).mpr h
  match hf : E as matching_of E with
  | $f => exact ⟨f⟩ by exact hf
  exhaustive by hall_from_card E hc
```

## 条件と結論をパターンで書く

`$S ⤳ $T as bipartite_graph X Y` の関係は `neighbors E S ⊆ T` である。
`where T.card < S.card` を加えると、Hall 条件に違反する部分集合の組を表す。
このような組の不在が Hall 条件と同値であることを、`hall_iff_no_bad_pair` で証明する。
片方向では |S|≤|N(S)|≤|T|、逆方向では T=N(S) を使う。

`E matches $f as matching_of E` は、関数 f と、
単射性および `∀ x, E x (f x)` の証拠を持つ。
通常のパターン変数が対象そのものを束縛する場合とは異なり、
この専用マッチャーの `$f` はグラフから選ぶ関数を束縛する。

Lean 版では `hall` が存在方向、`matching_implies_hall` が逆方向を証明し、
`hall_iff_matching` が両方向をまとめる。
存在方向に利用する Mathlib の一般の有限 Hall 定理の名前と型は、コードと
[依存関係](examples/README.md) に明示する。
提案版の `hall_from_card` は同じ定理を適用する補助証明である。

## マッチャーの候補を具体的に定義する

`badPairs` は左右の全部分集合の組から、近傍の包含と要素数の不等式を満たす組を選ぶ。
`mem_badPairs` が列挙の結果とパターンの関係の同値性を証明する。
`matchings` は全関数 X→Y からマッチングの条件を満たす関数を選び、
`mem_matchings` がその所属の意味を証明する。
`pattern_hall` は違反する組の列挙が空ならマッチングの列挙が空でないことを証明する。

辺の判定を含む有限列挙には `DecidableRel E` を要求する。
数学的に任意の辺の関係を扱う場合は、古典論理による判定可能性を局所的に使える。
列挙方法の正しさと、効率のよいマッチング算法を実装することは別の作業である。
