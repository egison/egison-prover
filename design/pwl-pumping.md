# DFA の pumping lemma

DFA（決定性有限オートマトン）は、入力記号ごとに次の状態を一意に定める機械である。
`DFA Alpha Q` の状態型 Q を有限とし、開始状態を `M.start`、
指定した状態から語を読み終えた状態を `M.evalFrom` とする。
受理状態に到達する語の集合が `M.accepts` である。

受理される語 w が状態数 |Q| 以上の長さを持つなら、
w=x++y++z、y≠[]、|x|+|y|≤|Q| となる分解があり、
すべての自然数 k について x++y^k++z も受理される。
y^k は y を k 回連結した語であり、k=0 も含める。

## 完全なコード

- [Lean 版の全文](examples/lean/DesignExamples/Pumping.lean)
- [パターンマッチ指向版の全文](examples/pmop/DesignExamples/Pumping.pmop)
- [パターンの証拠を明示した Lean 版](examples/lean/DesignExamples/PatternStyle/Pumping.lean)

全文には定義・補助補題・主定理の証明を含む。共通の型、標準ライブラリへの依存、
記法、検査方法は [コードの一覧と仕様](examples/README.md) にまとめる。
Lean 版と、パターンの証拠を明示した Lean 版は Lean 4.31.0 / Mathlib v4.31.0 で検査する。
`.pmop` は完全な提案ソースであり、現在の処理系では直接検査できない。

以下は主証明を抜き出したもの。使用する定義・補助補題は上記の全文にある。

### Lean

```lean
theorem pumping_lemma (M : DFA Alpha Q) (w : List Alpha)
    (hacc : w ∈ M.accepts) (hlen : Fintype.card Q ≤ w.length) :
    ∃ x y z, IsPumpingDecomposition M w x y z := by
  obtain ⟨pre, q, mid, post, hsplit⟩ := run_repeats_state M w hlen
  obtain ⟨x, y, z, heq, hbound, hne, hx, hy, hz⟩ :=
    split_to_loop M w pre q mid post hlen hsplit
  refine ⟨x, y, z, heq, hne, hbound, ?_⟩
  intro k
  change M.evalFrom M.start (x ++ repeatWord y k ++ z) ∈ M.accept
  rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append, hx,
    loop_iteration M q y hy k, hz]
  exact hacc
```

### パターンマッチ指向スタイル

```egison
theorem pumping_lemma (M : DFA Alpha Q) (w : List Alpha)
    (hacc : w ∈ M.accepts) (hlen : Fintype.card Q ≤ w.length) :
    ∃ x y z, IsPumpingDecomposition M w x y z := by
  match hsplit : (run M w).take (Fintype.card Q + 1) as list Q with
  | $pre ++ $q :: $mid ++ #q :: $post =>
    obtain ⟨x, y, z, heq, hbound, hne, hx, hy, hz⟩ :=
      split_to_loop M w pre q mid post hlen hsplit
    refine ⟨x, y, z, heq, hne, hbound, ?_⟩
    intro k
    change M.evalFrom M.start (x ++ repeatWord y k ++ z) ∈ M.accept
    rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append, hx,
      loop_iteration M q y hy k, hz]
    exact hacc
  exhaustive by run_repeats_state M w hlen
```

## 走行列の分解から入力語の分解へ

`run M w` は、長さ0〜|w|の各入力接頭辞を読み終えた状態のリストであり、
開始状態を含むため長さは |w|+1 である。
先頭 |Q|+1 状態に対して
`$pre ++ $q :: $mid ++ #q :: $post` というパターンを使う。
`run_repeats_state` は、重複がなければ列の長さは状態数以下になることから、この分解の存在を証明する。

マッチが与える等式から、2回の出現位置を
 i=|pre|、j=|pre|+|mid|+1 と定めると i<j≤|Q| となる。
`split_to_loop` はリストの添字で両位置の状態が q であることを取り出し、
x=w.take i、y=(w.take j).drop i、z=w.drop j と構成する。
分解の等式、長さの上限、yの非空性、
xを読むとqに到達し、yを読むとqに戻り、zの後は元の受理状態に到達することを、すべて証明する。
この補題は両ソースに本体を含める。

`loop_iteration` は k についての帰納法で、qからyをk回読んでもqに戻ることを証明する。
主証明はこれを接頭辞と接尾辞の評価へ組み込み、任意のkについての受理を得る。
パターンは走行列を分解する箇所に使い、反復による受理保存も完全な証明として含める。

## 主張と分解の型

重複状態の主張と証明の腕は同じリストパターンを使う。
主定理では、語の分解と全称命題 `∀ k` を `IsPumpingDecomposition` にまとめる。
マッチから得る構造的な等式と、そこから導く状態遷移・長さの性質を明確に区別する。
字母型 Alpha の有限性や、値の等式を判定できることは、一般の数学的な定理の前提には含めない。
