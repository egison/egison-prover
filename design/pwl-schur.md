# Schur S(2)=4

この文書の提案例は，マッチャー定義からパターンの条件を得て暗黙に使えることを前提とする．
その具体的な機構は今後設計する．共通の方針と検査用の Lean 版との区別は
[パターンの条件を暗黙に使う方針](implicit-conditions.md) に記す．

ここでは Schur 数を「単色の x+y=z を避けられる最大の区間の長さ」と定義する。
{1,…,5} の任意の2色塗りには、x,y,x+y が同色となる組があり、
{1,…,4} にはそのような組を持たない彩色がある。x=y も許す。
有限型 `D` の5つの値を `D.val` で自然数1〜5に写す。

証明は 1+1=2、2+2=4、1+4=5、2+3=5、1+3=4 の5つの組を使う。
1の色を col と束縛し、2、4、5、3の色を順に場合分けする。

## 完全なコード

- [Lean 版の全文](examples/lean/DesignExamples/Schur.lean)
- [パターンマッチ指向版の全文](examples/pmop/DesignExamples/Schur.pmop)
- [パターンの証拠を明示した Lean 版](examples/lean/DesignExamples/PatternStyle/Schur.lean)

全文には定義・補助補題・主定理の証明を含む。共通の型、標準ライブラリへの依存、
記法、検査方法は [コードの一覧と仕様](examples/README.md) にまとめる。
Lean 版と、パターンの証拠を明示した Lean 版は Lean 4.31.0 / Mathlib v4.31.0 で検査する。
`.pmop` は完全な提案ソースであり、現在の処理系では直接検査できない。

以下は主証明を抜き出したもの。使用する定義・補助補題は上記の全文にある。

### Lean

```lean
theorem schur_two (c : D → Color) : ∃ x y z, Monochromatic c x y z := by
  let col := c .one
  by_cases h2 : c .two = col
  · exact ⟨.one, .one, .two, col, rfl, rfl, h2, rfl⟩
  have h2' := Color.eq_opposite_of_ne h2
  by_cases h4 : c .four = col.opposite
  · exact ⟨.two, .two, .four, col.opposite, h2', h2', h4, rfl⟩
  have h4' : c .four = col := by
    have h := Color.eq_opposite_of_ne h4
    simpa using h
  by_cases h5 : c .five = col
  · exact ⟨.one, .four, .five, col, rfl, h4', h5, rfl⟩
  have h5' := Color.eq_opposite_of_ne h5
  by_cases h3 : c .three = col.opposite
  · exact ⟨.two, .three, .five, col.opposite, h2', h3, h5', rfl⟩
  have h3' : c .three = col := by
    have h := Color.eq_opposite_of_ne h3
    simpa using h
  exact ⟨.one, .three, .four, col, rfl, h3', h4', rfl⟩
```

### パターンマッチ指向スタイル

```egison
theorem schur_two (c : D → Color) :
    graph c matches $x → $col :: $y → #col :: #(x+y) → #col :: _
      as set (Nat × Color) := by
  match c as set (D → Color) with
  | #D.one → $col :: _ =>
    match c D.two as value Color with
    | #col =>
      exact ⟨1, col, 1⟩
    | #(col.opposite) =>
      match c D.four as value Color with
      | #(col.opposite) =>
        exact ⟨2, col.opposite, 2⟩
      | #col =>
        match c D.five as value Color with
        | #col =>
          exact ⟨1, col, 4⟩
        | #(col.opposite) =>
          match c D.three as value Color with
          | #(col.opposite) =>
            exact ⟨2, col.opposite, 3⟩
          | #col =>
            exact ⟨1, col, 3⟩
          exhaustive by (by simpa only [Color.opposite_opposite] using
            color_cases (c D.three) col.opposite)
        exhaustive by color_cases (c D.five) col
      exhaustive by (by simpa only [Color.opposite_opposite] using
            color_cases (c D.four) col.opposite)
    exhaustive by color_cases (c D.two) col
  exhaustive by at_key c D.one
```

## 同じ要素の再選択と加法の関係

`set` の `::` は所属する要素を選び、対象を減らさない。
1+1=2 と 2+2=4 の腕では同じ入力を2回選ぶので、この性質が必要である。
多重集合から出現を除いていく照合とは異なる。

`graph c` は `(d.val, c d)` の有限集合である。
結論の `$x → $col :: $y → #col :: #(x+y) → #col :: _` は、
3つのペアがこのグラフに所属することを表す。
x と y は自然数として束縛され、`#(x+y)` も自然数である。
和が1〜5の外にあると該当するキーが存在せず、マッチは成立しない。
この形では、範囲外の和を有限型の値に無理に変換する必要がない。

各腕は，観察した色の等式を暗黙に保持する．`exact ⟨x,col,y⟩` は値だけを与え，
`mem_graph` と色の等式，加法の計算から，結論が要求する3つの所属の証明項を構成するものとする．
例えば最初の腕では `c D.one = col` と `c D.two = col` から，
`(1,col)`，`(1,col)`，`(2,col)` の所属を示す．条件の取得とこの構成の機構は今後設計する．
キー1の観察は `at_key`、色の場合分けは `color_cases` で網羅性を与える。
二度反対色を取ると元の色になることも、共通コードで証明する。

## 下界のコード

4項を赤・青・青・赤と塗った彩色を `counterexample` として定義する。
`schur_four_counterexample` は、同色の正の x,y,z で x+y=z となる組がないことを証明する。
両ソースに上界と下界を含める。

`pattern_iff_ordinary` がパターンで表す主張と通常の存在命題の同値性を証明する。
証拠を明示した Lean 版にもこの同値性の完全な証明を含める。
