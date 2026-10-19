# Ramsey の完全なコード

Ramsey の定理 R(3,3)=6 を，通常の Lean，提案言語，パターンの関係と証拠を
明示した Lean の三つの形で記述する．6頂点での単色三角形の存在と，
5頂点での反例をいずれも保持する．通常の言明は，頂点の相異性と
辺の色の等式を直接書く．

| 内容 | 通常の Lean | 提案言語 | 証拠を明示した Lean |
|---|---|---|---|
| 色の型と補助補題 | [Common](lean/DesignExamples/Common.lean) | [Common](pmop/DesignExamples/Common.pmop) | [Common](lean/DesignExamples/PatternStyle/Common.lean) |
| 定義・補助補題・上界・下界 | [Ramsey](lean/DesignExamples/Ramsey.lean) | [Ramsey](pmop/DesignExamples/Ramsey.pmop) | [Ramsey](lean/DesignExamples/PatternStyle/Ramsey.lean) |

[PatternContracts.lean](lean/DesignExamples/PatternContracts.lean) は通常の Lean の
定義を用いて，星の存在と内部辺の場合分けを記述する．
[DesignExamples.lean](lean/DesignExamples.lean) が全モジュールを読み込む．
不要になった他の設計例と専用の補助部は削除した．過去の例は Git の履歴にある．

## 検査方法

Lean 4.31.0 と Mathlib v4.31.0 を使う．依存するリビジョンは
[lake-manifest.json](lean/lake-manifest.json) で固定する．`lean/` で実行する．

```sh
lake exe cache get  # 初回に依存ライブラリのコンパイル結果を取得する場合
lake build
lake env lean Audit.lean
```

[Audit.lean](lean/Audit.lean) は両 Lean 版の上界・下界，言明の同値性，網羅性の
証明が使う公理を表示する．未解決の穴や追加の公理で証明を代用しない．
下界は `decide` による証明であり，`native_decide` は使わない．

## 提案記法とその意味

マッチャー（matcher）は，対象の分解方法とパターンの関係を定める．
`$x` は選んだ値の束縛，`#e` は式 `e` との等式，`_` は束縛しない部分を表す．
`P & Q` は同じ対象への両条件，`P | Q` はいずれかの条件を要求する．
先に束縛した値を `#x` で参照するパターンを非線形パターンと呼ぶ．

有限関数の観察は，入力ごとに一つの `(a, f a)` を持つ多重集合を使う．
`$a → $b` は入出力の一組を選び，`::` はその出現を取り除く．
残りの型は `Multiset (A × B)` であり，全関数ではない．
Ramsey の辺のパターンは順序のない端点をどちらの向きでも選び，相異性を要求する．
一般の `Sym2 A` は対角の組も含むので，この条件をマッチャーに明示する．
異なる三つの辺が一つの頂点を共有するとき，他方の三端点も相異なる．

`e matches P as M` は，束縛値とパターンの関係の証明が存在するという命題である．
次の構文は，少なくとも一つの分岐が成立する証明を用いて場合分けする．

```text
match e as M with
| P => body
exhaustive by coverage
```

各分岐は自身の条件から結論を示す．前の分岐の不成立は仮定しない．
`exact ⟨values⟩` は変数の初出順に値だけを与え，システムが保持した条件と補題から
関係の証明を構成するものとする．その具体的な機構は未設計である．
必要なら `match h : ...` や `exact ⟨values⟩ by proof` によって証拠を明示できる．
内側の網羅性補題への相異性の証明引数も，外側の星の条件から補う前提である．

`.pmop` は現在の Haskell パーサでは検査できない提案ソースである．
`PatternStyle/` は省略した証拠の手動展開であり，自動変換の結果ではない．
存在命題から計算用の値を無条件に取り出す規則は仮定しない．
詳細は [条件を暗黙に使う方針](../implicit-conditions.md) を参照．

両版に同じ数学的な補助補題を与えて比較する方針は
[簡潔さの評価](../proof-brevity.md) に記す．
