# 数学的な例題の完全なコード

Ramsey の定理 R(3,3)=6 を，通常の Lean，提案言語，パターンの関係と証拠を
明示した Lean の三つの形で記述する．6頂点での単色三角形の存在と，
5頂点での反例をいずれも保持する．通常の言明は，頂点の相異性と
辺の色の等式を直接書く．

交代群の単純性についても，通常の言明を保って証明の途中だけにパターンを
使う例を追加する．以下に Ramsey のコードを案内し，後半で交代群の証明と
比較結果を説明する．

| 内容 | 通常の Lean | 提案言語 | 証拠を明示した Lean |
|---|---|---|---|
| 色の型と補助補題 | [Common](lean/DesignExamples/Common.lean) | [Common](pmop/DesignExamples/Common.pmop) | [Common](lean/DesignExamples/PatternStyle/Common.lean) |
| 五つの色からの同色三要素の選択 | [Pigeonhole](lean/DesignExamples/Pigeonhole.lean) | [Pigeonhole](pmop/DesignExamples/Pigeonhole.pmop) | [Pigeonhole](lean/DesignExamples/PatternStyle/Pigeonhole.lean) |
| 定義・補助補題・上界・下界 | [Ramsey](lean/DesignExamples/Ramsey.lean) | [Ramsey](pmop/DesignExamples/Ramsey.pmop) | [Ramsey](lean/DesignExamples/PatternStyle/Ramsey.lean) |

[PatternContracts.lean](lean/DesignExamples/PatternContracts.lean) は通常の Lean の
定義を用いて，星の存在と内部辺の場合分けを記述する．
[DesignExamples.lean](lean/DesignExamples.lean) が全モジュールを読み込む．
過去の設計例は Git の履歴にある．

## 検査方法

Lean 4.31.0 と Mathlib v4.31.0 を使う．依存するリビジョンは
[lake-manifest.json](lean/lake-manifest.json) で固定する．`lean/` で実行する．

```sh
lake exe cache get  # 初回に依存ライブラリのコンパイル結果を取得する場合
lake build
lake env lean Audit.lean
lake env lean AuditAlternating.lean
```

[Audit.lean](lean/Audit.lean) は両 Lean 版の上界・下界，言明の同値性，網羅性の
すべての補助定理を含む証明が使う公理を表示する．未解決の穴や追加の公理で証明を代用しない．
下界は `decide` による証明であり，`native_decide` は使わない．

## 鳩の巣原理の証明

`Pigeonhole.five_colors` は五つの入力を最初の三つと残りの二つに分ける．
最初の三つが同色なら終了する．そうでなければ，同色の二つと反対色の一つを選び，
残りの二つに前者と同色のものがあるか調べる．あれば前者の二つに加え，
なければ後者の一つに反対色の二つを加える．`three_color_cases` は八通りの色配置を
すべて証明し，`two_color_cases` は残り二つの場合分けを証明する．
入力の番号を区別する補題と `Fin.succAbove` の単射性によって，相異なる三端点を得る．
`PatternContracts.pigeonhole_edges_at` とパターン版は，この証明を用いる．
元の数え上げによる Lean の証明も保持する．

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

## 交代群の単純性

交代群 `Aₙ` は，`n` 点の置換のうち，偶数個の互換（二点を交換する置換）の
積で表せるものからなる群である．単純性とは，正規部分群（群の要素による
共役 `x ↦ g x g⁻¹` で保たれる部分群）が単位元だけの部分群と群全体に限られる性質である．
`n ≥ 5` なら `Aₙ` は単純である，という定理を扱う．

| 内容 | ソース |
|---|---|
| 通常の言明と証明 | [Alternating.lean](lean/DesignExamples/Alternating.lean) |
| パターンを使う提案ソース | [Alternating.pmop](pmop/DesignExamples/Alternating.pmop) |
| パターンの条件を手動で展開した証明 | [PatternStyle/Alternating.lean](lean/DesignExamples/PatternStyle/Alternating.lean) |
| 置換・局所的な条件・交換子の定義と計算 | [Common.lean](lean/DesignExamples/Alternating/Common.lean) |
| 場合分けの網羅性 | [Coverage.lean](lean/DesignExamples/Alternating/Coverage.lean) |
| 各場合から長さ3の巡回置換を作る共有補題 | [Reductions.lean](lean/DesignExamples/Alternating/Reductions.lean) |
| パターンの関係と通常の条件との同値性 | [Patterns.lean](lean/DesignExamples/Alternating/Patterns.lean) |
| 全補題の公理依存と，既存の単純性定理を使わないことの検査 | [AuditAlternating.lean](lean/AuditAlternating.lean) |

### 言明と証明の範囲

両 Lean 版と提案ソースは，同じ言明を持つ．`Nat.card α` は有限な型 `α` の
要素数，`alternatingGroup α` はその点の上の交代群である．

```lean
theorem alternating_simple (h5 : 5 ≤ Nat.card α) :
    IsSimpleGroup (alternatingGroup α)
```

`a5_simple` は `α = Fin 5` の系である．一般の `n ≥ 5` を証明しており，
有限個の次数の検査で一般の証明を代用していない．
Mathlib からは長さ3の巡回置換による生成と，それらが交代群内で共役であることを
使う．交代群の単純性を既に結論する定理は読み込まない．独立した監査で，
その既存定理が証明環境に存在しないことも確認する．

### 数学的な証明

`(a b c)` は `a → b → c → a` と動かす巡回置換で，積は右から作用する．
交換子を `[σ, τ] = σ τ σ⁻¹ τ⁻¹` とする．非自明な正規部分群 `N` から
`σ ≠ 1` を取り，次の四つの場合を考える．各行の異なる文字は相異なる点を表す．

| 場合 | 条件 | `N` の中に作るもの |
|---|---|---|
| 長さ3の巡回置換そのもの | `σ = (a b c)` | `σ` |
| 相異なる4点を順に送る | `σ a = b`, `σ b = c`, `σ c = d` | `[σ, (a b c)] = (a d b)` |
| 3点の巡回と別の動く点 | `σ a = b`, `σ b = c`, `σ c = a`, `σ d = e` | `[σ, (a b d)] = (a d c e b)` |
| 二つの互換 | `σ a = b`, `σ b = a`, `σ c = d`, `σ d = c` | 以下の第五の点による場合分け |

長さ5の巡回置換には，相異なる4点を順に送る場合の構成を適用する．
二つの互換がある場合は，`n ≥ 5` からそれらの外の点 `e` を選ぶ．
`σ e = e` なら `[σ, (a c e)] = (a b d e c)` である．
`σ e = f ≠ e` なら `f` も既存の五点とは異なり，
交換子は互いに点を共有しない `(b d f)(a e c)` になる．
これは3点の巡回と別の動く点を持つので，表の第三の場合へ進む．

網羅性の証明では，一つの動く点の行き先を3回まで追い，2点で戻るか，
3点で戻るか，4点が相異なるかを調べる．2点で戻るとき，偶置換は
一つの互換だけではないため，その外の動く点を取り，同じ分類を使う．
3点で戻るときは，それ以外の点をすべて固定するか，別の動く点があるかを調べる．
この証明が `cases_exhaustive` である．

すべての場合で `N` の中に長さ3の巡回置換を作れる．正規性と共役の補題から
すべての長さ3の巡回置換が `N` に入り，生成の補題から `N = Aₙ` が従う．
内部では `N` を置換群の部分群として扱い，交代群に含まれることと
偶置換による共役で保たれることを明示する．最後の共有補題が，これを
交代群そのものの正規部分群についての通常の単純性の言明へ接続する．

`A₅` では非単位元の形は `(a b c)`，`(a b)(c d)`，`(a b c d e)` である．
後二者について使う具体式は，独立した監査の末尾でも Lean の `decide` で検査する．
一般の証明には，その有限計算よりも強い，任意の相異なる点に対する共有補題を使う．

### パターンが表すもの

提案する `permutation α` は，元の置換から入出力の組を選ぶマッチャーである．
選択後の残りは入出力の組の多重集合であり，置換そのものではない．
`$a → $b` は `σ a = b` という条件と選んだ二点を与え，`::` はその入力キーを
取り除く．次のパターンは相異なる4点を順に送る場合に対応する．

```text
$a → $b :: #b → $c :: #c → $d :: #d → _ :: _
```

最後の `#d → _` によって，`d` も別の入力キーとして選ばれる．したがって
`a,b,c,d` の相異性が得られる．これを省くと `d = a` を許し，長さ3の巡回も
含まれるため，この場合の交換子の補題をそのまま使えない．
同様に，3点の巡回と別の動く点のパターンには `#e → _` を含める．

最初の分岐は，3点の巡回の観察と `#(cycle3 a b c)` を `&` で組み合わせる．
この等式は元の置換全体に対するもので，他の点をすべて固定することも保証する．
複数の分岐が成立することは許し，各分岐は自分自身の条件だけで結論を示す．

`Patterns.lean` の `Observes σ entries` は，選んだ入力の重複がないことと，
各組が `σ` の入出力であることを要求する．出力を束縛しない `#d → _` は，
関係を記述する際には常に決まる値 `σ d` を使って表す．四つのパターンの関係と
通常版の四条件が同値であることを証明し，同じ網羅性の証明を双方に使う．

提案ソースの補題呼出しでは，分岐内の条件から証明引数とそれに含まれる点の
引数を補完する方針を用いる．例えば `three_of_path4 hN hσ` の残る引数は，
束縛された `a,b,c,d` と，それらについて成立する `Path4` の証明である．
この補完機構は未実装であり，`PatternStyle/Alternating.lean` では変換をすべて
明示して検査する．`.pmop` は通常版と同じ Lean の共有補題を参照する提案ソースであり，
現在の Haskell 処理系で実行した結果ではない．

### 比較結果の再現

このディレクトリで次を実行する．

```sh
python3 compare_alternating.py
```

現在の書式では，`contains_three` の証明本体は通常版7行，提案記法11行，
手動展開8行である．パターンでは点の動きを分岐に直接表示するが，
同じ補題を用いる通常版に対して中心証明の行数は減っていない．
共有の数学的な準備と，パターン固有の関係の定義も分けて集計する．
詳しい数値と評価範囲は [簡潔さの評価](../proof-brevity.md) に記す．
