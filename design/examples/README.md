# 設計用の完全なコード

各例の型・定義・補助補題・主定理・証明を、Lean 版とパターンマッチ指向版で揃える。
途中の証明や補助関数を省略する記号、証明の代わりとなる追加の公理や、未解決の穴は置かない。
標準ライブラリの定義・定理は `import Mathlib` から利用する。

| 例 | Lean | パターンマッチ指向版 |
|---|---|---|
| 共通の型と分解補題 | [Common.lean](lean/DesignExamples/Common.lean) | [Common.pmop](pmop/DesignExamples/Common.pmop) |
| Ramsey R(3,3)=6 | [Ramsey.lean](lean/DesignExamples/Ramsey.lean) | [Ramsey.pmop](pmop/DesignExamples/Ramsey.pmop) |
| Schur S(2)=4 | [Schur.lean](lean/DesignExamples/Schur.lean) | [Schur.pmop](pmop/DesignExamples/Schur.pmop) |
| DFA の pumping lemma | [Pumping.lean](lean/DesignExamples/Pumping.lean) | [Pumping.pmop](pmop/DesignExamples/Pumping.pmop) |
| 一般の有限 Hall | [Hall.lean](lean/DesignExamples/Hall.lean) | [Hall.pmop](pmop/DesignExamples/Hall.pmop) |
| 対合の偶数性・和・部分集合の符号反転 | [Involution.lean](lean/DesignExamples/Involution.lean) | [Involution.pmop](pmop/DesignExamples/Involution.pmop) |
| 群の語の逆元消去・簡約 | [GroupWords.lean](lean/DesignExamples/GroupWords.lean) | [GroupWords.pmop](pmop/DesignExamples/GroupWords.pmop) |
| 全称的な言明・配置を使う変換 | [ConfigurationRules.lean](lean/DesignExamples/ConfigurationRules.lean) | [ConfigurationRules.pmop](pmop/DesignExamples/ConfigurationRules.pmop) |
| 有限置換の互換への分解 | [Permutations.lean](lean/DesignExamples/Permutations.lean) | [Permutations.pmop](pmop/DesignExamples/Permutations.pmop) |
| 歩道から道への変換 | [WalkPaths.lean](lean/DesignExamples/WalkPaths.lean) | [WalkPaths.pmop](pmop/DesignExamples/WalkPaths.pmop) |
| 解消規則・有限導出の正しさと充足不可能性 | [Resolution.lean](lean/DesignExamples/Resolution.lean) | [Resolution.pmop](pmop/DesignExamples/Resolution.pmop) |
| 閉じた歩道の挿入 | [WalkInsertion.lean](lean/DesignExamples/WalkInsertion.lean) | [WalkInsertion.pmop](pmop/DesignExamples/WalkInsertion.pmop) |
| 行列式の積の公式と長方形行列での項の打ち消し | [DeterminantProduct.lean](lean/DesignExamples/DeterminantProduct.lean) | [DeterminantProduct.pmop](pmop/DesignExamples/DeterminantProduct.pmop) |
| Cauchy–Binet の公式全体 | [CauchyBinet.lean](lean/DesignExamples/CauchyBinet.lean) | [CauchyBinet.pmop](pmop/DesignExamples/CauchyBinet.pmop) |
| 重み付き LGV の公式全体と有限有向グラフの場合 | [LGV.lean](lean/DesignExamples/LGV.lean) | [LGV.pmop](pmop/DesignExamples/LGV.pmop) |
| オイラー閉路の存在・必要十分条件 | [EulerCircuit.lean](lean/DesignExamples/EulerCircuit.lean) | [EulerCircuit.pmop](pmop/DesignExamples/EulerCircuit.pmop) |
| 隣接する同一要素の消去の局所合流性・合流性 | [LocalConfluence.lean](lean/DesignExamples/LocalConfluence.lean) | [LocalConfluence.pmop](pmop/DesignExamples/LocalConfluence.pmop) |
| 離れた逆元対の全候補の正しさ・任意の個数への拡張 | [TwoCancellations.lean](lean/DesignExamples/TwoCancellations.lean) | [TwoCancellations.pmop](pmop/DesignExamples/TwoCancellations.pmop) |
| 一般の鳩の巣原理 | [Pigeonhole.lean](lean/DesignExamples/Pigeonhole.lean) | [Pigeonhole.pmop](pmop/DesignExamples/Pigeonhole.pmop) |
| Erdős–Szekeres の5項の場合 | [ErdosSzekeres.lean](lean/DesignExamples/ErdosSzekeres.lean) | [ErdosSzekeres.pmop](pmop/DesignExamples/ErdosSzekeres.pmop) |

局所合流性の両版は、[TwoBlocks.lean](lean/DesignExamples/TwoBlocks.lean) /
[TwoBlocks.pmop](pmop/DesignExamples/TwoBlocks.pmop) の汎用的な区間分類と、
[AdjacentCancellationCommon.lean](lean/DesignExamples/AdjacentCancellationCommon.lean) /
[AdjacentCancellationCommon.pmop](pmop/DesignExamples/AdjacentCancellationCommon.pmop) の
定義・補助補題を共有する。完全な比較と現在の結果は
[局所合流性の設計例](../pwl-local-confluence.md) に記す。

逆元対の全候補の例は、[CertifiedList.lean](lean/DesignExamples/CertifiedList.lean) /
[CertifiedList.pmop](pmop/DesignExamples/CertifiedList.pmop)、
[ListCuts.lean](lean/DesignExamples/ListCuts.lean) /
[ListCuts.pmop](pmop/DesignExamples/ListCuts.pmop)、
[TwoCancellationsCommon.lean](lean/DesignExamples/TwoCancellationsCommon.lean) /
[TwoCancellationsCommon.pmop](pmop/DesignExamples/TwoCancellationsCommon.pmop) を共有する。
証拠を保持する有限列挙と、通常の列挙との等式は
[PatternStyle/TwoCancellations.lean](lean/DesignExamples/PatternStyle/TwoCancellations.lean) で検査する。
[わかりやすさと記述量の比較](../proof-brevity.md) に、Ramsey を基準とする評価条件、
補助証明を含む費用と自動化した Lean の比較対象を記す。

[構造と推論が見える例](../pwl-readable-proofs.md) に、解消規則と閉じた歩道の挿入を置く。
それぞれ [ResolutionCommon.lean](lean/DesignExamples/ResolutionCommon.lean) /
[ResolutionCommon.pmop](pmop/DesignExamples/ResolutionCommon.pmop)、
[WalkInsertionCommon.lean](lean/DesignExamples/WalkInsertionCommon.lean) /
[WalkInsertionCommon.pmop](pmop/DesignExamples/WalkInsertionCommon.pmop) の全定義と補助証明を共有する。
[PatternStyle/Resolution.lean](lean/DesignExamples/PatternStyle/Resolution.lean) と
[PatternStyle/WalkInsertion.lean](lean/DesignExamples/PatternStyle/WalkInsertion.lean) に
関係と腕を明示した検査用の版を置く。

行列式の積の公式では、[DeterminantProductCommon.lean](lean/DesignExamples/DeterminantProductCommon.lean) /
[DeterminantProductCommon.pmop](pmop/DesignExamples/DeterminantProductCommon.pmop) が、同じ像を持つ
二つの入力の関係と、その存在を示す補題を定める。
[PatternStyle/DeterminantProduct.lean](lean/DesignExamples/PatternStyle/DeterminantProduct.lean) は、
この関係から2添字を取り出し、項を打ち消して積の公式を導く全証明を含む。
証明は Mathlib の行列式の証明に基づく。改変部分の著作権表示をソースに残し、
ライセンスを [LICENSE-Mathlib](LICENSE-Mathlib) に置く。

Cauchy–Binet・LGV・オイラー閉路も、定理全体の両版を置く。
それぞれの共通の型と全補助証明は
[CauchyBinetCommon.lean](lean/DesignExamples/CauchyBinetCommon.lean) /
[CauchyBinetCommon.pmop](pmop/DesignExamples/CauchyBinetCommon.pmop)、
[LGVCommon.lean](lean/DesignExamples/LGVCommon.lean) /
[LGVCommon.pmop](pmop/DesignExamples/LGVCommon.pmop)、
[EulerCircuitCommon.lean](lean/DesignExamples/EulerCircuitCommon.lean) /
[EulerCircuitCommon.pmop](pmop/DesignExamples/EulerCircuitCommon.pmop) に含める。
[PatternStyle/CauchyBinet.lean](lean/DesignExamples/PatternStyle/CauchyBinet.lean)、
[PatternStyle/LGV.lean](lean/DesignExamples/PatternStyle/LGV.lean)、
[PatternStyle/EulerCircuit.lean](lean/DesignExamples/PatternStyle/EulerCircuit.lean) がパターン版の全証明の手動展開である。
Cauchy–Binet はパターン版の長方形行列の相殺補題を使う。
LGV は交点での二つの列の切断、オイラー閉路は未使用の辺につながる頂点での歩道の切断を使う。
[数学的な言明と証明の対応](../pwl-readable-proofs.md) に、補助証明と腕が使う証拠を記す。

LGV の移植・改変した証明ソースは
[AlgebraicCombinatorics/Determinants/LGV2.lean](https://github.com/faabian/algebraic-combinatorics/blob/3b333089a7a7cd6478065fcfbd91c2b566fccac0/AlgebraicCombinatorics/Determinants/LGV2.lean)
（Copyright Meta Platforms, Inc. and affiliates）に由来し、原著の **CC BY-NC 4.0（表示・非営利）** を維持する。
その対象は `LGV.lean`、`LGVCommon.lean`、`PatternStyle/LGV.lean` と対応する `.pmop` である。
著作権・出典と改変の記録をソースの先頭に明記し、
[LICENSE-AlgebraicCombinatorics](LICENSE-AlgebraicCombinatorics) に原著のライセンス全文を保存する。
これらのファイルにはリポジトリの MIT ライセンスを適用しない。
Mathlib 由来のソースは引き続き [LICENSE-Mathlib](LICENSE-Mathlib) の Apache 2.0 を維持する。

## 検査方法と依存関係

Lean 版は Lean 4.31.0 と Mathlib の `v4.31.0` を使う。
[lake-manifest.json](lean/lake-manifest.json) が依存リポジトリのコミットを固定する。
`lean/` ディレクトリで次を実行する。

```sh
lake update
lake build
```

初回は依存ライブラリと、そのコンパイル結果を取得する。
通常の検査では `lake build` だけでよい。
証明に使った公理は `lake env lean Audit.lean` で確認できる。
[Audit.lean](lean/Audit.lean) の全主定理について、Lean の標準の公理以外の依存や `sorryAx` はない。
全モジュールは
[DesignExamples.lean](lean/DesignExamples.lean) から読み込まれる。

パターンマッチ指向版の `.pmop` は、処理系に実装するための完全な**提案ソース**である。
現在の Haskell パーサでは検査できない。
数学的な定義と証明に加え、
[PatternContracts.lean](lean/DesignExamples/PatternContracts.lean) で
主要なパターンの関係と網羅性を Lean に記述して検査する。
この検査と、`.pmop` の構文解析・証明項への変換の検査は区別する。

さらに [PatternStyle/](lean/DesignExamples/PatternStyle/) に、各提案ソースの
パターンを存在命題と選言へ展開し、証拠の取り出しを明示した完全な Lean 版を置く。
`TwoCancellations` は、`matchAll` を証拠を保持する有限列挙の組合せへ展開した版である。
こちらも `lake build` に含める。型・補助補題・各腕の推論をまとめて検査するためのコードであり、
提案ソースから自動生成する変換器の実装ではない。
編集時には、通常の版・提案版・証拠を展開した版の定理と証明を同時に更新する。

Lean での展開には `∃`（命題としての存在）と選言を使う。
核の設計で用いる依存対型（値とその値に依存する証拠の組）との対応は、
値を計算に使える条件も含めて定義する必要がある。
命題の証明から任意の計算用の値を取り出せるという規則は前提にしない。
LGV の値を返す定義の手動展開は、証明付きの切断を選ぶ `vertexCut` を使う。
これは Lean の標準の選択公理を用いる `noncomputable` な定義である。
実行可能なリストの選択と証拠の生成は、処理系側で接続する必要がある。
有限列挙から値と証拠を構成する実行と、命題としての成立の検査を接続する。

両版の基礎部分には Lean と同じ数学ライブラリを想定する。
`.pmop` の `import Mathlib` は、その型・定義・定理を提案言語の標準ライブラリとして
利用する指定である。Lean の証明項を Haskell の核へ読み込む機能があるという意味ではない。
各版の `DesignExamples.Common` は上表のそれぞれのファイルを読み込む。
名前解決のルートは Lean 版では `lean/`、提案版では `pmop/` とする。

Hall の存在方向では、Mathlib の一般の有限 Hall 定理
`Finset.all_card_le_biUnion_card_iff_existsInjective'` を利用する。
追加コードには近傍の定義、パターン条件との同値性、逆方向の証明、
部分集合の組とマッチングを有限に列挙する関数、および列挙結果の正しさを含める。
Ramsey と Schur の下界、Erdős–Szekeres の有限の場合には、
Lean の `decide` による証明を用いる。`native_decide` は使わない。

## 提案ソースで共通に使う構文

マッチャーは、パターンが表す関係と対象の分解方法を定める。
`$x` は値の束縛、`_` は束縛しない選択、`#e` は値と式 `e` の等式、
`!p` はパターン `p` の不成立、`p & q` は同じ値についての両条件を表す。
`p | q` は選択肢ごとに値と証拠を持つ。
`?(P)` と `where P` は命題 `P` の証拠を要求する。
実行時にこれらを判定するには、判定可能性も必要になる。
`::` は `++` より強く結び付き、どちらも右に結合する。
`Literal.pos $p` と `Literal.neg #p` のような帰納型のコンストラクタパターンは、
そのコンストラクタと引数の型に従って照合する。解消規則のリテラルでは引数の型は V である。

`e matches P as M` は、P が束縛する値と、それらが M の関係を満たす証拠の存在を表す。
この存在命題の型と、腕が受け取る証拠の型を、以下の関係で定める。
否定パターンの内側の変数は、その不成立を述べる命題の中にだけ束縛され、
腕の外へ値として取り出せない。

```text
match h : e as M with
| P => body
exhaustive by coverage
```

腕のパターン変数は選ばれた値を持ち、`h` はその腕の関係の証拠を持つ。
`coverage` は腕のいずれかの成立を証明する。
選択肢の順序を変える場合は選言の除去・導入で対応付け、
証明に基づく場合分けでは最初の成功を選ぶという規則は要求しない。
どの腕も、その腕自身の関係だけを使って結論を証明する。

`exact ⟨束縛値⟩ by proof` は、値の組に対して関係の証拠を `proof` で構築する記法である。
`by proof` は任意の指定であり、省略すると腕で得た関係と証明済みの補題から
証明項を自動構成し、核で検査する。構造に含まれる所属・等式・相異性も、
マッチの証拠から自動的に環境へ渡す。
完全なソースでは、その構成に必要な証拠と数学的な推論を確認できるよう明示する。
通常の存在命題に対する `exact ⟨値, 証拠⟩` も使う。
定理の対象は `edge matches …` のように明示する。
`by`、`intro`、`obtain`、`rcases`、`rw`、`simp`、`omega`、`ring`、`induction`
などは Lean と同じ証明操作を想定し、核の証明項に変換する。
ここでは、未実装の操作の代わりに任意の証明を受理する規則は設けない。

`matchAll h : e as M with | P => body` は、成功する各分解の値と関係の証拠を
腕に渡し、腕の結果をすべて列挙する。成功しなければ空のリストであり、
`exhaustive by` を要求しない。列挙自体の正しさと完全性は、マッチャーの規則から証明する。
腕が証明付きの値を返せば、結果は証明付きの値のリストになる。
腕がリストを返す場合は、`List.flatten` で明示的に連結する。
逆元対の例では有限リストに対する実行を定義し、`keep`・`bind`・`mapWithProof` と
その汎用的な証明への展開を検査する。詳しい型と対応は [設計例](../proof-brevity.md) に記す。

[全称的な言明と配置を使う変換](../pwl-quantified-transforms.md) は，任意の逆元対の削除，
二つの等しい要素対の削除の合流性，LGVの任意の共有頂点での交換を扱う．
[ConfigurationRulesCommon.lean](lean/DesignExamples/ConfigurationRulesCommon.lean) と
[ConfigurationRulesCommon.pmop](pmop/DesignExamples/ConfigurationRulesCommon.pmop) は，
同じ関係，証拠付きの変換，汎用定理の完全な定義と証明を共有する．
`forallMatch` は `∀ b, R(e,b) → Q(b)` を表す全称命題で，列挙を実行しない．
存在は別の命題とし，値を返す変換には分解のデータを渡す．通常のLeanの言明との同値性，
型付きの道・端点・重み，配置の交換と選択の保存から対象の対合を導く定理，
共有頂点を変更する反例をLeanで検査する．提案記法の証明の導入形は `introMatch h` とする．

## マッチャーの対象型・残りの型・証拠

| マッチャー | 対象 | 束縛と関係 |
|---|---|---|
| `value A` | A の値 | `$x` は対象自身、`#e` は対象 = e、`!#e` は対象 ≠ e |
| `multiset A` | `Multiset A` | `$x :: $R` は対象 = x :: R。R も `Multiset A` |
| `multiset (A → B)` | 有限の型 A 上の全関数 | 全入力の `(a, f a)` の多重集合を観察。残りは `Multiset (A × B)` |
| `set (A → B)` | 有限の型 A 上の全関数 | キーの所属と出力の等式を返す。選択後も同じグラフを使う |
| `set (A × B)` | `Finset (A × B)` | `p → q` は所属するペアを選ぶ。選択しても対象は減らない |
| `list A` | `List A` | `::` と `++` はリストの等式による分解。残りも `List A` |
| `walk G` | `G.Walk s t` | `$pre ++ $v :: $post` は pre:s→v、post:v→t と `pre.append post = 対象`。`where Q` は条件 Q の証明を加える |
| `(M₁, …, Mₖ)` | 各 Mᵢ の対象型の組 | 各成分を対応するマッチャーで照合する。束縛は左から右に導入し、証拠は各成分の関係の連言 |
| `list (Fin n → A)` | 有限関数 | 入力位置の昇順に `(i, f i)` を並べる。前後関係は入力位置の不等式になる |
| `bipartite_graph X Y` | 辺の関係 `E : X → Y → Prop` | `$S ⤳ $T` は有限部分集合 S,T と `neighbors E S ⊆ T` の証拠 |
| `matching_of E` | 同じ辺の関係 E | `$f` は `X → Y` の関数、証拠は単射性と `∀ x, E x (f x)` |

関数の観察には有限な定義域を要求する。`matching_of` の `$f` は候補を選ぶ専用の規則であり、
対象 E 自体を束縛する通常の `$x` と区別する。
`bipartite_graph` の候補は左右の全部分集合の組、`matching_of` の候補は全関数であり、
具体的な列挙と所属の証明は Hall の両ソースに定義する。

`Sym2` のペアパターンは両端が異なる場合を扱い、両方向の観察を許す。
`Sym2.eq_swap` による等式の変換を使う。
多重集合一般では異なる出現が同じ値を持つこともある。
関数のグラフではキーが一度ずつ現れるため、異なる出現からキーの相異性を導ける。
この性質を使う Ramsey の同色3辺の証拠は `Star` で明示している。

## 各腕が使う証拠の具体的な型

- Ramsey の同色3辺：`Star edge v x y z c`。
  v と各頂点の相異性、x,y,z の相異性、3本の辺の色の等式を含む。
  内部辺の腕は p,q が x,y,z のいずれかであること、p≠q、辺の色を含む。
- Schur のキー観察：`c D.one = col`。色の腕は対象の色の等式。
  結論の関係は `(x,col)`、`(y,col)`、`(x+y,col)` の `graph c` への所属。
  グラフのキーを自然数にするので `#(x+y)` の式の型も自然数である。
  範囲外の和はグラフに所属しないためマッチが成立しない。
- 走行列と歩道の重複：`対象 = pre ++ q :: (mid ++ q :: post)`。
  2位置は `pre.length` と `pre.length + mid.length + 1` で、必ず前者が小さい。
  走行列から入力語へ移る証明は `split_to_loop` にすべて記述する。
- 解消規則：`C = pos p ::ₘ xs`、`D = neg p ::ₘ ys`、`R = xs + ys`。
  p の真偽による場合分けで、二つの前提から結論の節が真になることを示す。
  同じ規則を有限導出についての帰納法で使い、空の節の導出から充足不可能性を示す。
- 閉じた歩道の挿入：`w = pre ++ v :: post` と `loop = v :: (mid ++ [v])`。
  一頂点の `loop = [v]` の腕も含める。前半、閉じた歩道、後半の接続を証明し、
  出力の構成関係、始点・終点と辺の保存、長さの関係を結果に含める。
- 行列式の積の公式：`i ≠ j`、`p i = k`、`p j = k`。
  `SharedImage p` がこの存在を表す。2位置を交換して積を保ち、符号を反転することを
  `noninjective_cancel` の腕で証明し、展開後の和から積の公式を導く。
- LGV の二つの列：`Pᵢ.vertices = preI ++ v :: tailI` と `Pⱼ.vertices = preJ ++ v :: tailJ`。
  交点の選択は `getCanonicalIntersectionData` で先に固定する。交換後の頂点列、重みの積、
  符号、選択の保存、2回の交換で戻ることまで証明する。
- オイラー閉路の切断：`pre.append post = p` と `∃ w, G.Adj v w ∧ s(v,w) ∉ p.edges`。
  pre、post は頂点列ではなく端点付きの歩道である。残りのグラフの偶数性と、
  挿入する閉じた歩道の辺が元の歩道と重ならないことを共通の補助証明で示す。
- 対合の対：`S.val = x :: σ x :: R`。
  `pair_evidence` が所属、相異性、R と2要素を除いた集合の多重集合との等式を導く。
  閉性・対合・固定点の不在の引き継ぎと要素数の減少は `pair_remainder` で証明する。
- 群の語：`w = pre ++ g :: g⁻¹ :: post`。否定の腕ではこの分解の不成立。
  積の保存は `cancel_pair`、停止に使う長さの減少は帰納法の腕で証明する。
- 逆元対の全候補：`w = pre ++ g :: g⁻¹ :: (mid ++ k :: k⁻¹ :: post)`。
  2箇所の選択の証拠を組み合わせ、結果に積の保存と長さが4減る証明を添える。
  任意の n 箇所では、残りについての `GoodMany n` の証拠を再帰呼出しから受け取り、
  `extend_good` で次の段階へ渡す。証拠を除いたリストとの等式と、任意の個数の分解の完全性も証明する。
- 隣接する同一要素の消去：2つの証明から得た `(p,a,s,q,b,t)` を同時に照合する。
  共通の語の等式は `p ++ a :: a :: s = q ++ b :: b :: t`。
  各腕の6成分の等式と束縛値を `AdjacentCancellation.CutPatterns` で定める。
  `TwoBlocks.exhaustive` が任意の長さ2の区間を分類し、`cut_patterns` がその証拠を
  各腕へ対応付ける。網羅性と共通の消去結果の構成は、それぞれ証明を含める。
- 置換の固定点：`π a = a` と `graph S π = (a,a) :: R`。
  固定点でない腕は b≠a、c≠a、c∈S、π(a)=b、π(c)=a とグラフの分解。
  これらは `graph_cases` で証明する。小さい置換は `π * swap a c` として構成する。
- 単調部分列の腕：i<j、j<k、f(i)=x、f(j)=y、f(k)=z と、指定した2つの大小関係。
  5項の相対順序を `Fin 5` に写す証明も両ソースに含める。

## 実装につなぐ条件

処理系には、上記の関係の型を構成し、`match` と `exhaustive by` を証拠の除去へ変換する処理を実装する。
これらのソースを直接検査し、パターンを使う腕と Lean の証拠の受け渡しが対応することを確認する。
探索による実行では、候補の生成・判定とこの関係が一致することも証明する。
設計全体の課題は [review.md](../review.md) にまとめる。
