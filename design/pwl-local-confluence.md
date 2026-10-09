# 隣接する同じ2要素の消去：局所合流性の証明

## 定理と完全なコード

**局所合流性**とは、同じ対象から1回の書換えで得た2つの結果を、
さらに書き換えて同じ対象に到達させられる性質である。
ここでは、リストから隣接する同じ2要素を消す規則を扱う。

```text
pre ++ [a, a] ++ post → pre ++ post
```

要素型 A は任意である。要素同士の大小関係や、有限性は仮定しない。
前後のリストや、2箇所の間のリストは空でもよい。
証明としての分解を扱うため、等式の判定可能性も要求しない。
実行して消去箇所を探す場合には、要素の等式の判定が必要になる。

| 内容 | Lean | パターンマッチ指向版 |
|---|---|---|
| 任意の長さ2の区間の分類 | [TwoBlocks.lean](examples/lean/DesignExamples/TwoBlocks.lean) | [TwoBlocks.pmop](examples/pmop/DesignExamples/TwoBlocks.pmop) |
| 書換えの定義、各腕の関係、網羅性と共通の消去先 | [AdjacentCancellationCommon.lean](examples/lean/DesignExamples/AdjacentCancellationCommon.lean) | [AdjacentCancellationCommon.pmop](examples/pmop/DesignExamples/AdjacentCancellationCommon.pmop) |
| 局所合流性と合流性の主証明 | [LocalConfluence.lean](examples/lean/DesignExamples/LocalConfluence.lean) | [LocalConfluence.pmop](examples/pmop/DesignExamples/LocalConfluence.pmop) |
| パターンの束縛・関係・除去を明示した検査用の版 | [PatternStyle/LocalConfluence.lean](examples/lean/DesignExamples/PatternStyle/LocalConfluence.lean) | — |

全定義と補助補題を上記のファイルに含める。
両版で同じ数学的な型、補助補題と、その証明を使う。
検査方法と `.pmop` の位置付けは [コードの仕様](examples/README.md) に記す。

書換えの関係を、通常の存在命題として定義する。

```lean
def Step (w u : List A) : Prop :=
  ∃ pre a post, w = pre ++ a :: a :: post ∧ u = pre ++ post
```

`Join u v` は、ある z に対して、u と v のそれぞれが0回または1回の消去で
z に到達できることを表す。`Relation.ReflGen Step` は、Step に0回の書換えを加えた関係である。
証明する主定理は次の通常の命題であり、結論にパターンを使わない。

```lean
theorem local_confluence {w u v : List A}
    (hu : Step w u) (hv : Step w v) : Join u v
```

さらに **合流性**、すなわち任意の回数の消去で得た2つの結果が共通の語へ進めることも証明する。
`Relation.ReflTransGen Step` は、0回以上の消去を繰り返す関係である。
各分岐を高々1回で合わせられる上の性質から、Mathlib の
`Relation.church_rosser` を適用する。この一般的な定理は両版で同じように使う。
1回の消去で長さがちょうど2減ることも `step_length` で証明する。

## 2箇所の位置関係とその証拠

2つの Step の証明から、次の分解を取り出す。

```text
w = p ++ [a, a] ++ s     u = p ++ s
w = q ++ [b, b] ++ t     v = q ++ t
```

2箇所は次のいずれかである。

| 位置関係 | 元の語 | 両結果の共通の消去先 |
|---|---|---|
| 一致 | `pre ++ [x,x] ++ post` | `pre ++ post` |
| 1要素だけ重なる | `pre ++ [x,x,x] ++ post` | `pre ++ [x] ++ post` |
| 分離 | `pre ++ [x,x] ++ mid ++ [y,y] ++ post` | `pre ++ mid ++ post` |

重なりと分離では、どちらの箇所が先に現れるかについて両方向を扱う。
したがって完全なコードには5つの腕がある。
分離している2箇所で x = y でもよく、要素の相異性は要求しない。

`TwoBlocks.exhaustive` は、重複要素の消去から独立した汎用補題である。
任意の a,b,c,d とリスト p,s,q,t について、

```text
p ++ [a,b] ++ s = q ++ [c,d] ++ t
```

の2区間を分類する。その証明は `List.append_eq_append_iff` で前半のリストを比較し、
差のリストが0要素、1要素、2要素以上のどれかで場合分けする。
長さ2の区間の要素については仮定を置かない。

`cut_patterns` は、この補題に `[a,a]` と `[b,b]` を入れ、
各腕の束縛値と等式を組にする。その完全な関係は `CutPatterns` に定義する。
この補題は位置関係だけを分類し、合流性の結論や共通の消去先の存在を前提にしない。
分離時の追加の消去は、両版で共有する `join_disjoint` で証明する。

## 証明の途中で行うパターンマッチ

対象は元の語だけでなく、2つの書換えの証明から取り出した `(p,a,s,q,b,t)` である。
元の語に2組が存在するだけでは、与えられた2つの書換えに対応する組とは限らない。
この6成分を同時に照合することで、実際に選ばれた2箇所を分類する。

組のマッチャー `(M₁, …, Mₖ)` は、各成分を対応するマッチャーで照合する。
パターンの束縛を左から右に導入し、各成分の関係を連言として返す。
したがって、前の成分で束縛した値を後の `#` で参照できる。

例えば、最初の消去箇所が先に現れ、2箇所が分離している腕は次のように書く。

```egison
| ($pre, $x, $mid ++ $y :: #y :: $post,
    #(pre ++ [x, x] ++ mid), #y, #post) =>
```

この腕は、束縛値とともに次の6つの等式を受け取る。

```text
p = pre                  a = x
s = mid ++ [y,y] ++ post  q = pre ++ [x,x] ++ mid
b = y                    t = post
```

`simp_all` でこれらの等式とリストの連結を整理し、`join_disjoint` を適用する。
証拠を展開した Lean 版でも、同じ6つの等式に対して同じ操作を行う。
網羅性の証明は `exhaustive by cut_patterns …` として明示する。
各腕は、それ自身の関係だけから結論を証明する。

## 比較結果

同じ `cut_patterns`、`join_self`、`join_disjoint` を使う主証明を比較した結果、
この例では証明全体の記述量は減らない。

| 部分 | Lean | パターンマッチ指向版 |
|---|---:|---:|
| 共通の定義・補助部（TwoBlocks と AdjacentCancellationCommon） | 84行 | 84行 |
| `local_confluence` の宣言と証明 | 14行 | 22行 |
| `confluence` の宣言と証明 | 6行 | 6行 |
| 上記の合計 | 104行 | 112行 |

行数は空行とコメントを除く。主証明は宣言から証明末尾までを数え、
ファイルごとの import・namespace などの外枠は主証明の行数に含めない。
共通部はその2ファイルのコード行を数え、両側に同じ量を計上する。
検査用の手動展開は `local_confluence` が20行であり、変換器の実装を短縮量に含めない。
行数は配置にも依存するため、短縮の結論はコードの内容と合わせて判断する。

Lean は `rcases` で5つの選択肢と等式を取り出し、
`all_goals` で同じ証明操作を各場合に適用できる。
位置を添字で表し、`take`・`drop` を操作する必要はない。
パターン版は分離や重なりの形を直接読めるが、照合対象・各腕・網羅性の指定が加わる。
網羅性の補題を両版で共有しても、主証明は Lean の方が短い。

さらに Lean 版の `local_confluence_by_intervals` は、
`CutPatterns` への対応付けを経ず、`TwoBlocks.exhaustive` を直接用いて12行で証明する。
これは比較対象の Lean 記述を過度に長くしていないことを確認するための、同じ定理の別証明である。

この例は、複数の分解を突き合わせる証明をパターンで記述し、
その証拠を合流性の推論に使えることを示す。
簡潔さの評価では、パターンの条件が見えることに加え、
同じ汎用補題を使う通常の証明との記述量も比較する必要がある。

[わかりやすさと記述量の考察](proof-brevity.md) では、Ramsey を基準に構造の見え方を評価し、
分解の結果を証拠とともに保持して、
すべての結果に同じ推論を適用する場面を検証する。
位置関係の腕を書き換えることに加え、選択から結果の構成と再帰まで証拠を引き継ぐ規則を扱う。

## 検証

Lean 4.31.0 / Mathlib v4.31.0 のプロジェクトで、通常の証明と
パターンの関係を展開した証明をともに `lake build` に含める。
[Audit.lean](examples/lean/Audit.lean) で、汎用分類、腕への対応付け、長さの減少、
両版の局所合流性・合流性の公理への依存を確認する。
未解決の証明や、証明を代替する追加の公理は置かない。
`.pmop` の構文解析と証明項への自動変換は、現在の処理系では未実装である。
