# 全称的な言明と，選んだ配置を使う変換

パターンは，対象を分解して得る値と，それらの関係を記述する．この文書では，
その関係を使って「すべての分解について成立する性質」を述べ，選んだ分解から
結果とその正しさの証拠を構成する．群の語の逆元対削除，同一要素対の削除の
局所合流性，LGVの道の後半交換を具体例とする．

完全な型・定義・証明は
[通常のLeanと関係を明示した版](examples/lean/DesignExamples/ConfigurationRules.lean)，
[パターンマッチ指向版](examples/pmop/DesignExamples/ConfigurationRules.pmop) に置く．
後者は提案記法であり，意味と証明はLeanの対応版で検査する．
共通の完全な関係と補助証明は
[ConfigurationRulesCommon.lean](examples/lean/DesignExamples/ConfigurationRulesCommon.lean) と
[ConfigurationRulesCommon.pmop](examples/pmop/DesignExamples/ConfigurationRulesCommon.pmop) で共有する．
LGVの道の構成とその性質は，既存の完全なLGVの補助証明を共有する．

## 1．全称的な言明の意味と束縛

`forallMatch` を，パターンが記述するすべての配置についての命題とする．
`introMatch h` は，その命題を証明する際に任意の束縛値と関係の証拠 `h` を導入する．

```egison
forallMatch e as M with
| P => Q
```

束縛値の型を `B`，対象と束縛値との関係を `R(e,b)` とすると，意味は

\[
\forall b:B,\ R(e,b)\Rightarrow Q(b)
\]

である．`P` が導入した名前は `Q` の内部で利用できる．外側の文脈への参照は許すが，
この命題の外へ束縛を持ち出さない．複数の腕を記述した場合は，それぞれの全称命題の
連言とし，重なる腕にもそれぞれの主張を要求する．腕の順序には依存しない．

| 記述 | 意味 | 存在・計算について要求するもの |
|---|---|---|
| `e matches P as M` | `∃ b, R(e,b)` | 存在の証明 |
| `forallMatch e as M with \| P => Q` | `∀ b, R(e,b) → Q(b)` | 任意の配置についての推論 |
| `e matches !P as M` | `¬∃ b, R(e,b)` | 不存在の証明 |
| `matchAll ...` | 成功する配置の証拠付き列挙 | 列挙の正しさ・完全性と，実行のための条件 |

`forallMatch` は探索を実行しない．対象の有限性，等値性の決定可能性，網羅性の
証明を要求しない．配置が存在しないときも成立するため，配置が存在することを
述べるには別に `matches` を用いる．例えば空の語には削除箇所がないが，
「どの削除も積を保存する」は成立する．この区別もLeanで検査する．

不存在は，構成的にも `forallMatch ... => False` と同値である．また全称命題は，
すべての証拠付きの分解 `{b // R(e,b)}` に対する性質と同値である．
いずれも `AllMatches` の汎用的な同値定理として証明する．

## 2．例：どの逆元対の削除も積を保存する

`G` を群，`w : List G` を有限の語とする．積は左から右の順序で取る．
可換性も，`G` の有限性も，等値性の決定可能性も要求しない．通常のLeanでは，
次のように全称量化と分解の等式を記述する．

```lean
theorem cancel_all_explicit (w : List G) :
    ∀ pre g post, w = pre ++ g :: g⁻¹ :: post →
      (pre ++ post).prod = w.prod ∧ (pre ++ post).length + 2 = w.length
```

パターン版は，選ぶ箇所と残る部分を同じ式の中で表示する．

```egison
theorem cancel_all (w : List G) :
    forallMatch w as list G with
    | $pre ++ $g :: #(g⁻¹) :: $post =>
      (pre ++ post).prod = w.prod ∧ (pre ++ post).length + 2 = w.length := by
  introMatch h
  subst w
  constructor
  · exact (DesignExamples.GroupWords.cancel_pair pre g post).symm
  · simp only [List.length_append, List.length_cons]
    omega
```

`h` は `w = pre ++ g :: g⁻¹ :: post` である．分解を代入した後は，
両版とも同じ群の等式と長さの計算を使う．`cancel_all_iff_explicit` は，
二つの言明が同じことを述べることを証明する．

この例だけなら通常のLeanも短い．改善の候補は，量化・分解の等式・出力の構成を
共通のパターン記法で結び付けられることにある．定理の証明を短くする効果と，
言明で配置を確認しやすくする効果を別々に評価する．

### 前後の配置を表す関係

削除による入出力の関係を，一組のパターンで記述する．

```egison
def CancelsTo (w r : List G) : Prop :=
  (w, r) matches
    ($pre ++ $g :: #(g⁻¹) :: $post, #(pre ++ post))
    as (list G, list G)
```

これは `∃ pre g post, w = pre ++ g :: g⁻¹ :: post ∧ r = pre ++ post` と同値である．
二番目の成分の `#` は，出力が指定した残りに等しいことを要求する．
自由に選んだ出力ではなく，入力で選んだ部分から作る出力の関係である．
`CancelsTo w r` から積の保存と長さの減少を証明することも，完全なソースに含める．

### 実際の変換には選んだ配置を渡す

語だけを引数とすると，削除箇所がない場合と，複数ある場合を別に扱う必要がある．
そこで `cancelAt` は，分解の値と等式を含むデータを引数に取る．

```lean
def cancelAt (w : List G) (cut : {c // InverseMatch w c}) :
    {r // r.prod = w.prod ∧ r.length + 2 = w.length}
```

`c` のフィールドは `pre, g, post`，`InverseMatch w c` は上の分解の等式である．
返す値は `pre ++ post` であり，全称的な正しさの定理をこのデータに適用して証拠を付ける．
パターン版では，同じデータを単一腕の `match` のデータ網羅性として渡す．
ここで行うのは，選択済みのデータの分解であり，再探索ではない．

例えば `w = [g,g⁻¹,k,k⁻¹]` には二つの切断を渡せる．

| 渡す切断 | 削除後の語 |
|---|---|
| `pre=[], g=g, post=[k,k⁻¹]` | `[k,k⁻¹]` |
| `pre=[g,g⁻¹], g=k, post=[]` | `[g,g⁻¹]` |

両結果の積と長さは同じ法則を満たすが，結果の語そのものは異なることがある．
`two_cuts` は両方の証拠付きの入力と出力を構成する．存在の証明から出力を返す場合には，
別に構成的な選択か明示的な古典的選択を使う．

## 3．例：同じ語の二つの削除箇所は合流する

ここでは逆元対ではなく，**等しい隣接要素の対**を削除する．`Step w u` は
`w = pre ++ a :: a :: post` と `u = pre ++ post` が成り立つ削除である．
`Join u v` は，両結果から，それぞれ零回または一回の追加の削除で共通の語へ進めることを表す．
この一段階の合流の性質は，[完全な局所合流性の証明](pwl-local-confluence.md) で示している．

通常のLeanのコンパクトな言明は，名前付きの関係を使って書ける．

```lean
∀ u v, Step w u → Step w v → Join u v
```

パターン版では，二つの出力を別々に存在量化せず，選ぶ配置から直接作る．

```egison
theorem all_equal_cuts_join (w : List A) :
    forallMatch (w, w) as (list A, list A) with
    | ($p ++ $a :: #a :: $s, $q ++ $b :: #b :: $t) =>
      Join (p ++ s) (q ++ t)
```

同じ `w` を独立に二度観察するため，二つの選択は一致しても重なってもよい．
`a = b` は要求しない．相互の位置関係を，一致，一要素の重なり，分離に分類すると，
一致と重なりでは結果が同じになり，分離ではもう一方の対を削除して共通の語を得る．
`equal_cuts_iff_local` は，パターンの関係に基づく全称命題と上のLeanの命題の同値性を証明する．

名前付きの `Step` と `Join` は，両スタイルで利用できる．この例は行数の短縮を
保証する例ではなく，複数の変換を比較する言明にも全称パターンを使えることを示す．
具体的な配置を表示する版と，名前付きの関係を使う版を比較対象として保持する．

## 4．例：LGVの道の後半交換

`p,q` を非巡回有向グラフの道とし，共有頂点 `v` で切る．切断の関係は

\[
p=pre_I\mathbin{++}[v]\mathbin{++}tail_I,\qquad
q=pre_J\mathbin{++}[v]\mathbin{++}tail_J
\]

である．ここで等式は頂点列の等式を表す．前後の配置を同時に記述すると，
交換によって変わる部分と残る部分が見える．

```egison
def ExchangesTo (target result : List V × List V) : Prop :=
  (target, result) matches
    (($preI ++ $v :: $tailI, $preJ ++ #v :: $tailJ),
     (#(preI ++ v :: tailJ), #(preJ ++ v :: tailI)))
    as ((list V, list V), (list V, list V))
```

Leanの展開は，五つの切断成分を存在量化し，入力と出力について二つの組の
等式を要求するものである．`exchangesTo_iff_explicit` がこの対応を証明する．

この頂点列の関係に加え，実際の変換 `swapPathsAt p q cut` は辺と端点の証拠を
保持する二つの道を返す．次の性質を検査する．

- 頂点列は表示した後半交換の結果に等しい．
- 始点はそれぞれ保たれ，終点が交換される．
- 任意の可換環の辺重みに対して，二つの道の重みの積が保たれる．
- 任意の共有頂点での切断について，交換後の道と端点の性質が成立する．

最後の言明には，全称パターンを使う．

```egison
forallMatch (p.vertices, q.vertices) as (list V, list V) with
| ($preI ++ $v :: $tailI, $preJ ++ #v :: $tailJ) =>
  ∃ pq : Path D × Path D,
    (pq.1.vertices, pq.2.vertices) = (preI ++ v :: tailJ, preJ ++ v :: tailI) ∧
    pq.1.start = p.start ∧ pq.1.finish = q.finish ∧
    pq.2.start = q.start ∧ pq.2.finish = p.finish
```

頂点列だけから道であることを結論するのではなく，分解の等式と元の辺の証拠から
道を構成する．非巡回性は，切断する頂点の出現の一意性と，交換後の頂点の非反復を
保証する．`tail_swaps_all` と三つの `swapPathsAt_*` 定理がこの意味を検査する．
LGV全体の行列式の展開，符号反転，交点の選択の保存は，この局所的な交換に組み合わせる．

### 二度の交換と，交点を選び直すことの違い

同じ切断成分で後半を二度交換すれば，元の切断成分へ戻る．
`swapCut_involutive` は，配置のデータ上のこの対合を証明する．
しかし，変換後の対象から切断を選び直す場合には，選択の保存が必要である．
次の二つの道は，同じ頂点 `v,w` をこの順に通る．

```text
最初           a → v → x → w → b     c → v → y → w → d
v で交換       a → v → y → w → d     c → v → x → w → b
w で交換       a → v → y → w → b     c → v → x → w → d
```

三段目では終点は戻るが，中間の `x,y` が戻らない．すべての列は，同じ非巡回グラフの
道である．辺に沿って増える順位 `0,1,2,3,4` を各段階の頂点に与えられる．
第二の切断の正しさ，元に戻らないこと，各列の辺の連鎖と頂点の非反復をLeanで検査する．
したがって，任意に共有頂点を選んで交換できるという局所的な定理だけでは，
LGVの対合による相殺を完成できない．

### 選択と交換をつなぐ一般的な定理

`C` を選択した配置のデータの型，`X` を対象の型とする．`C` は，対象と束縛値と
関係の証拠を含む依存対（値に応じて型が変わる組）でもよい．
`source : C → X` は元の対象，`exchange : C → C` は配置の交換，
`select : X → C` は配置を選ぶ関数である．

次の三つの条件から，`F x = source (exchange (select x))` が対合であることを導く．

\[
\begin{aligned}
source(select(x))&=x,\\
exchange(exchange(c))&=c,\\
select(source(exchange(select(x))))&=exchange(select(x)).
\end{aligned}
\]

最後の条件は，変換後に選び直す配置が，交換後の配置そのものであるという選択の保存である．
`selected_involutive` の証明は，この等式で二度目の選択を置き換え，
配置の対合を使い，最後に元の対象を復元するだけである．
この条件は十分条件であり，対象の対合を証明するための唯一の条件とはしない．
配置のデータの表現に余分な情報がある場合には，必要な部分の一致を用いて
対象の復元を直接示すこともできる．

LGVでは，最小の交差する道，その道の最初の共有頂点，その頂点を通る最大の別の
道の添字を選ぶ．この数学的な選択が交換後にも保存されることを，
[完全なLGVの証明](pwl-readable-proofs.md) で示す．上の汎用定理は，
配置の局所的な交換と，対象上で繰り返す変換をつなぐ推論を再利用するためのものである．

## 5．二つの設計をつなぐ規則

入力の関係を `R(t,b)`，出力を作る式を `F(b)`，要求する性質を `S(t,r)` とする．
全称的な正しさの証明は

\[
\forall t,b,\ R(t,b)\Rightarrow S(t,F(b))
\]

である．分解のデータ `c : {b // R(t,b)}` を渡すと，

\[
\bigl(F(c.val),\;sound(t,c.val,c.property)\bigr)
  :\{r\mid S(t,r)\}
\]

を返せる．`applyCertified` はこの構成である．また，入出力の関係
`∃ b, R(t,b) ∧ r = F(b)` を満たす任意の出力についても `S(t,r)` を得る．

この二つの規則により，言明で書いた任意の配置に対する性質を，証明途中で選んだ
具体的な配置とその変換へ適用できる．変換は，組のパターンによる入出力関係と，
証拠付きの値を返す通常の関数で具体化する．
関係の表示，配置の選択，出力の構成，保存する性質を同じ名前と分解で追えることを評価する．

## 検査

`examples/lean/` で `lake build DesignExamples` と `lake env lean Audit.lean` を用いる．
検査対象には，全称命題の二つの同値性，削除の正しさ，二つの削除の合流性，
型付きの道の交換，重み，選択の保存から対合を導く定理，交点を変更する反例を含める．
完全な補助証明を共有し，通常のLeanにも同じ数学的な補題を与える．
