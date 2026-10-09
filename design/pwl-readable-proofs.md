# 構造と推論が見える証明の例

[わかりやすさの基準](proof-brevity.md) に従い、選ぶ配置、構成要素の関係、場合分けの理由、
結論の作り方をパターンから読める例を比較する。
新しい例として、**解消規則の正しさ**と**閉じた歩道の挿入**を置く。
前者は論理的な推論の形、後者は構造をつなぎ直す形を証明の途中で示す。

既存の例も含めると、次がこの基準に合う。

| 例 | パターンに現れる配置 | その配置を使う推論 |
|---|---|---|
| [Ramsey](pwl-ramsey.md) | 同色3辺と、その先の三角形 | 内部辺の色で場合分けし、単色三角形を作る |
| 解消規則 | p を含む節と、¬p を含む節、その残り | p の真偽にかかわらず、残りを合わせた節が真になる |
| 閉じた歩道の挿入 | 元の歩道の途中の v と、v から出て v に戻る歩道 | 同じ頂点で接続し、始点・終点を保った歩道を作る |
| [Pumping](pwl-pumping.md) | 走行列の同じ状態が現れる2位置 | その間をループとして反復する |
| [局所合流性](pwl-local-confluence.md) | 二つの消去箇所の一致・重なり・分離 | 位置関係ごとに共通の消去先を作る |
| [Schur](pwl-schur.md) | x、y、x+y と共通の色 | 加法の関係を持つ同色の三つ組を作る |

Ramsey と解消規則では、選んだ要素の関係が場合分けと結論に直接つながる。
歩道の挿入と pumping lemma では、パターンで選んだ区間が、その後の構成に直接使われる。
局所合流性では、各腕が数学的な位置関係を表すことに価値がある。
Schur は主張の x+y と色の関係が見え、証明では個々の数の色を順に調べる。
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

## 検査と設計への反映

両例の通常の Lean 版と、パターンの証拠を手動で展開した版を `lake build` に含める。
全定義と補助証明を保存し、両版で同じ数学的なライブラリと補助補題を使う。
[Audit.lean](examples/lean/Audit.lean) で公理への依存を確認する。
検査環境と `.pmop` の位置付けは [コードの仕様](examples/README.md) に揃える。
`.pmop` の構文解析と証明項への自動変換は実装する必要がある。

設計上は、**複数の構成要素が共有する値を、選択の形と構成結果の両方に示せること**を重視する。
解消規則では共有する変数 p、歩道の挿入では共有する頂点 v が推論を成立させる。
したがって、複数の前提から選んだ部分構造が同じ値でつながり、残りを使って結論を作る証明は、
次の例を探す際にも有望な候補となる。
主張と腕が同じ関係を使い、その関係の証拠を場合分け・再構成・帰納仮定へ渡せることを検査する。
