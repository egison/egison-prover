# Erdős–Szekeres の5項の場合

任意の線形順序における相異なる5項は、長さ3の狭義単調増加部分列または狭義単調減少部分列を持つ。
整数・実数もこの型の条件を満たす。出現位置の前後関係を保つリストパターンを使う。

## 完全なコード

- [Lean 版の全文](examples/lean/DesignExamples/ErdosSzekeres.lean)
- [パターンマッチ指向版の全文](examples/pmop/DesignExamples/ErdosSzekeres.pmop)
- [パターンの証拠を明示した Lean 版](examples/lean/DesignExamples/PatternStyle/ErdosSzekeres.lean)

全文には定義・補助補題・主定理の証明を含む。共通の型、標準ライブラリへの依存、
記法、検査方法は [コードの一覧と仕様](examples/README.md) にまとめる。
Lean 版と、パターンの証拠を明示した Lean 版は Lean 4.31.0 / Mathlib v4.31.0 で検査する。
`.pmop` は完全な提案ソースであり、現在の処理系では直接検査できない。

以下は主証明を抜き出したもの。使用する定義・補助補題は上記の全文にある。

### Lean

```lean
theorem erdos_szekeres_five {A : Type*} [LinearOrder A]
    (f : Fin 5 → A) (hf : Function.Injective f) : ∃ i j k, Triple f i j k := by
  classical
  let S := Finset.univ.image f
  have hcard : S.card = 5 := by simp [S, Finset.card_image_of_injective _ hf]
  let e : Fin 5 ≃o S := S.orderIsoOfFin hcard
  let g : Fin 5 → Fin 5 := fun i => e.symm ⟨f i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
  have hg : Function.Injective g := by
    intro i j he
    have hv := congrArg (fun k => (e k : A)) he
    exact hf (by simpa [g] using hv)
  have hlt : ∀ i j, g i < g j ↔ f i < f j := by
    intro i j
    exact e.symm.lt_iff_lt
  obtain ⟨i, j, k, hij, hjk, hmono⟩ := finite_case g hg
  refine ⟨i, j, k, hij, hjk, ?_⟩
  rcases hmono with hinc | hdec
  · exact Or.inl ⟨(hlt i j).mp hinc.1, (hlt j k).mp hinc.2⟩
  · exact Or.inr ⟨(hlt j i).mp hdec.2, (hlt k j).mp hdec.1⟩

-- Any longer sequence inherits the result by using its first five positions.
```

### パターンマッチ指向スタイル

```egison
theorem erdos_szekeres_five {A : Type*} [LinearOrder A]
    (f : Fin 5 → A) (hf : Function.Injective f) :
    f matches
      (_ ++ ($i → $x) :: _ ++ ($j → ($y & ?(x < y))) ::
        _ ++ ($k → ($z & ?(y < z))) :: _)
    | (_ ++ ($i → $x) :: _ ++ ($j → ($y & ?(y < x))) ::
        _ ++ ($k → ($z & ?(z < y))) :: _)
      as list (Fin 5 → A) := by
  classical
  let S := Finset.univ.image f
  have hcard : S.card = 5 := by simp [S, Finset.card_image_of_injective _ hf]
  let e : Fin 5 ≃o S := S.orderIsoOfFin hcard
  let g : Fin 5 → Fin 5 := fun i => e.symm ⟨f i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
  have hg : Function.Injective g := by
    intro i j he
    have hv := congrArg (fun k => (e k : A)) he
    exact hf (by simpa [g] using hv)
  have hlt : ∀ i j, g i < g j ↔ f i < f j := by
    intro i j
    exact e.symm.lt_iff_lt
  obtain ⟨i, j, k, hij, hjk, hmono⟩ := finite_case g hg
  rcases hmono with hinc | hdec
  · exact Or.inl ⟨i, f i, j, f j, k, f k⟩ by
      exact ⟨hij, hjk, rfl, rfl, rfl, (hlt i j).mp hinc.1, (hlt j k).mp hinc.2⟩
  · exact Or.inr ⟨i, f i, j, f j, k, f k⟩ by
      exact ⟨hij, hjk, rfl, rfl, rfl, (hlt j i).mp hdec.2, (hlt k j).mp hdec.1⟩
```

`finite_case` は `Fin 5 → Fin 5` の有限の主張を `decide` で証明する。
一般の値については、5つの値の有限集合を昇順に並べ、その順序を保つ全単射で `Fin 5` に写す。
その写像が大小関係と単射性を保つことを証明して、得た出現位置を元の列へ戻す。
`erdos_szekeres_prefix` は5項以上の任意の長さの列へ結果を広げる。
一般の r,s をパラメータにした長さ (r−1)(s−1)+1 の定理は、引き続き一般化する対象である。

`four_counterexample` は [2,4,1,3] が長さ3の単調部分列を持たないことを証明し、
5項が必要であることを示す。`es_two` は相異なる2項の増加・減少の場合分けを
任意の線形順序で証明する。両例もすべての版に含める。
