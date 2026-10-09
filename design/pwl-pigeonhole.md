# 一般の鳩の巣原理

有限の型 A,B について |B|<|A| なら、任意の関数 f:A→B は異なる2入力で同じ値を持つ。
関数のグラフの異なる2出現と同じ出力を、非線形パターンで選ぶ。

## 完全なコード

- [Lean 版の全文](examples/lean/DesignExamples/Pigeonhole.lean)
- [パターンマッチ指向版の全文](examples/pmop/DesignExamples/Pigeonhole.pmop)
- [パターンの証拠を明示した Lean 版](examples/lean/DesignExamples/PatternStyle/Pigeonhole.lean)

全文には定義・補助補題・主定理の証明を含む。共通の型、標準ライブラリへの依存、
記法、検査方法は [コードの一覧と仕様](examples/README.md) にまとめる。
Lean 版と、パターンの証拠を明示した Lean 版は Lean 4.31.0 / Mathlib v4.31.0 で検査する。
`.pmop` は完全な提案ソースであり、現在の処理系では直接検査できない。

以下は主証明を抜き出したもの。使用する定義・補助補題は上記の全文にある。

### Lean

```lean
theorem collision {A B : Type*} [Fintype A] [Fintype B] (f : A → B)
    (h : Fintype.card B < Fintype.card A) :
    ∃ x y, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f h
```

### パターンマッチ指向スタイル

```egison
theorem collision {A B : Type*} [Fintype A] [Fintype B] (f : A → B)
    (h : Fintype.card B < Fintype.card A) :
    f matches $x → $v :: $y → #v :: _ as multiset (A → B) := by
  obtain ⟨x, y, hxy, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
  exact ⟨x, f x, y⟩ by exact ⟨hxy, rfl, heq.symm⟩
```

`list_collision` は状態数より長いリストに対する重複位置の分解も証明する。
関数の候補は有限な全入力のグラフであり、同じ出力を持つキーの相異性を証拠として渡す。
