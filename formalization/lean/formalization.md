# 共通項の PTS の Lean 形式化の設計

対象は [system.md](../../doc/book/src/system.md) の共通項による PTS。
自然言語の相対無矛盾性証明は [分類付き補助体系の core](../../doc/book/src/props/props.md) を対象とし、共通項への移送と一般の datatype への拡張が残っている。
以下は未実装の設計案である。

## 1.1 presentation の照合

`RefType.System.Derives` を定義し、正本との導出可能性の対応を示す。

- 名前付き変数と右端への文脈拡張を、de Bruijn index・逆順リスト・`Lookup` に移す。
  末尾の変数規則と weakening から任意位置の lookup を導く。
- `propWeak` を設ける場合は `proveTerm`・`typeWeak`・`provableIntro` の合成へ戻せることを示す。
- `appElim` は正本の二 premise を使う。
  結果型の sorting は product generation・regularity・substitution から導く。
- choice、RunStep・run、Box、datatype、集合値の transport は、それぞれの構文・規則・意味を追加して照合する。

## モデル

[universe 仮定](../../doc/book/src/props/model.md#universes) のもとで `UniverseTower` を定義し、sort、product、集合演算、等号、存在、take の意味と法則を持たせる。
各 field の同時実現と、現在の [型コードモデル](../../doc/book/src/props/coded_model.md) との対応を示す。
soundness はこれらから証明する定理である。

解釈は導出に索引付けし、`SortDenotes`・`TypeDenotes`・`TermDenotes`・`ProvDenotes` と valid valuation を使う。
命題の真偽と証明項の値を区別し、proof term は一つの `proofVal` に解釈する。
同じ raw 項・文脈に対する導出間の値の一致を coherence として示す。

## 構文と導出の補題

1. sort 注釈を保つ一般 renaming と同時代入を定義し、恒等・合成・binder の持ち上げ・代入の可換性を証明する。
2. parallel reduction と complete development から confluence、joinability、head discrimination を示す。
3. regularity と、refinement を含む product・lambda・subset・take の generation を証明する。
4. sorting・typing・provability の subject reduction を同時に示す。
5. 完全注釈付き導出への elaboration と raw 導出への erase を構成する。
6. semantic renaming・substitution、解釈の存在・一意性、簡約と conversion の意味保存を同時に示す。
7. `falseProp := ∀ P : Prop, P` の解釈が偽であることから consistency を得る。

## 完全注釈付き導出

soundness の conversion case と、意味保存の beta case が互いを使うため、次の object を一つの tagged mutual family として `Type` に置く。

| object | index と保持する情報 |
| --- | --- |
| `DerivesPlus` | context・sequent、premise、WF、regularity |
| `LookupPlus` | context・変数位置・型・sort |
| `SubstPlus` | source / target、引数と prefix |
| `TypedStep` | 判断・source / target の項、一歩簡約 |
| `TypedPath` | context・sort・両端、簡約列 |
| `TypedConv` | context・sort・両端、conversion |
| `TypedJoin` | 二つの始点・共通終点と経路 |
| `CtxConvPlus` | source / target の文脈と対応 |
| `OriginPlus` | context と sorting / typing の導出 |

index は raw syntax とし、再帰する証明 object は strictly positive な field に置く。
endpoint の一致は equality field で保持する。
rank は immediate child の rank の和に1を加えて定め、生成した transport・elaboration certificate も child として数える。

同じ rank では次の phase 順序を使う。

1. renaming・substitution
2. generation・regularity
3. typed step・path・join
4. 解釈の存在
5. fundamental theorem
6. coherence

前の phase へ戻る参照は、rank が小さい certificate に限る。
`typeConv` は raw `BetaEq` を保持し、typed path の意味保存と coherence を経由する。
`Nonempty DerivesPlus` からの witness 選択は Lean の meta-level で行う。

各補題の自然言語側の依存関係は [typing](../../doc/book/src/props/typing.md)、[generation](../../doc/book/src/props/generation.md)、[意味保存](../../doc/book/src/props/semantic_conversion.md) を参照。
