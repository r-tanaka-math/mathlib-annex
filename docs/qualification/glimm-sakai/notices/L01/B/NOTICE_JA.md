# 出典・再利用・帰属

この Return は同一 B レーンの W01/W02 source を継承した候補 source です。
公開・Annex 合流は行っていません。Mathlib と Annex の exact 原版、使用した証明・定義・
instance と実読範囲は `PROVENANCE.json` および宣言ごとの `REUSE_LEDGER.json` にあります。
既存 Apache-2.0 条件を `LICENSES/Apache-2.0.txt` に保持します。著作権者を推測していません。

## 継承部分

W02 の全 Lean source は byte 不変で保持しています。全状態普遍表現の構成、literal
StrongDual の既存 scalar-valued Arens extension と包絡環の同定、一般有界密度の証明適応、
A の hereditary sandwich を利用した前向き証明などの帰属は、W02 の記録を引き継いでいます。
`PROVENANCE.json` の `authorship.exact_prior_attribution` と歴史的 provider 記録を参照してください。
歴史的 A/C の名前のみ変更した view は現在の import に使用せず、今回の exact W02 view に接続します。

## W03 の新作と証明適応

- `Enveloping/CARAverage.lean` は既存 `TensorAveraging.rowMap` と positivity を直接再利用します。
  行列単位、stage embedding、正規化、有限段階の密度も既存 CAR provider のものです。
  `CAR/FiniteAverage.lean` の `limitMatrixUnit_commute_rowAverage` の有限和計算を、
  `rho(eᵢⱼ)` と任意の target 引数に適応しています。公開 CAR source 内の平均を
  全 `B(H)` 上の写像と誤同定していません。
- Support corner は C の既存 carrier、norm、演算を使用します。全射と単射は W02 の
  onto/norm theorem を再利用し、実同型は Mathlib `StarAlgEquiv.ofBijective` です。
  非単位 corner からの abelian projection 移送では、C の whole-VN 同型用 pullback 証明を
  その実 corner に適応しています。全 VN 同士では C の `IsTypeI.map` を直接再利用します。
- 本質射影は既存 literal bidual unit の像です。表現合成の非零性は公開 Annex の
  `Quotient/SurjectiveRepresentation.lean` に同一 API があると確認し、新作の重複を削除しました。
- Positive bimodule family の compactness は既存の WOT ball compactness、positive-map
  norm bound、Mathlib の product compactness と Krein–Milman API に接続します。
  極値は scalar vector-image state family 自体から選択します。
- `NormalCompression` は既存圧縮、adjoint intertwiner、bicommutant theorem、VN の閉性と
  monotone convergence を再利用します。W02 の bimodule 計算を全 generated VN の middle
  element へ拡張した部分を明示しています。強極限からの実 LUB theorem は再証明していません。
- CAR commutant retraction、retraction に限った Schwarz、実 isometric compression に限った
  Schwarz、極値状態から full centre scalarity と実 GNS factor を得る組立ては、上記 API を
  使用した新しい証明本文です。一般 positive unital map に非可換 Schwarz を仮定しません。

数学的経路は、W01 で実読した S. Sakai, *On a characterization of type I C*-algebras*,
Bull. Amer. Math. Soc. 72 (1966), 508–512, DOI
`10.1090/S0002-9904-1966-11520-3` の positive bimodule extension と極値状態の経路です。
文献の存在を Lean 証明の代用にはしていません。今回の有限射影・spectral cutoff 残件は
`OBLIGATIONS.json` に具体化し、別論文を未読のまま証明済みとは記載していません。

受理済み Naimark や他 lane source の資格を新作 B source に転記していません。
すべての新 source は未 compile、compiled/generated census と kernel は未確認です。
