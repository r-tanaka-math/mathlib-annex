# 帰属・変更表示

上流の実 source、commit、Git blob、SHA-256、actual-read 範囲は `PROVENANCE.json` にあります。匿名 typed examples を含めた宣言ごとの候補比較・採否は `REUSE_LEDGER.json` にあります。原版の完全な source や原 Return ZIP を再配布する包装にはしていません。

Mathlib は固定 commit、Annex は現 dispatch に記録された公開 commit と受理済み source の系譜を用いています。Annex の Ryotaro Tanaka 氏の copyright・author・Apache-2.0 notice は `THIRD_PARTY_NOTICES.md` に保持し、license 全文は `LICENSES/Apache-2.0.txt` に保持しました。原 A/B Return と指定 Mathlib／Annex のこの license 本文の SHA-256 は `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` です。

新作と再利用の区別は次のとおりです。

- `CompressionCorner` の実 support/corner は provider API の再利用です。有界強収束の閉 convergence locus の証明経路には既存 `Enveloping/ApproximateUnit` の adaptation があります。
- `MinimalColumn`、`SpectralCutoff`、`OrthogonalSequence`、`MinimalColumnTransfer` は既存の最小射影・scalar corner・support・正負部分・級数・連続性 API を組み合わせた新証明です。既存 C の最小射影→abelian 補題は、そのまま直接使用しています。
- `Sakai` は W03 `FactorRestriction` の実制限・商の証明を非 type I に一般化した adaptation と、A/B の既存順方向の API 合成です。
- `UnitizationSubquotient` は A W03 `NonUnitalGCRSubalgebra` の局所的な実 range 構成を公開一般補題へ取り出し、実商 diagram を追加した adaptation です。
- `DiffuseFactor` と `CARTraceTest` は W03 の実極値 state/GNS 構成、既存 CAR trace モデル、および今回の移送定理を接続します。CAR のモデル、II₁ 性、trace vector、巡回性を作り直していません。

W04の mathematical route の原資料は、前回dispatch `GLIMM_SAKAI_W03_AUDIT_AND_COMBINED_LOCAL_L01_DISPATCH_R1.zip` の外部参照 `MATH/MINIMAL_COLUMN_TRANSFER_ROUTE_JA.md` です。このReturnには同梱せず、原dispatchのidentityと当該資料の記録hashを `PROVENANCE.json` に保持します。その資料は proof proposal であり、Lean provider とみなしていません。今回の Lean 本文がどの主張を実装したかは `REPORT_JA.md` と宣言台帳に明示しました。

原 A W03・B W03・C W02 の既存 153 source の公開許諾・kernel 資格は変更していません。新 W04 source の exact release grant も推論せず、`OWNER_EXACT_RELEASE_DECISION_PENDING` のままです。これは依頼された source handoff の完成を妨げる確認要求ではなく、将来の公開時の帰属状態を正確に保持する記録です。

## W05の追加分

上記は継承したW04の帰属記録です。W05では次を追加しました。

- `TraceMatrixCompression` はMathlibの実行列・Euclidean演算子同値・adjoint圧縮の正性と、Annexの実CAR有限段階を再利用する新証明です。非零像ベクトルの正規化は同じBのW04 `MinimalColumn` の初等的議論を、内部minimalityを要求しない形へ適用したproof adaptationです。
- `TraceBimoduleMap` は固定B `PositiveBimodule` のcompact familyとmap recoveryを直接利用します。閉条件を共通cluster pointへ移す証明経路は固定B `CommutantRetraction` を参照したadaptationで、値域・有限段階・norm densityの接続は今回の実sourceにあります。
- `Equivalences` は同じBのW04条件付きconsumerの矛盾を、実Eを供給した公開定理へ組み立てたadaptationと、Aの既存internal/GCR同値のAPI合成です。Aの証明を複製していません。

今回の数学routeは現dispatch `MATH/TRACE_BIMODULE_MAP_ROUTE_JA.md` の制作指示です。予約名や提案式を証明済みproviderとしては扱っていません。実sourceのrepo/ref/path/blob/hash、actual-read範囲、宣言ごとの再利用と新規部分は台帳にあります。公開sourceのcache保存時の末尾LF訂正は、取得したGit blobに戻すbyte訂正であり、上流sourceの変更ではありません。

W05新規sourceもintended Apache-2.0として記録し、依頼されたsource handoffを行っています。exact contributionの公開・許諾状態は別工程のままで、本Chatでは公開していません。
