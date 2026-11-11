# Source と許諾の区分

この Return は非公開の source 制作候補である。新規 original source の予定公開条件は Apache-2.0。exact source identity に対する新しい公開許諾・release・Annex admission をこの作業で認定していない。`PROVENANCE.json` の `new_original_license` は `OWNER_EXACT_RELEASE_DECISION_PENDING`。

`LICENSE` と `UPSTREAM_THIRD_PARTY_NOTICES.md` は pinned Annex `5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e` から原 byte のまま保持した。後者にある上流 repository 内の相対リンクは、その pin の repository に対する参照であり、本 Return に存在しない upstream ファイルを同梱した意味ではない。今回 Lip 系の source port は行っていない。

`TypeI/PureStateExtension.lean` は同 pin の `State/Extension.lean` の証明経路・局所 instance パターンを一般化した。元 file に copyright/Authors 行はないため、新しい作者名を推測して加えていない。変更内容と exact git blob を source header と PROVENANCE に表示した。その他の upstream 数学 source は import/API 使用であり、Return へ vendor していない。

`TOOLS/static_lean.py` と `TOOLS/safe_zip.py` は、入力 dispatch の短い診断 helper を無改変で保持した operational code である。入力と同じ byte/hash を PROVENANCE に記録する。Return の `CHECK.py` は今回作成した小さな内容整合性 checker。

Sakai/Blackadar の数学的出典と Lean code adaptation の出典は別に記録した。論文・書籍本文の長い引用や証明全文は同梱していない。元原稿、LFH、Card、website の許諾・公開状態には触れていない。

## W02 継続

14 W01 production headers を予定 license の意味へ整合した。新たな6 production modules も同じ candidate header を用いる。上流 LICENSE/notice と既存 adaptation 表示は保持した。W02 の新しい数学本文は既存 API の適用と独立した証明の組立てで、上流の proof body を丸ごと port していない。新 source の exact 公開許諾を認定していない。

## W03 継続

受理済み W02 の91改名・14 header修理を保ち、新たな11 production modulesと11 consumersに同じ予定licenseのcandidate表示を付した。既存 W02 の数学source 36ファイルのうち35はbyte同一で、GSS moduleだけに新しい同値とimport/docを追加した。既存宣言183件の名前・書かれた型・証明は保持している。

W03 は非単位的 CFC、実 hereditary 同型、局所単位上の行列作用、実CAR商への証明を新たに組み立てた。上流数学source本文をvendorせず、既存CFC/行列/閉包/商/CAR APIを再利用した。新sourceの公開許諾、Annex受入、kernel認定を意味しない。公開v0.6.1と旧L01の対応は05の境界を維持し、同名providerを二重にロードしていない。
