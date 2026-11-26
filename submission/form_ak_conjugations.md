# SAIR Proof Track 投稿用フォーム

| 項目 | 入力内容 |
|---|---|
| Title | Exactly nine ordinary moves and two conjugations for AK(1), with a uniform n+6 lower bound for AK(n) |
| Authors | Hideto Iitsuka |
| Claim type | Proof of AC |
| Result completeness | Partial result |
| Description | [英語の投稿本文](description_ak_conjugations.md) を全文使用。共役回数、最短手数、一様下界の証明と9手の操作列を収録。 |
| References | Hideto Iitsuka, [ACC-P000032](https://competition.sair.foundation/contributor-network/acc/ACC-P000032) |
| Repository link / Commit SHA | 任意。本文だけで提出可能。コードを添える場合は、該当コミットを公開した後、`https://github.com/suii00/sair-acc-proof` とその40桁の SHA を一緒に入力。 |
| arXiv / Paper Link | 任意。空欄。 |

## 再現と共同検証

macOS のクリーンビルドで、新規25件を含む131定理の公理を確認した。すべて Lean の標準公理の範囲に収まり、最短9手と操作別下限も別のファイルから再確認した。`scripts/reproduce.sh` で公式定義に対するビルドと公理監査を、`python3 research/ak1-conjugations/check.py` で9手の自由簡約、四点の全置換、100例の行列計算を再現できる。[Lean の全ビルド記録](../logs/build_ak_conjugations.log) · [独立した Python 検算](../research/ak1-conjugations/check.py)

Gemini 4 Neon が共役回数をテーマに選んだ。Fable 5.2 は部分群グラフを使って別証を与え、一様な証明で合成数を法に取る点を点検した。最終査読では9手のすべての中間語と、右乗算5回・反転2回・共役2回の最適性を独立に確認した。[Fable の証明と操作列](../research/ak1-conjugations/fable.md)

Open Math OS の `sair-acc-proof` プロジェクトで `siege-workflow` を数学的査読に、`lean-workflow` を有限証明書の独立検査と Linux 再ビルドに使用した。Linux の固定版 Lean 4.29.1 では依存ライブラリと基準コミットのビルドキャッシュを再利用し、提出候補の10ファイルのハッシュを照合した。最短距離を含む新規定理を再コンパイルし、131件の公理検査がすべて成功した。数学的査読で9手の最短性と全パラメータの下界を確認した。四点の別実装でも、1回以下の共役で到達できる置換の組に目標が含まれないことを Lean で確認した。[AK(1) 査読](https://os.openmathmodel.org/app/t/o-1c8a367d-9425-412d-b0df-c332a6c601b5/p-16764613ac5a4732871a91dfb31065e7/please-act-as-an-1upq) · [四点の検査](https://os.openmathmodel.org/app/t/o-1c8a367d-9425-412d-b0df-c332a6c601b5/p-16764613ac5a4732871a91dfb31065e7/independently-verify-the-s4-2zy0) · [全パラメータの査読](https://os.openmathmodel.org/app/t/o-1c8a367d-9425-412d-b0df-c332a6c601b5/p-16764613ac5a4732871a91dfb31065e7/independent-referee-check-for-5fir) · [提出候補ソースの Linux 再ビルド](https://os.openmathmodel.org/app/t/o-1c8a367d-9425-412d-b0df-c332a6c601b5/p-16764613ac5a4732871a91dfb31065e7/verify-the-attached-six-b317)
