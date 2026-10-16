# package 単位の検査成果物

実装済み。
現在の API と保存形式は [sema](../../src/sema/README.md)、[project](../../src/project/README.md)、[resolver](../../src/resolve/README.md) を参照。

## 再利用の単位

| identity | 内容 |
| --- | --- |
| `PackageInstanceId` | 正規化した package root |
| `PackageInputKey` | 処理系・設定・自身のソースと manifest・名前付き直接依存の入力キー |
| `ArtifactKey` | 入力キーと検査範囲 |
| `ObjectDigest` | 個別 object の内容 digest |

成果物は自身の宣言と依存成果物への参照を持つ。
依存の訪問順や無関係な利用側からキーを独立させ、diamond の共通依存は同じ instance として読む。
別 root の nominal identity は区別する。

resolver・raw・kernel の import/export API が保存用 ID と実行時 ID を対応付ける。
部分成果物の重複宣言も、同じ入力と identity を確認して共有する。
結果 object と環境 object を分け、無変更検査では結果だけを読む。
途中再開は現在の package の状態と依存参照を checkpoint に保存する。

## 検証

[キャッシュの受け入れテスト](../../tests/cache) と [内部テスト](../../src/sema/tests) は、入力変更、別利用側、diamond、依存順、部分検査、途中再開、破損、並行公開と GC を確認する。
[計測ツール](../../benchmarks/README.md) では chain・diamond と実ライブラリについて cold・warm・編集・別利用側・中断再開を比較する。
保存量、I/O、検査数、時間、peak RSS を同じ入力・ビルド・実行列で測る。
