# 保存用 identity と再配置

この crate は resolver・raw・kernel が共通に使う identity の対応表と、保存形式の決定的な直列化を提供する。
言語上の package identity と、現在の arena の割当番号を分離するための基盤である。

`Identity` はテーブルの名前と、そのテーブルが使う整数または arena と整数の組である。
`Relocation` は古い identity から新しい identity への対応を保持する。
`Relocation::collecting()` では、同じ訪問処理を使って到達する identity を収集する。
予約されていない参照、異なるテーブル間の対応、矛盾する再予約はエラーになる。

`Relocate` derive は保存対象のフィールドをたどる。
`serde(skip)` と `relocate(skip)` のフィールドは再構築される作業用データとして扱う。
束縛変数の index や宣言の位置は通常の整数のまま保存し、大域参照だけに明示的な identity 実装を付ける。
生成された名前に埋め込まれた identity も同じ対応表を使う。

`Arc` と `Rc` の訪問は型と元のアドレスで共有を追跡する。
対応表が元の値と再配置後の値を保持するので、アドレスの再利用による取り違えを防ぎ、共有 DAG の各ノードを一度だけ処理する。
実際に利用中の環境は変更せず、export または import の作業用データを再配置する。

`canonical::to_vec` は postcard と互換のバイナリ表現を生成し、map のキーをエンコードした byte 列で整列する。
出力サイズと構造の深さに上限を設ける。
集合には `canonical::serialize_set` を使い、意味上順序を持つ配列はその順序を保つ。
共有する配列や namespace の合成表は elaboration 側の専用テーブル形式と組み合わせる。

検査セッションの永続化は [sema の artifact store](../sema/src/artifact_store.rs) が担う。
manifest の `graph` は kernel の不変ページとセッション情報の分割 object を列挙し、完了台帳と resolver・raw の索引を保持する checkpoint と結び付ける。
同じストアへ保存済みのページは再符号化せず、次の manifest から参照する。
ページの checksum と入力を復元前に照合し、読込後も kernel の identity を同じセッション内で保持する。
これらの参照は既存の lease・store lock・GC に含まれ、利用中のページと checkpoint を保護する。

セッション情報の区切りは内容から決め、前方に情報を追加した場合も後続の共通部分を共有する。
公開先への転送は object の digest ごとに一度行い、同じ filesystem では不変 object を hard link で共有する。
別の filesystem では圧縮済みの内容を一時ファイルへコピーして原子的に公開する。
転送前に長さと digest を照合し、manifest の公開と object の pin は共通の store lock で調停する。
作成中の object は lease の追記式 journal に登録し、manifest の公開前も GC から保護する。
