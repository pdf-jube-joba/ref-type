# L04 検査の再開

基点: main bd8fd86d5368968ff22e06f81beb5469bc348623。
作業先: /workspace/ref-type-l04、ブランチ codex/l04-characteristic-series。

```sh
cd /workspace/ref-type-l04
/workspace/ref-type/target/debug/cli libs/algebra/characteristic_series --module characteristic_series --cache-stats --diagnostics compact --report-json work/l04-target.json
/workspace/ref-type/target/debug/cli libs/algebra/characteristic_series --cache-stats --diagnostics compact --report-json work/l04-dependencies.json
```

workspace の libs/refcache を再利用する。
処理系がない場合は `CARGO_TARGET_DIR=/workspace/ref-type/target cargo build -p cli --locked --offline` でビルドする。

有理数可換環、任意精度の和・積・単位逆・零定数項での合成・指数、それらの切断整合性を実装済み。
単位逆の積の法則、基本対称式の置換不変性、任意の根数・任意次数での Newton 恒等式を検査済み。
直近の対象検査は work/newton-check.log で成功。
残作業は特性級数・乗法列・次数4/8の係数計算、公開多項式 API、利用例、README、依存を含む最終検査、PR。

特性級数を生成関数から構成し、任意の精度変更との整合性を実装した。
`work/generate_l04.py` は次数8まで（Chern 根の次数4）の表に対する具体的な等式証明を生成する。
`Rational/Computed.ref` の各算術補題も商と交差積の等式を通常の kernel で検査する。
次の検査対象は `characteristic_series.Characteristic`、ログは `work/tables-check.log`。

任意の有理係数可換環で Todd・L・A-hat の根追加に対する次数8の公式と、Chern 指標の正次数の公式を生成した。
`PolynomialCalculation` の証明は primitive な環の法則と具体的な有理数の等式だけを使う。
同分母加算と分数拡大の補題を追加し、大きい交差積の直接簡約を除いた。
最初の係数表検査は180秒の時間上限となったため、この補題を用いた新しい証明で再検査する。
