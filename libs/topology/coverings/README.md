# 被覆空間とモノドロミー

`Projection[E, B, total, base, projection]` は全空間、底空間、位相と射影を受け取る。
`Covering` は連続性、全射性、および各底点の近傍でファイバーに離散位相を入れた積への局所自明化を要求する。

| module | 内容 |
| --- | --- |
| `Around` | 局所自明化、局所切断、シートの添字と連続性 |
| `Lifting.Existence` / `Uniqueness` | 道の持ち上げの存在と一意性 |
| `Lifting.Squares` | 指定された初期辺からの正方形全体の持ち上げ |
| `Lifting.Homotopy` | 射影した道の端点固定ホモトピーの反映 |
| `Transport` / `Homotopy` / `Classes` | 一意な道の持ち上げ、終点輸送、ホモトピー不変性と商への降下 |
| `Transport.Groupoid` / `Action` | 基本亜群による輸送、基本群のファイバー上の右作用 |
| `Fundamental` | 被覆が誘導する基本群の準同型の単射性 |
| `Fundamental.Monodromy` | 像と安定化部分群の一致、連結被覆のファイバーと剰余類集合の同変全単射 |

持ち上げの存在には区間・正方形のコンパクト性と有限細分を使う。
一意性は局所自明化の離散ファイバーと、離散空間への連続な道の定値性から示す。
局所自明性から持ち上げを証明しており、`Covering` の定義に持ち上げの存在や分類は含めていない。

`Fundamental[e].Monodromy[covering]` の `imageMembership` は
\(p_*\pi_1(E,e)\) とモノドロミーの安定化部分群の一致である。
全空間が道連結なら `orbit` と `inverseOrbit` は、その部分群の左剰余類集合とファイバーの相互逆を与える。

分類定理の完成には、局所道連結かつ半局所単連結な底空間に対する任意の部分群からの被覆の構成、同じ部分群に対応する基点付き被覆の同型、基点を忘れたときの共役類との対応が必要である。

```sh
target/debug/cli libs/topology/coverings --module covering_spaces
```
