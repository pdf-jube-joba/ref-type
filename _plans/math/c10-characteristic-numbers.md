# C10 特性数と具体的な多様体

## 要件

- 主な実装先は `characteristic_numbers`。
- 閉多様体の基本類への評価から Stiefel–Whitney 数、Pontryagin 数、安定複素多様体の Chern 数を構成する。
- 実・複素射影空間の滑らかなモデルと位相的モデルを比較し、接束の安定表示から特性数を計算する。
- 直積・向き反転・安定法束による計算との整合性と、低次元の非零な具体値を公開する。

## 依存するタスク

- [C09 Chern 指標と乗法的特性類](c09-chern-character-genera.md)
- [G11 向きと基本類](g11-fundamental-classes.md)
- [G10 handle 分解と有限 CW 型](g10-handles-finite-cw.md)
