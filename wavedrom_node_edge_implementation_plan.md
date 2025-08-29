# WaveDrom Node/Edge SystemVerilogアサーション生成 作業リスト

## プロジェクト概要
WaveDromのnode/edge記法からSystemVerilogアサーションを生成する機能を実装する。
既存の自動生成機能を削除し、明示的なnode/edge記法のみを使用したシンプルで正確なシステムに置き換える。

## 設計方針
- **Sharp Lines（直線）**: 厳密なタイミング制約
- **Splines（曲線）**: 柔軟なタイミング制約
- 公式WaveDrom仕様に準拠した実装

---

## フェーズ1: 既存機能の削除・整理

### 1.1 既存自動生成機能の完全削除
- [ ] `src/extension.ts`の`_generateSVAFromJSON`メソッド内の複雑なロジックを削除
- [ ] 関連する解析メソッドを削除:
  - [ ] `_analyzeWaveformDetails`
  - [ ] `_parseExtendedConfig`  
  - [ ] `_analyzeProtocolPatterns`
  - [ ] `_generateOptimizedAssertions`
  - [ ] その他の自動検出・解析機能
- [ ] 複雑な設定解析機能（assertion_config等）を削除

### 1.2 WaveDrom専用骨格の作成
- [ ] 新しい`_generateSVAFromWaveDrom`メソッドの骨格作成
- [ ] 基本的なJSONバリデーション機能のみ保持
- [ ] シンプルなエラーハンドリング機能

---

## フェーズ2: Node解析機能の実装

### 2.1 Node位置解析器
- [ ] `signal[].node`文字列パーサーの作成
  - [ ] 文字位置からノードIDを抽出
  - [ ] ノードID（a,b,c...）と位置インデックスのマッピング
- [ ] ノード情報構造体の定義
  ```typescript
  interface NodeInfo {
    id: string;           // 'a', 'b', 'c'...
    signalName: string;   // 'req', 'ack', 'data'...
    position: number;     // タイミング位置
    eventType: string;    // 'rising_edge', 'falling_edge', 'data_change'
  }
  ```

### 2.2 Signal状態検出器
- [ ] Wave文字列解析機能
  - [ ] `wave`文字列とnode位置の組み合わせ解析
  - [ ] 各位置での信号状態変化の特定
- [ ] 信号イベント分類器
  - [ ] 立ち上がりエッジ検出（0→1）
  - [ ] 立ち下がりエッジ検出（1→0）
  - [ ] データ変化検出（x→値, 値→値）
  - [ ] 安定状態検出

### 2.3 Node-to-Signal マッピング
- [ ] ノードIDから信号名・イベント特定機能
- [ ] SystemVerilog関数へのマッピング
  - [ ] `$rose(signal)` - 立ち上がりエッジ
  - [ ] `$fell(signal)` - 立ち下がりエッジ  
  - [ ] `$changed(signal)` - データ変化
  - [ ] `$stable(signal)` - 安定状態

---

## フェーズ3: Edge解析機能の実装

### 3.1 Edge記法パーサー
- [ ] Sharp Lines記法解析器
  - [ ] `-` - 基本接続
  - [ ] `-|` - 即座の因果関係
  - [ ] `-|-` - 1サイクル遅延
  - [ ] `-|->` - 厳密な遅延関係
  - [ ] `-|>` - 短い厳密遅延
  - [ ] `|->` - 条件付き厳密関係
  - [ ] `<->` - 厳密な双方向関係
  - [ ] `->` - 厳密な方向性
  - [ ] `+` - 論理AND関係

- [ ] Splines記法解析器
  - [ ] `~` - 柔軟な接続
  - [ ] `-~` - 柔軟な関係
  - [ ] `-~>` - 柔軟な遅延関係
  - [ ] `~->` - 柔軟な方向性
  - [ ] `<~>` - 柔軟な双方向関係
  - [ ] `<-~>` - 広範囲双方向

### 3.2 Edge情報構造体
- [ ] Edge情報の定義
  ```typescript
  interface EdgeInfo {
    fromNodeId: string;
    toNodeId: string;
    edgeType: 'sharp' | 'spline';
    operator: string;     // '-|', '-~>', '<->', etc.
    description?: string; // オプショナルな説明文
  }
  ```

### 3.3 Edge-to-SystemVerilog マッピング辞書
- [ ] Sharp Lines → SystemVerilog変換テーブル
- [ ] Splines → SystemVerilog変換テーブル
- [ ] 設計指針に基づくマッピング実装

---

## フェーズ4: SystemVerilogアサーション生成エンジン

### 4.1 Property文生成器
- [ ] Node/Edge情報からproperty文生成
- [ ] タイミング演算子の選択ロジック
  - [ ] Sharp Lines: `##1`, `##2`, `|=>`, `|->`, `iff`
  - [ ] Splines: `##[0:$]`, `##[1:$]`, `s_eventually`
- [ ] 複合条件の生成（and, or, not）

### 4.2 Assert/Assume/Cover文生成器
- [ ] Property文をassert文に変換
- [ ] クロック条件の自動検出・付加
- [ ] リセット条件の自動付加
- [ ] Assert強度の選択（assert, assume, cover）

### 4.3 モジュール構造生成器
- [ ] 完全なSystemVerilogモジュール生成
- [ ] 信号宣言の自動生成（input/output/logic）
- [ ] 信号幅の自動検出
- [ ] インデント・フォーマット機能
- [ ] コメント生成機能

---

## フェーズ5: テスト・検証

### 5.1 基本記法テスト
- [ ] `node_edge_sample.json`での動作確認
  - [ ] `a~c t1` (Spline記法)
  - [ ] `d-|->b t2` (Sharp Line記法)
  - [ ] `e-|h setup` (基本Sharp記法)
  - [ ] `h<->c sync` (双方向Sharp記法)

### 5.2 複合パターンテスト
- [ ] `simple_protocol.json`での状態機械テスト
- [ ] `pipeline_example.json`での複雑パイプラインテスト
- [ ] 複数の記法が混在するケースのテスト

### 5.3 SystemVerilog文法検証
- [ ] 生成されたコードの構文チェック
- [ ] SystemVerilogシミュレータでの検証
- [ ] アサーション実行テスト

---

## フェーズ6: 最適化・仕上げ

### 6.1 エラーハンドリング強化
- [ ] 不正なnode記法の検出
- [ ] 不正なedge記法の検出
- [ ] 未定義ノード参照の検出
- [ ] ユーザーフレンドリーなエラーメッセージ

### 6.2 出力フォーマット最適化
- [ ] 可読性の高いSystemVerilogコード生成
- [ ] 適切なインデントとコメント
- [ ] 生成日時・設定情報の自動付加
- [ ] デバッグ情報の出力オプション

### 6.3 ドキュメント・設計指針の完成
- [ ] 実装結果に基づく設計指針の検証・更新
- [ ] 使用例の追加
- [ ] トラブルシューティングガイド
- [ ] APIドキュメントの作成

---

## 成果物

### 最終的な成果物
1. **WaveDrom Node/Edge → SystemVerilog変換エンジン**
2. **Sharp Lines/Splines完全対応**
3. **公式WaveDrom仕様準拠の実装**
4. **包括的なテストケース**
5. **完全なドキュメント**

### 技術仕様
- TypeScript実装
- VS Code拡張機能として統合
- WaveDrom公式仕様100%準拠
- SystemVerilog IEEE 1800準拠

---

## 開始確認

**フェーズ1（既存機能削除）から開始準備完了**

次のステップ: `src/extension.ts`の既存自動生成機能を削除し、シンプルなWaveDrom専用の骨格を作成する。
