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
- [x] `signal[].node`文字列パーサーの作成
  - [x] 文字位置からノードIDを抽出
  - [x] ノードID（a,b,c...）と位置インデックスのマッピング
- [x] ノード情報構造体の定義
  ```typescript
  interface NodeInfo {
    id: string;           // 'a', 'b', 'c'...
    signalName: string;   // 'req', 'ack', 'data'...
    position: number;     // タイミング位置
    eventType: string;    // 'rising_edge', 'falling_edge', 'data_change'
  }
  ```

### 2.2 Signal状態検出器
- [x] Wave文字列解析機能
  - [x] `wave`文字列とnode位置の組み合わせ解析
  - [x] 各位置での信号状態変化の特定
- [x] 信号イベント分類器
  - [x] 立ち上がりエッジ検出（0→1）
  - [x] 立ち下がりエッジ検出（1→0）
  - [x] データ変化検出（x→値, 値→値）
  - [x] 安定状態検出

### 2.3 Node-to-Signal マッピング
- [x] ノードIDから信号名・イベント特定機能
- [x] SystemVerilog関数へのマッピング
  - [x] `$rose(signal)` - 立ち上がりエッジ
  - [x] `$fell(signal)` - 立ち下がりエッジ  
  - [x] `$changed(signal)` - データ変化
  - [x] `$stable(signal)` - 安定状態

---

## フェーズ3: Edge解析機能の実装

### 3.1 Edge記法パーサー
- [x] Sharp Lines記法解析器
  - [x] `-` - 基本接続
  - [x] `-|` - 即座の因果関係
  - [x] `-|-` - 1サイクル遅延
  - [x] `-|->` - 厳密な遅延関係
  - [x] `-|>` - 短い厳密遅延
  - [x] `|->` - 条件付き厳密関係
  - [x] `<->` - 厳密な双方向関係
  - [x] `->` - 厳密な方向性
  - [x] `+` - 論理AND関係

- [x] Splines記法解析器
  - [x] `~` - 柔軟な接続
  - [x] `-~` - 柔軟な関係
  - [x] `-~>` - 柔軟な遅延関係
  - [x] `~->` - 柔軟な方向性
  - [x] `<~>` - 柔軟な双方向関係
  - [x] `<-~>` - 広範囲双方向

### 3.2 Edge情報構造体
- [x] Edge情報の定義
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
- [x] Sharp Lines → SystemVerilog変換テーブル
- [x] Splines → SystemVerilog変換テーブル
- [x] 設計指針に基づくマッピング実装

---

## フェーズ4: SystemVerilogアサーション生成エンジン

### 4.1 Property文生成器
- [x] Node/Edge情報からproperty文生成
- [x] タイミング演算子の選択ロジック
  - [x] Sharp Lines: `##1`, `##2`, `|=>`, `|->`, `iff`
  - [x] Splines: `##[0:$]`, `##[1:$]`, `s_eventually`
- [x] 複合条件の生成（and, or, not）

### 4.2 Assert/Assume/Cover文生成器
- [x] Property文をassert文に変換
- [x] クロック条件の自動検出・付加
- [x] リセット条件の自動付加
- [x] Assert強度の選択（assert, assume, cover）

### 4.3 モジュール構造生成器
- [x] 完全なSystemVerilogモジュール生成
- [x] 信号宣言の自動生成（input/output/logic）
- [x] 信号幅の自動検出
- [x] インデント・フォーマット機能
- [x] コメント生成機能

---

## フェーズ5: テスト・検証

### 5.1 基本記法テスト
- [x] `node_edge_sample.json`での動作確認
  - [x] `a~c t1` (Spline記法)
  - [x] `d-|->b t2` (Sharp Line記法)
  - [x] `e-|h setup` (基本Sharp記法)
  - [x] `h<->c sync` (双方向Sharp記法)

### 5.2 複合パターンテスト
- [x] `simple_protocol.json`での状態機械テスト
- [x] `pipeline_example.json`での複雑パイプラインテスト
- [x] 複数の記法が混在するケースのテスト

### 5.3 SystemVerilog文法検証
- [x] 生成されたコードの構文チェック
- [x] SystemVerilogシミュレータでの検証
- [x] アサーション実行テスト

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
