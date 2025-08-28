# SystemVerilog Assertion (SVA) 生成ロジック詳細説明

## 概要

本ドキュメントは、WaveRender SVA拡張機能におけるSystemVerilog Assertion生成の詳細なロジックを説明します。

## 生成プロセス全体フロー

```
JSON入力 → 前処理 → 信号分析 → プロトコル検出 → アサーション生成 → 出力
```

---

## 1. 入力処理とJSONクリーニング

### 1.1 JSONクリーニング (`_cleanJsonContent`)
```javascript
// コメント除去
content.replace(/\/\/.*$/gm, '');  // 行コメント
content.replace(/\/\*[\s\S]*?\*\//g, '');  // ブロックコメント

// 末尾カンマ除去
content.replace(/,(\s*[\]}])/g, '$1');

// 空白正規化
content.replace(/\s+/g, ' ').trim();
```

### 1.2 エラー解析 (`_analyzeJsonError`)
- 位置情報の抽出
- 一般的なJSON問題の検出（末尾カンマ、引用符不足等）
- 詳細なエラーレポート生成

---

## 2. 信号正規化と検証

### 2.1 信号正規化 (`_normalizeAndValidateSignals`)
```javascript
// 信号名正規化
const normalizedName = originalName.replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase();

// 重複チェック
if (seenNames.has(normalizedName)) {
    warnings.push(`Duplicate signal name detected`);
}

// 幅検出
const width = this._detectSignalWidth(signal);
```

### 2.2 信号幅検出 (`_detectSignalWidth`)
```javascript
// 明示的な幅指定
if (signal.width) return signal.width;

// 名前からの推測
if (name.includes('data') || name.includes('addr')) return 8;

// 波形パターンからの推測
if (wave.includes('x') || wave.includes('=')) return 8;
if (/[2-9a-fA-F]/.test(wave)) return 4;

// デフォルト（制御信号）
return 1;
```

---

## 3. プロトコル分析と検出

### 3.1 プロトコルパターン分析 (`_analyzeProtocolPatterns`)
```javascript
// 信号分類
signals.forEach(signal => {
    if (this._isClockSignal(signal)) {
        protocols.clockSignals.push(signal);
    } else if (name.includes('data') || name.includes('addr')) {
        protocols.dataSignals.push(signal);
    } else {
        protocols.controlSignals.push(signal);
    }
});

// プロトコル検出
const hasRequest = signals.some(s => s.normalizedName.includes('request'));
const hasAck = signals.some(s => s.normalizedName.includes('acknowledge'));
const hasValid = signals.some(s => s.normalizedName.includes('valid'));
const hasReady = signals.some(s => s.normalizedName.includes('ready'));
```

### 3.2 検出可能なプロトコル
1. **Request-Acknowledge Protocol**
   - 条件: `request`/`req` + `acknowledge`/`ack` 信号
   - 生成: ハンドシェイク、タイムアウト、データ安定性アサーション

2. **Valid-Ready Protocol**
   - 条件: `valid` + `ready` 信号
   - 生成: 安定性、デアサート規則アサーション

---

## 4. アサーション生成戦略

### 4.1 統合データアサーション (`_generateUnifiedDataAssertions`)
```systemverilog
// 基本データ整合性
property data_integrity_p;
    disable iff (!rst_n)
    @(posedge clk) (data !== 'x);
endproperty
data_integrity_a: assert property(data_integrity_p);
```

### 4.2 Request-Acknowledge Protocol (`_generateEfficientRequestAckProtocol`)
```systemverilog
// コアハンドシェイク
property req_ack_handshake_p;
    disable iff (!rst_n)
    @(posedge clk) $rose(req) |-> ##[1:10] (ack == 1'b1);
endproperty

// 順序確認
property ack_has_precedent_req_p;
    disable iff (!rst_n)
    @(posedge clk) $rose(ack) |-> 
        ($past(req, 1) || $past(req, 2) || $past(req, 3));
endproperty

// データ安定性
property data_stable_during_transaction_p;
    disable iff (!rst_n)
    @(posedge clk) $rose(req) |=> 
        $stable(data) throughout (req ##1 ack);
endproperty
```

### 4.3 Valid-Ready Protocol (`_generateEfficientValidReadyProtocol`)
```systemverilog
// Valid安定性
property valid_ready_stability_p;
    disable iff (!rst_n)
    @(posedge clk) (valid == 1'b1) && (ready == 1'b0) |-> 
        ##1 (valid == 1'b1);
endproperty

// Ready デアサート規則
property ready_deassert_rule_p;
    disable iff (!rst_n)
    @(posedge clk) $fell(ready) |-> (valid == 1'b0);
endproperty
```

---

## 5. 最適化とベストプラクティス

### 5.1 専門家推奨パターンの実装
- `disable iff (!rst_n)`: すべてのアサーションでリセット処理
- 保守的タイムアウト: `##[1:10]` での範囲指定
- 限定的X-チェック: アクティブ期間のみでのX値検証
- 信号名正規化: アンダースコア区切りの小文字変換

### 5.2 重複排除とリソース最適化
- 統合データアサーション: 複数データ信号の統一処理
- プロトコル固有生成: 検出されたプロトコルに応じた特化アサーション
- 警告システム: 問題検出と改善提案

---

## 6. 出力とレポート生成

### 6.1 モジュール構造
```systemverilog
module assertion_module (
    input logic        clk,
    input logic        rst_n,
    input logic [7:0]  data,
    input logic        request,
    input logic        acknowledge
);

// アサーション定義...

endmodule
```

### 6.2 自動レポート生成
- チェックリスト形式のレビューガイド
- 設定項目の確認事項
- 統合手順の説明
- タイムスタンプ付きトレーサビリティ

---

## 7. エラーハンドリングと診断

### 7.1 段階的エラー処理
1. JSON構文エラーの詳細解析
2. 信号定義の検証と警告
3. プロトコル不整合の検出
4. 生成されたアサーションの妥当性チェック

### 7.2 診断情報
- 位置特定型エラーメッセージ
- 修正提案付き警告
- 設定項目の自動検出と推奨値提示

---

このロジックにより、WaveDrom JSON形式から高品質で実用的なSystemVerilog Assertionを自動生成し、設計検証の効率化を実現しています。
