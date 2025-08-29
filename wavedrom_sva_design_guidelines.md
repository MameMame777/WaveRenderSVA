# WaveDrom to SystemVerilog Assertion 設計指針

## 基本方針

**Sharp Lines（直線）**: 厳密なタイミング制約  
**Splines（曲線）**: 柔軟なタイミング制約

この区別により、異なる用途のSystemVerilogアサーションを効率的に生成する。

## WaveDrom記法とSystemVerilogアサーションマッピング

### 1. Sharp Lines（厳密なタイミング）

| WaveDrom記法 | 意味 | SystemVerilog出力 |
|-------------|------|------------------|
| `a-b` | 基本接続 | `// connection: a to b` |
| `a-\|b` | 即座の因果関係 | `$rose(sig_a) \|=> $rose(sig_b)` |
| `a-\|-b` | 1サイクル遅延 | `$rose(sig_a) \|=> ##1 $rose(sig_b)` |
| `a-\|->b` | 厳密な遅延関係 | `$rose(sig_a) \|=> ##1 $rose(sig_b)` |
| `a-\|>b` | 短い厳密遅延 | `$rose(sig_a) \|=> $rose(sig_b)` |
| `a\|->b` | 条件付き厳密関係 | `sig_a \|-> $rose(sig_b)` |
| `a<->b` | 厳密な双方向関係 | `$rose(sig_a) iff $rose(sig_b)` |
| `a->b` | 厳密な方向性 | `$rose(sig_a) \|=> $rose(sig_b)` |
| `a+b` | 論理AND関係 | `$rose(sig_a) and $rose(sig_b)` |

### 2. Splines（柔軟なタイミング）

| WaveDrom記法 | 意味 | SystemVerilog出力 |
|-------------|------|------------------|
| `a~b` | 柔軟な接続 | `$rose(sig_a) \|=> s_eventually $rose(sig_b)` |
| `a-~b` | 柔軟な関係 | `$rose(sig_a) \|=> ##[0:$] $rose(sig_b)` |
| `a-~>b` | 柔軟な遅延関係 | `$rose(sig_a) \|=> ##[1:$] $rose(sig_b)` |
| `a~->b` | 柔軟な方向性 | `$rose(sig_a) \|-> s_eventually $rose(sig_b)` |
| `a<~>b` | 柔軟な双方向関係 | `$rose(sig_a) \|-> s_eventually $rose(sig_b)` |
| `a<-~>b` | 広範囲双方向 | `$rose(sig_a) \|=> ##[0:$] $rose(sig_b)` |

## 実装戦略

### 1. Node解析
- `signal[].node`文字列から文字位置を抽出
- 各ノードIDと信号名、タイミング位置をマッピング
- Wave文字列と組み合わせて信号状態を特定

### 2. Edge解析パターン
```typescript
// Sharp Lines検出
if (edge.includes('-|') || edge.includes('->') || edge.includes('<->')) {
  // 厳密なタイミング制約生成
}

// Splines検出  
if (edge.includes('~') || edge.includes('-~') || edge.includes('<~>')) {
  // 柔軟なタイミング制約生成
}
```

### 3. SystemVerilog生成ルール

#### 厳密なタイミング（Sharp）
- 具体的なサイクル数指定: `##1`, `##2`, `##3`
- 即座の関係: `|=>`
- 条件付き関係: `|->`
- 双方向等価: `iff`

#### 柔軟なタイミング（Spline）
- 範囲指定: `##[0:$]`, `##[1:$]`
- 最終的な到達: `s_eventually`
- 時間窓指定: `##[min:max]`
- 弱い含意: `|->` + `s_eventually`

## 用途別推奨記法

### プロトコル検証
- **厳密なハンドシェイク**: `req-|->ack`
- **柔軟なフロー制御**: `data-~>valid`

### データ整合性
- **同期関係**: `clk_a<->clk_b`  
- **非同期相関**: `event_a<~>event_b`

### タイミング制約
- **固定レイテンシ**: `start-|->complete`
- **可変レイテンシ**: `trigger-~>response`

## 実装優先順位

1. **Sharp Lines基本記法** - 厳密制約の実装
2. **Splines基本記法** - 柔軟制約の実装  
3. **複合記法サポート** - より複雑なパターン
4. **最適化とエラーハンドリング**

この設計指針に基づき、WaveDromの表現力を最大限活用したSystemVerilogアサーション生成を実装する。
