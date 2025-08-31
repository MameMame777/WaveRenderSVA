# WaveDrom文法 ↔ SystemVerilogアサーション対応表

## 本プロジェクト(WaveRenderSVA)の現在実装仕様 - SystemVerilog LRM準拠版

## Issue #2 対応 - 安定性と変化検出オペレータ

### 新規追加オペレータ

| WaveDrom演算子 | 意味 | SystemVerilog関数 | 説明 |
|-------------|-----|-----------------|-----|
| `<->` | 安定性チェック | `$stable(signal)` | 信号が変化せず安定していることを検証 |
| `<~>` | 変化検出 | `$changed(signal)` | 信号が変化したことを検証 |

### 実装例

#### 安定性アサーション (`<->`)
```json
{
  "signal": [
    {"name": "data_bus", "wave": "x===x", "node": ".a"},
    {"name": "enable", "wave": "01..0", "node": ".b"}
  ],
  "edge": ["a<->b"]
}
```

生成されるSystemVerilog：
```systemverilog
property edge_a_to_b_0;
  @(posedge clk) disable iff (!rst_n)
  $stable(data_bus) |=> $stable(enable);
endproperty
```

#### 変化検出アサーション (`<~>`)
```json
{
  "signal": [
    {"name": "counter", "wave": "0123.", "node": ".a"},
    {"name": "clock", "wave": "p....", "node": ".b"}
  ],
  "edge": ["a<~>b"]
}
```

生成されるSystemVerilog：
```systemverilog
property edge_a_to_b_0;
  @(posedge clk) disable iff (!rst_n)
  $changed(counter) |=> ##[0:3] $changed(clock);
endproperty
```

## 用語定義 (Definitions)

### SystemVerilog LRM準拠用語

- **Overlapped implication (`|->`)**: 
  - Aが成立したサイクルと同一サイクルからBの評価を開始する意味
  - 例: `A |-> B` は A が true の同サイクルからシーケンスを評価開始
  - タイミング: `req`がサイクル5で成立 → サイクル5からack評価開始

- **Non-overlapped implication (`|=>`)**: 
  - Aが成立した「次のサイクル」からBの評価を開始する意味
  - 例: `A |=> B` は A が true の次サイクルからシーケンスを評価開始
  - タイミング: `req`がサイクル5で成立 → サイクル6からack評価開始

- **weak / strong (sequence semantics)**: 
  - `weak(##[0:$] B)` はシミュレーション終了時にBが来なくても成立する可能性がある
  - `strong(##[0:$] B)` または単に `##[0:$] B` は Bが必ず来なければ不成立
  - **注意**: implication (`|->`, `|=>`) の種類とは別概念

- **N (timingDiff)**: 
  - `N` は WaveDrom の node 位置差を整数で表したもの
  - 計算方法: `target.position - source.position`（詳細は §5 に記載）
  - 例: ノード`a`が位置1、ノード`b`が位置3 → `N = 2`

⚠️ **重要な注意事項**

- `|->` は **overlapped implication**（Aと同じサイクルからBを評価）
- `|=>` は **non-overlapped implication**（Aの次サイクルからBを評価）
- 「双方向」を実現するには2本のアサーションが必要
- `##[0:$]` は標準的な「いつか」を表現（unbounded eventually）

## サンプルJSON例

以下の標準的なWaveDrom JSONを参考に、WaveDrom記法とSystemVerilogアサーションの対応を説明します：

```json
{
  "signal": [
    { "name": "enable",   "wave": "01...........0.", "node": ".c........." },
    { "name": "Spilne-A", "wave": "01........0....", "node": ".a........j" },
    { "name": "Spilne-B", "wave": "0.1.......0.1..", "node": "..b.......i" },
    { "name": "Spilne-C", "wave": "0..1....0...1..", "node": "...c....h.." },
    { "name": "Spilne-D", "wave": "0...1..0.....1.", "node": "....d..g..." },
    { "name": "Spilne-E", "wave": "0....10.......1", "node": ".....ef...." },
    {},
    { "name": "Sharp-A", "wave": "01........0....", "node": ".k........u" },
    { "name": "Sharp-B", "wave": "0.1.......0.1..", "node": "..l........v" },
    { "name": "Sharp-C", "wave": "0..1....0...1..", "node": "...m....w.." },
    { "name": "Sharp-D", "wave": "0...1..0.....1.", "node": "....n..x..." },
    { "name": "Sharp-E", "wave": "0....10.......1", "node": ".....o.y..." }
  ],
  "edge": [
    // --- spline edges ---
    "a~b t1 ", 
    "c-~a t2 ", 
    "c-~>d time 3", 
    "d~-e",
    "e~>f", 
    "f->g ", 
    "g-~>h", 
    "h~>i $iff (enable)$", 
    "h~->j",
    // --- sharp line edges ---
    "k->l   A->B",      
    "m-|>n  C-|>D",     
    "m-|->o C-|->E",    
    "n<->o  D<->E",     
    "k|->m  A|->C",     
    "l-| -n B-| -D",    
    "o-|u   E-|A",      
    "u+v    A+B",       
    "w-z    C-D"        
  ]
}
```

```html
<object type="wavedrom_operators_example.svg" data="./wavedrom_operators_example.svg"></object>
```


**重要**: 上記は有効なJSON形式です。各signalオブジェクトには必ず`"node"`プロパティを含める必要があります。

### 1. Sharp Lines (厳密なタイミング制約)

| WaveDrom文法 | オペレータ | 生成されるSystemVerilogアサーション | implication種別 | 説明 |
|-------------|-----------|-----------------------------------|----------------|------|
| `A<->B` | `<->` | 2本のアサーション生成 (A→B, B→A) | 双方向 | AとBが双方向関係 |
| `A-\|->B` | `-\|->` | `A \|=> ##N B` | non-overlapped | AのNサイクル後に必ずB |
| `A-\|>B` | `-\|>` | `A \|=> B` | non-overlapped | Aの次サイクルで必ずB |
| `A\|->B` | `\|->` | `A \|-> ##N B` | overlapped | AのNサイクル後にB（同サイクル評価開始） |
| `A-\|-B` | `-\|-` | `A \|=> ##1 B` | non-overlapped | Aの1サイクル後に必ずB |
| `A->B` | `->` | `A \|=> ##N B` | non-overlapped | AのNサイクル後に必ずB |
| `A-\|B` | `-\|` | `A \|=> B` | non-overlapped | Aと同時にB |
| `A+B` | `+` | `(A && B)` | combinational | AとBが同サイクル成立 |
| `A-B` | `-` | `A \|=> ##N B` | non-overlapped | AのNサイクル後にB |

### 2. Splines (柔軟なタイミング制約)

| WaveDrom文法 | オペレータ | 生成されるSystemVerilogアサーション | implication種別 | 説明 |
|-------------|-----------|-----------------------------------|----------------|------|
| `A<-~>B` | `<-~>` | `A \|=> ##[0:$] B` | non-overlapped | Aの後、いつか必ずB |
| `A<~>B` | `<~>` | `A \|-> ##[0:$] B` | overlapped | Aの後、いつかB（同サイクル評価開始） |
| `A-~>B` | `-~>` | `A \|=> ##[1:$] B` | non-overlapped | Aの後、1サイクル以降にB |
| `A~->B` | `~->` | `A \|-> ##[0:$] B` | overlapped | Aの後、いつかB（同サイクル評価開始） |
| `A-~B` | `-~` | `A \|=> ##[0:$] B` | non-overlapped | Aの後、いつか必ずB |
| `A~-B` | `~-` | `A \|=> ##[0:$] B` | non-overlapped | Aの後、いつか必ずB |
| `A~>B` | `~>` | `A \|-> ##[0:$] B` | overlapped | Aの後、いつかB（同サイクル評価開始） |
| `A~B` | `~` | `A \|=> ##[0:$] B` | non-overlapped | Aの後、いつか必ずB（次サイクル評価開始） |

**注意**: Splinesでは基本的に`##[0:$]`（unbounded eventually）を使用。実用では`##[0:100]`等のbounded制約を推奨。

### 3. Overlapped/Non-overlapped Implicationの詳細説明

#### SystemVerilog LRM準拠の正確な定義

##### Overlapped Implication (`|->`)
- **意味**: Aが成立したサイクルと同じサイクルからBの評価を開始
- **使用例**: `req |-> ##[1:3] ack` → reqが来たサイクルから、1-3サイクル以内にackを評価
- **タイミング**: `req`がサイクル5で成立 → サイクル5からack評価開始

##### Non-overlapped Implication (`|=>`)
- **意味**: Aが成立した次のサイクルからBの評価を開始  
- **使用例**: `req |=> ##2 ack` → reqが来た次のサイクルから2サイクル後にack評価
- **タイミング**: `req`がサイクル5で成立 → サイクル6からack評価開始

#### weak/strong sequenceについて（implicationとは別概念）

SystemVerilogのweak/strongは**sequence**の性質であり、**implication**の種類ではありません：

```systemverilog
// weak sequence - Bが来なくてもシミュレーション終了時に成立可能
property weak_example;
  req |-> weak(##[0:$] ack);
endproperty

// strong sequence - Bが必ず来る必要がある  
property strong_example;
  req |-> strong(##[0:$] ack);
endproperty

// 標準のuntil演算子
property until_example;
  req |-> (busy until done);
endproperty
```

#### 双方向関係の実装方法

WaveDromの`<->`は**2本のアサーション**を生成して真の双方向関係を実現：

```systemverilog
// A <-> B の場合の生成例

// A -> B方向
property a_to_b_p;
  @(posedge clk) disable iff (!rst_n)
  $rose(A) |=> $rose(B);
endproperty
a_to_b_a: assert property(a_to_b_p)
  else $error("[SVA] Bidirectional violation A->B: at time %0t", $time);

// B -> A方向  
property b_to_a_p;
  @(posedge clk) disable iff (!rst_n)
  $rose(B) |=> $rose(A);
endproperty
b_to_a_a: assert property(b_to_a_p)
  else $error("[SVA] Bidirectional violation B->A: at time %0t", $time);
```

**注意**: `<->`は単純な`(A == B)`ではなく、因果関係を持つ双方向制約として実装されます。

### 4. ノードイベント変換 (現在実装)

| ノードタイプ | SystemVerilog関数 | 使用例 | 説明 |
|-------------|------------------|--------|------|
| `rising_edge` | `$rose(signal)` | `$rose(req)` | 立ち上がりエッジ検出 |
| `falling_edge` | `$fell(signal)` | `$fell(ack)` | 立ち下がりエッジ検出 |
| `data_change` | `$changed(signal)` | `$changed(data)` | データ変化検出 |
| `stable` | `$stable(signal)` | `$stable(data)` | 安定状態検出 |
| デフォルト | `signal` | `req` | 信号直接参照 |

### 5. タイミング計算詳細

#### timingDiff の計算方法（厳密仕様）

##### 基本計算ルール
- **ソース**: WaveDromのnode文字列内でのノード位置（0-based index）
- **計算式**: `timingDiff = targetNode.position - sourceNode.position`
- **位置取得**: 左から右へのインデックス（ドット`.`含む全文字を対象）

##### 詳細な位置計算例
```typescript
// node文字列: ".a..b.c"
// 位置マッピング:
//   位置0: '.' → なし
//   位置1: 'a' → ノードa
//   位置2: '.' → なし  
//   位置3: '.' → なし
//   位置4: 'b' → ノードb
//   位置5: '.' → なし
//   位置6: 'c' → ノードc

const nodePositions = {
  'a': 1,
  'b': 4, 
  'c': 6
};

// エッジ "a->b" の場合
const timingDiff = nodePositions['b'] - nodePositions['a']; // 4 - 1 = 3
// 結果: A |=> ##3 B
```

##### 境界条件の処理

| ケース | timingDiff | Sharp Lines結果 | Splines結果 | 説明 |
|--------|-----------|----------------|-------------|------|
| 同位置 | `0` | `A \|=> B` | `A \|-> ##[0:$] B` | 同サイクル |
| 正の差 | `N > 0` | `A \|=> ##N B` | `A \|-> ##[0:$] B` | 通常の遅延 |
| 負の差 | `N < 0` | `A \|=> ##${abs(N)} B` | `A \|-> ##[0:$] B` | 逆方向エッジ（警告出力） |
| 不一致長 | - | `A \|=> ##1 B` | `A \|-> ##[0:$] B` | デフォルトフォールバック |

##### wave文字列長不一致の処理
```typescript
function handleWaveLengthMismatch(signals: Signal[]): void {
  const maxLength = Math.max(...signals.map(s => s.wave.length));
  
  signals.forEach(signal => {
    if (signal.wave.length < maxLength) {
      console.warn(`信号 ${signal.name}: wave長 ${signal.wave.length} < 最大長 ${maxLength}`);
      // nodeが範囲外の場合は無効として扱う
    }
    
    if (signal.node && signal.node.length !== signal.wave.length) {
      console.warn(`信号 ${signal.name}: node長とwave長が不一致`);
      // 短い方に合わせて処理
    }
  });
}
```

#### 詳細計算ロジック (TypeScript実装例)

```typescript
interface NodePosition {
  name: string;
  position: number;
  signal: string;
}

function calculateTiming(sourceNode: NodePosition, targetNode: NodePosition, operator: string): string {
  const timingDiff = targetNode.position - sourceNode.position;
  
  // 逆方向エッジの処理
  if (timingDiff < 0) {
    console.warn(`逆方向エッジ検出: ${sourceNode.name}->${targetNode.name}, diff=${timingDiff}`);
    return `##${Math.abs(timingDiff)}`;
  }
  
  // Sharp Lines: 正確なタイミング
  if (isSharpOperator(operator)) {
    return timingDiff > 0 ? `##${timingDiff}` : '';
  }
  
  // Splines: 柔軟なタイミング
  if (timingDiff === 0) {
    return operator.includes('|->') ? '##[0:$]' : '##[0:$]';
  }
  
  return operator.includes('|->') ? '##[0:$]' : `##[1:$]`;
}

function isSharpOperator(op: string): boolean {
  return ['->', '|->', '|=>', '-|>', '-|-', '-|', '+', '-'].includes(op.replace(/[<>]/g, ''));
}
```

#### エッジケース処理

| ケース | 処理方法 | 生成結果 | 説明 |
|--------|---------|---------|------|
| `timingDiff < 0` | `Math.abs(timingDiff)` | `##2` (逆方向) | 警告出力 + 絶対値使用 |
| `timingDiff = 0` | 同サイクル | `''` (Sharp) / `##[0:$]` (Spline) | オペレータ依存 |
| ノード不一致 | デフォルト値 | `##1` | フォールバック処理 |
| 無効ポジション | エラー回復 | `##[0:$]` | 最大限柔軟な制約 |

#### 条件付きタイミング生成

```typescript
// Sharp Lines
timingDiff > 0 ? `##${timingDiff}` : ''

// Splines  
##[min:max(timingDiff+offset, minimum)]
```

### 6. 実装例

#### 入力WaveDrom JSON

```json
{
  "signal": [
    {"name": "clk", "wave": "p......"},
    {"name": "req", "wave": "01....0", "node": ".a....."},
    {"name": "ack", "wave": "0.1..0.", "node": "..b...."},
    {"name": "data", "wave": "x=..=.x", "data": ["A", "B"], "node": ".c..d.."}
  ],
  "edge": [
    "a~>b",
    "c->a"
  ]
}
```

#### 生成されるSystemVerilogアサーション

```systemverilog
// Edge-based properties generated from WaveDrom (LRM準拠版)
property edge_a_to_b_0;
  @(posedge clk) disable iff (!rst_n)
  $rose(req) |-> ##[0:$] $rose(ack);
endproperty
edge_a_to_b_0_a: assert property(edge_a_to_b_0)
  else $error("[SVA] Edge timing violation: %s -> %s at time %0t (operator: ~>)", "a", "b", $time);

property edge_c_to_a_1;
  @(posedge clk) disable iff (!rst_n)
  $changed(data) |=> $rose(req);
endproperty
edge_c_to_a_1_a: assert property(edge_c_to_a_1)
  else $error("[SVA] Edge timing violation: %s -> %s at time %0t (operator: ->)", "c", "a", $time);
```

### 7. タイミング計算

- **N**: ノード間の位置差 (WaveDromのwave文字列内での位置)
- **Sharp Lines**: 正確なタイミング (`##N`)
- **Splines**: 範囲タイミング (`##[min:max]` または `s_eventually`)

### 7. エラーハンドリング

- **レベル**: `$error` (シミュレーション継続)
- **情報**: タイムスタンプ、信号名、オペレータ情報を含む
- **フォーマット**: `[SVA] Edge timing violation: source -> target at time Nt (operator: op)`

#### 詳細エラー処理戦略

##### 無効エッジの処理
```typescript
function handleInvalidEdge(edgeString: string, availableNodes: string[]): string {
  const [source, target] = parseEdgeNodes(edgeString);
  
  if (!availableNodes.includes(source)) {
    console.warn(`[WaveRenderSVA] 未定義ノード: ${source}, デフォルト処理適用`);
    return generateDefaultAssertion(target);
  }
  
  if (!availableNodes.includes(target)) {
    console.warn(`[WaveRenderSVA] 未定義ノード: ${target}, デフォルト処理適用`);
    return generateDefaultAssertion(source);
  }
  
  return null; // 正常処理へ
}

function generateDefaultAssertion(validNode: string): string {
  return `// 警告: 部分的なエッジ処理\n` +
         `property default_${validNode}_p;\n` +
         `  @(posedge clk) disable iff (!rst_n)\n` +
         `  $rose(${validNode}) |=> ##1 1'b1; // デフォルト制約\n` +
         `endproperty`;
}
```

##### JSON解析エラー回復
```typescript
function parseWaveDromJSON(jsonString: string): Partial<WaveDromData> {
  try {
    return JSON.parse(jsonString);
  } catch (error) {
    console.error(`[WaveRenderSVA] JSON解析エラー: ${error.message}`);
    
    // 部分的回復試行
    try {
      const partialData = attemptPartialParse(jsonString);
      console.warn(`[WaveRenderSVA] 部分的解析成功: ${partialData.validSignals.length}信号処理`);
      return partialData;
    } catch (recoveryError) {
      console.error(`[WaveRenderSVA] 回復不可能: ${recoveryError.message}`);
      return { signal: [], edge: [] };
    }
  }
}
```

##### 構文エラー（$...$）の処理
```typescript
function parseConditionString(comment: string): AssertionConditions {
  const dollarRegex = /\$([^$]+)\$/g;
  const conditions: AssertionConditions = { iff: [], disable_iff: [] };
  let match;
  
  while ((match = dollarRegex.exec(comment)) !== null) {
    try {
      const conditionText = match[1].trim();
      
      if (conditionText.startsWith('iff ')) {
        conditions.iff.push(conditionText.substring(4));
      } else if (conditionText.startsWith('disable_iff ')) {
        conditions.disable_iff.push(conditionText.substring(12));
      }
    } catch (error) {
      console.warn(`[WaveRenderSVA] 条件解析エラー: ${match[1]}, スキップ`);
    }
  }
  
  return conditions;
}
```

#### エラー分類とフォールバック

| エラータイプ | 処理方法 | フォールバック | ログレベル |
|-------------|---------|-------------|-----------|
| 無効ノード | 警告 + デフォルト制約 | `##1` | WARN |
| JSON構文エラー | 部分解析試行 | 空配列 | ERROR |
| 条件解析失敗 | 条件無視 | 通常アサーション | WARN |
| タイミング計算エラー | 最大制約 | `##[0:$]` | WARN |
| 未知オペレータ | 近似マッピング | `|=>` | INFO |

### 8. 制約事項とベストプラクティス

#### SystemVerilog LRM準拠事項

1. すべてのアサーションは `@(posedge clk) disable iff (!rst_n)` を使用
2. `##[0:$]` によるunbounded eventuallyは標準準拠
3. `|->` (weak) と `|=>` (strong) の意味的違いを明確に区別
4. 双方向関係は2本のアサーションで実装

#### 推奨事項

- **Bounded Eventually**: 実務では`##[0:$]`より`##[0:100]`等の有界を推奨
- **Strong vs Weak**: プロトコル仕様に応じて適切に選択
- **Timeout値**: 実設計のlatency仕様に合わせた調整が必要

#### 非推奨・削除された要素（LRM準拠版）

- ❌ `s_eventually` → ✅ `##[0:$]` または `strong(##[0:$])` に置換
- ❌ `s_until`, `s_until_with` → ベンダ依存拡張（非標準）
- ❌ `iff` 単体使用 → ✅ `(A == B)` で同値関係表現
- ❌ `and` 演算子 → ✅ `&&` に統一

#### 標準SVA推奨構文

| 目的 | 標準SVA構文 | 説明 |
|------|------------|------|
| weak eventually | `weak(##[0:$] B)` | Bが来なくてもシミュレーション終了時成立可能 |
| strong eventually | `strong(##[0:$] B)` または `##[0:$] B` | Bが必ず来る必要がある |
| until演算子 | `(busy until done)` | doneが成立するまでbusyを評価 |

### 9. 拡張機能

- ノード記法による正確な位置指定 (`"node": ".a........j"`)
- エッジラベル処理 (`"a~b t1"`, `"h~>i some text"`)
- 逆方向エッジ解析 (`"c-~a"`, `"h~->j"`)
- コメントからのタイミングヒント抽出
- 信号幅自動検出
- プロトコル固有の最適化
- カスタムプロパティ生成

#### 条件指定機能（iff/disable iff）

エッジコメントに`$...$`識別子で囲んだ`iff`や`disable_iff`キーワードを含めることで、アサーションに条件を追加可能：

```json
{
  "edge": [
    "a->b $iff (enable)$",
    "c~>d $disable_iff (!rst_n)$",
    "e->f $iff (mode == 2'b01)$ timing_check",
    "g~h $disable_iff (!clk_en)$ timeout"
  ]
}
```

#### 生成されるSystemVerilogアサーション例

```systemverilog
// iff条件付きアサーション
property edge_a_to_b_0;
  @(posedge clk) 
  A |=> ##N B iff (enable);
endproperty

// disable iff条件付きアサーション  
property edge_c_to_d_1;
  @(posedge clk) disable iff (!rst_n)
  C |-> ##[0:$] D;
endproperty

// 複合条件
property edge_e_to_f_2;
  @(posedge clk)
  E |=> ##N F iff (mode == 2'b01);
endproperty

// disable iff + 追加ラベル
property edge_g_to_h_3;
  @(posedge clk) disable iff (!clk_en)
  G |=> ##[0:$] H;
endproperty
```

#### コメント解析ルール

| コメントパターン | 生成される条件 | 説明 |
|-----------------|---------------|------|
| `"a->b $iff (condition)$"` | `A \|=> B iff (condition);` | iff条件付きアサーション |
| `"a->b $disable_iff (!rst)$"` | `@(posedge clk) disable iff (!rst) A \|=> B;` | disable iff条件付き |
| `"a->b $iff (en)$ label"` | `A \|=> B iff (en);` + ラベル"label" | 条件+ラベル併用 |
| `"a->b $disable_iff (!rst)$ $iff (mode)$"` | `@(posedge clk) disable iff (!rst) A \|=> B iff (mode);` | 両方の条件指定 |

#### 識別子ルール

- **`$...$`**: アサーション条件指定の識別子
- **通常のテキスト**: ラベルやコメントとして扱われる
- **複数条件**: 複数の`$...$`ブロックで異なる条件を指定可能
- **構文解析**: `$`で囲まれた部分のみアサーション生成に使用

#### パース規則詳細

##### 適用順序
1. **disable_iff**: クロッキングレベルで先に適用
2. **iff**: プロパティレベルで後に適用
3. **複数の同種条件**: AND演算子で結合

##### 文法エラー時のフォールバック
```typescript
// パースエラー処理例
function parseConditionSafely(dollarContent: string): string | null {
  try {
    if (dollarContent.startsWith('iff ')) {
      const condition = dollarContent.substring(4).trim();
      if (isValidSystemVerilogExpression(condition)) {
        return `iff (${condition})`;
      }
    }
    return null; // 無効な条件は無視
  } catch (error) {
    console.warn(`条件解析失敗: ${dollarContent}, デフォルト処理適用`);
    return null;
  }
}
```

##### 例外処理ケース
| 入力例 | 処理結果 | 理由 |
|-------|---------|------|
| `$iff (en&valid)$` | `iff (en&valid)` | 正常処理 |
| `$iff (en &&)$` | 無視 | 構文エラー |
| `$disable_iff$` | 無視 | 条件式欠如 |
| `$unknown_keyword (x)$` | 無視 | 未対応キーワード |

### 10. sample.json実例パターン

| sample.jsonのエッジ | 解析結果 | 説明 |
|-------------------|---------|------|
| `"a~b t1"` | ノードa→ノードb、ラベル"t1" | スプライン接続 |
| `"c-~a t2"` | ノードc→ノードa、ラベル"t2" | 逆方向柔軟関係 |
| `"c-~>d time 3"` | ノードc→ノードd、ラベル"time 3" | 柔軟遅延関係 |
| `"d~-e"` | ノードd→ノードe | 逆スプライン |
| `"e~>f"` | ノードe→ノードf | スプライン矢印 |
| `"f->g"` | ノードf→ノードg | シャープライン矢印 |
| `"g-~>h"` | ノードg→ノードh | 柔軟遅延 |
| `"h~>i some text"` | ノードh→ノードi、ラベル"some text" | ラベル付きスプライン |
| `"h~->j"` | ノードh→ノードj | スプライン方向 |

#### WaveDrom高度機能への対応状況

##### 現在対応済み
- 基本エッジオペレータ（Sharp Lines, Splines）
- ノード位置指定 (`"node": ".a........j"`)
- エッジラベル処理
- 条件指定（`$...$`識別子）

##### 将来対応予定（v1.x）
```json
{
  "signal": [
    {"name": "clk", "wave": "p......", "period": 2},
    {"name": "bus", "wave": "x=..=.x", "data": ["A", "B"], 
     "node": ".a..b..", "group": ["req", "ack"]},
    {"name": "group_sig", "wave": "0.1.0..", "node": ".c.d.."}
  ],
  "edge": [
    "a~>b periodic_check", 
    "c<->d $iff (group_enable)$ sync"
  ],
  "config": {"hscale": 2, "skin": "lowkey"}
}
```

##### 未対応（将来拡張）
| 機能 | 対応予定 | 理由 |
|------|---------|------|
| グループ化 (`{}`) | v2.0 | バスプロトコル対応に必要 |
| 周期波形 (`p`, `n`) | v1.5 | クロック関連制約で有用 |
| 複合データ (`data`) | v1.3 | データ依存アサーション |
| WaveJSON拡張 | v2.5 | 独自フォーマット対応 |

### 11. 実装ガイド

#### TypeScript核心実装

```typescript
// メインエントリーポイント
export class WaveformToSVAGenerator {
  private nodePositions: Map<string, NodePosition> = new Map();
  private generatedProperties: string[] = [];

  public generateSVA(waveDromJSON: string): SVAGenerationResult {
    try {
      const data = this.parseWaveDromJSON(waveDromJSON);
      this.extractNodePositions(data.signal);
      
      const properties = data.edge.map((edge, index) => 
        this.generatePropertyFromEdge(edge, index)
      );
      
      return {
        success: true,
        properties,
        warnings: this.warnings,
        statistics: this.getGenerationStats()
      };
    } catch (error) {
      return this.handleGenerationError(error);
    }
  }

  private generatePropertyFromEdge(edgeString: string, index: number): string {
    const edgeInfo = this.parseEdgeString(edgeString);
    const timing = this.calculateTiming(edgeInfo.source, edgeInfo.target, edgeInfo.operator);
    const conditions = this.parseConditions(edgeInfo.comment);
    
    return this.buildSVAProperty(edgeInfo, timing, conditions, index);
  }
}
```

#### テストケース例（Jest）

```typescript
describe('WaveformToSVAGenerator', () => {
  let generator: WaveformToSVAGenerator;
  
  beforeEach(() => {
    generator = new WaveformToSVAGenerator();
  });

  test('基本的なSharp Line変換', () => {
    const input = {
      "signal": [
        {"name": "req", "wave": "01.0", "node": ".a.b"},
        {"name": "ack", "wave": "0.10", "node": "..c."}
      ],
      "edge": ["a->c"]
    };
    
    const result = generator.generateSVA(JSON.stringify(input));
    
    expect(result.success).toBe(true);
    expect(result.properties[0]).toContain('req |=> ##1 ack');
  });

  test('条件付きアサーション', () => {
    const input = {
      "signal": [
        {"name": "req", "wave": "01", "node": ".a"},
        {"name": "ack", "wave": "01", "node": ".b"}
      ],
      "edge": ["a->b $iff (enable)$"]
    };
    
    const result = generator.generateSVA(JSON.stringify(input));
    expect(result.properties[0]).toContain('iff (enable)');
  });

  test('双方向関係', () => {
    const input = {
      "signal": [
        {"name": "sig_a", "wave": "01", "node": ".a"},
        {"name": "sig_b", "wave": "01", "node": ".b"}
      ],
      "edge": ["a<->b"]
    };
    
    const result = generator.generateSVA(JSON.stringify(input));
    expect(result.properties.length).toBe(2); // A->B, B->A
    expect(result.properties[0]).toContain('sig_a |=> sig_b');
    expect(result.properties[1]).toContain('sig_b |=> sig_a');
  });

  test('無効ノードエラー処理', () => {
    const input = {
      "signal": [{"name": "req", "wave": "01", "node": ".a"}],
      "edge": ["a->x"] // 'x'は存在しない
    };
    
    const result = generator.generateSVA(JSON.stringify(input));
    expect(result.success).toBe(true);
    expect(result.warnings.length).toBeGreaterThan(0);
    expect(result.warnings[0]).toContain('未定義ノード: x');
  });

  test('構文エラー条件', () => {
    const input = {
      "signal": [
        {"name": "req", "wave": "01", "node": ".a"},
        {"name": "ack", "wave": "01", "node": ".b"}
      ],
      "edge": ["a->b $iff (invalid_syntax))$"] // 構文エラー
    };
    
    const result = generator.generateSVA(JSON.stringify(input));
    expect(result.properties[0]).not.toContain('iff (invalid_syntax))'); // 無効な条件は無視
  });
});
```

#### 生成SVAのモジュールラップ例

```systemverilog
// 生成されるモジュール例
module wavedrom_assertions #(
  parameter string MODULE_NAME = "wavedrom_checker"
)(
  input logic clk,
  input logic rst_n,
  // プロトコル信号
  input logic req,
  input logic ack,
  input logic enable,
  input logic [1:0] mode
);

  // プロパティ定義
  property edge_a_to_b_0;
    @(posedge clk) disable iff (!rst_n)
    $rose(req) |=> ##2 $rose(ack) iff (enable);
  endproperty

  property edge_c_to_d_1;
    @(posedge clk) disable iff (!rst_n)
    $changed(mode) |-> ##[0:$] $rose(ack);
  endproperty

  // アサーション定義
  edge_a_to_b_0_a: assert property(edge_a_to_b_0)
    else $error("[%s] Edge timing violation: req -> ack at time %0t (operator: ->)", 
                MODULE_NAME, $time);

  edge_c_to_d_1_a: assert property(edge_c_to_d_1)
    else $error("[%s] Edge timing violation: mode -> ack at time %0t (operator: ~>)", 
                MODULE_NAME, $time);

  // カバレッジ
  edge_a_to_b_0_c: cover property(edge_a_to_b_0);
  edge_c_to_d_1_c: cover property(edge_c_to_d_1);

endmodule
```

#### アサーション命名規則

| 要素 | 命名規則 | 例 |
|------|---------|-----|
| プロパティ | `edge_{source}_to_{target}_{index}_p` | `edge_a_to_b_0_p` |
| アサーション | `edge_{source}_to_{target}_{index}_a` | `edge_a_to_b_0_a` |
| カバー | `edge_{source}_to_{target}_{index}_c` | `edge_a_to_b_0_c` |
| 双方向A→B | `bidir_{source}_to_{target}_{index}_p` | `bidir_a_to_b_0_p` |
| 双方向B→A | `bidir_{target}_to_{source}_{index}_p` | `bidir_b_to_a_0_p` |

#### パフォーマンス最適化

```typescript
// 大規模JSON処理用ストリーミング
export class StreamingSVAGenerator {
  private chunkSize = 1000; // エッジ処理単位
  
  public async generateSVAStream(
    jsonStream: ReadableStream<string>
  ): Promise<AsyncGenerator<string, void, unknown>> {
    const reader = jsonStream.getReader();
    let buffer = '';
    
    try {
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        
        buffer += value;
        const chunks = this.extractCompleteChunks(buffer);
        
        for (const chunk of chunks) {
          yield this.processChunk(chunk);
        }
      }
    } finally {
      reader.releaseLock();
    }
  }
}
```

### 12. ユーザーガイド

#### VS Code拡張機能の使用方法

##### ステップ1: WaveDrom JSONファイルの準備

```json
{
  "signal": [
    {"name": "clk", "wave": "p......"},
    {"name": "req", "wave": "01....0", "node": ".a....."},
    {"name": "ack", "wave": "0.1..0.", "node": "..b...."}
  ],
  "edge": [
    "a->b $iff (enable)$ req_ack_protocol"
  ]
}
```

##### ステップ2: VS Codeでの変換実行

1. JSONファイルを開く
2. `Ctrl+Shift+P` → "WaveRenderSVA: Generate SystemVerilog Assertions"
3. 出力パネルで生成されたSVAを確認
4. `.sv`ファイルとして保存

##### ステップ3: 生成SVAの検証

```systemverilog
// 生成された出力例
module assertion_checker(
  input logic clk,
  input logic rst_n,
  input logic enable,
  input logic req,
  input logic ack
);

property edge_a_to_b_0;
  @(posedge clk) disable iff (!rst_n)
  $rose(req) |=> ack iff (enable);
endproperty

edge_a_to_b_0_a: assert property(edge_a_to_b_0)
  else $error("[SVA] Edge timing violation: a -> b at time %0t", $time);

endmodule
```

#### トラブルシューティング

##### Q: エッジが認識されない
**症状**: `"a->b"`が無視される
**原因**: ノード`a`または`b`が`node`文字列に存在しない
**解決法**: 
```json
// ❌ 間違い
{"name": "req", "wave": "01", "node": ".x"}
"a->b"

// ✅ 正しい
{"name": "req", "wave": "01", "node": ".a"}
{"name": "ack", "wave": "01", "node": ".b"}
"a->b"
```

##### Q: 条件が適用されない
**症状**: `$iff (enable)$`が無視される
**原因**: `$`記号の不正な使用
**解決法**:
```json
// ❌ 間違い
"a->b iff (enable)"
"a->b $(enable)$"

// ✅ 正しい
"a->b $iff (enable)$"
```

##### Q: 生成されたSVAでシンタックスエラー
**症状**: SystemVerilogコンパイルエラー
**原因**: 信号名に無効文字が含まれる
**解決法**: 信号名を英数字+アンダースコアのみに制限

#### ベストプラクティス

##### 1. 命名規則
```json
{
  "signal": [
    {"name": "clk", "wave": "p......"},           // クロックは必須
    {"name": "rst_n", "wave": "10....."},         // リセットは推奨
    {"name": "req_valid", "wave": "01....0"},     // わかりやすい信号名
    {"name": "ack_ready", "wave": "0.1..0."}      // スネークケース推奨
  ]
}
```

##### 2. タイミング設計
```json
{
  "edge": [
    "a->b timeout",              // Sharp Line: 正確なタイミング
    "c~>d eventual",             // Spline: 柔軟なタイミング
    "e->f $iff (enable)$ check"  // 条件付き: 実用的制約
  ]
}
```

##### 3. 段階的開発
1. **フェーズ1**: 基本的なリクエスト-応答
2. **フェーズ2**: エラー条件の追加
3. **フェーズ3**: パフォーマンス制約
4. **フェーズ4**: 複合プロトコル

#### 用語集

| 用語 | 定義 | 例 |
|------|------|-----|
| **N** | timingDiffの値（ノード間位置差） | N=2 → `##2` |
| **Sharp Lines** | 厳密なタイミング制約 | `->`, `\|->` |
| **Splines** | 柔軟なタイミング制約 | `~>`, `<~>` |
| **Overlapped** | 同サイクル評価開始 | `\|->` |
| **Non-overlapped** | 次サイクル評価開始 | `\|=>` |
| **$...$識別子** | アサーション条件指定 | `$iff (enable)$` |

---

## 仕様情報

WaveRenderSVA v0.27.0の実装仕様に基づく

### バージョン互換性
- **WaveDrom**: v2.x互換
- **SystemVerilog**: IEEE 1800-2017 LRM準拠
- **VS Code**: 1.85.0以降

### ライセンス
- MIT License（WaveDromライブラリ互換）
- SystemVerilog生成コードはプロジェクト依存
