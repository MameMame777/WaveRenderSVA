# JSON拡張機能実装提案

## 拡張機能の実装段階

### 1. Phase 1実装: 基本設定拡張 (即座に実装可能)

以下の機能追加により、現在のアサーション生成を大幅に改善できます：

#### 1.1 アサーション設定セクション
```typescript
interface AssertionConfig {
  clock_signal?: string;
  reset_signal?: string;
  module_name?: string;
  timeout_cycles?: {
    request_ack?: number;
    data_stable?: number;
    default?: number;
  };
  assertion_strength?: {
    data_integrity?: 'assert' | 'assume' | 'cover';
    timing_constraints?: 'assert' | 'assume' | 'cover';
    protocol_compliance?: 'assert' | 'assume' | 'cover';
  };
}
```

#### 1.2 信号レベル設定
```typescript
interface SignalConfig {
  width?: number;
  type?: 'clock' | 'control' | 'data_bus' | 'address';
  stability_required?: boolean;
  x_check_mode?: 'always' | 'active_only' | 'never';
  edge_sensitive?: boolean;
  glitch_detection?: boolean;
}
```

### 2. 実装修正案

現在の`_generateSVAFromJSON`メソッドを以下のように拡張：

```typescript
private _generateSVAFromJSON(jsonData: any): string {
  // 拡張設定の解析
  const config = this._parseAssertionConfig(jsonData);
  
  // 基本情報
  let svaCode = `// SystemVerilog Assertions generated from Extended WaveDrom JSON\n`;
  svaCode += `// Generated on ${new Date().toISOString()}\n`;
  svaCode += `// Configuration: ${JSON.stringify(config, null, 2)}\n\n`;
  
  // モジュール名のカスタマイズ
  const moduleName = config.module_name || 'assertion_module';
  const clockSignal = config.clock_signal || 'clk';
  const resetSignal = config.reset_signal || 'rst_n';
  
  // 信号の詳細解析
  const { validSignals, warnings } = this._normalizeAndValidateSignalsExtended(
    jsonData.signal, 
    config.signal_configs || {}
  );
  
  // タイムアウト値の適用
  const timeoutCycles = this._calculateTimeouts(config.timeout_cycles || {});
  
  // 拡張プロトコル分析
  const protocolAnalysis = this._analyzeExtendedProtocols(validSignals, config.protocols || []);
  
  // モジュール生成
  svaCode += this._generateExtendedModule(
    moduleName, 
    validSignals, 
    clockSignal, 
    resetSignal,
    protocolAnalysis,
    timeoutCycles,
    config
  );
  
  return svaCode;
}
```

### 3. 拡張メソッドの追加

#### 3.1 設定解析メソッド
```typescript
private _parseAssertionConfig(jsonData: any): AssertionConfig {
  const assertionConfig = jsonData.assertion_config || {};
  
  return {
    clock_signal: assertionConfig.clock_signal || 'clk',
    reset_signal: assertionConfig.reset_signal || 'rst_n',
    module_name: assertionConfig.module_name || 'assertion_module',
    timeout_cycles: {
      request_ack: assertionConfig.timeout_cycles?.request_ack || 10,
      data_stable: assertionConfig.timeout_cycles?.data_stable || 5,
      default: assertionConfig.timeout_cycles?.default || 10
    },
    assertion_strength: {
      data_integrity: assertionConfig.assertion_strength?.data_integrity || 'assert',
      timing_constraints: assertionConfig.assertion_strength?.timing_constraints || 'assume',
      protocol_compliance: assertionConfig.assertion_strength?.protocol_compliance || 'assert'
    },
    signal_configs: assertionConfig.signal_configs || {},
    protocols: assertionConfig.protocols || [],
    generation_options: assertionConfig.generation_options || {}
  };
}
```

#### 3.2 拡張信号正規化
```typescript
private _normalizeAndValidateSignalsExtended(
  signals: any[], 
  signalConfigs: Record<string, any>
): { validSignals: any[], warnings: string[] } {
  const validSignals: any[] = [];
  const warnings: string[] = [];
  const seenNames = new Set<string>();
  
  signals.forEach((signal, index) => {
    if (!signal || !signal.name || !signal.wave) {
      warnings.push(`Invalid signal at index ${index}`);
      return;
    }
    
    const signalName = signal.name;
    const signalConfig = signalConfigs[signalName] || {};
    const normalizedName = signalName.replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase();
    
    // 重複チェック
    if (seenNames.has(normalizedName)) {
      warnings.push(`Duplicate signal: ${signalName}`);
      return;
    }
    seenNames.add(normalizedName);
    
    // 幅の決定（設定優先）
    const width = signalConfig.width || this._detectSignalWidth(signal);
    
    // 拡張信号オブジェクト
    validSignals.push({
      ...signal,
      originalName: signalName,
      normalizedName: normalizedName,
      detectedWidth: width,
      config: signalConfig,
      type: signalConfig.type || this._detectSignalType(signal),
      stabilityRequired: signalConfig.stability_required || false,
      xCheckMode: signalConfig.x_check_mode || 'active_only'
    });
  });
  
  return { validSignals, warnings };
}
```

#### 3.3 拡張アサーション生成
```typescript
private _generateExtendedAssertions(
  signals: any[], 
  protocols: any[], 
  config: AssertionConfig
): string {
  let assertions = '';
  
  // プロトコル固有アサーション
  protocols.forEach(protocol => {
    switch(protocol.type) {
      case 'request_acknowledge':
        assertions += this._generateCustomReqAckProtocol(protocol, config);
        break;
      case 'valid_ready':
        assertions += this._generateCustomValidReadyProtocol(protocol, config);
        break;
      case 'axi4_lite':
        assertions += this._generateAXI4LiteProtocol(protocol, config);
        break;
    }
  });
  
  // 信号固有アサーション
  signals.forEach(signal => {
    if (signal.config.glitch_detection) {
      assertions += this._generateGlitchDetection(signal, config.clock_signal);
    }
    
    if (signal.config.stability_required) {
      assertions += this._generateStabilityAssertions(signal, config);
    }
  });
  
  // カバレッジ生成
  if (config.generation_options?.include_coverage) {
    assertions += this._generateCoverageProperties(signals, protocols);
  }
  
  return assertions;
}
```

### 4. 実装例: カスタムReq-Ackプロトコル

```typescript
private _generateCustomReqAckProtocol(protocol: any, config: AssertionConfig): string {
  const reqName = protocol.request_signal;
  const ackName = protocol.acknowledge_signal;
  const timeoutCycles = protocol.properties?.timeout_cycles || config.timeout_cycles.request_ack;
  const strength = config.assertion_strength.protocol_compliance;
  
  let assertions = `  // Custom Request-Acknowledge Protocol: ${protocol.name}\n`;
  
  // 基本ハンドシェイク
  assertions += `  property ${reqName}_${ackName}_handshake_p;\n`;
  assertions += `    disable iff (!${config.reset_signal})\n`;
  assertions += `    @(posedge ${config.clock_signal}) $rose(${reqName}) |-> ##[1:${timeoutCycles}] (${ackName} == 1'b1);\n`;
  assertions += `  endproperty\n`;
  assertions += `  ${reqName}_${ackName}_handshake_a: ${strength} property(${reqName}_${ackName}_handshake_p);\n\n`;
  
  // 未処理リクエスト制限
  if (protocol.properties?.max_outstanding) {
    const maxOut = protocol.properties.max_outstanding;
    assertions += `  property ${reqName}_max_outstanding_p;\n`;
    assertions += `    disable iff (!${config.reset_signal})\n`;
    assertions += `    @(posedge ${config.clock_signal}) $countones({${Array(maxOut).fill(`$past(${reqName}, ${i})`).join(', ')}}) <= ${maxOut};\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${reqName}_max_outstanding_a: ${strength} property(${reqName}_max_outstanding_p);\n\n`;
  }
  
  return assertions;
}
```

### 5. 利用例

```json
{
  "signal": [...],
  "assertion_config": {
    "clock_signal": "system_clk",
    "reset_signal": "system_rst_n", 
    "module_name": "memory_controller_assertions",
    "timeout_cycles": {
      "request_ack": 20,
      "data_stable": 3
    },
    "protocols": [
      {
        "type": "request_acknowledge",
        "name": "memory_access",
        "request_signal": "mem_req",
        "acknowledge_signal": "mem_ack",
        "data_signals": ["mem_addr", "mem_wdata"],
        "properties": {
          "max_outstanding": 4,
          "timeout_cycles": 25
        }
      }
    ],
    "assertion_strength": {
      "protocol_compliance": "assert",
      "data_integrity": "assert"
    }
  }
}
```

この拡張により、現在のシンプルなアサーション生成から、実用的で柔軟性の高いSystemVerilog Assertion生成システムへと大幅に向上します。
