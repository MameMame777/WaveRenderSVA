# JSON拡張による柔軟なアサーション生成案

## 現在のJSON構造 vs 拡張案

### 現在のWaveDrom JSON
```json
{
  "signal": [
    {"name": "clk", "wave": "p......"},
    {"name": "request", "wave": "0.1...0"},
    {"name": "acknowledge", "wave": "0...1.0"},
    {"name": "data", "wave": "x.=...x", "data": ["A1"]}
  ]
}
```

### 拡張JSON案1: アサーション設定セクション
```json
{
  "signal": [
    {"name": "clk", "wave": "p......"},
    {"name": "request", "wave": "0.1...0"},
    {"name": "acknowledge", "wave": "0...1.0"},
    {"name": "data", "wave": "x.=...x", "data": ["A1"]}
  ],
  "assertion_config": {
    "clock_signal": "clk",
    "reset_signal": "rst_n",
    "timeout_cycles": {
      "request_ack": 15,
      "data_stable": 5
    },
    "protocols": [
      {
        "type": "request_acknowledge",
        "request_signal": "request",
        "acknowledge_signal": "acknowledge",
        "data_signals": ["data"],
        "custom_properties": {
          "max_outstanding": 2,
          "priority_levels": ["high", "low"]
        }
      }
    ],
    "assertion_strength": {
      "data_integrity": "assert",
      "timing_constraints": "assume",
      "protocol_compliance": "assert"
    }
  }
}
```

### 拡張JSON案2: 信号レベル設定
```json
{
  "signal": [
    {
      "name": "clk", 
      "wave": "p......",
      "signal_config": {
        "type": "clock",
        "frequency": "100MHz",
        "duty_cycle": 50
      }
    },
    {
      "name": "request", 
      "wave": "0.1...0",
      "signal_config": {
        "type": "control",
        "assertion_rules": [
          "no_glitch",
          "setup_hold_check"
        ],
        "timing_constraints": {
          "setup_time": "2ns",
          "hold_time": "1ns"
        }
      }
    },
    {
      "name": "data", 
      "wave": "x.=...x", 
      "data": ["A1"],
      "signal_config": {
        "type": "data",
        "width": 32,
        "encoding": "binary",
        "stability_rules": [
          "stable_during_valid",
          "no_x_when_active"
        ],
        "constraint_mode": "conservative"
      }
    }
  ]
}
```

### 拡張JSON案3: 階層的アサーション
```json
{
  "signal": [...],
  "assertion_hierarchy": {
    "interface_level": {
      "axi4_lite": {
        "address_phase": {
          "signals": ["awvalid", "awready", "awaddr"],
          "properties": ["valid_ready_handshake", "address_alignment"]
        },
        "data_phase": {
          "signals": ["wvalid", "wready", "wdata"],
          "properties": ["data_stability", "strobe_consistency"]
        }
      }
    },
    "transaction_level": {
      "read_transaction": {
        "sequence": ["arvalid", "arready", "rvalid", "rready"],
        "properties": ["ordering", "completion"]
      }
    }
  }
}
```

## 実装可能な拡張機能

### 1. 高度なタイミング制約
```json
"timing_constraints": {
  "setup_time": "2ns",
  "hold_time": "1ns",
  "clock_to_out": "5ns",
  "recovery_time": "3ns",
  "removal_time": "1ns"
}
```

### 2. カスタムプロパティテンプレート
```json
"custom_properties": {
  "fifo_protocol": {
    "template": "property ${name}_fifo_p; @(posedge clk) ${condition} |-> ##[1:${delay}] ${consequence}; endproperty",
    "parameters": {
      "delay": 3,
      "condition": "push && !full",
      "consequence": "!empty"
    }
  }
}
```

### 3. 条件付きアサーション
```json
"conditional_assertions": {
  "enable_conditions": ["system_enabled", "test_mode"],
  "disable_conditions": ["debug_mode", "scan_mode"],
  "severity_levels": {
    "critical": "error",
    "warning": "warning",
    "info": "info"
  }
}
```

### 4. プロトコル固有設定
```json
"protocol_specific": {
  "axi4": {
    "version": "4.0",
    "data_width": 64,
    "address_width": 32,
    "max_burst_length": 256,
    "exclusive_access": true
  },
  "pcie": {
    "version": "3.0",
    "lanes": 4,
    "max_payload_size": 256
  }
}
```

## 拡張実装の優先度

### Phase 1: 基本設定拡張 (即座に実装可能)
1. アサーション設定セクション
2. 信号幅の明示的指定
3. タイムアウト値のカスタマイズ
4. アサーション強度設定

### Phase 2: 高度なタイミング (中期実装)
1. セットアップ/ホールド時間
2. クロック制約
3. タイミング関係の明示的指定

### Phase 3: プロトコル固有 (長期実装)
1. 標準プロトコルテンプレート
2. カスタムプロパティ定義
3. 階層的アサーション

## 実装例: 拡張JSONの処理

```typescript
private _parseExtendedConfig(jsonData: any): AssertionConfig {
  const config = jsonData.assertion_config || {};
  
  return {
    clockSignal: config.clock_signal || 'clk',
    resetSignal: config.reset_signal || 'rst_n',
    timeoutCycles: config.timeout_cycles || {},
    protocols: config.protocols || [],
    assertionStrength: config.assertion_strength || {},
    timingConstraints: config.timing_constraints || {}
  };
}

private _generateExtendedAssertions(signals: any[], config: AssertionConfig): string {
  let assertions = '';
  
  // プロトコル固有アサーション
  config.protocols.forEach(protocol => {
    switch(protocol.type) {
      case 'request_acknowledge':
        assertions += this._generateCustomReqAck(protocol, config);
        break;
      case 'axi4_lite':
        assertions += this._generateAXI4LiteAssertions(protocol, config);
        break;
    }
  });
  
  return assertions;
}
```

## 結論

JSONの拡張により以下が実現可能：

1. **設定の明示化**: タイムアウト、信号幅、プロトコル設定
2. **柔軟なタイミング**: セットアップ/ホールド時間、クロック制約
3. **プロトコル特化**: AXI4、PCIe等の標準プロトコル対応
4. **階層的構造**: インターフェース/トランザクションレベル
5. **カスタマイズ**: ユーザー定義プロパティテンプレート

これらの拡張により、より実用的で現実的なSystemVerilog Assertionの生成が可能になります。
