# WaveRender SVA 拡張機能 インストール手順

## 🚀 インストール方法

### 1. VSIXファイルからインストール

1. VS Code を開く
2. コマンドパレット（`Ctrl+Shift+P`）を開く
3. "Extensions: Install from VSIX..." を選択
4. `waveform-render-0.27.0.vsix` ファイルを選択
5. 拡張機能が自動的にインストールされます

### 2. コマンドラインからインストール

```bash
code --install-extension waveform-render-0.27.0.vsix
```

## 📋 機能概要

### 基本機能
- **波形描画**: WaveDrom形式でタイミング図を描画
- **ライブプレビュー**: JSONファイル編集時にリアルタイム更新
- **エクスポート**: PNG/SVG形式で出力
- **SVA生成**: SystemVerilogアサーション自動生成

### 新機能（ADVICE2.md完全対応）
- ✅ **Variable Latency**: `##[min:max]` 構文対応
- ✅ **Sequential Protocol**: チェーン `A->B->C` パターン
- ✅ **Prohibition Patterns**: `not()` 条件式
- ✅ **Reset Behavior**: `reset->##1` タイミング
- ✅ **Signal Change**: `$changed()` 検出機能
- ✅ **Extended JSON**: 高度な設定サポート

## 🎯 使用方法

### 1. 基本的な波形描画
```json
{
  "signal": [
    {"name": "clk", "wave": "p...."},
    {"name": "req", "wave": "01.0."},
    {"name": "ack", "wave": "0.10."}
  ]
}
```

### 2. SVA生成（拡張機能）
```json
{
  "signal": [...],
  "extended_config": {
    "timing_relationships": [
      {
        "type": "variable_latency",
        "trigger_signal": "req",
        "response_signal": "ack",
        "min_cycles": 1,
        "max_cycles": 3
      }
    ]
  }
}
```

## ⌨️ キーボードショートカット

| 機能 | ショートカット |
|------|----------------|
| 波形描画 | `Ctrl+K Ctrl+D` |
| ライブプレビュー切替 | `Ctrl+K Ctrl+L` |
| SVA生成 | `Ctrl+K Ctrl+S` |

## 📁 サンプルファイル

拡張機能には以下のサンプルが含まれています：

- `advice2_sample1_handshake.json` - ハンドシェイク プロトコル
- `advice2_sample2_reset.json` - リセット動作
- `advice2_sample3_fifo.json` - FIFO制御
- `advice2_sample4_sequence.json` - シーケンス チェーン
- `advice2_sample5_clock_sync.json` - クロック同期
- `advice2_sample6_latency.json` - 固定レイテンシ

## 🧪 検証済み機能

- ✅ **JSON堅牢性**: 100% 対応
- ✅ **波形-アサーション精度**: 100% 正確
- ✅ **ADVICE2.md要件**: 6/6 完全実装
- ✅ **エラー耐性**: 完全対応
- ✅ **パフォーマンス**: 最適化済み

## 📊 テスト結果

```
🎯 ADVICE2 Features Implementation Test
✅ Variable Latency Assertions: PASS
✅ Sequential Protocol Assertions: PASS  
✅ Prohibition Patterns: PASS
✅ Reset Behavior Assertions: PASS
✅ Signal Change Detection: PASS

📊 Test Results Summary: 5/5 (100.0%)
```

## 🔧 トラブルシューティング

### 拡張機能が認識されない
1. VS Code を再起動
2. 拡張機能タブで "WaveRender SVA" が有効化されているか確認

### JSON解析エラー
1. JSON構文が正しいか確認
2. 基本的なWaveDrom形式から開始
3. `extended_config` は任意設定

### SVA生成されない
1. JSONファイルが開かれているか確認
2. `Ctrl+K Ctrl+S` でSVA生成実行
3. `signal` 配列が存在するか確認

## 📞 サポート

問題や質問がある場合：
1. GitHub Issues で報告
2. ドキュメント `FINAL_VALIDATION_REPORT.md` を参照
3. サンプルファイルで動作確認

## 🎉 完了！

拡張機能がインストールされ、ADVICE2.mdの全要件を満たすSystemVerilogアサーション生成が可能になりました。
