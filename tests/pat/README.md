# Test Patterns Directory

## 📋 ディレクトリ概要

このディレクトリには、テストパターン（JSON）とアサーション例が格納されています。

## 📄 格納ファイル

### Issue #3 テストパターン
- **issue3_node_timing_test.json** - Issue #3 専用テストケース
  - 隣接ノードsplineパターン
  - 長距離splineパターン
  - 正確タイミングパターン
  - 全演算子カバレッジ

- **advanced_logic.json** - 実用的ハンドシェイクパターン
  - enable/data/valid/ready信号
  - f~>g, g->k, k-|>m エッジ
  - Issue #3 主要検証ケース

### 包括的テストパターン
- **comprehensive_test.json** - 全機能統合テスト
  - 15信号、34エッジ
  - 全WaveDrom演算子
  - Issue #2 実装検証

## 🎯 ファイル形式

### WaveDrom JSON構造
```json
{
  "signal": [
    { "name": "signal_name", "wave": "pattern", "node": ".nodepos." }
  ],
  "edge": ["node1->node2", "node3~>node4"]
}
```

### 命名規則
- **機能別**: `[issue/feature]_[description]_test.json`
- **パターン別**: `[pattern_type]_[scenario].json`
- **統合**: `comprehensive_[scope].json`

## 🧪 テストカテゴリ

1. **基本機能**: 基本演算子動作確認
2. **Issue検証**: 特定Issue実装の検証
3. **統合テスト**: 全機能の統合動作確認
4. **回帰テスト**: 既存機能の維持確認

## 📈 今後の拡張

新しいテストパターン追加時の指針：
- 特定機能に特化したテストケース
- エッジケースとエラーケースの包含
- 実用的なユースケースの反映
- 既存テストとの重複回避

---

**更新日**: 2025年9月1日
