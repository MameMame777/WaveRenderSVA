# Test Reports Directory

## 📋 ディレクトリ概要

このディレクトリには、テスト実行結果と検証レポートが格納されています。

## 📄 格納ファイル

### 検証結果
- **verification_results.json** - メインテスト実行結果
  - 実行サマリー
  - 統計情報
  - 演算子サポート状況
  - Issue実装検証結果

## 📊 レポート形式

### verification_results.json 構造
```json
{
  "execution": {
    "timestamp": "ISO8601",
    "success": boolean,
    "totalSignals": number,
    "totalEdges": number,
    "nodeCount": number
  },
  "statistics": {
    "propertyCount": number,
    "warningCount": number,
    "errorCount": number
  },
  "operatorSupport": {
    "~>": boolean,
    "-|>": boolean,
    "|->": boolean,
    "<->": boolean,
    "<~>": boolean
  },
  "issueImplementation": {
    "feature1": boolean,
    "feature2": boolean
  }
}
```

## 🎯 品質指標

### 成功基準
- **エラー数**: 0
- **テスト成功率**: 100%
- **演算子サポート**: 全対応
- **Issue実装**: 完全実装

### 監視項目
- プロパティ生成数
- 警告数（許容範囲内）
- 実行時間
- メモリ使用量

## 📈 履歴管理

テスト結果は実行のたびに上書きされますが、重要なマイルストーンでは手動バックアップを推奨：
- Issue実装完了時
- リリース前検証時
- 重大バグ修正後

## 🔍 結果分析

### 警告の分類
1. **逆方向エッジ**: 設計上の警告（機能上問題なし）
2. **未サポート演算子**: 将来実装予定
3. **構文警告**: JSON構造の軽微な問題

### エラーの対応
- エラー発生時は即座に調査・修正
- 回帰テストで再発防止確認
- ドキュメント更新

---

**更新日**: 2025年9月1日
