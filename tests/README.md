# WaveRenderSVA Tests - Integrated Test Suite

このディレクトリは、WaveRenderSVA extensionの統合テストスイートです。全ての機能テスト、リグレッションテスト、Issue検証を一つのスクリプトで実行できます。

## 📁 ディレクトリ構造

```
tests/
├── integrated_test_suite.js     # 🎯 統合テストスイート (メイン実行ファイル)
├── doc/                         # 📚 テスト仕様書・設計ドキュメント
│   ├── integrated_test_specification.md  # 統合テスト仕様書
│   └── (その他ドキュメント)
├── pat/                         # 📁 テストパターン (JSON)
│   ├── comprehensive_test.json   # 包括機能テスト
│   ├── issue3_node_timing_test.json  # Issue #3 ノードタイミングテスト  
│   └── advanced_logic.json      # 高度なロジックパターン
├── report/                      # 📊 テスト実行結果・レポート
│   ├── integrated_test_results.json   # JSON形式の詳細結果
│   └── integrated_test_report.md      # Markdown形式のレポート
├── regression_test.js           # 🔧 レガシー リグレッションテスト
├── test_verification.js         # 🔧 レガシー 検証テスト
└── README.md                    # このファイル
```

## � 統合テスト実行

### メインコマンド
```bash
# testsディレクトリから実行
cd tests
node integrated_test_suite.js
```

### 期待される出力
```
🚀 Starting WaveRenderSVA Integrated Test Suite
🧪 Testing: comprehensive_functionality
   ✅ PASSED
🧪 Testing: issue3_node_timing  
   ✅ PASSED
🔧 Timing-Aware Implication Operator Regression Tests
   ✅ Same-position test: ✅
   ✅ Different-position test: ✅
📊 Results: 6/6 tests passed
🎉 ALL TESTS PASSED!
```

## 📋 テストカバレッジ

### 1. 機能テスト
- ✅ **包括機能テスト**: 全演算子とフィーチャーの動作確認
- ✅ **Issue #3**: ノードベースタイミング計算検証
- ✅ **高度なロジック**: 複雑なパターンと関係性

### 2. リグレッションテスト  
- ✅ **同位置ノード**: `|->` (overlapped implication) 使用確認
- ✅ **異位置ノード**: `|=>` (non-overlapped implication) 使用確認
- ✅ **混合タイミング**: 元のレビュー指摘事項修正確認

### 3. 演算子サポート
- ✅ **`~>`**: Spline (柔軟タイミング)
- ✅ **`-|>`**: Sharp (正確タイミング)
- ✅ **`->`**: Simple (基本)
- ✅ **`|->` **: Immediate (即時)
- ✅ **`<->`**: Stability (安定性)
- ✅ **`<~>`**: Change (変化検出)

## 📊 レポート生成

テスト実行後、以下のレポートが自動生成されます：

### JSON レポート (`report/integrated_test_results.json`)
- 詳細な実行結果データ
- テストごとの分析情報
- タイミング演算子の詳細統計

### Markdown レポート (`report/integrated_test_report.md`)
- 人間が読みやすい形式
- テスト結果サマリーテーブル
- 成功率とプロパティ統計
- 演算子サポート状況

## � 個別テスト実行

### レガシーテスト (後方互換性用)
```bash
# 元の包括テスト
node test_verification.js

# 元のリグレッションテスト  
node regression_test.js
```

### カスタムテスト
```javascript
const IntegratedTestSuite = require('./integrated_test_suite.js');
const suite = new IntegratedTestSuite();

// 個別テスト実行
suite.runTest('custom_test', 'Description', testData);
```

## ✅ 期待される結果

- **34個のSVAプロパティ**が正常に生成される
- **5/5のWaveDromオペレータ**がサポートされる
- **0個のエラー** - 全アサーションがコンパイル可能
- **13個の警告** - 逆方向エッジと因果関係の警告（期待される動作）

## 📊 テスト成果

このテストスイートにより、以下が実証されます：

1. **Issue #2の完全実装** - `<->` (stable throughout) と `<~>` (changed detection) オペレータ
2. **SystemVerilog LRM準拠** - 正しい`throughout`構文の使用
3. **堅牢なエラーハンドリング** - 全エッジケースの適切な処理
4. **本格運用対応** - 製品品質レベルの信頼性

## 📖 関連ドキュメント

- `./COMPREHENSIVE_TEST_SPECIFICATION.md` - 完全なテスト仕様（JSON定義、タイミングチャート、結果分析を含む）
- `../WAVEDROM_SVA_MAPPING.md` - WaveDromからSVAへのマッピング仕様
