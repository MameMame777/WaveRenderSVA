# WaveRenderSVA Tests - Directory Structure

このディレクトリは、WaveRenderSVA extensionのテスト関連ファイルを体系的に管理するために整理されています。

## 📁 ディレクトリ構造

```
tests/
├── doc/           # テスト仕様書・設計ドキュメント
├── pat/           # テストパターン (JSON) とアサーション
├── report/        # テスト実行結果・レポート
├── test_verification.js  # メインテスト実行スクリプト
└── README.md      # このファイル
```

## 📂 各ディレクトリの役割

### `/doc` - Documentation
- **目的**: テスト仕様書、設計ドキュメント、技術資料
- **格納対象**: 
  - Issue実装仕様書
  - テスト設計書
  - API仕様書
  - 技術的詳細ドキュメント

### `/pat` - Test Patterns
- **目的**: テストパターン（JSON）とアサーション例
- **格納対象**:
  - WaveDrom JSON テストファイル
  - 生成されたSystemVerilog アサーション例
  - テストケース定義ファイル
  - パターン別テストデータ

### `/report` - Test Reports
- **目的**: テスト実行結果、検証レポート
- **格納対象**:
  - テスト実行結果JSON
  - 検証レポート
  - パフォーマンス測定結果
  - 品質保証レポート

## 🚀 テスト実行

```bash
# testsディレクトリから実行
cd tests
node test_verification.js
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
