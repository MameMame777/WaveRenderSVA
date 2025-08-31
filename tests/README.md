# WaveRenderSVA Tests

## 📋 テスト構成

このディレクトリには、WaveRenderSVA拡張機能の最終テストスイートが含まれています。

### ファイル構成

- **`comprehensive_test.json`** - 包括的テストデータ
  - 15の信号定義
  - 34のエッジ関係
  - 全WaveDrom文法要素をカバー
  - Issue #2実装のテストケースを含む

- **`test_verification.js`** - 最終検証スクリプト
  - SVA生成の完全性チェック
  - オペレータサポート検証
  - エラー・警告の分析
  - Issue #2機能の動作確認

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
