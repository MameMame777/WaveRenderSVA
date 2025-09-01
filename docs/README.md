# Documentation Directory

## 📋 ディレクトリ構造変更のお知らせ

**テスト関連ドキュメントは `tests/` ディレクトリに移動されました。**

## 🔄 移行完了

### 以前の構造
```
docs/
├── Issue3_ComprehensiveTestDocumentation.md
├── Issue3_NodeBasedTiming_TestReport.md
└── Issue3_TestResults_JSONandAssertions.md
```

### 新しい構造
```
tests/
├── doc/           # 📚 テスト仕様書・設計ドキュメント
├── pat/           # 🧪 テストパターン (JSON) とアサーション
├── report/        # 📊 テスト実行結果・レポート
└── test_verification.js
```

## 📄 移動されたファイル

- **Issue #3 統合資料** → `tests/doc/Issue3_Integrated_Complete_Documentation.md`
- **包括的テスト仕様** → `tests/doc/COMPREHENSIVE_TEST_SPECIFICATION.md`
- **テストパターン** → `tests/pat/` 配下
- **実行結果** → `tests/report/` 配下

## 🎯 新構造の利点

1. **体系的管理**: テスト関連ファイルの一元化
2. **役割明確化**: doc/pat/report の明確な分離
3. **拡張性**: 新しいIssue追加時の構造拡張容易
4. **保守性**: 関連ファイルの発見・更新が簡単

## 🚀 今後の利用方法

```bash
# テスト仕様確認
cat tests/doc/Issue3_Integrated_Complete_Documentation.md

# テスト実行
cd tests && node test_verification.js

# 結果確認
cat tests/report/verification_results.json
```

## 📚 参考

詳細な使用方法は以下を参照してください：
- `tests/README.md` - テストディレクトリ構造の詳細
- `tests/doc/README.md` - ドキュメント管理指針
- `tests/pat/README.md` - テストパターン管理指針
- `tests/report/README.md` - レポート管理指針

---

**移行完了日**: 2025年9月1日  
**移行対象**: Issue #3 関連ドキュメント全て  
**新規ファイル追加場所**: `tests/doc/` ディレクトリ
