#!/usr/bin/env node

// Advice2.md Requirements Analysis
// Check current implementation against the SVA examples in advice2.md

class Advice2RequirementsAnalyzer {
    constructor() {
        this.requirements = [
            {
                id: 1,
                name: "ハンドシェイク信号の検証",
                description: "req が立ったら、3 サイクル以内に ack が 1 になる",
                pattern: "req |-> ##[1:3] ack",
                currentSupport: "partial",
                needsEnhancement: true
            },
            {
                id: 2,
                name: "リセット動作の確認", 
                description: "reset がアサートされたら、次サイクルで ready=0、その後 busy=0",
                pattern: "reset |-> ##1 (!ready && !busy)",
                currentSupport: "basic",
                needsEnhancement: true
            },
            {
                id: 3,
                name: "FIFO のオーバーフロー防止",
                description: "fifo_full が 1 のときに write_enable が 1 になってはいけない",
                pattern: "not (fifo_full && write_enable)",
                currentSupport: "none",
                needsEnhancement: true
            },
            {
                id: 4,
                name: "プロトコル・シーケンスの順序確認",
                description: "start → data_valid → done の順番で信号が出る",
                pattern: "start |-> ##[1:5] data_valid ##[1:5] done",
                currentSupport: "partial",
                needsEnhancement: true
            },
            {
                id: 5,
                name: "クロック同期の検証",
                description: "clk_enable が 1 なら clk_out もトグルする", 
                pattern: "clk_enable |-> $changed(clk_out)",
                currentSupport: "none",
                needsEnhancement: true
            },
            {
                id: 6,
                name: "レイテンシ制約",
                description: "命令 issue から正確に 4 サイクル後に commit が出る",
                pattern: "issue |-> ##4 commit",
                currentSupport: "good",
                needsEnhancement: false
            }
        ];
        
        this.analysisResults = [];
    }

    // 現在の実装と要件の比較分析
    analyzeCurrentImplementation() {
        console.log('🎯 Advice2.md要件分析');
        console.log('=====================\n');

        this.requirements.forEach(req => {
            console.log(`📋 要件${req.id}: ${req.name}`);
            console.log(`   説明: ${req.description}`);
            console.log(`   パターン: ${req.pattern}`);
            console.log(`   現在のサポート: ${this.getSupportStatusText(req.currentSupport)}`);
            console.log(`   強化必要: ${req.needsEnhancement ? 'Yes' : 'No'}`);
            
            this.analysisResults.push({
                requirement: req,
                status: req.currentSupport,
                needsWork: req.needsEnhancement
            });
            
            console.log('');
        });
    }

    // サポート状況のテキスト変換
    getSupportStatusText(status) {
        const statusMap = {
            'good': '✅ 十分サポート',
            'partial': '⚠️ 部分的サポート', 
            'basic': '🔶 基本的サポート',
            'none': '❌ 未サポート'
        };
        return statusMap[status] || '❓ 不明';
    }

    // 不足している機能の特定
    identifyMissingFeatures() {
        console.log('🔍 不足機能の特定');
        console.log('=================\n');

        const missingFeatures = [
            {
                feature: "可変範囲レイテンシ（##[M:N]）",
                description: "1〜3サイクルのような範囲指定",
                priority: "高",
                examples: ["##[1:3] ack", "##[1:5] data_valid"]
            },
            {
                feature: "禁止条件アサーション",
                description: "not (condition) パターン",
                priority: "高", 
                examples: ["not (fifo_full && write_enable)"]
            },
            {
                feature: "複合シーケンス",
                description: "A → B → C のようなチェーンアサーション",
                priority: "中",
                examples: ["start |-> ##[1:5] data_valid ##[1:5] done"]
            },
            {
                feature: "信号変化検出",
                description: "$changed(), $rose(), $fell() の活用",
                priority: "中",
                examples: ["clk_enable |-> $changed(clk_out)"]
            },
            {
                feature: "条件付きリセット動作",
                description: "リセット時の複数信号同時制御",
                priority: "低",
                examples: ["reset |-> ##1 (!ready && !busy)"]
            }
        ];

        missingFeatures.forEach((feature, index) => {
            console.log(`🔧 機能${index + 1}: ${feature.feature}`);
            console.log(`   説明: ${feature.description}`);
            console.log(`   優先度: ${feature.priority}`);
            console.log(`   例: ${feature.examples.join(', ')}`);
            console.log('');
        });

        return missingFeatures;
    }

    // 改善提案の生成
    generateEnhancementProposals() {
        console.log('💡 改善提案');
        console.log('===========\n');

        const proposals = [
            {
                title: "可変レイテンシアサーション生成",
                description: "##[min:max] 形式での範囲指定レイテンシ",
                implementation: "JSON設定で min/max latency 指定",
                benefit: "より柔軟なタイミング制約"
            },
            {
                title: "禁止条件アサーション",
                description: "同時に1になってはいけない信号の検出",
                implementation: "conflict_signals 設定追加",
                benefit: "バス競合、FIFO溢れ等の防止"
            },
            {
                title: "シーケンシャルプロトコル",
                description: "A→B→C の順序制約アサーション",
                implementation: "sequence_chain 設定追加",
                benefit: "プロトコル順序の自動検証"
            },
            {
                title: "信号変化監視",
                description: "$changed, $rose, $fell の自動生成",
                implementation: "edge_detection 設定追加",
                benefit: "クロック同期、状態変化の検証"
            }
        ];

        proposals.forEach((proposal, index) => {
            console.log(`💡 提案${index + 1}: ${proposal.title}`);
            console.log(`   内容: ${proposal.description}`);
            console.log(`   実装: ${proposal.implementation}`);
            console.log(`   効果: ${proposal.benefit}`);
            console.log('');
        });

        return proposals;
    }

    // 総合評価とレポート
    generateComprehensiveReport() {
        console.log('📊 総合評価レポート');
        console.log('==================\n');

        const totalRequirements = this.requirements.length;
        const wellSupported = this.requirements.filter(r => r.currentSupport === 'good').length;
        const partiallySupported = this.requirements.filter(r => r.currentSupport === 'partial').length;
        const needsWork = this.requirements.filter(r => r.needsEnhancement).length;

        console.log(`📈 要件カバレッジ:`);
        console.log(`   総要件数: ${totalRequirements}`);
        console.log(`   十分サポート: ${wellSupported} (${((wellSupported/totalRequirements)*100).toFixed(1)}%)`);
        console.log(`   部分サポート: ${partiallySupported} (${((partiallySupported/totalRequirements)*100).toFixed(1)}%)`);
        console.log(`   改善必要: ${needsWork} (${((needsWork/totalRequirements)*100).toFixed(1)}%)`);

        const overallScore = ((wellSupported * 100 + partiallySupported * 60) / totalRequirements).toFixed(1);
        console.log(`\n🎯 総合スコア: ${overallScore}%`);

        console.log('\n🎯 推奨アクション:');
        if (overallScore >= 80) {
            console.log('   ✅ 現在の実装は advice2.md の要件をよくカバーしています');
            console.log('   📈 残りの機能を追加すれば完璧になります');
        } else if (overallScore >= 60) {
            console.log('   ⚠️  基本的な要件はカバーしていますが、重要な機能が不足しています');
            console.log('   🔧 優先度の高い機能から実装することを推奨します');
        } else {
            console.log('   ❌ advice2.md の要件との差が大きいです');
            console.log('   🚨 包括的な機能追加が必要です');
        }

        return {
            totalRequirements,
            wellSupported,
            partiallySupported,
            needsWork,
            overallScore: parseFloat(overallScore)
        };
    }

    // 全分析実行
    runCompleteAnalysis() {
        this.analyzeCurrentImplementation();
        const missingFeatures = this.identifyMissingFeatures();
        const proposals = this.generateEnhancementProposals();
        const report = this.generateComprehensiveReport();

        return {
            requirements: this.requirements,
            missingFeatures,
            proposals,
            overallAssessment: report
        };
    }
}

// 分析実行
if (require.main === module) {
    const analyzer = new Advice2RequirementsAnalyzer();
    const analysis = analyzer.runCompleteAnalysis();
    
    // JSON出力
    const fs = require('fs');
    fs.writeFileSync('./advice2_requirements_analysis.json', JSON.stringify(analysis, null, 2));
    console.log('\n📄 詳細分析結果: advice2_requirements_analysis.json に保存されました');
}

module.exports = Advice2RequirementsAnalyzer;
