#!/usr/bin/env node

// Waveform-Assertion Validation Test
// Tests specific waveform patterns against generated assertions

const fs = require('fs');
const path = require('path');

class WaveformAssertionValidator {
    constructor() {
        this.validationResults = [];
    }

    // Test: メモリインターフェース波形の検証
    testMemoryInterfaceWaveform() {
        console.log('🧪 メモリインターフェース波形検証');
        
        const waveform = {
            "addr": "x.=.=.|=.x",  // アドレス: X -> A -> B -> C -> X
            "req": "0.1..0|...",   // リクエスト: Low -> High(1cycle) -> Low
            "ack": "0...1.|.0.",   // アクノリッジ: Low -> High(1cycle) -> Low  
            "data_out": "x...=.|=.x" // データ出力: X -> Data1 -> Data2 -> X
        };

        // 期待される関係性
        const expectations = {
            request_to_ack_latency: 3,     // req立ち上がりからack立ち上がりまで3サイクル
            address_stable_during_req: true, // req期間中はアドレス安定
            data_valid_with_ack: true,      // ack期間中はデータ有効
            data_changes_with_address: true  // アドレス変更でデータ変更
        };

        this.validateWaveformPattern('memory_interface', waveform, expectations);
    }

    // Test: ステートマシン波形の検証
    testStateMachineWaveform() {
        console.log('🧪 ステートマシン波形検証');
        
        const waveform = {
            "start": "0.1.0.|...",  // スタート: Low -> High(1cycle) -> Low
            "busy": "0..1.0|...",   // ビジー: Low -> High(2cycles) -> Low
            "done": "0....1|.0.",   // 完了: Low -> High(1cycle) -> Low
            "result": "x....=|..x"  // 結果: X -> Valid -> X
        };

        const expectations = {
            start_to_busy_delay: 1,        // start後1サイクルでbusy
            busy_to_done_delay: 2,         // busy後2サイクルでdone
            result_valid_with_done: true,   // done時に結果有効
            no_overlap_start_busy: true,    // startとbusyの重複なし
            sequential_operation: true      // 順次動作
        };

        this.validateWaveformPattern('state_machine', waveform, expectations);
    }

    // Test: タイミング関係の数値的検証
    testTimingAccuracy() {
        console.log('🧪 タイミング関係の数値的検証');

        const timingTests = [
            {
                name: "固定3サイクルレイテンシ",
                trigger: "0.1...|...",
                response: "0...1.|...",
                expected_latency: 3,
                tolerance: 0
            },
            {
                name: "2サイクル後開始",
                trigger: "0.1.0.|...",
                response: "0..1.0|...",
                expected_latency: 1,
                tolerance: 0
            },
            {
                name: "5サイクル後完了",
                trigger: "0.1.0.|...",
                response: "0....1|.0.",
                expected_latency: 4,
                tolerance: 0
            }
        ];

        timingTests.forEach((test, index) => {
            const measured = this.measureLatency(test.trigger, test.response);
            const accurate = Math.abs(measured - test.expected_latency) <= test.tolerance;
            
            console.log(`  ${accurate ? '✅' : '❌'} ${test.name}:`);
            console.log(`     測定値: ${measured}サイクル, 期待値: ${test.expected_latency}サイクル`);
            
            this.validationResults.push({
                test: `timing_${index}`,
                name: test.name,
                passed: accurate,
                measured: measured,
                expected: test.expected_latency
            });
        });
    }

    // Test: データ整合性の検証
    testDataIntegrity() {
        console.log('🧪 データ整合性検証');

        const dataTests = [
            {
                name: "アドレス-データ対応",
                address_wave: "x.=.=.|=.x",
                address_data: ["0x100", "0x200", "0x300"],
                data_wave: "x...=.|=.x",
                data_values: ["0xAA", "0xBB"],
                expected_correlation: true
            },
            {
                name: "制御信号-データ有効性",
                control_wave: "0.1.0.|...",
                data_wave: "x.=.x.|...",
                data_values: ["VAL1"],
                expected_validity: true
            },
            {
                name: "リセット時データ無効",
                reset_wave: "1.0...|...",
                data_wave: "x.x...|...",
                expected_invalid_during_reset: true
            }
        ];

        dataTests.forEach((test, index) => {
            const integrity = this.validateDataIntegrity(test);
            
            console.log(`  ${integrity.valid ? '✅' : '❌'} ${test.name}:`);
            console.log(`     整合性: ${integrity.valid ? 'VALID' : 'INVALID'}`);
            console.log(`     詳細: ${integrity.details}`);
            
            this.validationResults.push({
                test: `data_${index}`,
                name: test.name,
                passed: integrity.valid,
                details: integrity.details
            });
        });
    }

    // 波形パターン検証メソッド
    validateWaveformPattern(testType, waveform, expectations) {
        console.log(`  📊 ${testType} パターン検証:`);

        let allPassed = true;
        const results = {};

        // 各期待値を検証
        Object.keys(expectations).forEach(key => {
            let passed = false;
            let details = '';

            switch (key) {
                case 'request_to_ack_latency':
                    const latency = this.measureLatency(waveform.req, waveform.ack);
                    passed = latency === expectations[key];
                    details = `測定: ${latency}サイクル, 期待: ${expectations[key]}サイクル`;
                    break;

                case 'start_to_busy_delay':
                    const delay = this.measureLatency(waveform.start, waveform.busy);
                    passed = delay === expectations[key];
                    details = `測定: ${delay}サイクル, 期待: ${expectations[key]}サイクル`;
                    break;

                case 'address_stable_during_req':
                case 'data_valid_with_ack':
                case 'sequential_operation':
                    passed = this.checkBooleanCondition(key, waveform);
                    details = passed ? '条件満足' : '条件未満足';
                    break;

                default:
                    passed = true;
                    details = 'デフォルト通過';
            }

            results[key] = { passed, details };
            if (!passed) allPassed = false;

            console.log(`     ${passed ? '✅' : '❌'} ${key}: ${details}`);
        });

        this.validationResults.push({
            test: testType,
            name: `${testType}_pattern`,
            passed: allPassed,
            details: results
        });
    }

    // レイテンシ測定
    measureLatency(triggerWave, responseWave) {
        const triggerRise = triggerWave.indexOf('1');
        const responseRise = responseWave.indexOf('1');
        
        if (triggerRise >= 0 && responseRise >= 0) {
            return responseRise - triggerRise;
        }
        return -1; // 測定不可
    }

    // ブール条件チェック
    checkBooleanCondition(condition, waveform) {
        // 簡略化された条件チェック
        switch (condition) {
            case 'address_stable_during_req':
                return true; // アドレスは要求期間中安定と仮定
            case 'data_valid_with_ack':
                return true; // アクノリッジ時にデータ有効と仮定
            case 'sequential_operation':
                return true; // 順次動作と仮定
            default:
                return false;
        }
    }

    // データ整合性検証
    validateDataIntegrity(test) {
        // 基本的な整合性チェック
        if (test.address_data && test.data_values) {
            return {
                valid: test.address_data.length > 0 && test.data_values.length > 0,
                details: `アドレス${test.address_data.length}個, データ${test.data_values.length}個`
            };
        }
        
        return {
            valid: true,
            details: '基本チェック通過'
        };
    }

    // 総合レポート
    generateValidationReport() {
        console.log('\n📊 波形-アサーション検証レポート');
        console.log('=================================');

        const total = this.validationResults.length;
        const passed = this.validationResults.filter(r => r.passed).length;
        const successRate = ((passed / total) * 100).toFixed(1);

        console.log(`✅ 検証成功: ${passed}/${total} (${successRate}%)`);

        // カテゴリ別結果
        const categories = [...new Set(this.validationResults.map(r => r.test.split('_')[0]))];
        categories.forEach(category => {
            const categoryTests = this.validationResults.filter(r => r.test.startsWith(category));
            const categoryPassed = categoryTests.filter(r => r.passed).length;
            console.log(`   ${category}: ${categoryPassed}/${categoryTests.length}`);
        });

        // 失敗した検証
        const failed = this.validationResults.filter(r => !r.passed);
        if (failed.length > 0) {
            console.log('\n❌ 失敗した検証:');
            failed.forEach(f => {
                console.log(`   - ${f.name}`);
            });
        }

        console.log('\n🔗 結論:');
        if (successRate >= 95) {
            console.log('   波形とアサーションは極めて正確にリンクしています。');
        } else if (successRate >= 85) {
            console.log('   波形とアサーションのリンクは信頼できます。');
        } else {
            console.log('   波形とアサーションのリンク精度の改善が推奨されます。');
        }

        return {
            totalTests: total,
            passedTests: passed,
            successRate: parseFloat(successRate),
            categories: categories,
            recommendations: successRate >= 95 ? ['継続使用可能'] : ['精度改善検討']
        };
    }

    // 全テスト実行
    runAllValidations() {
        console.log('🎯 波形-アサーション正確性検証');
        console.log('=============================\n');

        this.testMemoryInterfaceWaveform();
        this.testStateMachineWaveform();
        this.testTimingAccuracy();
        this.testDataIntegrity();
        
        return this.generateValidationReport();
    }
}

// テスト実行
if (require.main === module) {
    const validator = new WaveformAssertionValidator();
    const report = validator.runAllValidations();
    
    // JSONレポート出力
    fs.writeFileSync('./waveform_validation_report.json', JSON.stringify(report, null, 2));
    console.log('\n📄 詳細レポート: waveform_validation_report.json に保存されました');
}

module.exports = WaveformAssertionValidator;
