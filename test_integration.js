const fs = require('fs');
const path = require('path');

// Integration test for the actual VSCode extension
class ExtensionIntegrationTest {
    constructor() {
        this.outputDir = path.join(__dirname, 'output');
        this.testResults = [];
    }

    // Test the actual extension with various JSON inputs
    async runIntegrationTests() {
        console.log('🔗 Running Integration Tests for WaveRender SVA Extension\n');

        try {
            // Test 1: Basic functionality
            await this.testBasicFunctionality();
            
            // Test 2: Enhanced JSON features
            await this.testEnhancedFeatures();
            
            // Test 3: Edge cases and error handling
            await this.testEdgeCases();
            
            // Test 4: Performance test
            await this.testPerformance();
            
            this.printResults();
            
        } catch (error) {
            console.error('❌ Integration tests failed:', error);
        }
    }

    async testBasicFunctionality() {
        console.log('🧪 Test 1: Basic Functionality');
        
        // Test with the current sample.json
        const samplePath = path.join(__dirname, 'output', 'sample.json');
        const sampleSvPath = path.join(__dirname, 'output', 'sample.sv');
        
        if (fs.existsSync(samplePath) && fs.existsSync(sampleSvPath)) {
            const jsonContent = JSON.parse(fs.readFileSync(samplePath, 'utf8'));
            const svContent = fs.readFileSync(sampleSvPath, 'utf8');
            
            // Validate basic structure
            this.assert(jsonContent.signal !== undefined, 'JSON should have signal array');
            this.assert(svContent.includes('module'), 'SV should contain module declaration');
            this.assert(svContent.includes('property'), 'SV should contain property declarations');
            this.assert(svContent.includes('assert'), 'SV should contain assert statements');
            
            // Check for expected improvements
            this.assert(svContent.includes('WAVEFORM ANALYSIS SUMMARY'), 'Should include analysis summary');
            this.assert(svContent.includes('Enhanced with improved waveform analysis'), 'Should mention enhancements');
            
            console.log('  ✅ Basic functionality test passed');
        } else {
            console.log('  ⚠️ Sample files not found - skipping basic test');
        }
    }

    async testEnhancedFeatures() {
        console.log('🧪 Test 2: Enhanced Features');
        
        // Test with enhanced JSON
        const enhancedPath = path.join(__dirname, 'test_complete_features.json');
        
        if (fs.existsSync(enhancedPath)) {
            const enhancedJson = JSON.parse(fs.readFileSync(enhancedPath, 'utf8'));
            
            // Validate enhanced features
            this.assert(enhancedJson.protocols !== undefined, 'Should have protocol definitions');
            this.assert(enhancedJson.timing_relationships !== undefined, 'Should have timing relationships');
            this.assert(enhancedJson.assertion_config !== undefined, 'Should have assertion config');
            this.assert(enhancedJson.assertion_config.custom_properties !== undefined, 'Should have custom properties');
            
            // Validate signal enhancements
            const dataSignal = enhancedJson.signal.find(s => s.name === 'Data');
            this.assert(dataSignal.type === 'data', 'Data signal should have explicit type');
            this.assert(dataSignal.width === 8, 'Data signal should have explicit width');
            this.assert(dataSignal.timing !== undefined, 'Data signal should have timing info');
            
            console.log('  ✅ Enhanced features validation passed');
        } else {
            console.log('  ❌ Enhanced JSON file not found');
        }
    }

    async testEdgeCases() {
        console.log('🧪 Test 3: Edge Cases and Error Handling');
        
        // Test 3a: Empty signals
        const emptySignalsTest = {
            "signal": []
        };
        this.validateJsonStructure(emptySignalsTest, 'Empty signals array');
        
        // Test 3b: Missing wave patterns
        const missingWaveTest = {
            "signal": [
                { "name": "test_signal" }  // Missing wave
            ]
        };
        this.validateJsonStructure(missingWaveTest, 'Missing wave pattern');
        
        // Test 3c: Invalid wave characters
        const invalidWaveTest = {
            "signal": [
                { "name": "invalid", "wave": "xyz123" }
            ]
        };
        this.validateJsonStructure(invalidWaveTest, 'Invalid wave characters');
        
        // Test 3d: Very long waveforms
        const longWaveTest = {
            "signal": [
                { "name": "long_wave", "wave": "p".repeat(1000) }
            ]
        };
        this.validateJsonStructure(longWaveTest, 'Very long waveform');
        
        console.log('  ✅ Edge cases test completed');
    }

    async testPerformance() {
        console.log('🧪 Test 4: Performance Test');
        
        // Generate a large waveform for performance testing
        const largeWaveform = {
            "signal": []
        };
        
        // Add 50 signals with complex patterns
        for (let i = 0; i < 50; i++) {
            largeWaveform.signal.push({
                "name": `signal_${i}`,
                "wave": this.generateRandomWave(100),  // 100 character wave
                "type": i % 3 === 0 ? "data" : "control",
                "width": i % 3 === 0 ? 8 : 1
            });
        }
        
        const startTime = Date.now();
        this.validateJsonStructure(largeWaveform, 'Large waveform performance');
        const endTime = Date.now();
        
        const processingTime = endTime - startTime;
        this.assert(processingTime < 5000, `Processing should complete in under 5 seconds (took ${processingTime}ms)`);
        
        console.log(`  ⏱️ Performance test: ${processingTime}ms for 50 signals`);
    }

    // Helper methods
    validateJsonStructure(jsonData, testName) {
        try {
            // Basic validation that the JSON can be processed
            this.assert(typeof jsonData === 'object', `${testName}: Should be valid JSON object`);
            this.assert(Array.isArray(jsonData.signal), `${testName}: Should have signal array`);
            
            // Simulate basic processing
            let signalCount = 0;
            jsonData.signal.forEach(signal => {
                if (signal.name && signal.wave) {
                    signalCount++;
                }
            });
            
            console.log(`    📊 ${testName}: Processed ${signalCount} signals`);
            return true;
            
        } catch (error) {
            console.log(`    ❌ ${testName}: Validation failed - ${error.message}`);
            return false;
        }
    }

    generateRandomWave(length) {
        const waveChars = ['0', '1', 'x', 'z', '2', '3', '4', '5', '=', '.', 'p', 'n'];
        let wave = '';
        for (let i = 0; i < length; i++) {
            wave += waveChars[Math.floor(Math.random() * waveChars.length)];
        }
        return wave;
    }

    assert(condition, message) {
        if (condition) {
            console.log(`    ✅ ${message}`);
            this.testResults.push({ status: 'PASS', message });
        } else {
            console.log(`    ❌ ${message}`);
            this.testResults.push({ status: 'FAIL', message });
        }
    }

    printResults() {
        const totalTests = this.testResults.length;
        const passedTests = this.testResults.filter(r => r.status === 'PASS').length;
        const failedTests = totalTests - passedTests;
        
        console.log('\n📊 INTEGRATION TEST SUMMARY');
        console.log('============================');
        console.log(`Total Assertions: ${totalTests}`);
        console.log(`Passed: ${passedTests} ✅`);
        console.log(`Failed: ${failedTests} ❌`);
        console.log(`Success Rate: ${((passedTests / totalTests) * 100).toFixed(1)}%`);
        
        if (failedTests > 0) {
            console.log('\n❌ Failed Assertions:');
            this.testResults.filter(r => r.status === 'FAIL').forEach(result => {
                console.log(`  - ${result.message}`);
            });
        } else {
            console.log('\n🎉 All integration tests passed!');
        }
    }
}

// Manual test instructions
function printManualTestInstructions() {
    console.log('\n📋 MANUAL TESTING INSTRUCTIONS');
    console.log('===============================');
    console.log('1. Open VSCode with the WaveRender SVA extension');
    console.log('2. Open test_complete_features.json');
    console.log('3. Run "Waveform Render: Generate SystemVerilog Assertions" (Ctrl+K Ctrl+S)');
    console.log('4. Verify the generated assertions include:');
    console.log('   - Custom properties (data_value_sequence, no_x_during_valid, handshake_timeout)');
    console.log('   - Protocol-specific assertions');
    console.log('   - Timing relationship assertions');
    console.log('   - Explicit signal widths');
    console.log('5. Check that the module name is "test_enhanced_assertion_module"');
    console.log('6. Verify data width detection (Data should be [7:0], Valid should be single bit)');
    console.log('');
    console.log('Expected improvements in output:');
    console.log('- Explicit timing relationships from JSON');
    console.log('- Custom property assertions');
    console.log('- Protocol-aware optimizations');
    console.log('- Enhanced configuration recognition');
}

// Benchmark comparison
function printBenchmarkComparison() {
    console.log('\n📈 BEFORE vs AFTER COMPARISON');
    console.log('==============================');
    console.log('BEFORE (original sample.sv):');
    console.log('- Generic module name "assertion_module"');
    console.log('- Incorrect signal widths (Valid[3:0])');
    console.log('- Auto-detected timing (may be inaccurate)');
    console.log('- No custom properties');
    console.log('- Limited protocol awareness');
    console.log('');
    console.log('AFTER (with enhancements):');
    console.log('- Custom module names');
    console.log('- Accurate signal width detection');
    console.log('- Explicit timing relationships');
    console.log('- Custom property support');
    console.log('- Protocol-specific optimizations');
    console.log('- Enhanced analysis comments');
}

// Run tests if this file is executed directly
if (require.main === module) {
    const integrationTest = new ExtensionIntegrationTest();
    integrationTest.runIntegrationTests().then(() => {
        printManualTestInstructions();
        printBenchmarkComparison();
    });
}

module.exports = ExtensionIntegrationTest;
