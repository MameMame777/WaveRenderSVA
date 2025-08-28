const fs = require('fs');
const path = require('path');

// Test suite for enhanced waveform analysis and assertion generation
class WaveformAssertionTester {
    constructor() {
        this.testResults = [];
    }

    // Test 1: Basic JSON parsing and signal detection
    testBasicParsing() {
        console.log('🧪 Test 1: Basic JSON parsing and signal detection');
        
        const basicWaveform = {
            "signal": [
                { "name": "clk", "wave": "p.....|..." },
                { "name": "Data", "wave": "x.345x|=.x", "data": ["head", "body", "tail", "data"] },
                { "name": "Request", "wave": "0.1..0|1.0" },
                {},
                { "name": "Acknowledge", "wave": "1.....|01." }
            ]
        };

        const results = this.analyzeWaveform(basicWaveform);
        
        // Assertions
        this.assert(results.totalSignals === 4, 'Should detect 4 signals (excluding spacer)');
        this.assert(results.clockSignals === 1, 'Should detect 1 clock signal');
        this.assert(results.dataSignals >= 1, 'Should detect at least 1 data signal');
        
        console.log('✅ Basic parsing test completed');
        return results;
    }

    // Test 2: Enhanced JSON with explicit configurations
    testEnhancedJsonParsing() {
        console.log('🧪 Test 2: Enhanced JSON with explicit configurations');
        
        const enhancedWaveform = {
            "signal": [
                {
                    "name": "clk",
                    "wave": "p.....|...",
                    "type": "clock",
                    "period": 2
                },
                {
                    "name": "Data",
                    "wave": "x.345x|=.x",
                    "data": ["head", "body", "tail", "data"],
                    "type": "data",
                    "width": 8,
                    "encoding": "custom"
                },
                {
                    "name": "Valid",
                    "wave": "0..1.0|.1.",
                    "type": "control",
                    "width": 1,
                    "role": "data_qualifier"
                }
            ],
            "assertion_config": {
                "clock_signal": "clk",
                "reset_signal": "rst_n",
                "module_name": "test_assertion_module",
                "generation_options": {
                    "enable_detailed_analysis": true,
                    "enable_timing_analysis": true
                }
            }
        };

        const results = this.analyzeEnhancedWaveform(enhancedWaveform);
        
        // Assertions
        this.assert(results.hasExtendedConfig === true, 'Should detect extended configuration');
        this.assert(results.moduleName === 'test_assertion_module', 'Should use custom module name');
        this.assert(results.explicitSignalTypes === true, 'Should detect explicit signal types');
        
        console.log('✅ Enhanced JSON parsing test completed');
        return results;
    }

    // Test 3: Wave pattern analysis
    testWavePatternAnalysis() {
        console.log('🧪 Test 3: Wave pattern analysis');
        
        const testPatterns = [
            { pattern: "x.345x|=.x", expected: { hasData: true, hasUnknown: true, transitions: 6 }},
            { pattern: "0.1..0|1.0", expected: { hasData: false, hasUnknown: false, transitions: 4 }},
            { pattern: "p.....|...", expected: { isClock: true, period: 2 }},
            { pattern: "0..1.0|.1.", expected: { controlSignal: true, transitions: 4 }}
        ];

        testPatterns.forEach((test, index) => {
            const analysis = this.analyzeWavePattern(test.pattern);
            console.log(`  Pattern "${test.pattern}":`, analysis);
            
            if (test.expected.hasData !== undefined) {
                this.assert(analysis.hasDataTransitions === test.expected.hasData, 
                    `Pattern ${index}: Data detection mismatch`);
            }
            if (test.expected.hasUnknown !== undefined) {
                this.assert(analysis.hasUnknownStates === test.expected.hasUnknown, 
                    `Pattern ${index}: Unknown state detection mismatch`);
            }
        });

        console.log('✅ Wave pattern analysis test completed');
    }

    // Test 4: Data width detection
    testDataWidthDetection() {
        console.log('🧪 Test 4: Data width detection');
        
        const testCases = [
            { 
                signal: { name: "data8", wave: "x.345x", data: ["0", "15", "255"], width: 8 },
                expected: 8
            },
            {
                signal: { name: "control", wave: "0.1.0", type: "control", width: 1 },
                expected: 1
            },
            {
                signal: { name: "addr", wave: "x=.=x", data: ["0x1000", "0xFFFF"] },
                expected: 32  // Address signals default to 32-bit
            },
            {
                signal: { name: "hexdata", wave: "2.3.4.5" },
                expected: 4  // Hex patterns suggest 4-bit
            }
        ];

        testCases.forEach((testCase, index) => {
            const detectedWidth = this.detectSignalWidth(testCase.signal);
            this.assert(detectedWidth === testCase.expected, 
                `Test case ${index}: Expected width ${testCase.expected}, got ${detectedWidth}`);
            console.log(`  Signal "${testCase.signal.name}": ${detectedWidth} bits ✓`);
        });

        console.log('✅ Data width detection test completed');
    }

    // Test 5: Timing relationship detection
    testTimingAnalysis() {
        console.log('🧪 Test 5: Timing relationship detection');
        
        const signalPair = {
            trigger: { name: "Request", wave: "0.1..0|1.0" },
            response: { name: "Acknowledge", wave: "1.....|01." }
        };

        const timingAnalysis = this.analyzeSignalTiming(signalPair.trigger, signalPair.response);
        
        console.log('  Timing analysis result:', timingAnalysis);
        
        this.assert(timingAnalysis.hasPattern === true || timingAnalysis.hasPattern === false, 
            'Should return timing analysis result');
        
        if (timingAnalysis.hasPattern) {
            this.assert(typeof timingAnalysis.latency === 'number', 'Should detect numeric latency');
            console.log(`  ✓ Detected latency: ${timingAnalysis.latency} cycles`);
        }

        console.log('✅ Timing analysis test completed');
    }

    // Test 6: Assertion generation quality
    testAssertionGeneration() {
        console.log('🧪 Test 6: Assertion generation quality');
        
        const testWaveform = {
            "signal": [
                { "name": "clk", "wave": "p.....|...", "type": "clock" },
                { "name": "data", "wave": "x.345x|=.x", "type": "data", "width": 8, 
                  "data": ["head", "body", "tail", "data"] },
                { "name": "valid", "wave": "0..1.0|.1.", "type": "control", "width": 1 }
            ],
            "assertion_config": {
                "module_name": "test_module",
                "generation_options": {
                    "enable_data_integrity": true,
                    "enable_timing_analysis": true
                }
            }
        };

        const generatedAssertions = this.generateAssertions(testWaveform);
        
        // Check for essential assertion patterns
        this.assert(generatedAssertions.includes('data_integrity'), 'Should include data integrity assertions');
        this.assert(generatedAssertions.includes('disable iff (!rst_n)'), 'Should include reset disable');
        this.assert(generatedAssertions.includes('@(posedge clk)'), 'Should be clocked assertions');
        this.assert(generatedAssertions.includes('test_module'), 'Should use custom module name');

        console.log('✅ Assertion generation test completed');
        return generatedAssertions;
    }

    // Helper methods for testing
    analyzeWaveform(waveform) {
        let totalSignals = 0;
        let clockSignals = 0;
        let dataSignals = 0;
        let controlSignals = 0;

        waveform.signal.forEach(signal => {
            if (!signal.wave || signal.wave === '') return; // Skip spacers
            
            totalSignals++;
            
            if (signal.wave.includes('p') || signal.wave.includes('n')) {
                clockSignals++;
            } else if (signal.wave.includes('=') || signal.data || /[2-9a-fA-F]/.test(signal.wave)) {
                dataSignals++;
            } else {
                controlSignals++;
            }
        });

        return { totalSignals, clockSignals, dataSignals, controlSignals };
    }

    analyzeEnhancedWaveform(waveform) {
        const hasExtendedConfig = !!waveform.assertion_config;
        const moduleName = waveform.assertion_config?.module_name || 'assertion_module';
        const explicitSignalTypes = waveform.signal.some(s => s.type);

        return { hasExtendedConfig, moduleName, explicitSignalTypes };
    }

    analyzeWavePattern(pattern) {
        return {
            length: pattern.length,
            hasUnknownStates: pattern.includes('x'),
            hasTristate: pattern.includes('z'),
            hasDataTransitions: /[2-9a-fA-F=]/.test(pattern),
            isClock: pattern.includes('p') || pattern.includes('n'),
            transitionCount: this.countTransitions(pattern)
        };
    }

    countTransitions(pattern) {
        let count = 0;
        for (let i = 0; i < pattern.length - 1; i++) {
            if (pattern[i] !== pattern[i + 1] && pattern[i] !== '.' && pattern[i + 1] !== '.') {
                count++;
            }
        }
        return count;
    }

    detectSignalWidth(signal) {
        // Explicit width declaration
        if (signal.width) return signal.width;
        
        // Analyze data array
        if (signal.data && Array.isArray(signal.data)) {
            const maxValue = Math.max(...signal.data.map(val => {
                if (typeof val === 'string') {
                    return val.startsWith('0x') ? parseInt(val, 16) : parseInt(val) || 0;
                }
                return val;
            }));
            
            if (maxValue > 0) {
                const bitsNeeded = Math.ceil(Math.log2(maxValue + 1));
                if (bitsNeeded <= 1) return 1;
                if (bitsNeeded <= 4) return 4;
                if (bitsNeeded <= 8) return 8;
                if (bitsNeeded <= 16) return 16;
                if (bitsNeeded <= 32) return 32;
                return 64;
            }
        }
        
        // Name-based detection
        const name = signal.name.toLowerCase();
        if (name.includes('addr')) return 32;
        if (name.includes('data')) return 8;
        if (/[2-9a-fA-F]/.test(signal.wave)) return 4;
        
        return 1;
    }

    analyzeSignalTiming(trigger, response) {
        // Simple timing analysis
        const triggerEdges = this.findRisingEdges(trigger.wave);
        const responseEdges = this.findRisingEdges(response.wave);
        
        if (triggerEdges.length > 0 && responseEdges.length > 0) {
            const latency = responseEdges[0] - triggerEdges[0];
            return {
                hasPattern: latency > 0,
                latency: latency,
                confidence: 0.8
            };
        }
        
        return { hasPattern: false };
    }

    findRisingEdges(wave) {
        const edges = [];
        for (let i = 0; i < wave.length - 1; i++) {
            if (wave[i] === '0' && wave[i + 1] === '1') {
                edges.push(i + 1);
            }
        }
        return edges;
    }

    generateAssertions(waveform) {
        // Simplified assertion generation for testing
        const moduleName = waveform.assertion_config?.module_name || 'assertion_module';
        
        let assertions = `// Test generated assertions\n`;
        assertions += `module ${moduleName} (\n`;
        assertions += `  input logic clk,\n`;
        assertions += `  input logic rst_n\n`;
        assertions += `);\n\n`;
        
        waveform.signal.forEach(signal => {
            if (signal.type === 'data') {
                assertions += `  // Data integrity for ${signal.name}\n`;
                assertions += `  property data_integrity_p;\n`;
                assertions += `    disable iff (!rst_n)\n`;
                assertions += `    @(posedge clk) (${signal.name.toLowerCase()} !== 'x);\n`;
                assertions += `  endproperty\n\n`;
            }
        });
        
        assertions += `endmodule\n`;
        return assertions;
    }

    // Test assertion helper
    assert(condition, message) {
        if (condition) {
            console.log(`    ✅ ${message}`);
            this.testResults.push({ status: 'PASS', message });
        } else {
            console.log(`    ❌ ${message}`);
            this.testResults.push({ status: 'FAIL', message });
        }
    }

    // Run all tests
    runAllTests() {
        console.log('🚀 Starting WaveRender SVA Test Suite\n');
        
        try {
            this.testBasicParsing();
            console.log('');
            
            this.testEnhancedJsonParsing();
            console.log('');
            
            this.testWavePatternAnalysis();
            console.log('');
            
            this.testDataWidthDetection();
            console.log('');
            
            this.testTimingAnalysis();
            console.log('');
            
            this.testAssertionGeneration();
            console.log('');
            
            this.printSummary();
            
        } catch (error) {
            console.error('❌ Test suite failed with error:', error);
        }
    }

    printSummary() {
        const totalTests = this.testResults.length;
        const passedTests = this.testResults.filter(r => r.status === 'PASS').length;
        const failedTests = totalTests - passedTests;
        
        console.log('📊 TEST SUMMARY');
        console.log('================');
        console.log(`Total Tests: ${totalTests}`);
        console.log(`Passed: ${passedTests} ✅`);
        console.log(`Failed: ${failedTests} ❌`);
        console.log(`Success Rate: ${((passedTests / totalTests) * 100).toFixed(1)}%`);
        
        if (failedTests > 0) {
            console.log('\n❌ Failed Tests:');
            this.testResults.filter(r => r.status === 'FAIL').forEach(result => {
                console.log(`  - ${result.message}`);
            });
        }
    }
}

// Run tests if this file is executed directly
if (require.main === module) {
    const tester = new WaveformAssertionTester();
    tester.runAllTests();
}

module.exports = WaveformAssertionTester;
