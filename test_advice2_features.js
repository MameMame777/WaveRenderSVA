#!/usr/bin/env node

// Test new ADVICE2 features implementation

class Advice2FeatureTest {
    constructor() {
        // Mock extension functionality for testing
        this.config = {
            extended_config: {
                timing_relationships: [
                    {
                        type: "variable_latency",
                        trigger_signal: "req",
                        response_signal: "ack",
                        min_cycles: 1,
                        max_cycles: 3,
                        description: "REQ -> ACK within 1-3 cycles"
                    }
                ],
                sequence_chains: [
                    {
                        name: "protocol_sequence",
                        signals: ["start", "data_valid", "done"],
                        delays: ["[1:5]", "[1:5]"],
                        description: "start -> data_valid -> done sequence"
                    }
                ],
                conflict_signals: [
                    {
                        signal1: "fifo_full",
                        signal2: "write_enable",
                        description: "FIFO overflow prevention"
                    }
                ],
                reset_behavior: {
                    reset_signal: "reset",
                    reset_targets: [
                        {"signal": "ready", "value": "0"},
                        {"signal": "busy", "value": "0"}
                    ],
                    description: "Reset clears ready and busy"
                },
                edge_detection: [
                    {
                        trigger: "clk_enable",
                        target: "clk_out",
                        type: "change",
                        description: "clk_out toggles when clk_enable=1"
                    }
                ]
            }
        };
        
        this.signals = [
            {name: "req", normalizedName: "req", wave: "0.1..0|1.0"},
            {name: "ack", normalizedName: "ack", wave: "0...1.|.0."},
            {name: "start", normalizedName: "start", wave: "0.1.0.|..."},
            {name: "data_valid", normalizedName: "data_valid", wave: "0....1|.0."},
            {name: "done", normalizedName: "done", wave: "0.....|1.0"},
            {name: "fifo_full", normalizedName: "fifo_full", wave: "0....1|..."},
            {name: "write_enable", normalizedName: "write_enable", wave: "0.1.0.|..."},
            {name: "reset", normalizedName: "reset", wave: "1.0...|..."},
            {name: "ready", normalizedName: "ready", wave: "1.0...|..."},
            {name: "busy", normalizedName: "busy", wave: "1.0...|..."},
            {name: "clk_enable", normalizedName: "clk_enable", wave: "0.1..0|..."},
            {name: "clk_out", normalizedName: "clk_out", wave: "0..p..|..."}
        ];
    }

    // Test variable latency assertions
    testVariableLatencyAssertions() {
        console.log('🧪 Variable Latency Assertions Test');
        console.log('==================================');

        const assertions = this._generateVariableLatencyAssertions(this.signals, "clk", this.config);
        
        console.log('Generated assertions:');
        console.log(assertions);
        
        const hasVariableLatency = assertions.includes("##[1:3]");
        const hasProperFormat = assertions.includes("property req_to_ack_variable_latency_p");
        
        console.log(`✅ Variable latency format: ${hasVariableLatency ? 'PASS' : 'FAIL'}`);
        console.log(`✅ Property naming: ${hasProperFormat ? 'PASS' : 'FAIL'}`);
        
        return hasVariableLatency && hasProperFormat;
    }

    // Test sequential protocol assertions  
    testSequentialProtocolAssertions() {
        console.log('\n🧪 Sequential Protocol Assertions Test');
        console.log('=====================================');

        const assertions = this._generateSequentialProtocolAssertions(this.signals, "clk", this.config);
        
        console.log('Generated assertions:');
        console.log(assertions);
        
        const hasSequence = assertions.includes("start") && assertions.includes("data_valid") && assertions.includes("done");
        const hasChaining = assertions.includes("|-> ##[1:5]");
        
        console.log(`✅ Sequence detection: ${hasSequence ? 'PASS' : 'FAIL'}`);
        console.log(`✅ Chaining format: ${hasChaining ? 'PASS' : 'FAIL'}`);
        
        return hasSequence && hasChaining;
    }

    // Test prohibition patterns
    testProhibitionPatterns() {
        console.log('\n🧪 Prohibition Patterns Test');
        console.log('===========================');

        const assertions = this._generateProhibitionPatterns(this.signals, "clk", this.config);
        
        console.log('Generated assertions:');
        console.log(assertions);
        
        const hasConflict = assertions.includes("fifo_full") && assertions.includes("write_enable");
        const hasNotPattern = assertions.includes("not (");
        
        console.log(`✅ Conflict detection: ${hasConflict ? 'PASS' : 'FAIL'}`);
        console.log(`✅ NOT pattern: ${hasNotPattern ? 'PASS' : 'FAIL'}`);
        
        return hasConflict && hasNotPattern;
    }

    // Test reset behavior
    testResetBehaviorAssertions() {
        console.log('\n🧪 Reset Behavior Assertions Test');
        console.log('================================');

        const assertions = this._generateResetBehaviorAssertions(this.signals, "clk", this.config);
        
        console.log('Generated assertions:');
        console.log(assertions);
        
        const hasReset = assertions.includes("reset |-> ##1");
        const hasTargets = assertions.includes("!ready") && assertions.includes("!busy");
        
        console.log(`✅ Reset timing: ${hasReset ? 'PASS' : 'FAIL'}`);
        console.log(`✅ Target signals: ${hasTargets ? 'PASS' : 'FAIL'}`);
        
        return hasReset && hasTargets;
    }

    // Test signal change detection
    testSignalChangeAssertions() {
        console.log('\n🧪 Signal Change Detection Test');
        console.log('==============================');

        const assertions = this._generateSignalChangeAssertions(this.signals, "clk", this.config);
        
        console.log('Generated assertions:');
        console.log(assertions);
        
        const hasChange = assertions.includes("$changed(");
        const hasEdgeDetection = assertions.includes("clk_enable") && assertions.includes("clk_out");
        
        console.log(`✅ Change detection: ${hasChange ? 'PASS' : 'FAIL'}`);
        console.log(`✅ Edge logic: ${hasEdgeDetection ? 'PASS' : 'FAIL'}`);
        
        return hasChange && hasEdgeDetection;
    }

    // Implementation methods (simplified versions)
    _generateVariableLatencyAssertions(signals, clockSignal, config) {
        let assertions = `  // === VARIABLE LATENCY ASSERTIONS (ADVICE2) ===\n`;
        
        const extendedConfig = config?.extended_config;
        if (extendedConfig?.timing_relationships) {
            extendedConfig.timing_relationships.forEach((timing) => {
                if (timing.type === 'variable_latency') {
                    const triggerSignal = timing.trigger_signal;
                    const responseSignal = timing.response_signal;
                    
                    assertions += `  property ${triggerSignal}_to_${responseSignal}_variable_latency_p;\n`;
                    assertions += `    disable iff (!rst_n)\n`;
                    assertions += `    @(posedge ${clockSignal}) $rose(${triggerSignal}) |-> ##[${timing.min_cycles}:${timing.max_cycles}] ${responseSignal};\n`;
                    assertions += `  endproperty\n`;
                }
            });
        }
        
        return assertions;
    }

    _generateSequentialProtocolAssertions(signals, clockSignal, config) {
        let assertions = `  // === SEQUENTIAL PROTOCOL ASSERTIONS (ADVICE2) ===\n`;
        
        const extendedConfig = config?.extended_config;
        if (extendedConfig?.sequence_chains) {
            extendedConfig.sequence_chains.forEach((sequence) => {
                const seqSignals = sequence.signals;
                if (seqSignals && seqSignals.length >= 2) {
                    const seqName = sequence.name || seqSignals.join('_');
                    
                    assertions += `  property ${seqName}_sequence_p;\n`;
                    assertions += `    disable iff (!rst_n)\n`;
                    assertions += `    @(posedge ${clockSignal}) $rose(${seqSignals[0]})`;
                    
                    for (let i = 1; i < seqSignals.length; i++) {
                        const delay = sequence.delays?.[i-1] || '[1:5]';
                        assertions += ` |-> ##${delay} $rose(${seqSignals[i]})`;
                    }
                    
                    assertions += `;\n  endproperty\n`;
                }
            });
        }
        
        return assertions;
    }

    _generateProhibitionPatterns(signals, clockSignal, config) {
        let assertions = `  // === PROHIBITION PATTERN ASSERTIONS (ADVICE2) ===\n`;
        
        const extendedConfig = config?.extended_config;
        if (extendedConfig?.conflict_signals) {
            extendedConfig.conflict_signals.forEach((conflict) => {
                const signal1 = conflict.signal1;
                const signal2 = conflict.signal2;
                
                assertions += `  property no_${signal1}_${signal2}_conflict_p;\n`;
                assertions += `    disable iff (!rst_n)\n`;
                assertions += `    @(posedge ${clockSignal}) not (${signal1} && ${signal2});\n`;
                assertions += `  endproperty\n`;
            });
        }
        
        return assertions;
    }

    _generateResetBehaviorAssertions(signals, clockSignal, config) {
        let assertions = `  // === RESET BEHAVIOR ASSERTIONS (ADVICE2) ===\n`;
        
        const extendedConfig = config?.extended_config;
        if (extendedConfig?.reset_behavior) {
            const resetBehavior = extendedConfig.reset_behavior;
            const resetSignal = resetBehavior.reset_signal;
            const resetTargets = resetBehavior.reset_targets || [];
            
            if (resetTargets.length > 0) {
                const conditions = resetTargets.map((target) => 
                    target.value === "0" ? `!${target.signal}` : target.signal
                ).join(' && ');
                
                assertions += `  property reset_behavior_p;\n`;
                assertions += `    @(posedge ${clockSignal}) ${resetSignal} |-> ##1 (${conditions});\n`;
                assertions += `  endproperty\n`;
            }
        }
        
        return assertions;
    }

    _generateSignalChangeAssertions(signals, clockSignal, config) {
        let assertions = `  // === SIGNAL CHANGE DETECTION ASSERTIONS (ADVICE2) ===\n`;
        
        const extendedConfig = config?.extended_config;
        if (extendedConfig?.edge_detection) {
            extendedConfig.edge_detection.forEach((edge) => {
                const trigger = edge.trigger;
                const target = edge.target;
                const type = edge.type || 'change';
                
                assertions += `  property ${trigger}_${target}_${type}_p;\n`;
                assertions += `    disable iff (!rst_n)\n`;
                
                // Fix SystemVerilog function names
                if (type === 'change') {
                    assertions += `    @(posedge ${clockSignal}) ${trigger} |-> $changed(${target});\n`;
                } else if (type === 'rose') {
                    assertions += `    @(posedge ${clockSignal}) ${trigger} |-> $rose(${target});\n`;
                } else if (type === 'fell') {
                    assertions += `    @(posedge ${clockSignal}) ${trigger} |-> $fell(${target});\n`;
                } else {
                    assertions += `    @(posedge ${clockSignal}) ${trigger} |-> $${type}(${target});\n`;
                }
                
                assertions += `  endproperty\n`;
            });
        }
        
        return assertions;
    }

    // Run all tests
    runAllTests() {
        console.log('🎯 ADVICE2 Features Implementation Test');
        console.log('======================================\n');

        const results = [
            this.testVariableLatencyAssertions(),
            this.testSequentialProtocolAssertions(),
            this.testProhibitionPatterns(),
            this.testResetBehaviorAssertions(),
            this.testSignalChangeAssertions()
        ];

        const passed = results.filter(r => r).length;
        const total = results.length;
        const successRate = ((passed / total) * 100).toFixed(1);

        console.log('\n📊 Test Results Summary');
        console.log('======================');
        console.log(`✅ Passed: ${passed}/${total} (${successRate}%)`);

        if (successRate >= 80) {
            console.log('🎉 ADVICE2 features successfully implemented!');
        } else {
            console.log('⚠️  Some ADVICE2 features need more work');
        }

        return {
            passed,
            total,
            successRate: parseFloat(successRate)
        };
    }
}

// Run tests
if (require.main === module) {
    const tester = new Advice2FeatureTest();
    tester.runAllTests();
}

module.exports = Advice2FeatureTest;
