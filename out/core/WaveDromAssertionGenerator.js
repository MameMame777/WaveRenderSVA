"use strict";
// =============================================================================
// WaveDrom to SystemVerilog Assertion Generator - 実際の実装
// =============================================================================
Object.defineProperty(exports, "__esModule", { value: true });
exports.WaveDromAssertionGenerator = void 0;
class WaveDromAssertionGenerator {
    constructor() {
        this.errors = [];
        this.warnings = [];
    }
    generateAssertions(wavedrom) {
        this.errors = [];
        this.warnings = [];
        try {
            // 基本検証
            this.validateInput(wavedrom);
            // SystemVerilogコード生成
            const systemverilog = this.generateSystemVerilogCode(wavedrom);
            return {
                success: true,
                systemverilog,
                errors: this.errors,
                warnings: this.warnings
            };
        }
        catch (error) {
            this.errors.push(error instanceof Error ? error.message : String(error));
            return {
                success: false,
                systemverilog: '',
                errors: this.errors,
                warnings: this.warnings
            };
        }
    }
    validateInput(wavedrom) {
        if (!wavedrom.signal || wavedrom.signal.length === 0) {
            throw new Error('No signals found in WaveDrom JSON');
        }
        if (!wavedrom.edge || wavedrom.edge.length === 0) {
            throw new Error('No edges found in WaveDrom JSON');
        }
        // 信号検証
        wavedrom.signal.forEach((signal, index) => {
            if (!signal.name) {
                throw new Error(`Signal at index ${index} has no name`);
            }
            if (!signal.wave) {
                throw new Error(`Signal '${signal.name}' has no wave pattern`);
            }
        });
    }
    generateSystemVerilogCode(wavedrom) {
        let code = '// Generated SystemVerilog Assertions\n';
        code += '// Generated from WaveDrom JSON\n\n';
        if (!wavedrom.edge)
            return code;
        wavedrom.edge.forEach((edge, index) => {
            try {
                const assertion = this.processEdge(edge, wavedrom.signal, index);
                code += assertion + '\n';
            }
            catch (error) {
                this.warnings.push(`Failed to process edge '${edge}': ${error}`);
            }
        });
        return code;
    }
    processEdge(edge, signals, index) {
        // エッジパターン解析
        const edgePattern = /([a-z]+)([-|~<>]+)([a-z]+)\s*(\w+)?\s*(\[.*\])?/;
        const match = edge.match(edgePattern);
        if (!match) {
            throw new Error(`Invalid edge format: ${edge}`);
        }
        const [, fromNode, operator, toNode, name, condition] = match;
        // ノードから信号を検索
        const fromSignal = this.findSignalByNode(fromNode, signals);
        const toSignal = this.findSignalByNode(toNode, signals);
        if (!fromSignal) {
            throw new Error(`Signal not found for node: ${fromNode}`);
        }
        if (!toSignal) {
            throw new Error(`Signal not found for node: ${toNode}`);
        }
        // SystemVerilog生成
        return this.generatePropertyCode(fromNode, toNode, operator, fromSignal, toSignal, signals, condition, index);
    }
    findSignalByNode(node, signals) {
        return signals.find(signal => signal.node && signal.node.includes(node)) || null;
    }
    generatePropertyCode(fromNode, toNode, operator, fromSignal, toSignal, allSignals, condition, index) {
        let code = `property prop_${fromNode}_to_${toNode}_${index};\n`;
        code += '  @(posedge clk)';
        // 条件処理
        if (condition) {
            code += this.parseCondition(condition);
        }
        else {
            code += ' disable iff (!rst_n)';
        }
        code += '\n  ';
        // イベント検出
        const fromEvent = this.detectEvent(fromSignal, fromNode);
        const toEvent = this.detectEvent(toSignal, toNode);
        // 演算子とタイミング
        const svOperator = this.convertOperator(operator);
        const timing = this.calculateTiming(fromNode, toNode, allSignals);
        code += `${fromEvent} ${svOperator}${timing} ${toEvent};\n`;
        code += 'endproperty\n';
        code += `assert property(prop_${fromNode}_to_${toNode}_${index}) else $fatal(1, "Assertion failed: prop_${fromNode}_to_${toNode}_${index}");\n`;
        return code;
    }
    parseCondition(condition) {
        let result = '';
        // disable iff 処理
        const disableMatch = condition.match(/disable iff \(([^)]+)\)/);
        if (disableMatch) {
            result += ` disable iff (${disableMatch[1]})`;
        }
        // iff 処理
        const iffMatch = condition.match(/(?:^|\s)iff \(([^)]+)\)/);
        if (iffMatch) {
            result += ` iff (${iffMatch[1]})`;
        }
        return result;
    }
    detectEvent(signal, node) {
        if (!signal.node || !signal.wave) {
            return `$changed(${signal.name})`;
        }
        const nodeIndex = signal.node.indexOf(node);
        if (nodeIndex === -1) {
            return `$changed(${signal.name})`;
        }
        const waveChar = signal.wave[nodeIndex];
        const prevChar = nodeIndex > 0 ? signal.wave[nodeIndex - 1] : '0';
        // 立ち上がり/立ち下がり検出
        if (prevChar === '0' && waveChar === '1') {
            return `$rose(${signal.name})`;
        }
        else if (prevChar === '1' && waveChar === '0') {
            return `$fell(${signal.name})`;
        }
        else if (waveChar !== prevChar && waveChar !== '.' && waveChar !== prevChar) {
            return `$changed(${signal.name})`;
        }
        return `$rose(${signal.name})`;
    }
    convertOperator(operator) {
        const operatorMap = {
            '-|->': '|=>',
            '|->': '|->',
            '<->': '<->',
            '-|': '|=>',
            '->': '|->',
            '-~>': '|=>',
            '~': '|->',
            '<~>': '<~>'
        };
        return operatorMap[operator] || '|->';
    }
    calculateTiming(fromNode, toNode, signals) {
        let fromPos = -1;
        let toPos = -1;
        // ノード位置を検索
        for (const signal of signals) {
            if (signal.node) {
                const fromIdx = signal.node.indexOf(fromNode);
                const toIdx = signal.node.indexOf(toNode);
                if (fromIdx !== -1)
                    fromPos = fromIdx;
                if (toIdx !== -1)
                    toPos = toIdx;
            }
        }
        if (fromPos === -1 || toPos === -1) {
            return '';
        }
        const delay = toPos - fromPos;
        if (delay === 0)
            return '';
        if (delay === 1)
            return ' ##1';
        if (delay > 1)
            return ` ##${delay}`;
        return '';
    }
}
exports.WaveDromAssertionGenerator = WaveDromAssertionGenerator;
//# sourceMappingURL=WaveDromAssertionGenerator.js.map