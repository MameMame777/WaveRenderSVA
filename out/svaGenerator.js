"use strict";
/**
 * WaveDrom to SystemVerilog Assertion (SVA) Generator
 *
 * Based on WAVEDROM_SVA_MAPPING.md specification
 * Implements IEEE 1800-2017 LRM compliant SystemVerilog assertions
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.WaveformToSVAGenerator = void 0;
/**
 * Main SVA Generator Class
 * Implements the complete specification from WAVEDROM_SVA_MAPPING.md
 */
class WaveformToSVAGenerator {
    constructor() {
        this.nodePositions = new Map();
        this.generatedProperties = [];
        this.warnings = [];
        this.errors = [];
        this.embeddedSignals = new Set(); // Track embedded signals
    }
    /**
   * Main entry point for SVA generation
   * @param waveDromJSON WaveDrom JSON string
   * @returns SVA generation result
   */
    generateSVA(waveDromJSON) {
        try {
            // Reset state
            this.nodePositions.clear();
            this.generatedProperties = [];
            this.warnings = [];
            this.errors = [];
            this.embeddedSignals.clear(); // Reset embedded signals
            const data = this.parseWaveDromJSON(waveDromJSON);
            this.extractNodePositions(data.signal);
            const properties = data.edge.map((edge, index) => this.generatePropertyFromEdge(edge, index)).filter(prop => prop !== null);
            return {
                success: true,
                properties,
                warnings: this.warnings,
                errors: this.errors,
                statistics: this.getGenerationStats(data.edge),
                signals: this.extractSignalNames(data.signal)
            };
        }
        catch (error) {
            return this.handleGenerationError(error);
        }
    }
    /**
   * Parse WaveDrom JSON with error recovery
   */
    parseWaveDromJSON(jsonString) {
        try {
            return JSON.parse(jsonString);
        }
        catch (error) {
            this.errors.push(`JSON parsing error: ${error instanceof Error ? error.message : String(error)}`);
            // Attempt partial recovery
            try {
                const partialData = this.attemptPartialParse(jsonString);
                this.warnings.push(`Partial parsing successful: ${partialData.signal.length} signals processed`);
                return partialData;
            }
            catch (recoveryError) {
                this.errors.push(`回復不可能: ${recoveryError instanceof Error ? recoveryError.message : String(recoveryError)}`);
                return { signal: [], edge: [] };
            }
        }
    }
    /**
   * Extract node positions from signal definitions
   * Based on specification Section 5: タイミング計算詳細
   */
    extractNodePositions(signals) {
        signals.forEach(signal => {
            if (!signal.node)
                return;
            // Parse node string: ".a..b.c" -> positions {a:1, b:4, c:6}
            for (let i = 0; i < signal.node.length; i++) {
                const char = signal.node[i];
                if (char !== '.' && char !== '') {
                    const eventType = this.determineEventType(signal.wave, i);
                    const nodePos = {
                        name: char,
                        position: i,
                        signal: signal.name,
                        eventType
                    };
                    this.nodePositions.set(char, nodePos);
                }
            }
        });
    }
    /**
   * Determine event type based on wave pattern
   * Based on specification Section 4: ノードイベント変換
   */
    determineEventType(wave, position) {
        if (position === 0 || position >= wave.length)
            return 'default';
        // Get actual values at current and previous positions (resolve dots)
        const currentValue = this.getActualWaveValue(wave, position);
        const previousValue = this.getActualWaveValue(wave, position - 1);
        // Rising edge: 0->1, l->h, L->H
        if ((previousValue === '0' && currentValue === '1') ||
            (previousValue === 'l' && currentValue === 'h') ||
            (previousValue === 'L' && currentValue === 'H')) {
            return 'rising_edge';
        }
        // Falling edge: 1->0, h->l, H->L
        if ((previousValue === '1' && currentValue === '0') ||
            (previousValue === 'h' && currentValue === 'l') ||
            (previousValue === 'H' && currentValue === 'L')) {
            return 'falling_edge';
        }
        // Data change: x->= or =->x or =->= (different data)
        if (currentValue === '=' || previousValue === '=') {
            return 'data_change';
        }
        // Stable: same value
        if (currentValue === previousValue) {
            return 'stable';
        }
        return 'default';
    }
    /**
     * Get actual wave value at position, resolving dots to previous values
     */
    getActualWaveValue(wave, position) {
        if (position < 0 || position >= wave.length)
            return '';
        const char = wave[position];
        // If it's a dot, find the last non-dot value
        if (char === '.') {
            for (let i = position - 1; i >= 0; i--) {
                const prevChar = wave[i];
                if (prevChar !== '.') {
                    return prevChar;
                }
            }
            return '0'; // Default if no previous value found
        }
        return char;
    }
    /**
   * Generate SystemVerilog property from edge string
   * Core implementation based on specification tables with enhanced analysis
   */
    generatePropertyFromEdge(edgeString, index) {
        const edgeInfo = this.parseEdgeString(edgeString);
        if (!edgeInfo) {
            this.warnings.push(`Edge parsing failed: "${edgeString}"`);
            return null;
        }
        // Check if nodes exist
        const sourceNode = this.nodePositions.get(edgeInfo.source);
        const targetNode = this.nodePositions.get(edgeInfo.target);
        if (!sourceNode || !targetNode) {
            this.warnings.push(`Undefined node: ${!sourceNode ? edgeInfo.source : edgeInfo.target} in edge "${edgeString}"`);
            return this.generateDefaultAssertion(edgeInfo, index);
        }
        // Enhanced: Analyze edge direction for potential issues
        const directionAnalysis = this.analyzeEdgeDirection(sourceNode, targetNode, edgeInfo.operator);
        if (directionAnalysis) {
            this.warnings.push(directionAnalysis);
        }
        // Calculate timing
        const timing = this.calculateTiming(sourceNode, targetNode, edgeInfo.operator);
        // Parse conditions
        const conditions = this.parseConditions(edgeInfo.comment || '');
        return this.buildSVAProperty(edgeInfo, sourceNode, targetNode, timing, conditions, index);
    }
    /**
   * Parse edge string into components
   * Examples: "a->b", "c~>d", "e<->f", "g->h $iff (enable)$ label"
   */
    parseEdgeString(edgeString) {
        // Remove extra whitespace and handle spaces in edge patterns
        const cleaned = edgeString.trim();
        // Handle special patterns with spaces like "b-| -a"
        const normalizedEdge = cleaned.replace(/\s+/g, ' ').replace(/(-\|)\s+(-[a-zA-Z])/g, '$1$2');
        // Extract edge pattern and comment
        const spaceIndex = normalizedEdge.search(/\s(?![a-zA-Z]*[-|~><=+])/);
        const edgePart = spaceIndex > 0 ? normalizedEdge.substring(0, spaceIndex) : normalizedEdge;
        const comment = spaceIndex > 0 ? normalizedEdge.substring(spaceIndex + 1) : '';
        // Parse operator patterns based on specification tables
        // Order matters - more specific patterns first
        const sharpLinePatterns = [
            /<->/, /-\|->/, /-\|>/, /-\|-/, /-\|/, /\|=>/, /\|->/, /->/, /\+/, /-/
        ];
        const splinePatterns = [
            /<-~>/, /<~>/, /-~>/, /~->/, /-~/, /~-/, /~>/, /~/
        ];
        let operator = '';
        let isSharpLine = false;
        // Check sharp line patterns first
        for (const pattern of sharpLinePatterns) {
            const match = edgePart.match(pattern);
            if (match) {
                operator = match[0];
                isSharpLine = true;
                break;
            }
        }
        // Check spline patterns if not sharp line
        if (!operator) {
            for (const pattern of splinePatterns) {
                const match = edgePart.match(pattern);
                if (match) {
                    operator = match[0];
                    isSharpLine = false;
                    break;
                }
            }
        }
        if (!operator) {
            this.warnings.push(`未知のオペレータ: ${edgePart} (full: "${edgeString}")`);
            return null;
        }
        // Extract source and target nodes
        const [source, target] = edgePart.split(operator);
        if (!source || !target) {
            this.warnings.push(`Invalid edge format: ${edgePart}`);
            return null;
        }
        return {
            source: source.trim(),
            target: target.trim(),
            operator,
            comment,
            isSharpLine
        };
    }
    /**
   * Calculate enhanced timing constraint
   * Issue #3: Use precise node positions instead of fixed ranges
   */
    calculateTiming(sourceNode, targetNode, operator) {
        const timingDiff = targetNode.position - sourceNode.position;
        // Handle reverse direction edges with better warnings
        if (timingDiff < 0) {
            this.warnings.push(`Reverse edge detected: ${sourceNode.name}->${targetNode.name}, time diff=${timingDiff} cycles - specification review required`);
            this.warnings.push(`Reverse causality detected: ${sourceNode.name}->${targetNode.name} may be opposite of normal protocol direction. Specification review recommended.`);
            // For reverse edges, use absolute timing
            const absTiming = Math.abs(timingDiff);
            return absTiming === 0 ? '' : `##${absTiming}`;
        }
        // Use precise timing based on actual node positions and operator type
        if (timingDiff === 0) {
            // Same clock cycle - immediate response
            return '';
        }
        // Handle different operators according to WAVEDROM_SVA_MAPPING.md
        if (operator.includes('~>')) {
            // Spline operator: flexible range from 0 to actual timing difference
            // This allows for any timing within the specified range
            return `##[0:${timingDiff}]`;
        }
        else if (operator.includes('|->')) {
            // Sharp immediate implication: same cycle
            return '';
        }
        else if (operator.includes('-|>') || operator.includes('|=>')) {
            // Sharp next-cycle operators: exact timing
            return timingDiff === 1 ? '##1' : `##${timingDiff}`;
        }
        else if (operator.includes('->')) {
            // Simple arrow: immediate implication for same cycle, otherwise exact timing
            return timingDiff === 0 ? '' : `##${timingDiff}`;
        }
        else {
            // Default behavior: flexible range with small tolerance
            const maxDelay = Math.max(1, timingDiff);
            return `##[0:${maxDelay}]`;
        }
    }
    /**
   * Check if operator is sharp line type
   */
    isSharpOperator(op) {
        return ['->', '|->', '|=>', '-|>', '-|-', '-|', '+', '-'].includes(op.replace(/[<>]/g, ''));
    }
    /**
   * Analyze edge direction and suggest fixes for reverse causality
   */
    analyzeEdgeDirection(sourceNode, targetNode, _operator) {
        const timingDiff = targetNode.position - sourceNode.position;
        if (timingDiff < 0) {
            // Common protocol patterns that might be reversed
            const sourceSignal = sourceNode.signal.toLowerCase();
            const targetSignal = targetNode.signal.toLowerCase();
            // Check for common handshake patterns
            if ((sourceSignal.includes('ack') && targetSignal.includes('req')) ||
                (sourceSignal.includes('ready') && targetSignal.includes('valid')) ||
                (sourceSignal.includes('grant') && targetSignal.includes('request'))) {
                return `Warning: ${sourceNode.signal} -> ${targetNode.signal} appears to be reverse of typical handshake pattern. Please verify edge definition.`;
            }
            // Check for reset/enable patterns
            if ((sourceSignal.includes('reset') && !targetSignal.includes('reset')) ||
                (sourceSignal.includes('enable') && !targetSignal.includes('enable'))) {
                return `Note: ${sourceNode.signal} -> ${targetNode.signal} differs from typical reset/enable signal usage pattern.`;
            }
        }
        return null;
    }
    /**
   * Parse enhanced conditions from comment string with logical operators
   * Supports: $&(condition)$, $|(condition)$, $!(condition)$, $->(condition)$, $iff(condition)$
   */
    parseConditions(comment) {
        const dollarRegex = /\$([^$]+)\$/g;
        const conditions = {
            iff: [],
            disable_iff: [],
            and: [],
            or: [],
            not: [],
            implies: []
        };
        let match;
        while ((match = dollarRegex.exec(comment)) !== null) {
            try {
                const conditionText = match[1].trim();
                // Enhanced logical operators
                if (conditionText.startsWith('&(') && conditionText.endsWith(')')) {
                    // $&(condition)$ - AND logic
                    const cleanCondition = conditionText.slice(2, -1).trim();
                    conditions.and.push(cleanCondition);
                    this.extractSignalsFromCondition(cleanCondition);
                }
                else if (conditionText.startsWith('|(') && conditionText.endsWith(')')) {
                    // $|(condition)$ - OR logic
                    const cleanCondition = conditionText.slice(2, -1).trim();
                    conditions.or.push(cleanCondition);
                    this.extractSignalsFromCondition(cleanCondition);
                }
                else if (conditionText.startsWith('!(') && conditionText.endsWith(')')) {
                    // $!(condition)$ - NOT logic
                    const cleanCondition = conditionText.slice(2, -1).trim();
                    conditions.not.push(cleanCondition);
                    this.extractSignalsFromCondition(cleanCondition);
                }
                else if (conditionText.startsWith('->(') && conditionText.endsWith(')')) {
                    // $->(condition)$ - IMPLIES logic
                    const cleanCondition = conditionText.slice(3, -1).trim();
                    conditions.implies.push(cleanCondition);
                    this.extractSignalsFromCondition(cleanCondition);
                }
                else if (conditionText.startsWith('iff(') && conditionText.endsWith(')')) {
                    // $iff(condition)$ - IFF logic (backward compatibility)
                    const cleanCondition = conditionText.slice(4, -1).trim();
                    conditions.and.push(cleanCondition); // Treat as AND for safer semantics
                    this.extractSignalsFromCondition(cleanCondition);
                }
                else if (conditionText.startsWith('iff ')) {
                    // Legacy: "iff condition" pattern
                    const iffContent = conditionText.substring(4).trim();
                    const cleanCondition = iffContent.replace(/^\(|\)$/g, '').trim();
                    conditions.and.push(cleanCondition);
                    this.extractSignalsFromCondition(cleanCondition);
                }
                else if (conditionText.startsWith('disable_iff ')) {
                    const disableContent = conditionText.substring(12).trim();
                    const cleanCondition = disableContent.replace(/^\(|\)$/g, '').trim();
                    conditions.disable_iff.push(cleanCondition);
                    this.extractSignalsFromCondition(cleanCondition);
                }
            }
            catch (_error) {
                this.warnings.push(`Condition parsing error: ${match[1]}, skipped`);
            }
        }
        return conditions;
    }
    /**
     * Extract signal names from condition strings
     */
    extractSignalsFromCondition(condition) {
        // Match signal names (alphanumeric identifiers)
        const signalMatches = condition.match(/\b[a-zA-Z_][a-zA-Z0-9_]*\b/g);
        if (signalMatches) {
            for (const signal of signalMatches) {
                // Exclude SystemVerilog keywords and common non-signal words
                if (!this.isSystemVerilogKeyword(signal) && signal !== 'rst_n' && signal !== 'clk') {
                    this.embeddedSignals.add(signal);
                }
            }
        }
    }
    /**
     * Check if a word is a SystemVerilog keyword
     */
    isSystemVerilogKeyword(word) {
        const keywords = [
            'and', 'or', 'not', 'iff', 'disable_iff', 'implies', 'throughout',
            'property', 'endproperty', 'assert', 'assume', 'cover', 'expect',
            'logic', 'input', 'output', 'module', 'endmodule', 'always',
            'posedge', 'negedge', 'clock', 'reset', 'begin', 'end'
        ];
        return keywords.includes(word.toLowerCase());
    }
    /**
     * Adjust node event type based on edge operator (Issue #2)
     * <-> = stable, <~> = data_change
     */
    adjustNodeEventType(node, operator) {
        let newEventType = node.eventType;
        if (operator === '<->') {
            newEventType = 'stable';
        }
        else if (operator === '<~>') {
            newEventType = 'data_change';
        }
        // Return new node with adjusted event type
        return Object.assign(Object.assign({}, node), { eventType: newEventType });
    }
    /**
     * Build SVA expression with throughout/within operators for Issue #2
     */
    buildSpecialSVAExpression(sourceNode, targetNode, timing, operator) {
        const sourceEvent = this.getEventFunction(sourceNode);
        const targetEvent = this.getEventFunction(targetNode);
        if (operator === '<->') {
            // Use correct throughout syntax for stability
            const sourceSignal = sourceNode.signal;
            const targetSignal = targetNode.signal;
            if (sourceSignal === targetSignal) {
                // Same signal: just check stability
                return `$stable(${sourceSignal})`;
            }
            else {
                // Cross-signal: target signal should be stable throughout source signal stability period
                // Pattern: $stable(data) throughout $stable(req) 
                // This means: while source is stable, target must also be stable
                return `$stable(${targetSignal}) throughout $stable(${sourceSignal})`;
            }
        }
        else if (operator === '<~>') {
            // Use standard SVA syntax for change detection
            if (timing && timing !== '') {
                // Extract timing range from timing string like "##[0:3]"
                const timingMatch = timing.match(/##\[(\d+):(\d+)\]/);
                if (timingMatch) {
                    const [, min, max] = timingMatch;
                    return `${sourceEvent} |-> ##[${min}:${max}] ${targetEvent}`;
                }
                else {
                    // Fallback to default range
                    return `${sourceEvent} |-> ##[0:10] ${targetEvent}`;
                }
            }
            else {
                // Simple change detection with default range
                return `${sourceEvent} |-> ##[1:10] ${targetEvent}`;
            }
        }
        // Fallback to normal expression
        const implication = this.getImplicationOperator(operator);
        const timingStr = timing ? ` ${timing}` : '';
        return `${sourceEvent} ${implication}${timingStr} ${targetEvent}`;
    }
    /**
   * Build complete SVA property string - Enhanced version with logical operators
   */
    buildSVAProperty(edgeInfo, sourceNode, targetNode, timing, conditions, index) {
        // Issue #2: Override event types based on edge operator
        const adjustedSourceNode = this.adjustNodeEventType(sourceNode, edgeInfo.operator);
        const adjustedTargetNode = this.adjustNodeEventType(targetNode, edgeInfo.operator);
        // Issue #2: Use special SVA expressions for <-> and <~> with throughout/within
        let mainExpression;
        if (edgeInfo.operator === '<->' || edgeInfo.operator === '<~>') {
            mainExpression = this.buildSpecialSVAExpression(adjustedSourceNode, adjustedTargetNode, timing, edgeInfo.operator);
        }
        else {
            const sourceEvent = this.getEventFunction(adjustedSourceNode);
            const targetEvent = this.getEventFunction(adjustedTargetNode);
            const implication = this.getImplicationOperator(edgeInfo.operator);
            const timingStr = timing ? ` ${timing}` : '';
            mainExpression = `${sourceEvent} ${implication}${timingStr} ${targetEvent}`;
        }
        // Enhanced: Check for reverse causality and warn appropriately
        const timingDiff = targetNode.position - sourceNode.position;
        if (timingDiff < 0) {
            this.warnings.push(`Reverse causality detected: ${edgeInfo.source}->${edgeInfo.target} may be opposite of normal protocol direction. Specification review recommended.`);
        }
        // Build conditions with enhanced logical operators
        const disableIff = conditions.disable_iff.length > 0
            ? ` disable iff (${conditions.disable_iff.join(' && ')})`
            : ' disable iff (!rst_n)';
        // Enhanced: Build target expression with logical operators
        let finalExpression;
        if (edgeInfo.operator === '<->' || edgeInfo.operator === '<~>') {
            // For special operators, build the expression first, then apply conditions as guard
            const baseExpression = mainExpression;
            // Apply conditions as guard conditions at the front
            if (conditions.and.length > 0) {
                const guardExpr = conditions.and.join(' && ');
                finalExpression = `${guardExpr} |-> (${baseExpression})`;
            }
            else if (conditions.or.length > 0) {
                const guardExpr = conditions.or.join(' || ');
                finalExpression = `(${guardExpr}) |-> (${baseExpression})`;
            }
            else {
                finalExpression = baseExpression;
            }
        }
        else {
            // For normal operators, apply conditions to target event only
            const targetEvent = this.getEventFunction(adjustedTargetNode);
            const targetWithConditions = this.buildLogicalExpression(targetEvent, conditions);
            // Rebuild the full expression
            const sourceEvent = this.getEventFunction(adjustedSourceNode);
            const implication = this.getImplicationOperator(edgeInfo.operator);
            const timingStr = timing ? ` ${timing}` : '';
            finalExpression = `${sourceEvent} ${implication}${timingStr} ${targetWithConditions}`;
        }
        const propertyName = `edge_${edgeInfo.source}_to_${edgeInfo.target}_${index}`;
        // Enhanced: More informative error messages
        const timingStr = timing ? timing : '0';
        const errorMsg = `[SVA] Timing violation: ${sourceNode.signal}(${edgeInfo.source}) -> ${targetNode.signal}(${edgeInfo.target}) failed at cycle %0d with operator '${edgeInfo.operator}' (expected delay: ${timingStr})`;
        return `property ${propertyName};
  @(posedge clk)${disableIff}
  ${finalExpression};
endproperty
${propertyName}_a: assert property(${propertyName})
  else $error("${errorMsg}", ($time / $realtime));`;
    }
    /**
   * Build logical expression from conditions and target event
   */
    buildLogicalExpression(targetEvent, conditions) {
        const parts = [targetEvent];
        // Add AND conditions
        if (conditions.and.length > 0) {
            parts.push(...conditions.and);
        }
        // Handle OR conditions (group them separately)
        let expression = parts.length > 1 ? `(${parts.join(' && ')})` : parts[0];
        if (conditions.or.length > 0) {
            const orPart = conditions.or.join(' || ');
            expression = `(${expression} || ${orPart})`;
        }
        // Handle NOT conditions (apply to whole expression)
        if (conditions.not.length > 0) {
            const notConditions = conditions.not.map(cond => `!${cond}`).join(' && ');
            expression = `(${notConditions} && ${expression})`;
        }
        // Handle IMPLIES conditions
        if (conditions.implies.length > 0) {
            const impliesConditions = conditions.implies.join(' && ');
            expression = `(${impliesConditions} |-> ${expression})`;
        }
        // Handle legacy IFF conditions (for backward compatibility)
        if (conditions.iff.length > 0) {
            this.warnings.push(`Legacy iff condition detected: ${conditions.iff.join(', ')} - recommend using new $&()$ syntax`);
            expression = `(${conditions.iff.join(' && ')} && ${expression})`;
        }
        return expression;
    }
    /**
   * Get SystemVerilog event function based on event type
   * Based on specification Section 4: ノードイベント変換
   */
    getEventFunction(node) {
        switch (node.eventType) {
            case 'rising_edge':
                return `$rose(${node.signal})`;
            case 'falling_edge':
                return `$fell(${node.signal})`;
            case 'data_change':
                return `$changed(${node.signal})`;
            case 'stable':
                return `$stable(${node.signal})`;
            default:
                return node.signal;
        }
    }
    /**
   * Get SystemVerilog implication operator
   * Based on specification Section 1-2: Sharp Lines/Splines tables
   */
    getImplicationOperator(operator) {
        // Sharp Lines - exact timing
        switch (operator) {
            case '->':
            case '-|>':
            case '|=>':
            case '-|->':
            case '-|-':
            case '-|':
            case '-':
                return '|=>'; // non-overlapped
            case '|->':
                return '|->'; // overlapped
            case '+':
                return '&&'; // combinational
            default:
                break;
        }
        // Splines - flexible timing
        switch (operator) {
            case '~>':
            case '<~>':
            case '~->':
                return '|=>'; // non-overlapped for flexible timing
            case '-~>':
            case '-~':
            case '~-':
            case '~':
                return '|=>'; // non-overlapped
            default:
                this.warnings.push(`Unsupported operator: ${operator}, using default |=>`);
                return '|=>';
        }
    }
    /**
   * Generate bidirectional property (A <-> B becomes A->B and B->A)
   */
    /**
   * Generate default assertion for error recovery
   */
    generateDefaultAssertion(edgeInfo, index) {
        const propertyName = `edge_default_${index}`;
        return `// Warning: Partial edge processing (${edgeInfo.source} -> ${edgeInfo.target})
property ${propertyName};
  @(posedge clk) disable iff (!rst_n)
  1'b1 |=> ##1 1'b1; // Default constraint
endproperty
${propertyName}_a: assert property(${propertyName})
  else $error("[SVA] Default edge constraint at time %0t", $time);`;
    }
    /**
   * Attempt partial JSON parsing for error recovery
   */
    attemptPartialParse(jsonString) {
        // Simple recovery: try to extract signal and edge arrays
        const signalMatch = jsonString.match(/"signal"\s*:\s*\[([\s\S]*?)\]/);
        const edgeMatch = jsonString.match(/"edge"\s*:\s*\[([\s\S]*?)\]/);
        return {
            signal: signalMatch ? this.parseSignalArray(signalMatch[1]) : [],
            edge: edgeMatch ? this.parseEdgeArray(edgeMatch[1]) : []
        };
    }
    parseSignalArray(signalStr) {
        // Simplified signal parsing - would need more robust implementation
        try {
            return JSON.parse(`[${signalStr}]`);
        }
        catch (_a) {
            return [];
        }
    }
    parseEdgeArray(edgeStr) {
        // Simplified edge parsing
        try {
            return JSON.parse(`[${edgeStr}]`);
        }
        catch (_a) {
            return [];
        }
    }
    /**
   * Generate statistics for the result
   */
    getGenerationStats(edges) {
        let sharpLines = 0;
        let splines = 0;
        let bidirectional = 0;
        let conditional = 0;
        let invalidEdges = 0;
        edges.forEach(edge => {
            if (edge.includes('<->'))
                bidirectional++;
            if (edge.includes('$'))
                conditional++;
            const edgeInfo = this.parseEdgeString(edge);
            if (!edgeInfo) {
                invalidEdges++;
            }
            else if (edgeInfo.isSharpLine) {
                sharpLines++;
            }
            else {
                splines++;
            }
        });
        return {
            totalEdges: edges.length,
            sharpLines,
            splines,
            bidirectional,
            conditional,
            invalidEdges
        };
    }
    /**
   * Extract signal names from signal array and embedded conditions
   */
    extractSignalNames(signals) {
        const baseSignals = signals
            .filter(signal => signal.name && signal.name !== 'clk') // Exclude clock
            .map(signal => signal.name);
        // Add embedded signals from conditions
        const allSignals = [...new Set([...baseSignals, ...Array.from(this.embeddedSignals)])];
        return allSignals;
    }
    /**
   * Handle generation errors
   */
    handleGenerationError(error) {
        return {
            success: false,
            properties: [],
            warnings: this.warnings,
            errors: [`Generation error: ${error instanceof Error ? error.message : String(error)}`],
            statistics: {
                totalEdges: 0,
                sharpLines: 0,
                splines: 0,
                bidirectional: 0,
                conditional: 0,
                invalidEdges: 0
            },
            signals: []
        };
    }
}
exports.WaveformToSVAGenerator = WaveformToSVAGenerator;
//# sourceMappingURL=svaGenerator.js.map