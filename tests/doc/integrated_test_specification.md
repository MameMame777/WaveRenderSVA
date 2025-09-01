# WaveRenderSVA Integrated Test Specification

## Overview

This document provides comprehensive test specifications for the WaveRenderSVA extension, covering all functionality including the recent timing-aware implication operator enhancements.

## Test Architecture

### Test Categories

1. **Functional Tests**: Core SVA generation functionality
2. **Regression Tests**: Timing-aware implication operator fixes
3. **Integration Tests**: Complete workflow verification
4. **Performance Tests**: Generation speed and memory usage

### Test Data Organization

```
tests/
├── integrated_test_suite.js      # Main test runner
├── pat/                          # Test patterns
│   ├── comprehensive_test.json   # Full functionality test
│   ├── issue3_node_timing_test.json  # Node timing tests
│   └── advanced_logic.json       # Complex patterns
├── report/                       # Generated reports
│   ├── integrated_test_results.json
│   └── integrated_test_report.md
└── doc/                          # Documentation
    └── integrated_test_specification.md  # This file
```

## Test Specifications

### 1. Comprehensive Functionality Test

**Purpose**: Verify all core features work correctly

**Test Data**: `comprehensive_test.json`
- 15 signals with various wave patterns
- 34 edges covering all operator types
- Complex timing relationships

**Expected Results**:
- ✅ Properties generated: ≥30
- ✅ Errors: 0
- ✅ All operators supported: `~>`, `-|>`, `->`, `|->`, `<->`, `<~>`

### 2. Issue #3 Node-Based Timing Test

**Purpose**: Verify precise timing calculation from node positions

**Test Data**: `issue3_node_timing_test.json`
- Node-based timing calculations
- Adjacent and long-range timing relationships
- Exact timing constraints

**Expected Results**:
- ✅ Properties generated: ≥6
- ✅ Timing patterns: `##[0:1]`, `##[0:3]`, `##1`, `##4`
- ✅ Node position accuracy

### 3. Timing-Aware Implication Operator Tests

**Purpose**: Verify the fix for same-position vs different-position nodes

#### 3.1 Same-Position Node Test

**Test Pattern**:
```json
{
  "signal": [
    { "name": "sig1", "wave": "01.0", "node": ".a.b" },
    { "name": "sig2", "wave": "0.10", "node": ".c.d" }
  ],
  "edge": ["a->c", "b->d"]
}
```

**Expected Results**:
- ✅ `a->c`: Position difference = 0 → Use `|->`
- ✅ `b->d`: Position difference = 0 → Use `|->`

#### 3.2 Different-Position Node Test

**Test Pattern**:
```json
{
  "signal": [
    { "name": "req", "wave": "01..0", "node": ".a..b" },
    { "name": "ack", "wave": "0.1.0", "node": "..c.d" }
  ],
  "edge": ["a~>c", "b~>d"]
}
```

**Expected Results**:
- ✅ `a~>c`: Position difference = 1 → Use `|=>`
- ✅ `b~>d`: Position difference = 0 → Use `|=>`

#### 3.3 Mixed Timing Test (Original Issue)

**Test Pattern**:
```json
{
  "signal": [
    { "name": "req", "wave": "01..0.", "node": ".a..b." },
    { "name": "ack", "wave": "0.1.0.", "node": "..c.d." },
    { "name": "data", "wave": "x.==.x", "node": "..e.f." }
  ],
  "edge": ["a~>c", "c->e", "b-|>d"]
}
```

**Expected Results**:
- ✅ `a~>c`: Position 1→2, diff=1 → Use `|=>`
- ✅ `c->e`: Position 2→2, diff=0 → Use `|->` ⚡ **FIXED**
- ✅ `b-|>d`: Position 4→4, diff=0 → Use `|->` ⚡ **FIXED**

## Implementation Details

### Timing-Aware Operator Selection Algorithm

```typescript
private getTimingAwareImplicationOperator(operator: string, timingDiff: number): string {
  // Same position nodes (timingDiff === 0) use overlapped implication
  if (timingDiff === 0) {
    return '|->'; // Overlapped for same cycle
  }
  
  // Different position nodes use original operator mapping
  return this.getImplicationOperator(operator);
}
```

### Node Position Calculation

```typescript
const timingDiff = targetNode.position - sourceNode.position;
const implication = this.getTimingAwareImplicationOperator(edgeInfo.operator, timingDiff);
```

## Quality Assurance Criteria

### Pass Criteria

1. **Zero Critical Errors**: No generation failures
2. **Correct Operator Selection**: 
   - Same-position → `|->`
   - Different-position → `|=>`
3. **Complete Operator Support**: All 6 operators working
4. **Issue Implementations**: #2 and #3 features verified
5. **Performance**: <1s generation time for complex patterns

### Regression Detection

- Monitor for changes in implication operator distribution
- Verify no increase in error/warning counts
- Check property generation consistency

## Report Generation

### JSON Report Structure

```json
{
  "execution": { "timestamp", "testSuite", "environment" },
  "summary": { "totalTests", "passedTests", "failedTests" },
  "tests": { "testName": { "success", "properties", "analysis" } },
  "regression": { "timingAwareOperators": { "results" } }
}
```

### Markdown Report Sections

1. **Execution Summary**: Timestamps, environment
2. **Test Results Table**: Pass/fail status per test
3. **Summary Statistics**: Success rates, property counts
4. **Regression Analysis**: Timing operator verification
5. **Operator Support Matrix**: Feature completeness
6. **Conclusion**: Overall assessment

## Continuous Integration

### Automated Testing

```bash
# Run integrated test suite
cd tests
node integrated_test_suite.js

# Expected output
🎉 ALL TESTS PASSED!
📊 Results: X/X tests passed
📋 Generated XXX properties total
```

### Success Indicators

- Exit code 0
- All tests marked as ✅ PASSED
- Zero critical errors
- Report generation successful

## Troubleshooting

### Common Issues

1. **Properties not generated**: Check JSON syntax
2. **Wrong operators**: Verify node position calculation
3. **Missing features**: Ensure all operator types tested

### Debug Commands

```bash
# Detailed analysis
node integrated_test_suite.js > test_output.log 2>&1

# Check specific test
node -e "const Suite = require('./integrated_test_suite.js'); const s = new Suite(); s.runTest('test_name', 'desc', data);"
```

---

**Document Version**: v1.0
**Last Updated**: September 2, 2025
**Related Issues**: #2 (Operators), #3 (Node Timing)
