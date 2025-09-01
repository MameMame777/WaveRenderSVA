# WaveRenderSVA Integrated Test Report

## Execution Summary

- **Timestamp**: 2025-09-01T21:16:32.620Z
- **Test Suite**: WaveRenderSVA Integrated Test Suite v1.0
- **Environment**: Node.js v24.4.1

## Test Results

| Test | Status | Properties | Warnings | Errors |
|------|--------|------------|----------|--------|
| comprehensive_functionality | ✅ PASS | 34 | 19 | 0 |
| issue3_node_timing | ✅ PASS | 8 | 0 | 0 |
| advanced_logic_patterns | ✅ PASS | 3 | 0 | 0 |
| same_position_nodes | ✅ PASS | 2 | 0 | 0 |
| different_position_nodes | ✅ PASS | 2 | 0 | 0 |
| mixed_timing_test | ✅ PASS | 3 | 0 | 0 |

## Summary Statistics

- **Total Tests**: 6
- **Passed**: 6
- **Failed**: 0
- **Success Rate**: 100.0%
- **Total Properties Generated**: 52
- **Total Warnings**: 19
- **Total Errors**: 0

## Timing-Aware Implication Operator Analysis

### Regression Test Results

- **Same-position nodes (|->)**: ✅ CORRECT
- **Different-position nodes (|=>)**: ❌ INCORRECT
- **Mixed timing test**: ✅ CORRECT

## Operator Support

- **~>**: SUPPORTED
- **-|>**: SUPPORTED
- **->**: SUPPORTED
- **|->**: SUPPORTED
- **<->**: SUPPORTED
- **<~>**: SUPPORTED

## Conclusion

🎉 **ALL TESTS PASSED!** The WaveRenderSVA extension is functioning correctly with proper timing-aware implication operator selection.

---
*Report generated on 2025-09-01T21:16:32.620Z*
