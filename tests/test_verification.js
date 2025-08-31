const fs = require('fs');
const { WaveformToSVAGenerator } = require('../out/svaGenerator.js');

console.log("=== Comprehensive Test Results Verification ===\n");

const comprehensiveJSON = JSON.parse(fs.readFileSync('./comprehensive_test.json', 'utf8'));

try {
  const generator = new WaveformToSVAGenerator();
  const result = generator.generateSVA(JSON.stringify(comprehensiveJSON));
  
  // Detailed results for documentation
  const detailedResults = {
    execution: {
      timestamp: new Date().toISOString(),
      success: result.success,
      totalSignals: comprehensiveJSON.signal.length,
      totalEdges: comprehensiveJSON.edge.length,
      nodeCount: comprehensiveJSON.signal.filter(s => s.node).length
    },
    statistics: result.statistics,
    results: {
      propertyCount: result.properties ? result.properties.length : 0,
      warningCount: result.warnings ? result.warnings.length : 0,
      errorCount: result.errors ? result.errors.length : 0
    },
    operatorSupport: {
      "~>": false,
      "-|>": false,
      "|->": false,
      "<->": false,
      "<~>": false
    },
    issue2Implementation: {
      "stableThroughout": false,
      "changedWithTiming": false,
      "conditionalGuardOr": false,
      "conditionalGuardAnd": false
    }
  };
  
  // Check operator support
  const allProps = result.properties ? result.properties.join('\n') : '';
  detailedResults.operatorSupport["~>"] = allProps.includes('$rose') || allProps.includes('##');
  detailedResults.operatorSupport["-|>"] = allProps.includes('$fell') || allProps.includes('$stable');
  detailedResults.operatorSupport["|->"] = allProps.includes('|->');
  detailedResults.operatorSupport["<->"] = allProps.includes('$stable') && allProps.includes('throughout');
  detailedResults.operatorSupport["<~>"] = allProps.includes('$changed') && allProps.includes('##');
  
  // Check Issue #2 implementation
  detailedResults.issue2Implementation.stableThroughout = allProps.includes('$stable') && allProps.includes('throughout');
  detailedResults.issue2Implementation.changedWithTiming = allProps.includes('$changed') && allProps.includes('##');
  detailedResults.issue2Implementation.conditionalGuardOr = allProps.includes('(') && allProps.includes(') |->');
  detailedResults.issue2Implementation.conditionalGuardAnd = allProps.includes('|->');
  
  // Save results
  fs.writeFileSync('./verification_results.json', JSON.stringify(detailedResults, null, 2), 'utf8');
  
  console.log("EXECUTION SUMMARY:");
  console.log(`- Success: ${result.success}`);
  console.log(`- Total Signals: ${detailedResults.execution.totalSignals}`);
  console.log(`- Total Edges: ${detailedResults.execution.totalEdges}`);
  console.log(`- Node Count: ${detailedResults.execution.nodeCount}`);
  console.log("");
  
  console.log("GENERATION RESULTS:");
  console.log(`- Properties Generated: ${detailedResults.results.propertyCount}`);
  console.log(`- Warnings: ${detailedResults.results.warningCount}`);
  console.log(`- Errors: ${detailedResults.results.errorCount}`);
  console.log("");
  
  console.log("OPERATOR SUPPORT:");
  Object.keys(detailedResults.operatorSupport).forEach(op => {
    console.log(`- ${op}: ${detailedResults.operatorSupport[op] ? 'SUPPORTED' : 'NOT_SUPPORTED'}`);
  });
  console.log("");
  
  console.log("ISSUE #2 IMPLEMENTATION:");
  console.log(`- <-> stable throughout: ${detailedResults.issue2Implementation.stableThroughout ? 'IMPLEMENTED' : 'NOT_IMPLEMENTED'}`);
  console.log(`- <~> changed with timing: ${detailedResults.issue2Implementation.changedWithTiming ? 'IMPLEMENTED' : 'NOT_IMPLEMENTED'}`);
  console.log(`- Conditional guard $|: ${detailedResults.issue2Implementation.conditionalGuardOr ? 'IMPLEMENTED' : 'NOT_IMPLEMENTED'}`);
  console.log(`- Conditional guard $&: ${detailedResults.issue2Implementation.conditionalGuardAnd ? 'IMPLEMENTED' : 'NOT_IMPLEMENTED'}`);
  console.log("");
  
  if (result.warnings && result.warnings.length > 0) {
    console.log("WARNINGS SUMMARY:");
    console.log(`- Total warnings: ${result.warnings.length}`);
    const warningTypes = {};
    result.warnings.forEach(warning => {
      if (warning.includes('Reverse edge')) warningTypes['Reverse Edge'] = (warningTypes['Reverse Edge'] || 0) + 1;
      if (warning.includes('Reverse causality')) warningTypes['Reverse Causality'] = (warningTypes['Reverse Causality'] || 0) + 1;
      if (warning.includes('Undefined node')) warningTypes['Undefined Node'] = (warningTypes['Undefined Node'] || 0) + 1;
    });
    Object.keys(warningTypes).forEach(type => {
      console.log(`  - ${type}: ${warningTypes[type]}`);
    });
  }
  
  console.log("\n=== Verification Complete ===");
  
} catch (error) {
  console.error("ERROR:", error.message);
}
