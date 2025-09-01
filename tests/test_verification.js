const fs = require('fs');
const { WaveformToSVAGenerator } = require('../out/svaGenerator.js');

console.log("=== Comprehensive Test Results Verification ===\n");

const comprehensiveJSON = JSON.parse(fs.readFileSync('./pat/comprehensive_test.json', 'utf8'));

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
  fs.writeFileSync('./report/verification_results.json', JSON.stringify(detailedResults, null, 2), 'utf8');
  
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
  
  // Issue #3: Node-based timing calculation test
  console.log("ISSUE #3: NODE-BASED TIMING VERIFICATION:");
  
  // Test advanced_logic.json for precise timing
  try {
    const advancedLogicPath = '../examples/advanced_logic.json';
    const advancedLogicData = fs.readFileSync(advancedLogicPath, 'utf8');
    const advancedResult = generator.generateSVA(advancedLogicData);
    
    if (advancedResult.success) {
      console.log("✅ Advanced logic test successful");
      
      // Debug: Show all generated properties for analysis
      console.log("\nDEBUG: All generated properties:");
      advancedResult.properties.forEach((prop, idx) => {
        console.log(`  ${idx + 1}. ${prop}`);
      });
      
      // Check for specific timing patterns expected from Issue #3
      const splinePatterns = advancedResult.properties.filter(prop => prop.includes('##[0:'));
      const exactPatterns = advancedResult.properties.filter(prop => prop.includes('##') && !prop.includes('['));
      const immediatePatterns = advancedResult.properties.filter(prop => 
        !prop.includes('##') && (prop.includes('|->') || prop.includes('->')));
      
      console.log(`- Spline patterns (##[0:n]): ${splinePatterns.length}`);
      splinePatterns.forEach(p => console.log(`    ${p}`));
      
      console.log(`- Exact timing patterns (##n): ${exactPatterns.length}`);
      exactPatterns.forEach(p => console.log(`    ${p}`));
      
      console.log(`- Immediate patterns (no ##): ${immediatePatterns.length}`);
      immediatePatterns.forEach(p => console.log(`    ${p}`));
      
      // Verify expected f~>g timing (should be ##[0:1])
      const enableToDataPattern = advancedResult.properties.find(prop => 
        prop.includes('enable') && prop.includes('data') && prop.includes('##[0:1]')
      );
      
      if (enableToDataPattern) {
        console.log("✅ f~>g timing correctly calculated as ##[0:1]");
      } else {
        console.log("❌ f~>g timing calculation incorrect");
        console.log("Expected: ##[0:1] pattern in enable to data property");
      }
      
      // Verify g->k immediate timing (should have no ##)
      const dataToValidPattern = advancedResult.properties.find(prop => 
        prop.includes('data') && prop.includes('valid') && !prop.includes('##')
      );
      
      if (dataToValidPattern) {
        console.log("✅ g->k timing correctly calculated as immediate");
      } else {
        console.log("❌ g->k timing calculation incorrect");
        console.log("Expected: immediate (no ##) pattern in data to valid property");
      }
      
      // Verify k-|>m exact timing (should be ##2)
      const validCleanupPattern = advancedResult.properties.find(prop => 
        prop.includes('valid') && prop.includes('##2')
      );
      
      if (validCleanupPattern) {
        console.log("✅ k-|>m timing correctly calculated as ##2");
      } else {
        console.log("❌ k-|>m timing calculation incorrect");
        console.log("Expected: ##2 pattern in valid cleanup property");
      }
      
      detailedResults.issue3NodeTiming = {
        implemented: true,
        splinePatterns: splinePatterns.length,
        exactPatterns: exactPatterns.length,
        immediatePatterns: immediatePatterns.length,
        enableToDataCorrect: !!enableToDataPattern,
        dataToValidCorrect: !!dataToValidPattern,
        validCleanupCorrect: !!validCleanupPattern
      };
      
    } else {
      console.log("❌ Advanced logic test failed");
      detailedResults.issue3NodeTiming = { implemented: false, error: advancedResult.error };
    }
  } catch (error) {
    console.log(`❌ Issue #3 test exception: ${error.message}`);
    detailedResults.issue3NodeTiming = { implemented: false, exception: error.message };
  }
  
  // Test Issue #3 dedicated test file
  console.log("\nISSUE #3 DEDICATED TEST:");
  try {
    const issue3TestData = fs.readFileSync('./pat/issue3_node_timing_test.json', 'utf8');
    const issue3Result = generator.generateSVA(issue3TestData);
    
    if (issue3Result.success) {
      console.log("✅ Issue #3 dedicated test successful");
      console.log(`Generated ${issue3Result.properties.length} properties`);
      
      // Check specific patterns expected from our dedicated test
      const adjacentSpline = issue3Result.properties.filter(prop => prop.includes('##[0:1]'));
      const longRangeSpline = issue3Result.properties.filter(prop => prop.includes('##[0:3]'));
      const exactOne = issue3Result.properties.filter(prop => prop.includes('##1'));
      const exactFour = issue3Result.properties.filter(prop => prop.includes('##4'));
      
      console.log(`- Adjacent spline (##[0:1]): ${adjacentSpline.length} found`);
      console.log(`- Long range spline (##[0:3]): ${longRangeSpline.length} found`);
      console.log(`- Exact 1 clock (##1): ${exactOne.length} found`);
      console.log(`- Exact 4 clock (##4): ${exactFour.length} found`);
      
      // Update detailed results
      detailedResults.issue3DedicatedTest = {
        success: true,
        adjacentSplineCount: adjacentSpline.length,
        longRangeSplineCount: longRangeSpline.length,
        exactOneCount: exactOne.length,
        exactFourCount: exactFour.length,
        totalProperties: issue3Result.properties.length
      };
      
    } else {
      console.log("❌ Issue #3 dedicated test failed");
      detailedResults.issue3DedicatedTest = { success: false, error: issue3Result.error };
    }
  } catch (error) {
    console.log(`❌ Issue #3 dedicated test exception: ${error.message}`);
    detailedResults.issue3DedicatedTest = { success: false, exception: error.message };
  }
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
